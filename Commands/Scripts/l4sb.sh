#!/usr/bin/env bash
# ============================================================
# l4sb.sh — Lean4SemanticBench 展開コマンド
#
# 任意の Lake プロジェクトに解析用の衛星ワークスペースを生成し、
# decl_report → report.jsonl → 検査 → ビューア埋め込み までを一本化する。
# 使い方は `l4sb.sh help` または Commands/Scripts/README.md を参照。
#
# 原理(環境同一性):
#   decl_report は解析対象の olean を Lean.importModules (loadExts := true) で読む。
#   したがって「解析器を作った toolchain」=「対象をビルドした toolchain」、
#   「解析器が読む依存の実体」=「対象がビルドされた実体」でなければならない。
#   これを規約でなく構成で保証するため、対象の内側に衛星ワークスペース
#   <target>/.l4sb/ を生成する:
#     - lean-toolchain は対象から複写
#     - 対象パッケージをパス require(依存は対象の manifest から継承)
#     - packagesDir を対象側 .lake/packages に共有(mathlib 等の実体が一つになる)
#
# 依存の固定(禁止でなく検証):
#   衛星の依存は (a) 対象(パス) (b) 継承(対象 manifest のロック)
#   (c) importGraph(対象の依存木に無い場合のみ、対象 toolchain と同名の公式タグ)
#   の三種で、全てピン留めされている。manifest は公式の `lake update` に書かせ、
#   直後に「衛星と対象の両 manifest に現れる同名パッケージの rev が完全一致する」
#   ことを機械検査する。不一致なら復元を試みた上で必ず停止する。
#   黙って間違った環境を解析することは決してない。
#
# 出力の契約:
#   進捗・下請けコマンド(lake 等)の出力は全て stderr へ流す。
#   `report` の stdout は生成したレポートのパスただ一行
#   (`-- --minimal <宣言>` 透過時はそのテキストレポート)。
#   したがって `rep=$("$0" report <dir> <Mod>)` がそのまま成立する。
# ============================================================
set -euo pipefail

L4SB_VERSION="0.1.0"
PROG="$(basename "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd -- "$SCRIPT_DIR/../.." && pwd)"
GRAPH_DIR="$ROOT_DIR/Graph"
LIB_DIR="$SCRIPT_DIR/lib"
SAT_DIRNAME=".l4sb"
SAT_PKG_NAME="l4sbSatellite"

info() { echo "$PROG: $*" >&2; }
die()  { echo "$PROG: エラー: $*" >&2; exit 1; }

usage() {
  cat <<EOF
$PROG — Lean4SemanticBench 展開コマンド v$L4SB_VERSION

  $PROG init   <target-dir> [--force] [--import-graph-rev <rev>]
  $PROG report <target-dir> [<Module>...] [-o <out>] [--no-build] [--fetch-cache] [--import-all] [-- <decl_report 引数>]
  $PROG check  [<report.jsonl> | <target-dir>] [--decl <名前>...]
  $PROG web    [<report.jsonl> | <target-dir>]
  $PROG all    <target-dir> [report と同じ引数...]
  $PROG clean  <target-dir> [--purge]

  init    対象の内側に衛星ワークスペース <target>/$SAT_DIRNAME/ を生成する(冪等)
  report  対象をビルドし(=対象の .lake/build を更新する)、decl_report で
          report.jsonl + report.meta.json を生成する
  check   ldr_check.js でレポートの不変条件を検査する
  web     レポートをビューアへ埋め込む(Graph/Web/index.html を file:// で開くだけ)
  all     init → report → check → web を一括で行う(引数は report へ透過)
  clean   衛星を完全に削除する(対象には何も残らない)

詳細: Commands/Scripts/README.md
EOF
}

# ---------- preflight ----------
preflight() {
  command -v node >/dev/null 2>&1 || die "node が見つかりません(レポートの検査・埋め込みに利用します)"
  command -v lake >/dev/null 2>&1 || die "lake が見つかりません(elan を導入してください: https://leanprover-community.github.io/get_started.html)"
}

# ---------- 対象の解決と内省 ----------
resolve_target() {
  local t="$1"
  [ -d "$t" ] || die "対象ディレクトリがありません: $t"
  t="$(cd -- "$t" && pwd)"
  [ -f "$t/lean-toolchain" ] || die "lean-toolchain が見つかりません。Lake プロジェクトの根を指定してください: $t"
  echo "$t"
}

load_info() {  # $1 = target(絶対パス)。L4SB_* を設定する
  eval "$(node "$LIB_DIR/target_info.js" "$1")"
  [ -n "${L4SB_NAME:-}" ] || die "パッケージ名を検出できません(lakefile.toml / lakefile.lean / lake-manifest.json のいずれからも)"
  [ -n "${L4SB_TOOLCHAIN_TAG:-}" ] || die "toolchain を解釈できません: ${L4SB_TOOLCHAIN:-(空)}"
}

# ---------- ツール自身の鮮度 ----------
# 衛星はソース複写方式なので、Graph/LeanDeclReport の編集が反映されない罠がある。
# olean の鮮度(対象を先にビルドする)と同じ原理をツール自身にも適用する。
src_hash() {
  cat "$GRAPH_DIR/LeanDeclReport.lean" "$GRAPH_DIR/LeanDeclReport/"*.lean | sha256sum | cut -d' ' -f1
}

config_fingerprint() {  # $1 = importGraph rev。生成される lakefile.toml を決める入力の指紋
  printf '%s|%s|%s|%s|%s|%s' \
    "$L4SB_TOOLCHAIN" "$L4SB_NAME" "$L4SB_HAS_IMPORTGRAPH" "$L4SB_PKGDIR" "$1" "$L4SB_VERSION" \
    | sha256sum | cut -d' ' -f1
}

copy_sources() {  # $1 = sat
  cp "$GRAPH_DIR/LeanDeclReport.lean" "$1/"
  mkdir -p "$1/LeanDeclReport"
  cp "$GRAPH_DIR/LeanDeclReport/"*.lean "$1/LeanDeclReport/"
}

# ---------- TOML へ埋め込む値の検証 ----------
# TOML は不活性なデータだが、壊れた値の検出を parse エラー任せにせず、
# 文書に入る前(生成時)に止める。
check_ident() {  # $1 = ラベル, $2 = 値(パッケージ名・リビジョン)
  case "$2" in
    ""|*[!A-Za-z0-9_.-]*)
      die "$1 を TOML へ安全に埋め込めません(許可: 英数と _ . -): '$2'" ;;
  esac
}
check_relpath() {  # $1 = ラベル, $2 = 相対パス(packagesDir)
  case "$2" in
    ""|*[!A-Za-z0-9_./-]*)
      die "$1 を TOML へ安全に埋め込めません(許可: 英数と _ . / -): '$2'" ;;
  esac
}

# 衛星 lakefile は「コードではなくデータ」なので TOML で生成する。
# 必要だった唯一の分岐(importGraph の要否)は生成時点で確定している。
write_satellite_lakefile() {  # $1 = sat, $2 = importGraph rev
  local sat="$1" ig="$2"
  {
    echo "# 自動生成 ($PROG init v$L4SB_VERSION)。編集しないでください。"
    echo "# 作り直す:  $PROG init <target-dir> --force"
    echo "name = \"$SAT_PKG_NAME\""
    echo 'defaultTargets = ["decl_report"]'
    echo '# 対象と依存の実体を共有する。解析器が読む mathlib 等と、対象が検査された'
    echo '# mathlib 等が同一実体になる(環境同一性)。'
    echo "packagesDir = \"../$L4SB_PKGDIR\""
    echo ''
    echo '[[require]]'
    echo "name = \"$L4SB_NAME\""
    echo 'path = ".."'
    if [ "$L4SB_HAS_IMPORTGRAPH" != "1" ]; then
      echo ''
      echo '# 対象の依存木に importGraph が無いため、対象 toolchain と同名の公式タグで取得する'
      echo '[[require]]'
      echo 'name = "importGraph"'
      echo 'git = "https://github.com/leanprover-community/import-graph"'
      echo "rev = \"$ig\""
    fi
    echo ''
    echo '[[lean_lib]]'
    echo 'name = "LeanDeclReport"'
    echo ''
    echo '[[lean_exe]]'
    echo 'name = "decl_report"'
    echo 'root = "LeanDeclReport.Main"'
    echo 'supportInterpreter = true'
  } > "$sat/lakefile.toml"
}

# stamp は 3 行: 構成指紋 / ソースハッシュ / 採用した importGraph rev。
# rev を永続化するのは、report からの自動 init が
# `init --import-graph-rev X` での明示指定を黙って上書きしないため。
write_stamp() {  # $1 = sat, $2 = cfg, $3 = src, $4 = ig_rev
  printf '%s\n%s\n%s\n' "$2" "$3" "$4" > "$1/.l4sb-stamp"
}

# importGraph 公式タグの自動解決に失敗したときの退避候補(元の rev は含まない)。
#   1. -rcN を落とす(rc タグ未発行の期間がある)
#   2. パッチを落とす vX.Y.Z → vX.Y.0
#      import-graph はパッチ版タグを発行しない(v4.32.1 / v4.33.1 等の不在を
#      2026-09 に実確認)。パッチ版 toolchain とはソース互換なので vX.Y.0 で代替する。
ig_fallback_tags() {  # $1 = 失敗した rev
  local base="${1%%-rc*}"
  if [ "$base" != "$1" ]; then echo "$base"; fi
  if [[ "$base" =~ ^v([0-9]+)\.([0-9]+)\.([1-9][0-9]*)$ ]]; then
    echo "v${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.0"
  fi
  true
}

# ---------- init ----------
cmd_init() {
  local target="" force=0 igrev=""
  while [ $# -gt 0 ]; do
    case "$1" in
      --force) force=1; shift ;;
      --import-graph-rev) igrev="${2:?--import-graph-rev には値が必要です}"; shift 2 ;;
      -*) die "init: 不明なオプション: $1" ;;
      *) [ -z "$target" ] || die "init: 対象は一つだけ指定してください"; target="$1"; shift ;;
    esac
  done
  [ -n "$target" ] || die "init: 対象ディレクトリを指定してください"
  preflight
  target="$(resolve_target "$target")"
  load_info "$target"

  # 衛星は解析器のモジュール群(LeanDeclReport.*)を対象と同じワークスペースへ
  # 持ち込むため、対象自身が同名モジュールを提供していると Lake がモジュールの
  # 曖昧性で停止する(自己解析がこの典型)。誤誘導なエラーで落ちる前に、
  # 原因と正しい代替(衛星を使わない直接実行)を明示して止める。
  case " ${L4SB_LIBS:-} " in
    *" LeanDeclReport "*)
      die "対象がモジュール LeanDeclReport を提供しており、衛星の解析器と衝突します。自己解析は開発ワークスペースで直接実行してください: cd Graph && lake build decl_report && lake env .lake/build/bin/decl_report <Module> > report.jsonl" ;;
  esac

  local sat="$target/$SAT_DIRNAME"

  # importGraph のリビジョン(対象の依存木に居れば継承するので require 自体を生成しない)。
  # 決定順序: 明示指定 > 既存衛星が採用済みの rev(stamp 3 行目)
  #           > toolchain と同名の公式タグ(v4.33.0-rc1 / v4.30.0 で 1:1 を実確認済み)
  local ig_rev
  if [ -n "$igrev" ]; then
    ig_rev="$igrev"
  elif [ -f "$sat/.l4sb-stamp" ] && [ -n "$(sed -n '3p' "$sat/.l4sb-stamp")" ]; then
    ig_rev="$(sed -n '3p' "$sat/.l4sb-stamp")"
  else
    ig_rev="$L4SB_TOOLCHAIN_TAG"
  fi

  # 埋め込む値を生成前に検証する(壊れた値は文書に入る前に止める)
  check_ident "パッケージ名" "$L4SB_NAME"
  check_relpath "packagesDir" "$L4SB_PKGDIR"
  [ "$L4SB_HAS_IMPORTGRAPH" = "1" ] || check_ident "importGraph リビジョン" "$ig_rev"

  local want_src want_cfg
  want_src="$(src_hash)"
  want_cfg="$(config_fingerprint "$ig_rev")"

  if [ -d "$sat" ] && [ "$force" -eq 0 ] && [ -f "$sat/.l4sb-stamp" ]; then
    local have_cfg have_src
    have_cfg="$(sed -n '1p' "$sat/.l4sb-stamp")"
    have_src="$(sed -n '2p' "$sat/.l4sb-stamp")"
    if [ "$have_cfg" = "$want_cfg" ]; then
      if [ "$have_src" = "$want_src" ]; then
        info "既存の衛星を再利用します: $sat"
        return 0
      fi
      # 構成は同じでソースだけ更新された → 複写だけやり直す(ビルド資産は温存)
      info "解析器のソース更新を検出。衛星へ再複写します"
      copy_sources "$sat"
      write_stamp "$sat" "$want_cfg" "$want_src" "$ig_rev"
      return 0
    fi
    info "構成の変更(toolchain 等)を検出。衛星を再生成します"
  fi

  rm -rf "$sat"
  mkdir -p "$sat"
  printf '*\n' > "$sat/.gitignore"          # 生成物。対象のリポジトリを汚さない
  cp "$target/lean-toolchain" "$sat/lean-toolchain"
  copy_sources "$sat"

  write_satellite_lakefile "$sat" "$ig_rev"
  write_stamp "$sat" "$want_cfg" "$want_src" "$ig_rev"

  # manifest は公式の lake update に書かせる(手書き導出はスキーマ変遷に脆い)。
  # 衛星の依存は全てピン留めされているので、これは冪等のはずである —— が、
  # その仮定に依存せず、直後の事後検証で必ず確かめる。
  info "依存を解決します (lake update)"
  local resolved=0
  if ( cd "$sat" && lake update ) >&2; then
    resolved=1
  elif [ "$L4SB_HAS_IMPORTGRAPH" != "1" ] && [ -z "$igrev" ]; then
    # 公式タグの自動解決の退避(rc 落とし → パッチ落とし)。
    # lakefile は sed で書き換えず再生成し、成功したら stamp も採用 rev で
    # 書き直す(指紋と実内容の乖離を作らない)。
    local cand
    for cand in $(ig_fallback_tags "$ig_rev"); do
      info "importGraph のタグ $ig_rev の解決に失敗。$cand で再試行します"
      write_satellite_lakefile "$sat" "$cand"
      if ( cd "$sat" && lake update ) >&2; then
        ig_rev="$cand"
        want_cfg="$(config_fingerprint "$ig_rev")"
        write_stamp "$sat" "$want_cfg" "$want_src" "$ig_rev"
        resolved=1
        break
      fi
    done
  fi
  [ "$resolved" -eq 1 ] || die "依存の解決に失敗しました (lake update)。--import-graph-rev で明示指定できます"

  verify_identity "$target" "$sat"
  info "衛星ワークスペースを生成しました: $sat"
}

# 事後検証: 衛星と対象の両 manifest に現れる同名パッケージの rev が完全一致すること。
# 不一致が出た場合、共有 packagesDir が動かされた可能性があるので、対象側の
# ロックへ checkout で復元を試みた上で、必ず停止する。
verify_identity() {  # $1 = target, $2 = sat
  local target="$1" sat="$2" out rc=0
  out="$(node "$LIB_DIR/verify_manifest.js" "$target" "$sat")" || rc=$?
  local kind name rev_target rev_sat
  while IFS=' ' read -r kind name rev_target rev_sat; do
    case "$kind" in
      MISMATCH)
        info "リビジョン不一致: $name (対象 $rev_target / 衛星 $rev_sat)"
        if [ -d "$target/$L4SB_PKGDIR/$name/.git" ]; then
          info "  → 対象側のロック $rev_target へ復元を試みます"
          git -C "$target/$L4SB_PKGDIR/$name" checkout --quiet "$rev_target" \
            || info "  → 復元に失敗しました。手動確認が必要です: $target/$L4SB_PKGDIR/$name"
        fi
        ;;
      EXTRA)
        info "衛星のみの依存(検査対象外): $name @ ${rev_target:-?}" ;;
    esac
  done <<< "$out"
  [ "$rc" -eq 0 ] || die "環境同一性の検証に失敗しました。この状態では解析結果が対象の実体と食い違うため中断します。'$PROG init <target> --force' で再生成してください"
}

# ---------- report ----------
# stdout はレポートのパスただ一行(--minimal 透過時はそのテキスト)。
# lake などの下請けの出力は全て stderr へ流す。
cmd_report() {
  local target="" out="" nobuild=0 fetchcache=0
  local -a mods=() pass=()
  # `--` 以降は decl_report へそのまま透過する(引数文法を二重実装しない)。
  # 追記(+=)にすること: 代入だと --import-all 等の先行フラグを上書きしてしまう。
  while [ $# -gt 0 ]; do
    case "$1" in
      --) shift; pass+=("$@"); break ;;
      -o) out="${2:?-o には出力先が必要です}"; shift 2 ;;
      --no-build) nobuild=1; shift ;;
      --fetch-cache) fetchcache=1; shift ;;
      # モジュールシステムの対象で証明等の非公開情報まで読む(主要フラグなので
      # -- の奥に隠さず第一級で受け、decl_report へ透過する)
      --import-all) pass+=("--import-all"); shift ;;
      -*) die "report: 不明なオプション: $1 (decl_report への引数は -- の後に置いてください)" ;;
      *) if [ -z "$target" ]; then target="$1"; else mods+=("$1"); fi; shift ;;
    esac
  done
  [ -n "$target" ] || die "report: 対象ディレクトリを指定してください"
  preflight
  target="$(resolve_target "$target")"
  load_info "$target"
  cmd_init "$target"          # 衛星が無い/古い場合はここで整う(冪等)
  local sat="$target/$SAT_DIRNAME"

  if [ ${#mods[@]} -eq 0 ]; then
    # 既定値は lakefile の lean_lib 名。lib 名と import 可能なモジュール名が
    # 一致しない構成(root 指定・glob)もあるため、これはあくまで既定値であり
    # 明示指定が正である(README 参照)。
    read -r -a mods <<< "${L4SB_LIBS:-}"
    [ ${#mods[@]} -gt 0 ] || die "解析対象モジュールを指定してください(lakefile から lean_lib を検出できませんでした)"
    info "モジュール未指定のため lean_lib から推定: ${mods[*]}"
  fi

  # (1) 対象を先にビルドする。decl_report が読むのは olean であってソースではない。
  #     ソース編集直後に走らせると「古い環境の解析結果」という嘘が出る。
  if [ "$nobuild" -eq 1 ]; then
    info "--no-build: olean が最新であることは利用者の保証に委ねます(古いと結果も古い)"
  else
    # mathlib 依存の対象では、先にビルド済みキャッシュを取得する(標準作法)。
    # これが無いと fresh clone で mathlib のソースフルビルド(数時間)になる。
    # 毎回ネットワークを叩かないよう、取得は衛星ごとに一度だけ自動で行い
    # (成功印 .l4sb-cache-got)、以後は --fetch-cache で明示する。
    # 取得に失敗しても続行する — 正は常に直後の lake build。
    if [ "${L4SB_HAS_MATHLIB:-0}" = "1" ]; then
      if [ "$fetchcache" -eq 1 ] || [ ! -f "$sat/.l4sb-cache-got" ]; then
        info "mathlib 依存の対象です。ビルドキャッシュを取得します (lake exe cache get)"
        if ( cd "$target" && lake exe cache get ) >&2; then
          touch "$sat/.l4sb-cache-got"
        else
          info "キャッシュ取得に失敗しました(続行して通常ビルドします)"
        fi
      fi
    fi
    # 並列数は Lake に任せる(Lake 5.0.0 / v4.35.0 の `lake build` には並列数のオプションが無い。
    # `-j` を渡して「unknown short option」で CI が止まった。実測)。
    info "対象をビルドします: ${mods[*]}"
    if ! ( cd "$target" && lake build "${mods[@]}" ) >&2; then
      info "指定名でのビルドに失敗。既定ターゲットで再試行します (lake build)"
      ( cd "$target" && lake build ) >&2 \
        || die "対象のビルドに失敗しました(古い olean を解析しないため中断します)"
    fi
  fi

  # (2) 解析器を対象と同一環境でビルドし、(3) lake env で直接実行する。
  #     ビルドと実行を分離することで、解析器の stdout(JSONL)に
  #     ビルド系の出力が混ざる余地を構造的に無くす。
  info "解析器をビルドします"
  ( cd "$sat" && lake build decl_report ) >&2 \
    || die "解析器のビルドに失敗しました。対象の toolchain ($L4SB_TOOLCHAIN) が本ツールの対応範囲外の可能性があります"
  local bin="$sat/.lake/build/bin/decl_report"
  [ -x "$bin" ] || die "解析器の実行ファイルが見つかりません: $bin"

  # --minimal はテキストレポートなので JSONL に落とさず標準出力へ
  local is_minimal=0 a
  for a in ${pass[@]+"${pass[@]}"}; do [ "$a" = "--minimal" ] && is_minimal=1; done
  # 実行失敗時のヒント: TOML の未知キーは黙って無視されるため、もし対象 toolchain で
  # `supportInterpreter` が TOML 未対応なら、ここで初めて露見する(生成 lakefile の
  # .lean 化が必要になる)。黙って通り抜けることはなく、必ずこの地点で停止する。
  local run_hint="解析の実行に失敗しました。モジュール名を確認してください。インタプリタ関連のエラーの場合は、対象 toolchain で TOML の supportInterpreter が有効か疑ってください(README の反証条項)"
  if [ "$is_minimal" -eq 1 ]; then
    info "最小仮定レポート(テキスト)を出力します"
    ( cd "$sat" && lake env "$bin" "${mods[@]}" ${pass[@]+"${pass[@]}"} ) || die "$run_hint"
    return 0
  fi

  local report="$sat/report.jsonl"
  info "解析を実行します: decl_report ${mods[*]}${pass[0]:+ ${pass[*]}}"
  ( cd "$sat" && lake env "$bin" "${mods[@]}" ${pass[@]+"${pass[@]}"} > report.jsonl ) \
    || die "$run_hint"
  [ -s "$report" ] || die "レポートが空です(モジュール名が正しいか確認してください: ${mods[*]})"
  # 事後検証: 全行が name を持つ JSON であること。stdout 汚染・部分書き込みの
  # 有無を議論でなく機械検査で潰す(check を経ない素の report でも保証する)。
  node -e '
    const fs = require("fs");
    const lines = fs.readFileSync(process.argv[1], "utf8").split("\n").filter((l) => l.trim());
    let bad = 0;
    lines.forEach((l, i) => {
      try { if (!JSON.parse(l).name) throw 0; }
      catch { console.error(`  ${i + 1} 行目が JSON として不正です`); bad = 1; }
    });
    process.exit(bad);
  ' "$report" || die "生成された JSONL に不正な行があります(stdout 汚染・部分書き込みの疑い)"

  # 来歴サイドカー。ベンチとして比較可能にするため、何をいつどの環境で
  # 解析したかを機械可読で残す(本体 JSONL の決定的順序には手を触れない)。
  # 絶対パスは記録しない(公開共有時のローカル情報漏れ。名前+rev で同定は足りる)。
  # 作業ツリーが dirty なら旗を立てる — dirty のとき gitRev 単独では嘘になるため。
  local tool_rev target_rev target_dirty=""
  tool_rev="$(git -C "$ROOT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown)"
  target_rev="$(git -C "$target" rev-parse HEAD 2>/dev/null || echo "")"
  if [ -n "$target_rev" ] && [ -n "$(git -C "$target" status --porcelain 2>/dev/null)" ]; then
    target_dirty=1
  fi
  L4SB_M_TOOLVER="$L4SB_VERSION+$tool_rev" \
  L4SB_M_TARGET="$L4SB_NAME" L4SB_M_TARGETREV="$target_rev" \
  L4SB_M_DIRTY="$target_dirty" \
  L4SB_M_TOOLCHAIN="$L4SB_TOOLCHAIN" L4SB_M_MODULES="${mods[*]}" \
  L4SB_M_EXTRA="${pass[*]:-}" \
  L4SB_M_REPORT="$report" \
  node -e '
    const fs = require("fs"), e = process.env;
    const text = fs.readFileSync(e.L4SB_M_REPORT, "utf8");
    const lines = text.split("\n").filter((l) => l.trim());
    const meta = {
      tool: "Lean4SemanticBench", version: e.L4SB_M_TOOLVER,
      target: { name: e.L4SB_M_TARGET,
                gitRev: e.L4SB_M_TARGETREV || null,
                // dirty: rev の指すコミットに未反映の変更がある(再現性の限定)
                dirty: e.L4SB_M_DIRTY === "1",
                toolchain: e.L4SB_M_TOOLCHAIN },
      modules: e.L4SB_M_MODULES.split(" "),
      // decl_report への透過引数(--values 等はレポート内容に影響する入力)
      extraArgs: e.L4SB_M_EXTRA ? e.L4SB_M_EXTRA.split(" ") : [],
      generatedAt: new Date().toISOString(),
      declCount: lines.length, bytes: Buffer.byteLength(text),
    };
    fs.writeFileSync(e.L4SB_M_REPORT.replace(/\.jsonl$/, ".meta.json"),
                     JSON.stringify(meta, null, 2) + "\n");
  '

  local n
  n="$(grep -c . "$report" || true)"
  info "report.jsonl: $n 行 ($(du -h "$report" | cut -f1)) / 来歴: report.meta.json"
  if [ -n "$out" ]; then
    cp "$report" "$out"
    [ -f "${report%.jsonl}.meta.json" ] && cp "${report%.jsonl}.meta.json" "${out%.jsonl}.meta.json"
    info "複写しました: $out"
  fi
  echo "$report"
}

# ---------- report パスの解決(check / web 共通) ----------
resolve_report() {  # 引数: パス(report.jsonl か対象ディレクトリ)。空なら Graph/report.jsonl
  local r="${1:-}"
  if [ -z "$r" ]; then echo "$GRAPH_DIR/report.jsonl"; return; fi
  if [ -d "$r" ]; then
    [ -f "$r/$SAT_DIRNAME/report.jsonl" ] && { echo "$r/$SAT_DIRNAME/report.jsonl"; return; }
    die "レポートが見つかりません: $r/$SAT_DIRNAME/report.jsonl (先に '$PROG report $r' を実行してください)"
  fi
  echo "$r"
}

# ---------- check ----------
cmd_check() {
  preflight
  local report=""
  local -a rest=()
  while [ $# -gt 0 ]; do
    case "$1" in
      --decl) shift; rest+=("--decl" "$@"); break ;;
      -*) rest+=("$1"); shift ;;
      *) [ -z "$report" ] || die "check: レポートは一つだけ指定してください"; report="$1"; shift ;;
    esac
  done
  report="$(resolve_report "$report")"
  [ -f "$report" ] || die "レポートがありません: $report"
  node "$GRAPH_DIR/ldr_check.js" "$report" ${rest[@]+"${rest[@]}"}
}

# ---------- web ----------
# ビューアは file:// で開くだけで動く設計(Graph/README 参照)。
# ここでやるのはレポートの埋め込み(make_default_report.js)と、開くパスの提示だけ。
cmd_web() {
  preflight
  [ $# -le 1 ] || die "web: 引数はレポート(または対象ディレクトリ)一つだけです"
  local report="${1:-}"
  if [ -n "$report" ]; then
    report="$(resolve_report "$report")"
    [ -f "$report" ] || die "レポートがありません: $report"
    if [ "$report" != "$GRAPH_DIR/report.jsonl" ]; then
      cp "$report" "$GRAPH_DIR/report.jsonl"
      if [ -f "${report%.jsonl}.meta.json" ]; then
        cp "${report%.jsonl}.meta.json" "$GRAPH_DIR/report.meta.json"
      else
        # 来歴の無いレポートに、以前の別レポートの来歴が付いて「嘘」になるのを防ぐ。
        # meta なしは「来歴表示なし」という正直な状態に落とす。
        rm -f "$GRAPH_DIR/report.meta.json"
      fi
    fi
  fi
  [ -s "$GRAPH_DIR/report.jsonl" ] || die "Graph/report.jsonl がありません。'$PROG web <report.jsonl | target-dir>' で渡してください"
  node "$GRAPH_DIR/make_default_report.js" "$GRAPH_DIR/report.jsonl" >&2
  info "ブラウザで開く: file://$GRAPH_DIR/Web/index.html"
}

# ---------- all ----------
cmd_all() {
  [ $# -ge 1 ] || die "all: 対象ディレクトリを指定してください"
  local target
  target="$(resolve_target "$1")"; shift
  cmd_init "$target"
  cmd_report "$target" "$@" >&2      # パスは下で決定的に求まるので捕獲しない
  local report="$target/$SAT_DIRNAME/report.jsonl"
  local check_rc=0
  cmd_check "$report" || check_rc=$?
  cmd_web "$report"
  if [ "$check_rc" -ne 0 ]; then
    info "注意: ldr_check が失敗を報告しています(レポート自体は生成済み)"
    return "$check_rc"
  fi
}

# ---------- clean ----------
# 既定は衛星のみ削除。--purge を付けると、衛星が共有 packagesDir へ持ち込んだ
# 「対象の manifest に無いパッケージ」(依存ゼロの対象での importGraph / Cli 等)
# も削除する。既定で残すのは、再解析時の再クローンを省くキャッシュとして
# 有用なため。判定は verify_manifest の EXTRA(対象に無い git 依存)を流用する。
cmd_clean() {
  local target="" purge=0
  while [ $# -gt 0 ]; do
    case "$1" in
      --purge) purge=1; shift ;;
      -*) die "clean: 不明なオプション: $1" ;;
      *) [ -z "$target" ] || die "clean: 対象は一つだけ指定してください"; target="$1"; shift ;;
    esac
  done
  [ -n "$target" ] || die "clean: 対象ディレクトリを指定してください"
  target="$(resolve_target "$target")"
  local sat="$target/$SAT_DIRNAME"
  [ -e "$sat" ] || { info "衛星はありません: $sat"; return 0; }
  # 生成物であることを確認してから消す(自分の印が無いディレクトリは消さない)
  [ -f "$sat/.l4sb-stamp" ] || die "$sat に $PROG の生成印がありません。手動で確認してください"

  local -a extras=()
  if [ "$purge" -eq 1 ] && [ -f "$sat/lake-manifest.json" ]; then
    load_info "$target"
    local line kind name rest
    while IFS=' ' read -r kind name rest; do
      [ "$kind" = "EXTRA" ] && extras+=("$name")
    done < <(node "$LIB_DIR/verify_manifest.js" "$target" "$sat" || true)
  fi

  rm -rf "$sat"
  info "削除しました: $sat"

  for name in ${extras[@]+"${extras[@]}"}; do
    local pdir="$target/$L4SB_PKGDIR/$name"
    if [ -d "$pdir" ]; then
      rm -rf "$pdir"
      info "purge: 衛星が持ち込んだ共有パッケージを削除しました: $pdir"
    fi
  done
}

# ---------- dispatcher ----------
case "${1:-help}" in
  init)    shift; cmd_init "$@" ;;
  report)  shift; cmd_report "$@" ;;
  check)   shift; cmd_check "$@" ;;
  web)     shift; cmd_web "$@" ;;
  all)     shift; cmd_all "$@" ;;
  clean)   shift; cmd_clean "$@" ;;
  version) echo "$PROG $L4SB_VERSION" ;;
  help|-h|--help) usage ;;
  *) die "不明なサブコマンド: $1 ('$PROG help' で使い方を表示)" ;;
esac
