import Cslib.Crypto.Protocols.Commitment.Basic

/-!
# お題: コミットメント方式（cslib）の入口

解析の対象は cslib 側のモジュール `Cslib.Crypto.Protocols.Commitment.*`
（`Defs`: 方式の構文と正しさ、`Scheme`: 完全隠蔽・統計的隠蔽・完全拘束、
`Basic`: 隠蔽と拘束のトレードオフ）。宣言はそこに在る。

このファイルは `lake build Examples` でそれらのモジュールをビルドさせるための入口で、
宣言は持たない。解析は

    make all TARGET=Debug/Examples MODULES="Cslib.Crypto.Protocols.Commitment" ARGS="--import-all"

のように cslib 側のモジュール名を対象に指定する（`--import-all` はモジュールシステムの
対象で証明項まで読むため）。
-/
