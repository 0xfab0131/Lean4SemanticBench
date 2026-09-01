# Lean4SemanticBench — 利用者向けの入口
#
# 実体は Commands/Scripts/l4sb.sh。個別の段階(init / report / check / web)や
# 詳細な引数はそちらを直接使う(`make help` が一覧を表示する)。
#
#   make all TARGET=path/to/Project [MODULES="ModA ModB"] [ARGS=...]
#   make clean-sat TARGET=...        対象内の衛星 .l4sb/ を削除
#
# 開発用(解析器のビルド・スクリプト検査)は Makefile.dev にある。

L4SB    := Commands/Scripts/l4sb.sh
TARGET  ?= Debug/Examples
MODULES ?=
ARGS    ?=

.DEFAULT_GOAL := help
.PHONY: help all clean-sat

help:
	@$(L4SB) help
	@echo ""
	@echo "Makefile 変数:  TARGET=$(TARGET)  MODULES='$(MODULES)'  ARGS='$(ARGS)'"
	@echo "例:  make all TARGET=Debug/Examples"

all:
	$(L4SB) all $(TARGET) $(MODULES) $(ARGS)

clean-sat:
	$(L4SB) clean $(TARGET)
