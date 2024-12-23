.PHONY: hlint-fix hlint test build

HS_FILES := $(shell git ls-files | grep '.hs')

build:
	stack build

hlint-fix: $(HS_FILES)
	@for file in $^; do \
	echo "linting $$file"; \
	hlint $$file --refactor --refactor-options="--inplace --step"; \
	done

hlint: $(HS_FILES)
	@hlint $^

test:
	stack test --ta "--hide-successes"

