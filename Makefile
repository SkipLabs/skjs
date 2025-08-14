.PHONY: check
check:
	skargo check

.PHONY: build
build:
	skargo build

.PHONY: test
test:
	skargo test

.PHONY: fmt-sk
fmt-sk:
	find . -name \*.sk | parallel skfmt -i {}

.PHONY: fmt
fmt: fmt-sk

.PHONY: check-fmt
check-fmt:
	${MAKE} fmt
	if ! git diff --quiet --exit-code --ignore-submodules; then echo "make fmt changed some files:"; git diff --name-only; exit 1; fi

.PHONY: check-sh
check-sh:
	git ls-files "*.sh" | xargs shellcheck

.PHONY: clean
clean:
	skargo clean
