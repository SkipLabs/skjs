
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
	if ! git diff --quiet --exit-code; then echo "make fmt changed some files:"; git status --porcelain; exit 1; fi
