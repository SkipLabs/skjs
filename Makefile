PRETTIER_LOG_LEVEL?=warn

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
fmt-sk: # Keep in sync with bin/git_hooks/check_format.sh
	find . -name \*.sk | parallel skfmt -i {}

.PHONY: fmt-js
fmt-js: # Keep in sync with bin/git_hooks/check_format.sh
	npx prettier --log-level $(PRETTIER_LOG_LEVEL) --write .

.PHONY: fmt
fmt: fmt-sk fmt-js # Keep in sync with bin/git_hooks/check_format.sh

.PHONY: check-fmt
check-fmt:
	PRETTIER_LOG_LEVEL=debug ${MAKE} fmt
	if ! git diff --quiet --exit-code --ignore-submodules; then echo "make fmt changed some files:"; git diff --name-only; exit 1; fi

.PHONY: check-sh
check-sh:
	git ls-files "*.sh" | xargs shellcheck

.PHONY: clean
clean:
	skargo clean

# install the repo pre-commit hook locally
.git/hooks/pre-commit: bin/git_hooks/check_format.sh
	ln -s $(PWD)/bin/git_hooks/check_format.sh .git/hooks/pre-commit

.PHONY: setup-git-hooks
setup-git-hooks: .git/hooks/pre-commit
