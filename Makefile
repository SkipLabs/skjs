PRETTIER_LOG_LEVEL?=warn
PRETTIER_VERSION:=$(shell jq -r '.devDependencies.prettier' package.json)

.PHONY: check
check:
	skargo check

.PHONY: build
build:
	skargo build

JUNITXML_FLAGS=$(if $(JUNITXML),--junitxml $(JUNITXML))

.PHONY: test
test:
	skargo test $(JUNITXML_FLAGS)
	./tests/test_incremental.sh
	./tests/test_affected_files.sh
	./tests/test_stdin.sh
	./tests/test_config_change.sh

# Run only the CFG expectation tests (UPDATE_EXPECT=1 to regenerate expectations)
.PHONY: test-cfg
test-cfg:
	skargo test testCFG

.PHONY: fmt-sk
fmt-sk: # Keep in sync with bin/git_hooks/check_format.sh
	find . -name \*.sk | parallel skfmt -i {}

.PHONY: fmt-js
fmt-js: # Keep in sync with bin/git_hooks/check_format.sh
	npx -y prettier@$(PRETTIER_VERSION) --log-level $(PRETTIER_LOG_LEVEL) --write .

.PHONY: fmt
fmt: fmt-sk fmt-js # Keep in sync with bin/git_hooks/check_format.sh

.PHONY: check-fmt
check-fmt:
	PRETTIER_LOG_LEVEL=debug ${MAKE} fmt
	if ! git diff --quiet --exit-code --ignore-submodules; then echo "make fmt changed some files:"; git diff --name-only; exit 1; fi

.PHONY: check-sh
check-sh:
	git ls-files "*.sh" | xargs shellcheck

# Docker targets: run skargo commands inside the Skip Docker image.
# Override DOCKER_IMAGE or SKIP_DIR if needed:
#   make test-in-docker SKIP_DIR=/path/to/skip
#   make test-in-docker DOCKER_IMAGE=skiplabs/skip:0.1.0
# When running inside a devcontainer, commands run directly (no docker).
DOCKER_IMAGE?=skiplabs/skip:latest
SKIP_DIR?=$(CURDIR)/../skip

DOCKER_ENV_FLAGS=$(if $(UPDATE_EXPECT),-e UPDATE_EXPECT=$(UPDATE_EXPECT))

ifdef DEVCONTAINER
  DOCKER_RUN =
else
  DOCKER_RUN = docker run --rm $(DOCKER_ENV_FLAGS) -v "$(CURDIR):/work/skjs" -v "$(SKIP_DIR):/work/skip" -w /work/skjs $(DOCKER_IMAGE)
endif

.PHONY: test-in-docker
test-in-docker:
	$(DOCKER_RUN) make test

.PHONY: test-cfg-in-docker
test-cfg-in-docker:
	$(DOCKER_RUN) make test-cfg

%-in-docker:
	$(DOCKER_RUN) skargo $*

.PHONY: check-file-in-docker
check-file-in-docker:
	: $${FILE:?Usage: make check-file-in-docker FILE=path/to/file.ts [BIN=target/host/dev/skjs]}
	$(DOCKER_RUN) $(if $(BIN),$(BIN),skargo run --) check --import-stubs import-stubs "$(FILE)"

.PHONY: clean
clean:
	skargo clean

# install the repo pre-commit hook locally
.git/hooks/pre-commit: bin/git_hooks/check_format.sh
	ln -s $(PWD)/bin/git_hooks/check_format.sh .git/hooks/pre-commit

.PHONY: setup-git-hooks
setup-git-hooks: .git/hooks/pre-commit
