#!/bin/bash

# commit-msg hook: a commit that changes verification/ carries a commit
# record (.claude/skills/review/SKILL.md): trailers git can parse, with
# Outcome and Parts, and Trust unless the outcome is no-behaviour-change.

exec 1>&2

message_file=$1
git_dir=$(git rev-parse --git-dir)

# a merge commit has no record of its own
if [[ -f "$git_dir/MERGE_HEAD" ]]; then
    exit 0
fi

# only commits that change verification/ need a record; a reword changes no files
if ! git diff --cached --name-only | grep -q '^verification/'; then
    exit 0
fi

trailers=$(grep -v '^#' "$message_file" | git interpret-trailers --parse)
value () {
    printf '%s\n' "$trailers" | sed -n "s/^$1: //p" | head -n 1
}

outcome=$(value Outcome)
problems=()
case "$outcome" in
    verified|refused|gap|no-behaviour-change) ;;
    "") problems+=("no 'Outcome:' trailer") ;;
    *) problems+=("Outcome '$outcome' is not one of verified, refused, gap, no-behaviour-change") ;;
esac
if [[ -z "$(value Parts)" ]]; then
    problems+=("no 'Parts:' trailer")
fi
if [[ "$outcome" != "no-behaviour-change" && -z "$(value Trust)" ]]; then
    problems+=("no 'Trust:' trailer (write 'Trust: none' when nothing new is trusted)")
fi

if (( ${#problems[@]} )); then
    echo "This commit changes verification/ and its message is not a commit record:"
    for p in "${problems[@]}"; do
        echo "  - $p"
    done
    echo "Format: .claude/skills/review/SKILL.md. The trailers are the last block of"
    echo "the message, one 'Key: value' per line; git interpret-trailers --parse reads them."
    exit 1
fi
