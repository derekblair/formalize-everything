#!/bin/bash
# Review launcher — approvals ON, workspace-write sandbox.
# Deliberately NOT --dangerously-bypass-approvals-and-sandbox (safety flag,
# orchestrator 2026-11-05 10:53; that flag also skips the sandbox entirely).
# Method validated by probe 2026-11-05 ~11:32 PST and used for the #49/#50/#51
# re-review launches on bakkie: codex exec runs from inside a git repo with
# -s workspace-write --add-dir $HOME; any command needing approval outside
# the sandbox is DENIED, not auto-approved, and the lane must report that
# limitation in its report. --add-dir $HOME lets the lane write its report +
# evidence to $HOME as prior reviews did.
# DOMINIC variant: codex is the npm-global install at /root/.npm-global/bin/codex.
export PATH="/root/.npm-global/bin:$PATH"
rm -rf "$HOME/review-fe-pr59-codex"
git clone --branch books/rca-foundations https://github.com/derekblair/formalize-everything.git "$HOME/review-fe-pr59-codex" > "$HOME/review-fe-pr59-codex-clone.log" 2>&1 || exit 1
cd "$HOME/review-fe-pr59-codex" || exit 1
git rev-parse HEAD >> "$HOME/review-fe-pr59-codex-clone.log" 2>&1
codex exec -s workspace-write --add-dir /root "$(cat "$HOME/review-fe-pr59-brief.md")" < /dev/null > "$HOME/review-fe-pr59-codex.raw.log" 2>&1
echo "CODEX_EXIT:$?" >> "$HOME/review-fe-pr59-codex.raw.log"
