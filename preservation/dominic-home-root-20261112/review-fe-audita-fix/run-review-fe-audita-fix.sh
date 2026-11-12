#!/bin/sh
# Crossed-review runner for FE PR #64 (AuditA fix), dominic / chatgpt-proton.
# Launched by the formalization coordinator; run from inside the fresh clone.
export PATH=/root/.npm-global/bin:/root/.elan/bin:/usr/local/bin:/usr/bin:/bin
cd /root/review-fe-audita-fix || exit 1
codex exec -s workspace-write --add-dir /root "$(cat /root/review-fe-audita-fix-brief.md)" < /dev/null > /root/review-fe-audita-fix-codex.raw.log 2>&1
echo "CODEX_EXIT:$?" >> /root/review-fe-audita-fix-codex.raw.log
