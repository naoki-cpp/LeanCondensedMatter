#!/usr/bin/env bash
set -euo pipefail

# leanprover/lean-action v1 runs its unconditional elan-init.sh installer
# through curl without retry flags. On GitHub-hosted runners the elan release
# asset endpoint can transiently return HTTP 503 or 504, failing otherwise
# valid builds and compiled checks before Lean starts.
#
# Put a narrowly scoped curl wrapper ahead of the system binary for subsequent
# workflow steps. The wrapper executes the real curl with bounded retries,
# preserving all other arguments and curl's exit status.
wrapper_dir="${RUNNER_TEMP:?}/lean-action-curl-retry"
mkdir -p "$wrapper_dir"
cat > "$wrapper_dir/curl" <<'EOF'
#!/usr/bin/env bash
exec /usr/bin/curl --retry 6 --retry-all-errors --retry-delay 3 --connect-timeout 20 "$@"
EOF
chmod +x "$wrapper_dir/curl"
echo "$wrapper_dir" >> "${GITHUB_PATH:?}"
