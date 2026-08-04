#!/usr/bin/env bash
set -euo pipefail

MODULE_NAME="${1:-LeanCondensedMatter}"
ROOT_DIR="$(pwd)"
EXPORTER_DIR="$ROOT_DIR/_lean4export"
NANODA_DIR="$ROOT_DIR/_nanoda_lib"
EXPORT_FILE="$ROOT_DIR/_nanoda_export.txt"
CONFIG_FILE="$ROOT_DIR/_nanoda_config.json"

cleanup() {
  rm -rf "$EXPORTER_DIR" "$NANODA_DIR" "$EXPORT_FILE" "$CONFIG_FILE"
}
trap cleanup EXIT

if [[ -e "$EXPORTER_DIR" || -e "$NANODA_DIR" ]]; then
  echo "temporary nanoda directories already exist" >&2
  exit 1
fi

command -v cargo >/dev/null 2>&1 || {
  echo "cargo is required for the nanoda check" >&2
  exit 1
}

echo "Building lean4export with the project toolchain"
git clone --depth 1 https://github.com/leanprover/lean4export.git "$EXPORTER_DIR"
cp lean-toolchain "$EXPORTER_DIR/lean-toolchain"
(
  cd "$EXPORTER_DIR"
  lake build
)

echo "Building nanoda"
git clone --depth 1 --branch debug https://github.com/ammkrn/nanoda_lib.git "$NANODA_DIR"
(
  cd "$NANODA_DIR"
  cargo build --release
)

echo "Exporting Lean module: $MODULE_NAME"
lake env "$EXPORTER_DIR/.lake/build/bin/lean4export" "$MODULE_NAME" > "$EXPORT_FILE"

cat > "$CONFIG_FILE" <<EOF
{
  "export_file_path": "$EXPORT_FILE",
  "use_stdin": false,
  "permitted_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.trustCompiler"
  ],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
EOF

echo "Checking exported environment with nanoda"
"$NANODA_DIR/target/release/nanoda_bin" "$CONFIG_FILE"
