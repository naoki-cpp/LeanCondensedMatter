"""Check repository-relative Markdown link paths (no network or anchor validation)."""

import argparse
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit


FENCE = re.compile(r"^\s{0,3}(\x60{3,}|~{3,})(.*)$")
INLINE_CODE = re.compile(r"(?<!\x60)(\x60+)(?!\x60).*?(?<!\x60)\1(?!\x60)")
DESTINATION = r"(?:<([^>\n]+)>|([^\s()<>]+))"
INLINE_LINK = re.compile(r"\[[^\]\n]*\]\(\s*" + DESTINATION +
                         r"""(?:\s+(?:"[^"]*"|'[^']*'))?\s*\)""")
REFERENCE = re.compile(r"^\s{0,3}\[(?!\^)[^\]]+\]:\s*" + DESTINATION)


def destinations(document):
    """Yield line numbers and paths for simple inline links and reference definitions.

    Fenced code and inline code are excluded. This is a deliberately limited
    Markdown path audit, not a general Markdown parser.
    """
    fence = None
    for number, line in enumerate(document.splitlines(), 1):
        marker = FENCE.match(line)
        if fence is not None:
            if (marker and marker[1][0] == fence[0] and
                    len(marker[1]) >= len(fence) and not marker[2].strip()):
                fence = None
            continue
        if marker:
            fence = marker[1]
            continue
        line = INLINE_CODE.sub("", line)
        for match in INLINE_LINK.finditer(line):
            yield number, match[1] or match[2]
        match = REFERENCE.match(line)
        if match:
            yield number, match[1] or match[2]


def missing_links(root, document_path, document):
    for number, target in destinations(document):
        try:
            url = urlsplit(target)
        except ValueError:
            continue
        if url.scheme or url.netloc or not url.path:
            continue
        path = unquote(url.path)
        base = root if path.startswith("/") else (root / document_path).parent
        resolved = (base / path.lstrip("/")).resolve()
        if not resolved.is_relative_to(root.resolve()) or not resolved.exists():
            yield number, target


def tracked_documents(root):
    result = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.md"], cwd=root
    )
    for name in result.decode("utf-8").split("\0"):
        if name and not name.startswith(("docs/generated/", "docs-site/")):
            yield Path(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-only", action="store_true",
                        help="report missing paths without failing the command")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    count = 0
    missing = 0
    for path in tracked_documents(root):
        if not (root / path).is_file():
            continue
        count += 1
        document = (root / path).read_text(encoding="utf-8")
        for number, target in missing_links(root, path, document):
            print(f"{path}:{number}: missing local link: {target}")
            missing += 1
    print(f"Checked {count} tracked Markdown documents; {missing} missing local links.")
    return int(missing > 0 and not args.report_only)


if __name__ == "__main__":
    raise SystemExit(main())
