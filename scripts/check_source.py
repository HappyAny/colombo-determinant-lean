"""Verify the checksums of the published manuscript and proof files."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent.parent
checks = (root / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
for entry in checks:
    expected, relative = entry.split("  ", 1)
    source = (root / relative).resolve()
    if not source.is_relative_to(root.resolve()):
        raise SystemExit("Checksum entry escapes the repository")
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Checksum mismatch: {relative}")
print(f"Verified {len(checks)} file checksums. Run Lean for the mathematical check.")
