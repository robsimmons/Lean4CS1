#!/usr/bin/env python3
"""
Literate Lean → Markdown converter.
Processes files containing /-! @@@ ... @@@ -/ comment blocks:
  - Text between @@@ markers is emitted as-is (markdown)
  - Lean code outside the markers is wrapped in ```lean ... ``` blocks
"""

import sys
from pathlib import Path

SEPARATOR = "@@@"
CODE_START = "```lean"
CODE_END = "```"


def convert(lines):
    LIT, CODE = "lit", "code"
    mode = CODE
    segments = []  # list of (mode, [lines])
    current = []

    for line in lines:
        if SEPARATOR in line:
            if current:
                segments.append((mode, current))
                current = []
            mode = LIT if mode == CODE else CODE
        else:
            current.append(line)

    if current:
        segments.append((mode, current))

    out = []
    for mode, seg_lines in segments:
        if mode == LIT:
            out.extend(seg_lines)
        else:
            # strip leading/trailing blank lines, wrap in fences
            stripped = seg_lines
            while stripped and not stripped[0].strip():
                stripped = stripped[1:]
            while stripped and not stripped[-1].strip():
                stripped = stripped[:-1]
            if stripped:
                out.append(CODE_START)
                out.extend(stripped)
                out.append(CODE_END)
                out.append("")

    return "\n".join(out) + "\n"


def main():
    args = sys.argv[1:]
    if len(args) == 1:
        input_file = args[0]
        output_file = str(Path(input_file).with_suffix(".md"))
    elif len(args) == 2:
        input_file, output_file = args
    else:
        print("Usage: convert.py <input.lean> [output.md]", file=sys.stderr)
        sys.exit(1)

    with open(input_file, encoding="utf-8") as f:
        lines = f.read().splitlines()

    result = convert(lines)

    with open(output_file, "w", encoding="utf-8") as f:
        f.write(result)

    print(f"Formatted content written to {output_file}")


if __name__ == "__main__":
    main()
