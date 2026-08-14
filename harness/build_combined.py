#!/usr/bin/env python3
"""Concatenate every Thm2_NNN.lean into one Lean file with a probe after each,
recording the line offset of each agent's block so errors can be attributed."""
import glob, json, os, re, sys

SRC = "/Users/panda/Desktop/Lean/quick-test/formalizations"
HARNESS = "/Users/panda/Desktop/Lean/quick-test/harness"
OUT = os.path.join(HARNESS, "Combined.lean")
MAP = os.path.join(HARNESS, "linemap.json")

prelude = open(os.path.join(HARNESS, "prelude.lean")).read()
lines = prelude.splitlines()

spans = []
paths = sorted(glob.glob(os.path.join(SRC, "Thm2_*.lean")))
if len(sys.argv) > 1:
    paths = paths[: int(sys.argv[1])]
for path in paths:
    nnn = re.search(r"Thm2_(\d+)\.lean$", path).group(1)
    ns = f"Agent{nnn}"
    body = open(path).read().splitlines()
    # drop import lines (Mathlib is already imported by the prelude)
    body = [l for l in body if not l.strip().startswith("import ")]
    start = len(lines) + 1
    lines.append(f"-- ===== BEGIN {ns} =====")
    lines.extend(body)
    lines.append(f"run_cmd Lean.Elab.Command.liftTermElabM (acProbe `{ns})")
    end = len(lines)
    spans.append({"id": nnn, "ns": ns, "start": start, "end": end, "src": path})

open(OUT, "w").write("\n".join(lines) + "\n")
json.dump(spans, open(MAP, "w"), indent=1)
print(f"wrote {OUT}: {len(lines)} lines, {len(spans)} agents")
