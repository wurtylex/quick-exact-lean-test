#!/usr/bin/env python3
"""Build BridgeAll.lean: all 100 agent namespaces followed by 99 consecutive
bridge sections (001↔002, 002↔003, …, 099↔100).

Each bridge carries four obligations. Bridge bodies are read from
harness/bridges/Bridge_<i>_<j>.lean when present, otherwise stubbed with sorry.
"""
import glob, json, os, re, sys

ROOT = "/Users/panda/Desktop/Lean/quick-test"
SRC = f"{ROOT}/formalizations"
HARNESS = f"{ROOT}/harness"
BRIDGES = f"{ROOT}/bridges"
OUT = f"{HARNESS}/BridgeAll.lean"
MAP = f"{HARNESS}/bridgemap.json"

ids = sorted(re.search(r"Thm2_(\d+)\.lean$", p).group(1)
             for p in glob.glob(f"{SRC}/Thm2_*.lean"))

lines = open(f"{HARNESS}/bridge_prelude.lean").read().splitlines() + [""]
spans = []

for nnn in ids:
    body = [l for l in open(f"{SRC}/Thm2_{nnn}.lean").read().splitlines()
            if not l.strip().startswith("import ")]
    start = len(lines) + 1
    lines.append(f"-- ===== agent {nnn} =====")
    lines.extend(body)
    spans.append({"kind": "agent", "id": nnn, "ns": f"Agent{nnn}",
                  "start": start, "end": len(lines)})

def stub(i, j):
    A, B = f"Agent{i}", f"Agent{j}"
    return f"""namespace Bridge_{i}_{j}

/-- The two files' notions of a continuous piecewise linear function agree. -/
theorem cpwl (n : ℕ) : {A}.CPWL n = {B}.CPWL n := sorry

/-- The two files' network classes agree. -/
theorem relun (n k : ℕ) : {A}.ReLUn n k = {B}.ReLUn n k := sorry

/-- The two files' depth bounds agree in the range the theorem is stated for. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : {A}.depthBound n = {B}.depthBound n := sorry

/-- Hence the two renderings of Theorem 2 are equivalent. -/
theorem statement :
    (∀ n, 3 ≤ n → {A}.CPWL n = {A}.ReLUn n ({A}.depthBound n)) ↔
    (∀ n, 3 ≤ n → {B}.CPWL n = {B}.ReLUn n ({B}.depthBound n)) := sorry

end Bridge_{i}_{j}"""

for i, j in zip(ids, ids[1:]):
    path = f"{BRIDGES}/Bridge_{i}_{j}.lean"
    text = open(path).read() if os.path.exists(path) else stub(i, j)
    text = "\n".join(l for l in text.splitlines()
                     if not l.strip().startswith("import "))
    start = len(lines) + 1
    lines.append(f"-- ===== bridge {i} -> {j} =====")
    lines.extend(text.splitlines())
    lines.append(f"run_cmd Lean.Elab.Command.liftTermElabM (bridgeProbe `Bridge_{i}_{j})")
    spans.append({"kind": "bridge", "id": f"{i}_{j}", "ns": f"Bridge_{i}_{j}",
                  "a": f"Agent{i}", "b": f"Agent{j}",
                  "start": start, "end": len(lines),
                  "supplied": os.path.exists(path)})

open(OUT, "w").write("\n".join(lines) + "\n")
json.dump(spans, open(MAP, "w"), indent=1)
nb = sum(1 for s in spans if s["kind"] == "bridge")
ns = sum(1 for s in spans if s.get("supplied"))
print(f"wrote {OUT}: {len(lines)} lines, {len(ids)} agents, {nb} bridges "
      f"({ns} with supplied proofs, {nb-ns} stubbed)")
