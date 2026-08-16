#!/usr/bin/env python3
"""Build StarAll.lean: the reference + the sampled agent namespaces + one
comparison section per sampled agent.

Comparison bodies come from star/comparisons/Star_<nnn>.lean when present,
otherwise they are stubbed with `sorry` — so the file always elaborates and the
scaffold can be type-checked before any proof work is commissioned.
"""
import json, os, re, sys

ROOT = "/Users/panda/Desktop/Lean/quick-test"
SRC = f"{ROOT}/formalizations"
STAR = f"{ROOT}/star"
CMP = f"{STAR}/comparisons"
OUT = f"{STAR}/StarAll.lean"
MAP = f"{STAR}/starmap.json"

# Stratified sample across the four CPWL families.  020/027/084 are excluded:
# their own sources do not elaborate, so any comparison would be meaningless.
SAMPLE = {
    "local agreement (nhds / forall-eventually)":
        ["003", "004", "006", "010", "012", "016", "017", "018", "019", "022", "024", "025", "028", "035", "036", "040", "044", "045", "047", "055", "058", "065", "066", "067", "069", "071", "073", "075", "078", "080", "082", "085", "092", "096", "097", "099"],
    "polyhedral subdivision":
        ["001", "008", "014", "015", "021", "026", "029", "030", "032", "034", "037", "042", "046", "049", "050", "052", "053", "054", "057", "059", "062", "063", "068", "072", "074", "079", "081", "083", "086", "088", "090", "091", "093", "095", "098"],
    "pointwise affine selection":
        ["002", "005", "007", "013", "023", "031", "033", "038", "039", "041", "043", "051", "060", "064", "077"],
    "polyhedral + local":
        ["009", "011", "048", "056", "061", "070", "076", "087", "089", "094", "100"],
}
IDS = sorted(i for v in SAMPLE.values() for i in v)
FAMILY = {i: fam for fam, v in SAMPLE.items() for i in v}


def strip_imports(text):
    return "\n".join(l for l in text.splitlines()
                     if not l.strip().startswith("import "))


def stub(nnn):
    A = f"Agent{nnn}"
    return f"""namespace Star_{nnn}

/-- The two files' notions of a continuous piecewise linear function agree. -/
theorem cpwl (n : ℕ) : {A}.CPWL n = Ref.CPWL n := sorry

/-- The two files' network classes agree. -/
theorem relun (n k : ℕ) : {A}.ReLUn n k = Ref.ReLUn n k := sorry

/-- The two files' depth bounds agree in the range the theorem is stated for. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : {A}.depthBound n = Ref.depthBound n := sorry

/-- Hence the two renderings of Theorem 2 are equivalent. -/
theorem statement :
    (∀ n, 3 ≤ n → {A}.CPWL n = {A}.ReLUn n ({A}.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_{nnn}"""


lines = open(f"{STAR}/star_prelude.lean").read().splitlines() + [""]
spans = []

lines.append("-- ===== reference =====")
start = len(lines) + 1
lines.extend(strip_imports(open(f"{STAR}/Reference.lean").read()).splitlines())
spans.append({"kind": "reference", "id": "ref", "ns": "Ref",
              "start": start, "end": len(lines)})
lines.append("")

for nnn in IDS:
    start = len(lines) + 1
    lines.append(f"-- ===== agent {nnn} =====")
    lines.extend(strip_imports(open(f"{SRC}/Thm2_{nnn}.lean").read()).splitlines())
    lines.append("")
    spans.append({"kind": "agent", "id": nnn, "ns": f"Agent{nnn}",
                  "family": FAMILY[nnn], "start": start, "end": len(lines)})

for nnn in IDS:
    path = f"{CMP}/Star_{nnn}.lean"
    supplied = os.path.exists(path)
    text = strip_imports(open(path).read()) if supplied else stub(nnn)
    start = len(lines) + 1
    lines.append(f"-- ===== comparison {nnn} vs Ref =====")
    lines.extend(text.splitlines())
    lines.append(f"run_cmd Lean.Elab.Command.liftTermElabM (starProbe `Star_{nnn})")
    lines.append("")
    spans.append({"kind": "comparison", "id": nnn, "ns": f"Star_{nnn}",
                  "family": FAMILY[nnn], "supplied": supplied,
                  "start": start, "end": len(lines)})

open(OUT, "w").write("\n".join(lines) + "\n")
json.dump({"spans": spans, "sample": SAMPLE, "ids": IDS}, open(MAP, "w"), indent=1)
ns = sum(1 for s in spans if s.get("supplied"))
print(f"wrote {OUT}: {len(lines)} lines, {len(IDS)} agents "
      f"({ns} with supplied proofs, {len(IDS)-ns} stubbed)")
