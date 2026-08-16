#!/usr/bin/env python3
"""Turn the StarAll.lean log into a partition of the sampled formalizations.

The point of the star topology: every comparison is against the same reference,
so the verdicts compose.  Two files both PROVED equal to `Ref` are equal to each
other; a file PROVED equal and a file REFUTED are provably *not* equal.  No
result depends on any other, so one failed comparison costs one cell, not a
chain.
"""
import json, re, sys, collections, os

H = os.path.dirname(os.path.abspath(__file__))
LOG = sys.argv[1] if len(sys.argv) > 1 else os.path.join(H, "star.log")
meta = json.load(open(os.path.join(H, "starmap.json")))
raw = open(LOG, errors="replace").read().splitlines()

spans = meta["spans"]
ids = meta["ids"]
family = {s["id"]: s.get("family") for s in spans if s["kind"] == "comparison"}

PROBE = re.compile(r"@@STAR Star_(\S+) cpwl=(\S+) relun=(\S+) depth=(\S+) statement=(\S+)"
                   r" ownfalse=(\S+)")
OBLIG = ("cpwl", "relun", "depth", "statement", "ownfalse")

verdict = {}
for ln in raw:
    if m := PROBE.search(ln):
        verdict[m.group(1)] = dict(zip(OBLIG, m.groups()[1:]))

# errors, attributed to the comparison section they fall in
errors = collections.defaultdict(list)
for ln in raw:
    m = re.match(r".*StarAll\.lean:(\d+):\d+: error\(?([^)]*)\)?: (.*)", ln)
    if not m or "dependsOnNoncomputable" in m.group(2):
        continue
    line = int(m.group(1))
    s = next((s for s in spans if s["start"] <= line <= s["end"]), None)
    if s and s["kind"] == "comparison":
        errors[s["id"]].append((m.group(3) or m.group(2))[:160])

out = []
w = out.append
w("# Star comparison — 20 formalizations against one reference\n")
w("Each of the sampled formalizations is compared against")
w("[`Reference.lean`](Reference.lean) rather than against its neighbour.  The")
w("verdicts therefore **compose**: two files proved equal to `Ref` are equal to")
w("each other, and a proved-equal file and a refuted file are provably different.")
w("Nothing depends on anything else, so a failed comparison costs one cell rather")
w("than disconnecting a chain.\n")
w("Verdicts are read from each declaration's axiom set, so a `sorry` — including")
w("one laundered through another `sorry`-ed theorem — cannot be reported as a")
w("proof.  `ERROR` means the declaration did not elaborate.\n")

w("## Verdicts\n")
w("| file | family | `cpwl` | `relun` | `depth` | `statement` | own thm false | errors |")
w("|---|---|---|---|---|---|---|---:|")
for i in ids:
    v = verdict.get(i)
    e = len(errors.get(i, []))
    fam = (family.get(i) or "").replace("(nhds / ∀ᶠ)", "(nhds)")
    if v:
        w(f"| `{i}` | {fam} | {v['cpwl']} | {v['relun']} | {v['depth']} | "
          f"{v['statement']} | {v['ownfalse']} | {e or ''} |")
    else:
        w(f"| `{i}` | {fam} | — | — | — | — | — | {e or 'no probe'} |")
w("")

counts = {k: collections.Counter(verdict.get(i, {}).get(k, "NO-PROBE") for i in ids)
          for k in OBLIG}
w("| obligation | PROVED | REFUTED | SORRY | ERROR / other |")
w("|---|---:|---:|---:|---:|")
for k in OBLIG:
    c = counts[k]
    other = sum(n for kk, n in c.items() if kk not in ("PROVED", "REFUTED", "SORRY"))
    w(f"| `{k}` | {c['PROVED']} | {c['REFUTED']} | {c['SORRY']} | {other} |")
w("")

# ---------------------------------------------------------------- partition
same = [i for i in ids if verdict.get(i, {}).get("cpwl") == "PROVED"]
diff = [i for i in ids if verdict.get(i, {}).get("cpwl") == "REFUTED"]
open_ = [i for i in ids if i not in same and i not in diff]

w("## The partition\n")
w("Classified by `cpwl`, the obligation that carries the mathematical content.\n")
w(f"**Same theorem as the reference — {len(same)} of {len(ids)}**")
if same:
    w("\n" + ", ".join(f"`{i}`" for i in same) + "\n")
    w(f"These {len(same)} are equal to each other too, transitively, without any")
    w("pairwise comparison having been run.\n")
else:
    w("\n(none)\n")

w(f"**Provably a different theorem — {len(diff)} of {len(ids)}**")
if diff:
    w("\n" + ", ".join(f"`{i}`" for i in diff) + "\n")
    byfam = collections.Counter(family.get(i) for i in diff)
    w("by family: " + ", ".join(f"{v}× {k}" for k, v in byfam.most_common()) + "\n")
else:
    w("\n(none)\n")

w(f"**Undecided — {len(open_)} of {len(ids)}**")
if open_:
    w("\n" + ", ".join(f"`{i}`" for i in open_) + "\n")
    w("An honest `sorry` or a failed proof, not a verdict: these are neither")
    w("known-equal nor known-different.\n")
else:
    w("\n(none)\n")

if same and diff:
    w(f"So at least **two** distinct theorems are present among the {len(ids)}")
    w("sampled files, and the split is machine-proved in both directions.\n")

# ------------------------------------------------------------- side results
own = [i for i in ids if verdict.get(i, {}).get("ownfalse") == "PROVED"]
if own:
    w("## Files proved to state a *false* theorem\n")
    w("Stronger than \"differs from the reference\": these carry a direct proof")
    w("that their own Theorem 2 is false, with no dependence on the unproved")
    w("`Ref.theorem2`.\n")
    w(", ".join(f"`{i}`" for i in own) + "\n")

w("## Side results\n")
d = counts["depth"]
w(f"* `depthBound`: {d['PROVED']}/{len(ids)} proved identical to the reference's")
w("  `⌈log₃(n−1)⌉+1`, consistent with the earlier property test finding all 100")
w("  agree at every sample point.")
r = counts["relun"]
w(f"* `relun`: {r['PROVED']}/{len(ids)} proved, {r['REFUTED']} refuted.  The gap")
w("  is the *exactly k* vs *at most k* reading of hidden-layer count, which needs")
w("  the padding identity `x = relu x − relu (−x)` to close.")
w("")

nerr = sum(1 for i in ids if errors.get(i))
if nerr:
    w(f"## Comparisons that failed to elaborate — {nerr} / {len(ids)}\n")
    for i in ids:
        if errors.get(i):
            w(f"* **`{i}`** — {errors[i][0]}")
    w("")

text = "\n".join(out)
print(text)
open(os.path.join(H, "README.md"), "w").write(text + "\n")
json.dump({"verdict": verdict, "errors": dict(errors),
           "same": same, "different": diff, "undecided": open_},
          open(os.path.join(H, "star_analysis.json"), "w"), indent=1)
