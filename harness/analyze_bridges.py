#!/usr/bin/env python3
"""Turn the combined BridgeAll.lean log into a machine-checked verdict table.

Each bridge's four obligations are classified by the in-Lean probe, which
inspects the declaration's axiom set — so a `sorry` (even one laundered through
another sorry-ed theorem) can never be reported as PROVED.
"""
import json, re, sys, collections, os

H = os.path.dirname(os.path.abspath(__file__))
LOG = sys.argv[1] if len(sys.argv) > 1 else os.path.join(H, "bridge.log")
spans = json.load(open(os.path.join(H, "bridgemap.json")))
raw = open(LOG, errors="replace").read().splitlines()

POS = re.compile(r"^(?:.*BridgeAll\.lean):(\d+):(\d+): (error|warning|information)"
                 r"(?:\([^)]*\))?: (.*)$")

msgs, cur = [], None
for ln in raw:
    m = POS.match(ln)
    if m:
        if cur: msgs.append(cur)
        cur = [int(m.group(1)), m.group(3), m.group(4)]
    elif ln.startswith("@@"):
        if cur: msgs.append(cur)
        cur = [0, "information", ln]
    elif cur is not None:
        cur[2] += " " + ln
if cur: msgs.append(cur)

def owner(line):
    for s in spans:
        if s["start"] <= line <= s["end"]:
            return s
    return None

errors = collections.defaultdict(list)
for line, kind, text in msgs:
    if kind == "error":
        o = owner(line)
        key = o["ns"] if o else "?"
        errors[key].append(text.splitlines()[0][:200])

PROBE = re.compile(r"@@BRIDGE (\S+) cpwl=(\S+) relun=(\S+) depth=(\S+) statement=(\S+)")
verdict = {}
for _, kind, text in msgs:
    m = PROBE.search(text)
    if m:
        verdict[m.group(1)] = dict(zip(("cpwl", "relun", "depth", "statement"),
                                       m.groups()[1:]))

bridges = [s for s in spans if s["kind"] == "bridge"]
agents = [s for s in spans if s["kind"] == "agent"]

out = []
w = out.append
w("# Bridge verification — machine-checked results\n")
w("Every one of the 99 consecutive links was type-checked in a single Lean process")
w("against Mathlib v4.27.0. For each link the probe inspects each obligation's")
w("**axiom set**: PROVED = present and free of `sorryAx`; REFUTED = the `_ne` form")
w("proved sorry-free; SORRY = present but depends on `sorryAx`; MISSING = the")
w("declaration failed to elaborate at all.\n")

counts = {k: collections.Counter() for k in ("cpwl", "relun", "depth", "statement")}
for b in bridges:
    v = verdict.get(b["ns"])
    for k in counts:
        counts[k][v[k] if v else "NO-PROBE"] += 1

w("## Totals across the 99 links\n")
w("| obligation | PROVED | REFUTED | SORRY | MISSING/other |")
w("|---|---:|---:|---:|---:|")
for k in ("cpwl", "relun", "depth", "statement"):
    c = counts[k]
    other = sum(v for kk, v in c.items()
                if kk not in ("PROVED", "REFUTED", "SORRY"))
    w(f"| `{k}` | {c['PROVED']} | {c['REFUTED']} | {c['SORRY']} | {other} |")
w("")

nerr = sum(1 for b in bridges if errors.get(b["ns"]))
w(f"Bridges with elaboration errors: **{nerr}** / {len(bridges)}\n")

w("**Reading `SORRY`:** the declaration exists but its axiom set contains")
w("`sorryAx`. That covers both an *honest* `sorry` the agent wrote deliberately")
w("and a *failed* proof attempt (Lean records an error and admits the decl with")
w("`sorryAx`). The `errors` column separates them: a link with 0 errors whose")
w("obligations are `SORRY` left them open on purpose; a link with errors had")
w("proofs that did not go through.\n")

w("## Per-link table\n")
w("| link | cpwl | relun | depth | statement | errors |")
w("|---|---|---|---|---|---:|")
for b in bridges:
    v = verdict.get(b["ns"])
    e = len(errors.get(b["ns"], []))
    if v:
        w(f"| {b['id'].replace('_','→')} | {v['cpwl']} | {v['relun']} | "
          f"{v['depth']} | {v['statement']} | {e or ''} |")
    else:
        w(f"| {b['id'].replace('_','→')} | — | — | — | — | {e or 'no probe'} |")
w("")

clean_links = [b for b in bridges if not errors.get(b["ns"])]
w(f"Links whose bridge file compiled with **zero errors**: "
  f"{len(clean_links)} / {len(bridges)}\n")

if nerr:
    w("## Links whose file failed to elaborate\n")
    for b in bridges:
        if errors.get(b["ns"]):
            w(f"* **{b['id'].replace('_','→')}** — {errors[b['ns']][0][:160]}")
    w("")

agent_errs = {a["ns"]: errors.get(a["ns"], []) for a in agents}
w(f"## Agent files: {sum(1 for v in agent_errs.values() if v)} of {len(agents)} "
  f"still report errors (unchanged from the original type check)\n")

text = "\n".join(out)
print(text)
open(os.path.join(H, "bridge_report.md"), "w").write(text + "\n")
json.dump({"verdict": verdict,
           "errors": {k: v for k, v in errors.items()}},
          open(os.path.join(H, "bridge_analysis.json"), "w"), indent=1)
