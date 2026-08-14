#!/usr/bin/env python3
"""Parse the combined Lean log: report which formalizations type-check, then
cluster them (a) by exact structural identity of the fully-unfolded statement
of `theorem2` modulo naming, and (b) by the modelling choices that statement
encodes."""
import json, re, sys, collections, os

HARNESS = "/Users/panda/Desktop/Lean/quick-test/harness"
LOG = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HARNESS, "combined.log")
spans = json.load(open(os.path.join(HARNESS, "linemap.json")))
raw = open(LOG, errors="replace").read().splitlines()

POS = re.compile(r"^(?:.*Combined\.lean):(\d+):(\d+): (error|warning|information)"
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
            return s["ns"]
    return None

errors = collections.defaultdict(list)
for line, kind, text in msgs:
    if kind == "error":
        errors[owner(line)].append(text.splitlines()[0])

probe = collections.defaultdict(dict)
for line, kind, text in msgs:
    if kind != "information": continue
    for tag in ("SHALLOW", "DEEP", "PPSHALLOW", "PPDEEP", "PPCANON", "ERR"):
        p = "@@" + tag + " "
        if text.startswith(p):
            ns, _, val = text[len(p):].partition(" ")
            probe[ns][tag] = val.strip()
            break

all_ns = [s["ns"] for s in spans]

NONCOMP = "consider marking it as 'noncomputable'"
def severity(ns):
    errs = errors.get(ns, [])
    if not errs: return "clean"
    if all(NONCOMP in e for e in errs): return "noncomputable-only"
    return "error"

# ---------- canonical form ---------------------------------------------------
LOCAL = re.compile(r"Agent\d{3}\.[A-Za-z_][A-Za-z0-9_.'!?]*")
PREFIXES = [
    re.compile(r"^∀ (\S+) ≥ 3, "),
    re.compile(r"^∀ \((\S+) : ℕ\), 3 ≤ \1 → "),
    re.compile(r"^∀ \((\S+) : ℕ\), \1 ≥ 3 → "),
]

def canon(s):
    s = re.sub(r"\s+", " ", s).strip()
    mapping = {}
    def repl(m):
        n = m.group(0)
        mapping.setdefault(n, f"<L{len(mapping)}>")
        return mapping[n]
    s = LOCAL.sub(repl, s)
    for p in PREFIXES:
        m = p.match(s)
        if m:
            var = m.group(1)
            s = "∀N, " + s[m.end():]
            s = re.sub(r"(?<![A-Za-z0-9_])" + re.escape(var) + r"(?![A-Za-z0-9_])", "N", s)
            break
    s = s.replace("✝", "")
    return s

# ---------- modelling-choice features ---------------------------------------
def features(txt):
    f = {}
    if re.search(r"Nat\.clog 3", txt):                       f["depth"] = "Nat.clog 3 (n-1) + 1"
    elif re.search(r"Real\.logb 3 \(↑\w+ - 1\)", txt):       f["depth"] = "⌈logb 3 ((n:ℝ)-1)⌉₊ + 1"
    elif re.search(r"Real\.logb 3 ↑\(\w+ - 1\)", txt):       f["depth"] = "⌈logb 3 ↑(n-1)⌉₊ + 1  (ℕ-subtraction)"
    elif re.search(r"Real\.logb", txt):                      f["depth"] = "other logb form"
    else:                                                    f["depth"] = "??"

    rhs = txt.split("} = {", 1)[-1] if "} = {" in txt else txt
    f["depth_quant"] = "at most k" if re.search(r"∃ \S+ ≤ ", rhs) else "exactly k"

    lhs = txt.split("} = {", 1)[0] if "} = {" in txt else txt
    if "nhds" in lhs or "∀ᶠ" in lhs:                         f["cpwl"] = "local agreement (nhds / eventually)"
    elif "dist" in lhs:                                      f["cpwl"] = "local agreement (metric ball)"
    elif "⋃" in lhs or "IsOpen" in lhs or "⋂" in lhs:        f["cpwl"] = "polyhedral / covering subdivision"
    else:                                                    f["cpwl"] = "other"
    f["continuous"] = "yes" if "Continuous" in lhs else "NO"
    return f

clean_ish = [ns for ns in all_ns
             if severity(ns) != "error" and "PPCANON" in probe.get(ns, {})]
broken = [ns for ns in all_ns if ns not in clean_ish]

clusters = collections.defaultdict(list)
for ns in clean_ish:
    clusters[canon(probe[ns]["PPCANON"])].append(ns)

feat = {ns: features(probe[ns].get("PPDEEP", "")) for ns in clean_ish}
featgroups = collections.defaultdict(list)
for ns in clean_ish:
    k = (feat[ns]["cpwl"], feat[ns]["depth_quant"], feat[ns]["depth"], feat[ns]["continuous"])
    featgroups[k].append(ns)

out = []
w = out.append
w(f"# Theorem 2 formalization bake-off — {len(all_ns)} independent agents\n")
w("## 1. Type check (single Lean process, Mathlib v4.27.0)\n")
w(f"  compile with zero errors                : {sum(1 for n in all_ns if severity(n)=='clean')}")
w(f"  only error is a missing `noncomputable` : {sum(1 for n in all_ns if severity(n)=='noncomputable-only')}")
w(f"  genuine elaboration errors              : {sum(1 for n in all_ns if severity(n)=='error')}")
w("")
for ns in all_ns:
    if severity(ns) == "error":
        w(f"    {ns}: {errors[ns][0][:160]}")
w("")
w(f"## 2. Exact structural identity of the unfolded statement "
  f"({len(clusters)} distinct forms among {len(clean_ish)} usable)\n")
for i, (c, m) in enumerate(sorted(clusters.items(), key=lambda kv: (-len(kv[1]), kv[1][0])), 1):
    if len(m) > 1:
        w(f"  cluster {i} ({len(m)}): {', '.join(m)}")
singletons = [m[0] for c, m in clusters.items() if len(m) == 1]
w(f"  singletons ({len(singletons)}): every other file is structurally unique")
w("")
w(f"## 3. Modelling-choice groups ({len(featgroups)} distinct combinations)\n")
for k, m in sorted(featgroups.items(), key=lambda kv: -len(kv[1])):
    w(f"  [{len(m):3d}] CPWL={k[0]} | ReLU_(n,k)={k[1]} | depth={k[2]} | continuity={k[3]}")
    w(f"        {', '.join(m)}")
    w("")
w("## 4. Marginal distributions\n")
for field in ("cpwl", "depth_quant", "depth", "continuous"):
    c = collections.Counter(feat[ns][field] for ns in clean_ish)
    w(f"  {field}:")
    for k, v in c.most_common():
        w(f"      {v:3d}  {k}")
    w("")

text = "\n".join(out)
print(text)
open(os.path.join(HARNESS, "report.txt"), "w").write(text + "\n")
json.dump({"severity": {n: severity(n) for n in all_ns},
           "features": feat,
           "clusters": {str(i): m for i, (c, m) in enumerate(
               sorted(clusters.items(), key=lambda kv: -len(kv[1])), 1)},
           "canon": {n: canon(probe[n]["PPCANON"]) for n in clean_ish},
           "ppdeep": {n: probe[n].get("PPDEEP", "") for n in clean_ish}},
          open(os.path.join(HARNESS, "analysis.json"), "w"), indent=1)
