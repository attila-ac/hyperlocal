#!/usr/bin/env python3
import argparse
import re
from pathlib import Path
from collections import defaultdict, deque

IMPORT_RE = re.compile(r'^\s*import\s+(.+?)\s*$', re.M)

LEGACY_MOD = "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA"
THEOREM_MOD = "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem"

PATCH_TARGETS = [
    "Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge",
    "Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Discharge",
    "Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalytic_Discharge",
]

ROOTS = [
    "Hyperlocal.OneButton",
    "Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder",
    "Hyperlocal.Targets.XiPhaseLock",
]

AXIOM_MODULES_OF_INTEREST = {
    "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms":
        "Hyperlocal.Targets.XiPacket.RouteAJetCoordAxioms.Wc.payload",
    "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Axioms":
        "Hyperlocal.Targets.XiPacket.routeAJetCoordProvider_axiom",
}

WC_AXIOM_PATTERNS = [
    r"RouteAJetCoordAxioms\.Wc\.ax_wc_",
    r"import\s+Hyperlocal\.Targets\.XiPacket\.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms",
]

LEGACY_SYMBOL_PATTERNS = [
    r"\bJetQuotOp\.xiRouteA_jetPkg_w0At\b",
    r"\bJetQuotOp\.xiRouteA_jetPkg_wp2At\b",
    r"\bJetQuotOp\.xiRouteA_jetPkg_wp3At\b",
]

THEOREM_SYMBOL_PATTERNS = [
    r"\bJetQuotOpTheorem\.xiRouteA_jetPkg_w0At\b",
    r"\bJetQuotOpTheorem\.xiRouteA_jetPkg_wp2At\b",
    r"\bJetQuotOpTheorem\.xiRouteA_jetPkg_wp3At\b",
]


def rel_to_module(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def parse_imports(text: str):
    imports = []
    for m in IMPORT_RE.finditer(text):
        imports.extend(m.group(1).split())
    return imports


def bfs(graph, starts):
    dist = {}
    q = deque()
    for s in starts:
        if s in graph or s in reverse_graph:
            dist[s] = 0
            q.append(s)
    while q:
        u = q.popleft()
        for v in graph.get(u, []):
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def closure(graph, starts):
    seen = set()
    q = deque(starts)
    for s in starts:
        seen.add(s)
    while q:
        u = q.popleft()
        for v in graph.get(u, []):
            if v not in seen:
                seen.add(v)
                q.append(v)
    return seen


def modules_reaching(reverse_graph, mods):
    seen = set()
    q = deque(mods)
    for m in mods:
        seen.add(m)
    while q:
        u = q.popleft()
        for v in reverse_graph.get(u, []):
            if v not in seen:
                seen.add(v)
                q.append(v)
    return seen


ap = argparse.ArgumentParser()
ap.add_argument("--root", default="formalisation")
args = ap.parse_args()

root = Path(args.root).resolve()
lean_files = sorted(root.rglob("*.lean"))

module_to_path = {}
module_to_text = {}
module_to_imports = {}

for p in lean_files:
    mod = rel_to_module(root, p)
    txt = p.read_text(encoding="utf-8", errors="ignore")
    module_to_path[mod] = p
    module_to_text[mod] = txt

all_modules = set(module_to_path)

for mod, txt in module_to_text.items():
    imports = [x for x in parse_imports(txt) if x in all_modules]
    module_to_imports[mod] = imports

graph = defaultdict(set)
reverse_graph = defaultdict(set)
for mod, imports in module_to_imports.items():
    for imp in imports:
        graph[mod].add(imp)
        reverse_graph[imp].add(mod)

current_root_cone = closure(graph, [r for r in ROOTS if r in all_modules])

legacy_importers_all = sorted(reverse_graph.get(LEGACY_MOD, set()))
legacy_importers_live = [m for m in legacy_importers_all if m in current_root_cone]

legacy_symbol_users = []
theorem_symbol_users = []
wc_axiom_users_live = []

for mod, txt in module_to_text.items():
    if any(re.search(pat, txt) for pat in LEGACY_SYMBOL_PATTERNS):
        legacy_symbol_users.append(mod)
    if any(re.search(pat, txt) for pat in THEOREM_SYMBOL_PATTERNS):
        theorem_symbol_users.append(mod)
    if mod in current_root_cone and any(re.search(pat, txt) for pat in WC_AXIOM_PATTERNS):
        wc_axiom_users_live.append(mod)

# Simulate the retarget: patch-target imports of legacy module become theorem module.
sim_imports = {m: set(imps) for m, imps in module_to_imports.items()}
for mod in PATCH_TARGETS:
    if mod in sim_imports and LEGACY_MOD in sim_imports[mod]:
        sim_imports[mod].remove(LEGACY_MOD)
        sim_imports[mod].add(THEOREM_MOD)

sim_graph = defaultdict(set)
sim_reverse_graph = defaultdict(set)
for mod, imps in sim_imports.items():
    for imp in imps:
        sim_graph[mod].add(imp)
        sim_reverse_graph[imp].add(mod)

sim_root_cone = closure(sim_graph, [r for r in ROOTS if r in all_modules])

legacy_importers_live_after = sorted(
    m for m in sim_reverse_graph.get(LEGACY_MOD, set()) if m in sim_root_cone
)

axiom_modules_live_after = sorted(
    m for m in AXIOM_MODULES_OF_INTEREST if m in sim_root_cone
)

wc_modules_live_after = sorted(
    m for m in sim_root_cone
    if any(re.search(pat, module_to_text[m]) for pat in WC_AXIOM_PATTERNS)
)

next_axiom = None
if not legacy_importers_live_after:
    if "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms" in axiom_modules_live_after:
        next_axiom = AXIOM_MODULES_OF_INTEREST[
            "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms"
        ]
    elif "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Axioms" in axiom_modules_live_after:
        next_axiom = AXIOM_MODULES_OF_INTEREST[
            "Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Axioms"
        ]

print("=== ROUTE-A RETARGET PAYOFF REPORT ===")
print()
print(f"Legacy module          : {LEGACY_MOD}")
print(f"Theorem replacement    : {THEOREM_MOD}")
print()
print("Patch targets now:")
for m in PATCH_TARGETS:
    print(f"  - {m}")
print(f"Count                  : {len(PATCH_TARGETS)}")
print()

print("Current live legacy importers:")
for m in legacy_importers_live:
    print(f"  - {m}")
print(f"Count                  : {len(legacy_importers_live)}")
print()

print("Current files using legacy JetQuotOp symbols:")
for m in sorted(set(legacy_symbol_users)):
    print(f"  - {m}")
print(f"Count                  : {len(set(legacy_symbol_users))}")
print()

print("Current live wc-axiom users:")
for m in sorted(set(wc_axiom_users_live)):
    print(f"  - {m}")
print(f"Count                  : {len(set(wc_axiom_users_live))}")
print()

print("After simulated retarget:")
print(f"  live legacy importers remaining : {len(legacy_importers_live_after)}")
for m in legacy_importers_live_after:
    print(f"    - {m}")
print()

print("Axiom modules still in simulated live cone:")
for m in axiom_modules_live_after:
    print(f"  - {m} :: {AXIOM_MODULES_OF_INTEREST[m]}")
print()

if next_axiom is not None:
    print(f"Next likely killable axiom after retarget : {next_axiom}")
else:
    print("Next likely killable axiom after retarget : undetermined from graph alone")
print()

print("Estimated remaining files to touch for the wc seam:")
for m in wc_modules_live_after:
    print(f"  - {m}")
print(f"Count                  : {len(wc_modules_live_after)}")
print()

print("Interpretation:")
if len(legacy_importers_live_after) == 0:
    print("  - This retarget successfully removes the live cone's dependence on the legacy Route-A Leibniz wrapper.")
    print("  - The next narrow seam is the wc payload lane.")
else:
    print("  - The legacy wrapper still survives in the live cone after the proposed retarget.")
    print("  - Do not widen the refactor until the remaining importers are cleared.")
