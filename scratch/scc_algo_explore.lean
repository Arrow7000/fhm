/-!
# Kosaraju sketch for FHM binding SCCs (scratch — not in lake roots)

Target consumer: replace `sccIndexSets` in `SurfaceBridge`; keep
`sccBeforeEdges` + `kahnTopo` + `ValidBindingGroups`.

## Kahn cost (keep it)

With `n` bindings, `c ≤ n` SCCs, `E` dep edges, `E_c ≤ min(c², E)` condensation edges:

| Stage | What | Rough cost (current List impl) |
|-------|------|--------------------------------|
| **Partition (naive)** | O(n²) mutual-reach queries × DFS | **O(n³)–O(n⁴)** — the problem |
| Condensation edges | all SCC pairs × edge check | O(c² · …) ≤ ~O(n³) worst; usually ≪ partition |
| **Kahn loop** | peel indeg-0 on condensation | **O(c · E_c · c)** list-y ≈ **O(c³)** ≤ O(n³), on *tiny* c |

After Kosaraju, partition drops to ~O(n + E) (or O(n²) with our List/`bindSucc` style).
Kahn stays on `c` nodes. Even if every binding is its own SCC, Kahn is still
cheaper than today’s partition and already proved (~1200 LOC). **Do not replace
Kahn** unless we later care about polishing condensation build; the topo *proof*
reuse dominates any micro-optim of `kahnGo`.

## Kosaraju in one paragraph

1. DFS the digraph; append each vertex to `finish` when its exploration completes
   (postorder).
2. Build the **transpose** (reverse every edge).
3. DFS the transpose, seeding vertices in **decreasing** finish order.
   Each tree in this second forest is one SCC.

Why it works (proof outline, not code):
- Same SCC ⇒ mutually reachable ⇒ same second-pass tree.
- Same second-pass tree ⇒ paths both ways in the original
  (finish-order + transpose reachability).

## Suggested file split (when we implement for real)

```
FHM/Scc/Kosaraju.lean     -- abstract Digraph + kosaraju + Reach/Mutual theorems
FHM/SurfaceBridge.lean    -- sccIndexSets := kosaraju on bindSucc graph; Kahn unchanged
```

Spec to prove against (import / reuse, don’t fork):
- abstract `Reach` / `Mutual`, then glue `↔ DepReach` / `DepMutual` via existing
  `bindSucc` lemmas — or prove partition props at index level and reuse
  `sccOrderedIndexSets_*` that already lift to `ValidBindingGroups`.
-/

namespace SccExplore.Kosaraju

/-- Digraph on vertices `0 .. n-1`. -/
structure Digraph where
  n : Nat
  succ : Nat → List Nat

/-- Spec reachability (mirrors `DepReach`). -/
inductive Reach (g : Digraph) : Nat → Nat → Prop
  | refl {a} : Reach g a a
  | tail {a b c} : b ∈ g.succ a → Reach g b c → Reach g a c

def Mutual (g : Digraph) (a b : Nat) : Prop :=
  Reach g a b ∧ Reach g b a

/-- Transpose: `j ∈ succᵀ i` iff `i ∈ succ j`. Naive O(n²); fine for bindings. -/
def Digraph.transpose (g : Digraph) : Digraph where
  n := g.n
  succ := fun i => (List.range g.n).filter fun j => i ∈ g.succ j

/-! ### Pass 1 / pass 2 DFS (fuelled — total)

`visited` is a `Bool` array encoded as `List Bool` of length `n` for O(1)-ish
updates via `set` (still O(n) per set with List; HashMap later if needed).

State:
- pass 1: `acc` = finish stack (push on exit)
- pass 2: `acc` = current component (push on entry), flushed to `comps` at tree end
-/

def visitedGet (vis : List Bool) (i : Nat) : Bool := vis[i]?.getD true

def visitedSet (vis : List Bool) (i : Nat) : List Bool :=
  vis.set i true

/-- Recurse on unvisited successors; `fuel` ≤ n is enough if each call marks one. -/
def dfsFinish (g : Digraph) : Nat → List Bool → List Nat → Nat →
    List Bool × List Nat
  | 0, vis, finish, _ => (vis, finish)
  | fuel + 1, vis, finish, v =>
    if visitedGet vis v then (vis, finish)
    else
      let vis := visitedSet vis v
      let (vis, finish) :=
        (g.succ v).foldl
          (fun ⟨vis, finish⟩ u => dfsFinish g fuel vis finish u)
          (vis, finish)
      (vis, v :: finish)  -- postorder push

/-- First pass over all vertices in index order. `finish` = reverse postorder
    if we later reverse it; here we push on exit so head = last finished. -/
def finishOrder (g : Digraph) : List Nat :=
  let vis0 := List.replicate g.n false
  let rec go : Nat → List Bool → List Nat → List Nat
    | 0, _, finish => finish
    | fuel + 1, vis, finish =>
      match (List.range g.n).find? (fun v => !(visitedGet vis v)) with
      | none => finish
      | some v =>
        let (vis, finish) := dfsFinish g g.n vis finish v
        go fuel vis finish
  go (g.n + 1) vis0 []

/-- Second-pass DFS on `g` (caller passes transpose): collect one component. -/
def dfsCollect (g : Digraph) : Nat → List Bool → List Nat → Nat →
    List Bool × List Nat
  | 0, vis, comp, _ => (vis, comp)
  | fuel + 1, vis, comp, v =>
    if visitedGet vis v then (vis, comp)
    else
      let vis := visitedSet vis v
      let comp := v :: comp
      (g.succ v).foldl
        (fun ⟨vis, comp⟩ u => dfsCollect g fuel vis comp u)
        (vis, comp)

/-- Kosaraju: list of components (each a `List Nat`). Order of components follows
    second-pass discovery; **not** relied on for topo — Kahn still orders them. -/
def kosaraju (g : Digraph) : List (List Nat) :=
  let finish := finishOrder g           -- last finished at head
  let gt := g.transpose
  let vis0 := List.replicate g.n false
  -- Process in decreasing finish order = current `finish` head-first.
  let rec go : Nat → List Bool → List Nat → List (List Nat) → List (List Nat)
    | 0, _, _, comps => comps
    | fuel + 1, vis, [], comps => comps
    | fuel + 1, vis, v :: vs, comps =>
      if visitedGet vis v then go fuel vis vs comps
      else
        let (vis, comp) := dfsCollect gt g.n vis [] v
        go fuel vis vs (comps ++ [comp])
  go (g.n + 1) vis0 finish []

/-! ## Theorems to prove (complexity-first ordering)

Prefer many small lemmas over one fat invariant.

### A. Reach basics (~easy)
- `Reach_trans`, `Reach_of_mem_succ`, path list ↔ Reach

### B. Pass-1 finish order (~medium, local)
- `dfsFinish` marks `v`, only walks from `v`, terminates
- Edge `u → v` explored in same tree ⇒ `v` appears before `u` in `finish`
  (standard DFS parenthesis / “white-path” corollary) — **split into 3–4 lemmas**

### C. Transpose (~easy)
- `Reach gt a b ↔ Reach g b a`

### D. Pass-2 components (~medium–hard, but modular)
1. `kosaraju` output: nonempty parts, `flatten` permutes `range n`
2. same component ⇒ `Mutual g`
3. `Mutual g` ⇒ same component
   Prove (3) via: mutual ⇒ reach both ways ⇒ finish-order positions +
   transpose path forces same DFS tree (textbook Kosaraju argument, stepwise)

### E. FHM glue (~medium, mostly exists)
- `Reach ⟨n, bindSucc binds⟩ i j ↔ DepReach …` (reuse `canReach` proofs)
- `kosaraju ⟨…⟩` satisfies the partition hypotheses that `sccIndexSets` used
- `sccGroups` soundness = partition soundness + **existing** Kahn lemmas

Hardest agent traps to avoid: one giant “DFS state invariant.” Instead post
separate lemmas for visited monotonicity, acc contents, and edge/finish facts.
-/

-- sanity: empty / singleton shape (not #eval’d in lake; for manual play)
example : kosaraju ⟨0, fun _ => []⟩ = [] := by native_decide
example : kosaraju ⟨1, fun _ => []⟩ = [[0]] := by native_decide

end SccExplore.Kosaraju
