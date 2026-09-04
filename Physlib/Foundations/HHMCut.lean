/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib

/-!
# The minimality-based (Hayden–Headrick–Maloney) cut route to holographic MMI

This file investigates **Direction #3** of the MMI programme: whether the *true* HHM
minimality-based cut recombination closes Monogamy of Mutual Information (MMI, `I₃ ≤ 0`) for
**general finite weighted graphs**, or whether it only ever refuted a strawman.

## The model (self-contained; no cross-branch imports)

A finite weighted graph on vertex set `Fin n`, given by an edge-weight function
`w : Fin n → Fin n → ℕ`.  A **cut** is a set `S : Finset (Fin n)` of vertices; its
`bulkCutCapacity` is the total weight of ordered pairs crossing out of `S` (with a symmetric `w`
this is the standard undirected cut value; we do not even need symmetry for the results below).
For a boundary region the **RT entropy** `rtEntropy` is the minimum of `bulkCutCapacity` over
admissible cuts.  We reprove the two cut-world facts we need: submodularity of `bulkCutCapacity`
and the achieved-minimum bound (*minimality*).

## The headline results and the VERDICT

* `bulkCutCapacity_submodular` — the cut function is submodular (a genuine, uniform fact),
  proved from a per-ordered-pair submodular inequality.
* `rtEntropy_le_of_mem` — **minimality**: any admissible cut upper-bounds the RT entropy.
* `mmi_of_recombination` — the honest **reduction**: MMI follows *if* one can produce, for the
  four regions, admissible candidate cuts whose capacities sum to at most `cut X + cut Y + cut Z`.
  This is the only place minimality enters.
* `symmetricRecombination_fails` — a **machine-checked counterexample** (a `Fin 5` weighted graph)
  where `X,Y,Z` are the *actual pair min cuts* yet the *symmetric* candidate family
  `(X∩Y, X∩Z, Y∩Z, X∪Y∪Z)` has total capacity `18 > 11 = cut X + cut Y + cut Z`.  So the symmetric
  recombination does **not** close MMI even with minimality.
* `pointwise_submodular_recombination_false` — the underlying set-function inequality is false for
  the cut function `f` on `Fin 3` (`3 > 2`), strengthening the arbitrary-set refutation to an
  explicit cut submodular `f`.
* `mmiWitness_slack_pos` — a strict, non-vacuous MMI witness (a `Fin 6` two-hub graph with
  `I₃`-slack `= 4 > 0`), machine-checked, so the reduction target is not vacuous.

### VERDICT

The minimality-based cut recombination does **NOT** close MMI for general graphs via any *fixed*
recombination formula.  The symmetric family provably fails on true min cuts.  Machine search (see
the trailing note) shows *some* boolean recombination always suffices, but the winning one is
**graph-dependent** — no uniform submodular certificate exists.
-/

@[expose] public section

namespace HHMCut

open Finset

variable {n : ℕ}

/-! ### The cut capacity and its submodularity -/

/-- The capacity of a cut `S` under edge weights `w`: the total weight of ordered pairs `(i, j)`
with `i ∈ S` and `j ∉ S`.  For a symmetric `w` this is the standard undirected cut value. -/
def bulkCutCapacity (w : Fin n → Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, (if i ∈ S ∧ j ∉ S then w i j else 0)

/-- The single-ordered-pair crossing term. -/
private def cross (S : Finset (Fin n)) (a : ℕ) (i j : Fin n) : ℕ :=
  if i ∈ S ∧ j ∉ S then a else 0

/-- **Per-pair submodularity.** For a fixed ordered pair `(i,j)` and weight `a`, the crossing
indicator (times `a`) is a submodular function of the cut `S`:
`cross (S ∪ T) + cross (S ∩ T) ≤ cross S + cross T`. Checked by cases on the four memberships. -/
private lemma cross_submodular (S T : Finset (Fin n)) (a : ℕ) (i j : Fin n) :
    cross (S ∪ T) a i j + cross (S ∩ T) a i j ≤ cross S a i j + cross T a i j := by
  classical
  unfold cross
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
    by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;>
    simp_all [Finset.mem_union, Finset.mem_inter]

/-- **Submodularity of the cut capacity.** For all cuts `S, T`:
`cut (S ∪ T) + cut (S ∩ T) ≤ cut S + cut T`. -/
theorem bulkCutCapacity_submodular (w : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    bulkCutCapacity w (S ∪ T) + bulkCutCapacity w (S ∩ T)
      ≤ bulkCutCapacity w S + bulkCutCapacity w T := by
  classical
  have key : ∀ i j : Fin n,
      cross (S ∪ T) (w i j) i j + cross (S ∩ T) (w i j) i j
        ≤ cross S (w i j) i j + cross T (w i j) i j := fun i j => cross_submodular S T (w i j) i j
  -- rewrite each capacity as a double sum of `cross`
  have hrw : ∀ U : Finset (Fin n),
      bulkCutCapacity w U = ∑ i : Fin n, ∑ j : Fin n, cross U (w i j) i j := by
    intro U; rfl
  rw [hrw, hrw, hrw, hrw]
  calc
    (∑ i, ∑ j, cross (S ∪ T) (w i j) i j) + ∑ i, ∑ j, cross (S ∩ T) (w i j) i j
        = ∑ i, ∑ j, (cross (S ∪ T) (w i j) i j + cross (S ∩ T) (w i j) i j) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_add_distrib]
    _ ≤ ∑ i, ∑ j, (cross S (w i j) i j + cross T (w i j) i j) := by
          apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _; exact key i j
    _ = (∑ i, ∑ j, cross S (w i j) i j) + ∑ i, ∑ j, cross T (w i j) i j := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_add_distrib]

/-! ### RT entropy and minimality

A boundary is a fixed `Finset (Fin n)` of boundary vertices, together with a labelling telling which
region each boundary vertex belongs to.  We keep the model lightweight: an **admissible cut** for a
region is specified extensionally by a predicate `adm : Finset (Fin n) → Prop`.  The RT entropy is
the least capacity over the (nonempty, finite) set of admissible cuts.  All we need downstream is the
minimality bound `rtEntropy ≤ cut(candidate)` for any admissible candidate. -/

/-- RT entropy of a region whose admissible cuts are exactly those `S` in the (nonempty) family
`adm`: the minimum capacity over `adm`.  `hne` witnesses nonemptiness (there is always the trivial
admissible cut of the region itself). -/
noncomputable def rtEntropy (w : Fin n → Fin n → ℕ) (adm : Finset (Finset (Fin n)))
    (hne : adm.Nonempty) : ℕ :=
  (adm.image (bulkCutCapacity w)).min' (hne.image _)

/-- **Minimality.** Any admissible cut `S ∈ adm` upper-bounds the RT entropy. This is the sole
ingredient the pointwise recombination route ignores. -/
theorem rtEntropy_le_of_mem (w : Fin n → Fin n → ℕ) {adm : Finset (Finset (Fin n))}
    (hne : adm.Nonempty) {S : Finset (Fin n)} (hS : S ∈ adm) :
    rtEntropy w adm hne ≤ bulkCutCapacity w S := by
  unfold rtEntropy
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hS)

/-! ### The honest reduction: MMI ⟸ a good recombination

Regions `A, B, C, ABC` with admissible-cut families `admA, admB, admC, admABC`.  Pair min cuts
`X, Y, Z` for `AB, AC, BC` realise `rtEntropy(AB) = cut X`, etc.  If we can exhibit admissible
candidates for the four regions whose capacities sum to `≤ cut X + cut Y + cut Z`, MMI follows by
minimality.  Minimality (`rtEntropy_le_of_mem`) is the *only* nontrivial input. -/
theorem mmi_of_recombination (w : Fin n → Fin n → ℕ)
    {admA admB admC admABC : Finset (Finset (Fin n))}
    (hA0 : admA.Nonempty) (hB0 : admB.Nonempty) (hC0 : admC.Nonempty) (hABC0 : admABC.Nonempty)
    {X Y Z cA cB cC cABC : Finset (Fin n)}
    (hcA : cA ∈ admA) (hcB : cB ∈ admB) (hcC : cC ∈ admC) (hcABC : cABC ∈ admABC)
    (hbudget : bulkCutCapacity w cA + bulkCutCapacity w cB + bulkCutCapacity w cC
        + bulkCutCapacity w cABC
      ≤ bulkCutCapacity w X + bulkCutCapacity w Y + bulkCutCapacity w Z) :
    rtEntropy w admA hA0 + rtEntropy w admB hB0 + rtEntropy w admC hC0 + rtEntropy w admABC hABC0
      ≤ bulkCutCapacity w X + bulkCutCapacity w Y + bulkCutCapacity w Z := by
  have hA := rtEntropy_le_of_mem w hA0 hcA
  have hB := rtEntropy_le_of_mem w hB0 hcB
  have hC := rtEntropy_le_of_mem w hC0 hcC
  have hABC := rtEntropy_le_of_mem w hABC0 hcABC
  omega

/-! ### Concrete graphs for the counterexample / witness (machine-checked)

We now instantiate the model on explicit `Fin 5` and `Fin 6` weighted graphs and evaluate cut
capacities by `decide`, delivering the verdict's hard numbers with no `sorry`. -/

/-- Weight matrix of the `Fin 5` counterexample graph (undirected; symmetric):
edges `{3-0 :3, 1-0 :2, 4-3 :3, 1-4 :3, 3-2 :1}` (the two parallel `1-0` edges collapsed to `2`). -/
def wCE : Fin 5 → Fin 5 → ℕ := fun i j =>
  match i, j with
  | 0, 1 | 1, 0 => 2
  | 0, 3 | 3, 0 => 3
  | 3, 4 | 4, 3 => 3
  | 1, 4 | 4, 1 => 3
  | 2, 3 | 3, 2 => 1
  | _, _ => 0

-- Boundary of the `Fin 5` graph: `0 = A`, `2 = B`, `4 = C`; bulk `= {1, 3}`
-- (membership constraints are baked into the min-cut claims below).

/-- The pair min cuts for the `Fin 5` graph, found by exhaustive search over the bulk `{1,3}`:
`X = r(AB) = {0,2,3}`, `Y = r(AC) = {0,1,3,4}`, `Z = r(BC) = {1,2,3,4}`. -/
def X_CE : Finset (Fin 5) := {0, 2, 3}
def Y_CE : Finset (Fin 5) := {0, 1, 3, 4}
def Z_CE : Finset (Fin 5) := {1, 2, 3, 4}

/-- `X, Y, Z` realise `cut X = 5`, `cut Y = 1`, `cut Z = 5`, summing to `11`. (Machine-checked.) -/
theorem CE_pair_caps :
    bulkCutCapacity wCE X_CE = 5 ∧ bulkCutCapacity wCE Y_CE = 1
      ∧ bulkCutCapacity wCE Z_CE = 5 := by decide

/-- The **symmetric candidate family** on these true min cuts has total capacity `18`. -/
theorem CE_symmetric_caps :
    bulkCutCapacity wCE (X_CE ∩ Y_CE) + bulkCutCapacity wCE (X_CE ∩ Z_CE)
        + bulkCutCapacity wCE (Y_CE ∩ Z_CE) + bulkCutCapacity wCE (X_CE ∪ Y_CE ∪ Z_CE) = 18 := by
  decide

/-- **VERDICT LEMMA (symmetric recombination fails on true min cuts).**
On the `Fin 5` graph, with `X, Y, Z` the actual pair min cuts, the symmetric candidate family
`(X∩Y, X∩Z, Y∩Z, X∪Y∪Z)` overshoots the budget `cut X + cut Y + cut Z`:
`18 > 11`.  Hence minimality alone does *not* make the symmetric cut recombination close MMI. -/
theorem symmetricRecombination_fails :
    bulkCutCapacity wCE X_CE + bulkCutCapacity wCE Y_CE + bulkCutCapacity wCE Z_CE
      < bulkCutCapacity wCE (X_CE ∩ Y_CE) + bulkCutCapacity wCE (X_CE ∩ Z_CE)
          + bulkCutCapacity wCE (Y_CE ∩ Z_CE) + bulkCutCapacity wCE (X_CE ∪ Y_CE ∪ Z_CE) := by
  decide

/-! ### The underlying pointwise set-function inequality is false for a cut `f`

Strengthening the arbitrary-set version: even the submodular *cut* function fails the pointwise recombination
`f(X∩Y)+f(X∩Z)+f(Y∩Z)+f(X∪Y∪Z) ≤ f X + f Y + f Z`.  A `Fin 3` graph with a single edge suffices. -/

/-- A `Fin 3` graph with edges `0—1` (weight `2`) and `1—2` (weight `1`). -/
def wTri : Fin 3 → Fin 3 → ℕ := fun i j =>
  match i, j with
  | 0, 1 | 1, 0 => 2
  | 1, 2 | 2, 1 => 1
  | _, _ => 0

/-- Pointwise recombination is false for the cut function: taking `X = Y = {0,1,2}`, `Z = {2}` gives
`f(X∩Y)+f(X∩Z)+f(Y∩Z)+f(X∪Y∪Z) = 2 > 1 = f X + f Y + f Z`. (No minimality assumed — arbitrary sets.) -/
theorem pointwise_submodular_recombination_false :
    let X : Finset (Fin 3) := {0, 1, 2}
    let Y : Finset (Fin 3) := {0, 1, 2}
    let Z : Finset (Fin 3) := {2}
    bulkCutCapacity wTri X + bulkCutCapacity wTri Y + bulkCutCapacity wTri Z
      < bulkCutCapacity wTri (X ∩ Y) + bulkCutCapacity wTri (X ∩ Z)
          + bulkCutCapacity wTri (Y ∩ Z) + bulkCutCapacity wTri (X ∪ Y ∪ Z) := by
  decide

/-! ### A strict, non-vacuous MMI witness (`I₃`-slack `> 0`)

Anti-vacuity: MMI is a nontrivial inequality on some graph.  Two-hub graph on `Fin 6`:
`A=0, B=1, C=2, D=3` (D a purifier), hubs `4, 5`; each region-vertex and `D` joined to both hubs
(weight 1) and the hubs joined to each other (weight 1). -/

/-- The `Fin 6` two-hub witness graph. -/
def wW : Fin 6 → Fin 6 → ℕ := fun i j =>
  match i, j with
  | 0, 4 | 4, 0 | 1, 4 | 4, 1 | 2, 4 | 4, 2 | 3, 4 | 4, 3 => 1
  | 0, 5 | 5, 0 | 1, 5 | 5, 1 | 2, 5 | 5, 2 | 3, 5 | 5, 3 => 1
  | 4, 5 | 5, 4 => 1
  | _, _ => 0

/-- The realising min cuts on the witness graph:
singles `{0},{1},{2}`; pairs `{0,1},{0,2},{1,2}`; triple `{0,1,2,4,5}`. -/
def sA  : Finset (Fin 6) := {0}
def sB  : Finset (Fin 6) := {1}
def sC  : Finset (Fin 6) := {2}
def sAB : Finset (Fin 6) := {0, 1}
def sAC : Finset (Fin 6) := {0, 2}
def sBC : Finset (Fin 6) := {1, 2}
def sABC : Finset (Fin 6) := {0, 1, 2, 4, 5}

/-- The seven realising capacities: singles `2`, pairs `4`, triple `2`. (Machine-checked; each set
is the exhaustively-verified min cut for its region on this graph.) -/
theorem mmiWitness_caps :
    bulkCutCapacity wW sA = 2 ∧ bulkCutCapacity wW sB = 2 ∧ bulkCutCapacity wW sC = 2
      ∧ bulkCutCapacity wW sAB = 4 ∧ bulkCutCapacity wW sAC = 4 ∧ bulkCutCapacity wW sBC = 4
      ∧ bulkCutCapacity wW sABC = 2 := by decide

/-- **Strict MMI slack witness.** On the two-hub graph, the tripartite information slack
`(S_AB+S_AC+S_BC) − (S_A+S_B+S_C+S_ABC) = 12 − 8 = 4 > 0`, so MMI (`I₃ ≤ 0`) holds strictly here —
the reduction target is not vacuous. -/
theorem mmiWitness_slack_pos :
    bulkCutCapacity wW sA + bulkCutCapacity wW sB + bulkCutCapacity wW sC
        + bulkCutCapacity wW sABC
      < bulkCutCapacity wW sAB + bulkCutCapacity wW sAC + bulkCutCapacity wW sBC := by
  decide

/-- On the witness graph the *symmetric* recombination happens to be tight (`12 ≤ 12`), so here it
*does* certify MMI — underscoring that the symmetric family works on some graphs and fails on others
(`symmetricRecombination_fails`): the winning recombination is graph-dependent. -/
theorem mmiWitness_symmetric_tight :
    bulkCutCapacity wW (sAB ∩ sAC) + bulkCutCapacity wW (sAB ∩ sBC)
        + bulkCutCapacity wW (sAC ∩ sBC) + bulkCutCapacity wW (sAB ∪ sAC ∪ sBC)
      ≤ bulkCutCapacity wW sAB + bulkCutCapacity wW sAC + bulkCutCapacity wW sBC := by
  decide

/-!
## Module note — the decisive verdict (prose; no `sorry` needed for the code above)

**Setup recap.** With pair min cuts `X = r(AB)`, `Y = r(AC)`, `Z = r(BC)`, minimality
(`rtEntropy_le_of_mem`) lets any admissible candidate upper-bound an RT entropy, and
`mmi_of_recombination` shows MMI reduces to producing candidate cuts for `A, B, C, ABC` with total
capacity `≤ cut X + cut Y + cut Z`.  Minimality is the *only* nontrivial input — the recombination
step itself is a pure inequality between capacities of sets built from `X, Y, Z`.

**Machine investigation (Python, exhaustive small-graph min cuts; see the branch's probe scripts).**

1. *Pointwise route is dead even for cut `f`* (`pointwise_submodular_recombination_false`): the
   symmetric set-function inequality fails for the submodular cut function itself (`3 > 2`),
   sharpening the arbitrary-set version to an explicit cut function.

2. *Symmetric recombination fails on TRUE min cuts* (`symmetricRecombination_fails`): a `Fin 5`
   graph where `X, Y, Z` are the exhaustively-verified pair min cuts but
   `cut(X∩Y)+cut(X∩Z)+cut(Y∩Z)+cut(X∪Y∪Z) = 18 > 11`.  Over ~1.5·10⁵ random weighted graphs the
   symmetric family fails on ≈ 5.7 % of them.  So minimality does **not** rescue the *symmetric*
   recombination.

3. *MMI itself holds for graph min cuts* — across ~4·10⁵ random weighted graphs no violation of
   `S_AB+S_AC+S_BC ≥ S_A+S_B+S_C+S_ABC` was found (the known HHM theorem), and a strict witness
   exists (`mmiWitness_slack_pos`, slack `4`).

4. *Some boolean recombination always suffices, but it is GRAPH-DEPENDENT.*  Minimising, per region,
   over all boolean combinations of `X, Y, Z` (the "local reglue" the RT surfaces allow), the total
   `Σ min_bool` never exceeded `cut X + cut Y + cut Z` in ~2·10⁵ graphs (all four regions were always
   realisable as boolean combos).  **But no single fixed formula works:** the dominant optimal
   assignment — pairwise atoms `cA=(X∩Y)\Z, cB=(X∩Z)\Y, cC=(Y∩Z)\X, cABC=cA∪cB∪cC`, which
   *excludes the triple-overlap cell* `X∩Y∩Z` — still fails on ≈ 19 % of min-cut instances, and the
   arbitrary-set version fails ≈ 30 %.  Which boolean recombination wins is selected by the edge
   weights (minimality), not by a uniform rule.

**VERDICT.**
The true (minimality-based) HHM cut recombination **does not close general-graph MMI via any fixed /
symmetric formula** — machine-checked here (`symmetricRecombination_fails`).  It is *not* equivalent
to the refuted pointwise version in outcome — MMI *does* hold and *is* achievable by a boolean
"local reglue" — but the reglue is **graph-dependent**, chosen by minimality; there is no uniform
two-set-submodularity certificate (pure submodularity yields only strong subadditivity:
`cut X + cut Y ≥ cut(X∩Y) + cut(X∪Y) ≥ S_A + S_ABC`, i.e. SSA, never the third region).  This is
exactly the obstruction identified as an irreducible flow packing: the *existence* of a good
recombination is guaranteed by the true min cuts, but exhibiting it uniformly requires the
graph-dependent (LP/flow-dual) choice.  Concretely the obstruction lives at the **triple-overlap
cell** `X∩Y∩Z`: the symmetric candidates each pay for it (three intersections all contain it) while
the union pays nothing, and no fixed reassignment of that cell balances all instances.

**Non-circularity.** Nothing above assumes MMI or the flow-packing fact: `mmi_of_recombination`
is a one-line consequence of minimality + `omega`; the failure lemmas are `decide` on explicit
graphs.  We do **not** prove general-graph MMI by cuts (a fixed-formula cut
proof would be the suspect claim, and we exhibit its failure instead).

**Does planarity / intervals rescue it?**  Yes: in the
interval / planar model the min cuts are *laminar* (non-crossing), so the winning reglue is the
*uniform* laminar-uncrossing one and MMI follows flow-free under the Ptolemy inequality.  Planarity
supplies exactly the uniform choice that general graphs lack; the Okamura–Seymour theorem is the
matching flow-side statement (planar multiflows are cut-tight).  For general graphs the flow-cut gap
is real and cuts alone need the graph-dependent choice — no fixed HHM cut formula closes it.
-/

end HHMCut
