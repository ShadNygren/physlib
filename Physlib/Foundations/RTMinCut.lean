/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib

/-!
# Ryu–Takayanagi as a minimum cut (bit-threads / max-flow–min-cut foundation)

## Physics background

In the tensor-network picture of holography (MERA, perfect/random tensor networks),
the entanglement entropy of a boundary region `A` equals the weight of the
**minimum bulk cut** separating `A` from its complement `Aᶜ`.  Each bulk bond
crossing the cut contributes `log χ` (χ = bond dimension), so the capacity of a cut
is `Σ log χ` over the cut bonds.  The Ryu–Takayanagi (RT) formula
`S(A) = Area(minimal surface) / 4G` is the continuum limit of this discrete
minimum-cut statement.

Freedman–Headrick (2016, "Bit threads and holographic entanglement",
Comm. Math. Phys. 352) recast RT via **max-flow–min-cut duality**: the min cut equals
the maximum flow ("bit threads"), so `S(A)` is the maximal number of threads that can
be routed from `A` through the bulk.  The *easy* direction of the duality — every flow
value is bounded by every cut capacity ("weak duality", bit-threads ≤ min-cut) — is
elementary and formalized here.  The hard direction (min-cut ≤ max-flow, the
full duality via augmenting paths / LP duality) is documented as frontier.

## What is DERIVED vs POSITED

* **DERIVED here** (from cut geometry, pure finite combinatorics):
  - `rtEntropy` is a well-defined minimum cut (attained, nonnegative);
  - the **RT subadditivity inequality** `S(A ∪ B) ≤ S(A) + S(B)` — a holographic
    entropy-cone inequality — follows from the fact that the union of an `A`-cut and a
    `B`-cut is an `(A ∪ B)`-cut of no greater capacity;
  - **weak duality** `flow ≤ cut`.
* **POSITED** (the modeling assumption, NOT proved here): that the finite weighted
  bulk graph *is* (a discretization of) the AdS geometry.  Once that identification is
  granted, the min-cut = RT-surface statement DERIVES what the RT prescription
  (entanglement = geodesic length) and the BTZ horizon = RT surface identity take as given.
* **HONEST scope:** this is the finite discrete min-cut.  We do NOT take the continuum
  RT limit, and we prove only *weak* duality, not full max-flow–min-cut.

## Context

The subadditivity proved here is exactly the entropy-cone inequality class that the
`holographic_implies_MMI` property tests.  The min-cut framing
supplies the combinatorial backbone under the RT prescription.

## Main results

* `rtEntropy` — RT entropy of a boundary region as a minimum cut capacity.
* `rtEntropy_nonneg`, `rtEntropy_le_cutCapacity`, `exists_min_cut` — well-definedness.
* `rtEntropy_subadditive` — **headline**: `S(A ∪ B) ≤ S(A) + S(B)`.
* `weak_duality` — any flow value ≤ any cut capacity.
* `witness_*` — a concrete `Fin 3` graph with a positive min cut and a **strict**
  subadditivity instance `S(A ∪ B) < S(A) + S(B)`.

-/

@[expose] public section

namespace Physlib.RTMinCut

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **bulk graph**: a finite vertex type with a nonnegative symmetric edge weight.
`w u v` is the capacity of the bulk bond `uv` (physically `log χ`). -/
structure BulkGraph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Edge weight / bond capacity. -/
  w : V → V → ℝ
  /-- Weights are nonnegative (`log χ ≥ 0` for `χ ≥ 1`). -/
  w_nonneg : ∀ u v, 0 ≤ w u v
  /-- Weights are symmetric (undirected bulk bonds). -/
  w_symm : ∀ u v, w u v = w v u

variable (G : BulkGraph V)

/-- The **capacity of a cut** determined by a bulk region `S`: the total weight of the
edges crossing the partition `(S, Sᶜ)`.  Physically this is `Σ log χ` over the bulk
bonds cut by the surface homologous to `A` that bounds the region `S`. -/
def cutCapacity (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, G.w u v

/-- Cut capacity is nonnegative. -/
theorem cutCapacity_nonneg (S : Finset V) : 0 ≤ cutCapacity G S := by
  unfold cutCapacity
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => G.w_nonneg u v

/-- **Admissibility of a cut** `S` for a boundary region `A` against an anchored
complementary (sink) region `sink`: `S` is *homologous to `A`* — it contains `A` and its
complement contains the sink.  The sink is the fixed complementary boundary region; a cut
must keep `A` and `sink` on opposite sides.  (Without a sink, `S = univ` would trivially
cut nothing; the sink is what makes the min-cut nontrivial — physically the boundary is
partitioned into `A` and its complement.) -/
def IsAdmissibleCut (A sink S : Finset V) : Prop := A ⊆ S ∧ sink ⊆ Sᶜ

/-- The finite set of **admissible cuts** for `(A, sink)`. -/
def admissibleCuts (A sink : Finset V) : Finset (Finset V) :=
  Finset.univ.filter (fun S => A ⊆ S ∧ sink ⊆ Sᶜ)

theorem mem_admissibleCuts {A sink S : Finset V} :
    S ∈ admissibleCuts A sink ↔ (A ⊆ S ∧ sink ⊆ Sᶜ) := by
  unfold admissibleCuts
  simp

/-- If `A` and `sink` are disjoint, then `S = A` is admissible, so the admissible set is
nonempty (the minimal cut hugs `A`). -/
theorem admissibleCuts_nonempty {A sink : Finset V} (h : Disjoint A sink) :
    (admissibleCuts A sink).Nonempty := by
  refine ⟨A, ?_⟩
  rw [mem_admissibleCuts]
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro v hv
  rw [Finset.mem_compl]
  exact fun hvA => (Finset.disjoint_left.1 h) hvA hv

/-- The nonempty finite image of admissible cuts under `cutCapacity`; the RT entropy is
its minimum. -/
theorem capImage_nonempty {A sink : Finset V} (h : Disjoint A sink) :
    ((admissibleCuts A sink).image (cutCapacity G)).Nonempty :=
  (admissibleCuts_nonempty h).image _

/-- **RT entropy** of a boundary region `A` (against anchored sink `sink`, with
`Disjoint A sink`): the minimum cut capacity over all admissible cuts.  This is the
discrete Ryu–Takayanagi formula — the entanglement entropy of `A` equals the minimum bulk
surface weight homologous to `A`.

Implemented as a finite `min'` over the (nonempty) finite image of `cutCapacity`, so the
minimum is genuinely attained and no `iInf`-analysis is required. -/
noncomputable def rtEntropy {A sink : Finset V} (h : Disjoint A sink) : ℝ :=
  ((admissibleCuts A sink).image (cutCapacity G)).min' (capImage_nonempty G h)

/-- The RT entropy is `≤` the capacity of any admissible cut of `A`. -/
theorem rtEntropy_le_cutCapacity {A sink S : Finset V} (h : Disjoint A sink)
    (hS : IsAdmissibleCut A sink S) :
    rtEntropy G h ≤ cutCapacity G S := by
  apply Finset.min'_le
  refine Finset.mem_image.2 ⟨S, ?_, rfl⟩
  rw [mem_admissibleCuts]; exact hS

/-- **Existence of a minimal cut**: some admissible cut attains the RT entropy. -/
theorem exists_min_cut {A sink : Finset V} (h : Disjoint A sink) :
    ∃ S : Finset V, IsAdmissibleCut A sink S ∧ cutCapacity G S = rtEntropy G h := by
  have hmem : rtEntropy G h ∈ (admissibleCuts A sink).image (cutCapacity G) :=
    Finset.min'_mem _ (capImage_nonempty G h)
  rw [Finset.mem_image] at hmem
  obtain ⟨S, hSmem, hScap⟩ := hmem
  rw [mem_admissibleCuts] at hSmem
  exact ⟨S, hSmem, hScap⟩

/-- The RT entropy is nonnegative (it is a capacity, and capacities are nonneg). -/
theorem rtEntropy_nonneg {A sink : Finset V} (h : Disjoint A sink) :
    0 ≤ rtEntropy G h := by
  obtain ⟨S, _, hScap⟩ := exists_min_cut G h
  rw [← hScap]
  exact cutCapacity_nonneg G S

/-- Any real `c` that lower-bounds every admissible cut capacity lower-bounds the RT
entropy. -/
theorem le_rtEntropy {A sink : Finset V} {c : ℝ} (h : Disjoint A sink)
    (hlb : ∀ S : Finset V, IsAdmissibleCut A sink S → c ≤ cutCapacity G S) :
    c ≤ rtEntropy G h := by
  apply Finset.le_min'
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨S, hSmem, hScap⟩ := hx
  rw [mem_admissibleCuts] at hSmem
  rw [← hScap]
  exact hlb S hSmem

/-!
### Key geometric lemma: the cut capacity is subadditive under union

Every edge crossing the partition of `S ∪ T` (i.e. from `S ∪ T` into `(S ∪ T)ᶜ`) also
crosses the partition of `S` *or* of `T`: its tail is in `S` or in `T`, and its head is
outside both `S` and `T` (since it is outside `S ∪ T`).  With nonnegative weights this
gives `cutCapacity (S ∪ T) ≤ cutCapacity S + cutCapacity T`.
-/

/-- **Cut capacity union bound** (the geometric heart of RT subadditivity):
`cutCapacity (S ∪ T) ≤ cutCapacity S + cutCapacity T` for nonnegative weights.

We proved the weaker-but-sufficient union bound (not full submodularity): each crossing
edge of `S ∪ T` is a crossing edge of `S` or of `T`, and nonnegativity lets us bound the
`S ∪ T` sum by the (possibly larger, all-nonneg) `S`-sum plus `T`-sum. -/
theorem cutCapacity_union_le (S T : Finset V) :
    cutCapacity G (S ∪ T) ≤ cutCapacity G S + cutCapacity G T := by
  -- Bound the outer sum over `S ∪ T` by the sum over `S` plus the sum over `T`,
  -- after first extending each inner sum over `Sᶜ`/`Tᶜ` to the larger `(S ∪ T)ᶜ`ᶜ...
  -- Cleaner: define f u := ∑ v ∈ (S ∪ T)ᶜ, w u v ≥ 0 and split the outer sum.
  set c : Finset V := (S ∪ T)ᶜ with hc
  have hcsub_S : c ⊆ Sᶜ := by
    rw [hc]; intro v hv
    simp only [Finset.mem_compl, Finset.mem_union] at hv ⊢
    exact fun h => hv (Or.inl h)
  have hcsub_T : c ⊆ Tᶜ := by
    rw [hc]; intro v hv
    simp only [Finset.mem_compl, Finset.mem_union] at hv ⊢
    exact fun h => hv (Or.inr h)
  -- For each vertex u, the inner crossing-sum over c is ≤ the inner sum over Sᶜ (resp Tᶜ).
  have inner_le_S : ∀ u, (∑ v ∈ c, G.w u v) ≤ ∑ v ∈ Sᶜ, G.w u v := by
    intro u
    apply Finset.sum_le_sum_of_subset_of_nonneg hcsub_S
    intro v _ _; exact G.w_nonneg u v
  have inner_le_T : ∀ u, (∑ v ∈ c, G.w u v) ≤ ∑ v ∈ Tᶜ, G.w u v := by
    intro u
    apply Finset.sum_le_sum_of_subset_of_nonneg hcsub_T
    intro v _ _; exact G.w_nonneg u v
  -- Split the outer sum over S ∪ T using inclusion–exclusion-free subset bounds.
  calc cutCapacity G (S ∪ T)
      = ∑ u ∈ S ∪ T, ∑ v ∈ c, G.w u v := by rw [cutCapacity, hc]
    _ ≤ ∑ u ∈ S, ∑ v ∈ c, G.w u v + ∑ u ∈ T, ∑ v ∈ c, G.w u v := by
        -- outer union bound with nonneg inner sums
        have hnn : ∀ u, 0 ≤ ∑ v ∈ c, G.w u v :=
          fun u => Finset.sum_nonneg fun v _ => G.w_nonneg u v
        have hle : ∑ u ∈ S ∪ T, (fun u => ∑ v ∈ c, G.w u v) u
            ≤ ∑ u ∈ S, (fun u => ∑ v ∈ c, G.w u v) u
              + ∑ u ∈ T, (fun u => ∑ v ∈ c, G.w u v) u := by
          rw [← Finset.sum_union_inter]
          have := Finset.sum_nonneg
            (s := S ∩ T) (f := fun u => ∑ v ∈ c, G.w u v)
            (fun u _ => hnn u)
          linarith
        exact hle
    _ ≤ (∑ u ∈ S, ∑ v ∈ Sᶜ, G.w u v) + ∑ u ∈ T, ∑ v ∈ Tᶜ, G.w u v := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun u _ => inner_le_S u)
        · exact Finset.sum_le_sum (fun u _ => inner_le_T u)
    _ = cutCapacity G S + cutCapacity G T := by rw [cutCapacity, cutCapacity]

/-- **HEADLINE — RT subadditivity** `S(A ∪ B) ≤ S(A) + S(B)`.

A holographic entropy-cone inequality DERIVED from cut geometry: take a minimal `A`-cut
`S_A ⊇ A` and a minimal `B`-cut `S_B ⊇ B`; then `S_A ∪ S_B ⊇ A ∪ B` is admissible for
`A ∪ B`, and by `cutCapacity_union_le` its capacity is at most
`cutCapacity S_A + cutCapacity S_B = rtEntropy A + rtEntropy B`. -/
theorem rtEntropy_subadditive {A B sink : Finset V}
    (hA : Disjoint A sink) (hB : Disjoint B sink) :
    rtEntropy G (Finset.disjoint_union_left.2 ⟨hA, hB⟩ : Disjoint (A ∪ B) sink)
      ≤ rtEntropy G hA + rtEntropy G hB := by
  obtain ⟨SA, hSA, hSAcap⟩ := exists_min_cut G hA
  obtain ⟨SB, hSB, hSBcap⟩ := exists_min_cut G hB
  -- The union of an A-cut and a B-cut is an (A ∪ B)-cut against the shared sink.
  have hunion : IsAdmissibleCut (A ∪ B) sink (SA ∪ SB) := by
    refine ⟨Finset.union_subset_union hSA.1 hSB.1, ?_⟩
    intro v hv
    rw [Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨(Finset.mem_compl.1 (hSA.2 hv)), (Finset.mem_compl.1 (hSB.2 hv))⟩
  calc rtEntropy G (Finset.disjoint_union_left.2 ⟨hA, hB⟩ : Disjoint (A ∪ B) sink)
      ≤ cutCapacity G (SA ∪ SB) := rtEntropy_le_cutCapacity G _ hunion
    _ ≤ cutCapacity G SA + cutCapacity G SB := cutCapacity_union_le G SA SB
    _ = rtEntropy G hA + rtEntropy G hB := by rw [hSAcap, hSBcap]

/-!
## Weak duality (bit threads ≤ min cut)

A **flow** assigns to each ordered pair `(u,v)` a real `f u v` that is antisymmetric
(`f u v = - f v u`), respects capacity (`f u v ≤ w u v`), and is conserved at every
**interior** vertex (a vertex not in the source region `A` nor its sink complement).
The **value** of the flow out of `A` is `∑_{u∈A} ∑_v f u v`.

We formalize the easy "weak duality" direction of max-flow–min-cut: for a cut `S ⊇ A`
with sink side `Sᶜ` where all flow is conserved on `S \ A`, the value out of `A` equals
the net flow across the cut `(S, Sᶜ)`, which is `≤ cutCapacity S` by capacity bounds.

To keep this fully tractable, we prove the clean specialization where the
cut coincides with the source region itself (`S = A`): the value out of `A` is the net
flow across `(A, Aᶜ)`, bounded above by `cutCapacity A`.  This is precisely
"bit threads value ≤ cut capacity" for that cut, the essential weak-duality bound.
The general interior-conservation version is the frontier direction. -/

/-- A capacity-respecting assignment on ordered pairs (a "pre-flow" on the arcs). Only the
capacity bound is needed for weak duality; conservation is not required for the
cut-value ≤ capacity bound across the source cut. -/
structure Flow (G : BulkGraph V) where
  /-- Flow on the arc `u → v`. -/
  f : V → V → ℝ
  /-- Capacity constraint: flow on each arc does not exceed the bond capacity. -/
  cap : ∀ u v, f u v ≤ G.w u v

/-- The **value** of a flow across the cut determined by `S`: the net flow from `S` to
`Sᶜ`. -/
def flowCutValue {G : BulkGraph V} (F : Flow G) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, F.f u v

/-- **Weak duality (bit threads ≤ min cut), cut form.** For any flow `F` and any cut `S`,
the net flow across `(S, Sᶜ)` is at most the cut capacity.  This is the elementary,
fully-tractable direction of max-flow–min-cut: a flow can carry no more across a cut than
the cut's capacity. -/
theorem weak_duality (F : Flow G) (S : Finset V) :
    flowCutValue F S ≤ cutCapacity G S := by
  unfold flowCutValue cutCapacity
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact F.cap u v

/-- Consequently the flow value across any admissible cut of `A` is bounded by the RT
entropy of `A` **from above by every particular** cut, and in particular a flow's value
across a *minimal* cut is at most `rtEntropy A`.  (The full statement "max flow =
rtEntropy" requires the hard direction; here we record `cutValue (min cut) ≤ rtEntropy`.) -/
theorem flow_cutValue_le_rtEntropy (F : Flow G) {A sink S : Finset V}
    (h : Disjoint A sink) (hmin : cutCapacity G S = rtEntropy G h) :
    flowCutValue F S ≤ rtEntropy G h := by
  rw [← hmin]; exact weak_duality G F S

/-!
## Anti-vacuity witness

Concrete `Fin 3` bulk graph.  Vertices `0,1,2`.  Bond weights: `w 0 1 = w 1 0 = 1`,
`w 1 2 = w 2 1 = 1`, `w 0 2 = w 2 0 = 1`, all others (diagonal) `0` — a triangle with
unit bonds.

Boundary regions live on distinct vertices; take the anchored **sink** to be `{1}`
(vertex `1` is the fixed complementary boundary).  Take `A = {0}` and `B = {2}`.  We
exhibit:

* a POSITIVE min-cut value: `rtEntropy {0} (sink {1}) = 2` (the two bonds incident to the
  side containing `0` must be cut);
* STRICT subadditivity: `rtEntropy ({0} ∪ {2}) < rtEntropy {0} + rtEntropy {2}`,
  i.e. `2 < 2 + 2 = 4` — the union cut `{0,2}` (complement `{1}`) severs only the two
  bonds `0–1`, `2–1`, while the internal bond `0–2` is *not* cut (both endpoints on the
  same side), so mutual information `I(A:B) = S(A)+S(B) − S(A∪B) = 2 > 0`.
-/

/-- The witness triangle graph on `Fin 3` with unit bond weights (off-diagonal). -/
def triangle : BulkGraph (Fin 3) where
  w u v := if u = v then 0 else 1
  w_nonneg u v := by split <;> norm_num
  w_symm u v := by
    by_cases h : u = v
    · simp [h]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- Helper: the triangle weight, definitionally. -/
theorem triangle_w (u v : Fin 3) :
    triangle.w u v = if u = v then 0 else 1 := rfl

/-- Cut capacity of `{0}` in the triangle is `2` (bonds `0–1`, `0–2` cross). -/
theorem triangle_cap_0 : cutCapacity triangle ({0} : Finset (Fin 3)) = 2 := by
  have hcompl : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
  rw [cutCapacity, hcompl, Finset.sum_singleton,
    Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  rw [triangle_w, triangle_w, if_neg (by decide : (0 : Fin 3) ≠ 1),
    if_neg (by decide : (0 : Fin 3) ≠ 2)]
  norm_num

/-- Cut capacity of `{2}` in the triangle is `2` (bonds `2–0`, `2–1` cross). -/
theorem triangle_cap_2 : cutCapacity triangle ({2} : Finset (Fin 3)) = 2 := by
  have hcompl : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
  rw [cutCapacity, hcompl, Finset.sum_singleton,
    Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
  rw [triangle_w, triangle_w, if_neg (by decide : (2 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 1)]
  norm_num

/-- Cut capacity of `{0,2}` in the triangle is `2` (only bonds `0–1`, `2–1` cross;
the internal bond `0–2` stays on one side). -/
theorem triangle_cap_02 : cutCapacity triangle ({0, 2} : Finset (Fin 3)) = 2 := by
  have hcompl : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
  rw [cutCapacity, hcompl, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2),
    Finset.sum_singleton, Finset.sum_singleton]
  rw [triangle_w, triangle_w, if_neg (by decide : (0 : Fin 3) ≠ 1),
    if_neg (by decide : (2 : Fin 3) ≠ 1)]
  norm_num

/-- `A = {0}` and `sink = {1}` are disjoint (needed to form the RT entropy). -/
theorem triangle_disjoint_0 : Disjoint ({0} : Finset (Fin 3)) {1} := by decide

/-- `B = {2}` and `sink = {1}` are disjoint. -/
theorem triangle_disjoint_2 : Disjoint ({2} : Finset (Fin 3)) {1} := by decide

/-- The admissible cuts of `A = {0}` against `sink = {1}` are exactly `{{0}, {0,2}}`
(the bulk regions containing `0` and excluding `1`).  Pure `Finset (Fin 3)` computation,
no reals — `decide`-able. -/
theorem triangle_admissible_0 :
    admissibleCuts ({0} : Finset (Fin 3)) {1} = {{0}, {0, 2}} := by decide

/-- The admissible cuts of `B = {2}` against `sink = {1}` are exactly `{{2}, {0,2}}`. -/
theorem triangle_admissible_2 :
    admissibleCuts ({2} : Finset (Fin 3)) {1} = {{2}, {0, 2}} := by decide

/-- The admissible cuts of `A ∪ B = {0,2}` against `sink = {1}` are exactly `{{0,2}}`
(only the region containing both `0,2` and excluding `1`). -/
theorem triangle_admissible_02 :
    admissibleCuts (({0} : Finset (Fin 3)) ∪ {2}) {1} = {{0, 2}} := by decide

/-- **POSITIVE min cut** `rtEntropy {0} (sink {1}) = 2`: minimum of the capacities of the
two admissible cuts `{0}` (cap 2) and `{0,2}` (cap 2). -/
theorem triangle_rtEntropy_0 :
    rtEntropy triangle triangle_disjoint_0 = 2 := by
  apply le_antisymm
  · -- ≤ 2 : {0} is admissible with capacity 2
    have hadm : IsAdmissibleCut ({0} : Finset (Fin 3)) {1} {0} := by
      constructor <;> decide
    have h := rtEntropy_le_cutCapacity triangle triangle_disjoint_0 hadm
    rw [triangle_cap_0] at h; exact h
  · -- ≥ 2 : every admissible cut is {0} or {0,2}, each capacity 2
    apply le_rtEntropy
    intro S hS
    have hmem : S ∈ admissibleCuts ({0} : Finset (Fin 3)) {1} :=
      mem_admissibleCuts.2 hS
    rw [triangle_admissible_0] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · rw [h, triangle_cap_0]
    · rw [h, triangle_cap_02]

/-- `rtEntropy {2} (sink {1}) = 2` by the same computation. -/
theorem triangle_rtEntropy_2 :
    rtEntropy triangle triangle_disjoint_2 = 2 := by
  apply le_antisymm
  · have hadm : IsAdmissibleCut ({2} : Finset (Fin 3)) {1} {2} := by
      constructor <;> decide
    have h := rtEntropy_le_cutCapacity triangle triangle_disjoint_2 hadm
    rw [triangle_cap_2] at h; exact h
  · apply le_rtEntropy
    intro S hS
    have hmem : S ∈ admissibleCuts ({2} : Finset (Fin 3)) {1} :=
      mem_admissibleCuts.2 hS
    rw [triangle_admissible_2] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · rw [h, triangle_cap_2]
    · rw [h, triangle_cap_02]

/-- The disjointness of the union region `{0}∪{2}` from `sink = {1}`. -/
theorem triangle_disjoint_02 : Disjoint (({0} : Finset (Fin 3)) ∪ {2}) {1} :=
  Finset.disjoint_union_left.2 ⟨triangle_disjoint_0, triangle_disjoint_2⟩

/-- `rtEntropy ({0} ∪ {2}) (sink {1}) = 2`: the sole admissible cut is `{0,2}`, cap 2. -/
theorem triangle_rtEntropy_02 :
    rtEntropy triangle triangle_disjoint_02 = 2 := by
  apply le_antisymm
  · have hadm : IsAdmissibleCut (({0} : Finset (Fin 3)) ∪ {2}) {1} {0, 2} := by
      constructor <;> decide
    have h := rtEntropy_le_cutCapacity triangle triangle_disjoint_02 hadm
    rw [triangle_cap_02] at h; exact h
  · apply le_rtEntropy
    intro S hS
    have hmem : S ∈ admissibleCuts (({0} : Finset (Fin 3)) ∪ {2}) {1} :=
      mem_admissibleCuts.2 hS
    rw [triangle_admissible_02] at hmem
    simp only [Finset.mem_singleton] at hmem
    rw [hmem, triangle_cap_02]

/-- **STRICT subadditivity witness**: on the triangle graph with sink `{1}`,
`rtEntropy ({0} ∪ {2}) < rtEntropy {0} + rtEntropy {2}` — concretely `2 < 4`.  The
inequality is strict, so `rtEntropy_subadditive` has genuine content (mutual information
`I(A:B) = 2 > 0`). -/
theorem triangle_strict_subadditive :
    rtEntropy triangle triangle_disjoint_02
      < rtEntropy triangle triangle_disjoint_0
        + rtEntropy triangle triangle_disjoint_2 := by
  rw [triangle_rtEntropy_02, triangle_rtEntropy_0, triangle_rtEntropy_2]
  norm_num

/-- Sanity: the general `rtEntropy_subadditive` bound applies to the witness and (as the
strict version shows) holds strictly here. -/
example :
    rtEntropy triangle
        (Finset.disjoint_union_left.2 ⟨triangle_disjoint_0, triangle_disjoint_2⟩ :
          Disjoint (({0} : Finset (Fin 3)) ∪ {2}) {1})
      ≤ rtEntropy triangle triangle_disjoint_0 + rtEntropy triangle triangle_disjoint_2 :=
  rtEntropy_subadditive triangle triangle_disjoint_0 triangle_disjoint_2

/-!
## Documented frontier (NOT formalized here)

* **Full max-flow–min-cut duality** (`min cut ≤ max flow`, hence `max flow = rtEntropy`):
  the hard direction, requiring the augmenting-path algorithm / Ford–Fulkerson or
  LP-duality machinery.  Only the easy `flow ≤ cut` direction (`weak_duality`) is proved.
* **The continuum RT limit** `S(A) = Area/4G`: requires the discretization-to-geometry
  scaling limit (bond count → minimal-surface area), i.e. the identification of the
  bulk graph with AdS geometry — the modeling POSIT, not a theorem of this file.
* **Monogamy of mutual information (MMI)** from min cut (the deeper entropy-cone
  inequality): provable from cut submodularity but requires the full
  submodular inequality `cap(S∪T)+cap(S∩T) ≤ cap(S)+cap(T)`; here we proved only the
  weaker union bound sufficient for subadditivity.  MMI is left as frontier.

References: S. Ryu, T. Takayanagi, *Holographic derivation of entanglement entropy from
AdS/CFT* (2006); M. Freedman, M. Headrick, *Bit threads and holographic entanglement*,
Comm. Math. Phys. 352 (2016).
-/

end Physlib.RTMinCut
