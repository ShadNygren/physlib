/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib

/-!
# Cut submodularity ⟹ holographic entropy inequalities (SSA), with strong subadditivity

## Forest-level picture (what this file proves and why it matters)

In the holographic / tensor-network picture of emergent spacetime, the entanglement entropy
`S(A)` of a boundary region `A` is computed by the **Ryu–Takayanagi (RT) prescription**: it is
the capacity of the *minimum cut* separating `A` from a distinguished complementary "sink" region
in a finite weighted bulk graph. The geometry of these min-cuts is the source of the *holographic
entropy inequalities* — sharp constraints on entanglement that hold for geometric (min-cut) states
but **fail for general quantum states**. This file derives those inequalities from pure finite
combinatorics — no differential geometry, no operator theory.

The engine is **submodularity of the cut-capacity function**:
  `cap(S ∪ T) + cap(S ∩ T) ≤ cap(S) + cap(T)`,
a standard edge-by-edge fact for nonnegative symmetric weights. From it we derive the RT/geometric
form of **strong subadditivity (SSA)**:
  `S(A∪B) + S(B∪C) ≥ S(A∪B∪C) + S(B)`,
a headline holographic entropy inequality, by taking the min-cuts of the two pairs and combining
their union and intersection.

## Results

* `cutCapacity_submodular` — the engine: submodularity of the min-cut capacity.
* `rtEntropy_strong_subadditive` — the headline: strong subadditivity of the RT
  min-cut entropy, derived from submodularity.
* `ssa_strict_witness` — **anti-vacuity**: a concrete 4-vertex weighted graph on which SSA
  is *strict* (`S(AB)+S(BC) = 10 > 6 = S(ABC)+S(B)`) with all four min-cuts *positive*
  (`5, 5, 5, 1`). This certifies the inequality has genuine content, not a `0 ≤ 0` vacuity.

## DERIVED vs POSITED

* **DERIVED (from finite cut geometry, no extra axioms):** submodularity (`cutCapacity_submodular`)
  and strong subadditivity (`rtEntropy_strong_subadditive`). These are theorems of finite
  combinatorics/discrete optimization.
* **POSITED (the modeling assumption, not proved here):** that the bulk tensor-network graph
  approximates an AdS geometry, i.e. that the RT min-cut prescription *is* the entanglement entropy
  of the physical state. That is a physics modeling choice; given it, SSA of the geometric entropy
  is a theorem.

## Context: the SSA branch of the holographic entropy cone

The monogamy of mutual information (MMI) is often *axiomatized* as a property of holographic
(min-cut) entropies. This file instead *derives* the submodularity engine and SSA — the same
geometric source — from finite cut geometry, replacing an assumed input by a proven theorem for the
SSA branch of the entropy cone. It uses an anchored-sink construction for the admissible cuts
(`IsAdmissibleCut A sink S := A ⊆ S ∧ sink ⊆ Sᶜ`, with `Disjoint A sink`) to avoid the
`S = univ ⇒ every cut 0` vacuity trap. See the note below (`## Monogamy of mutual information (MMI)`)
for why full MMI does *not* reduce to a single pointwise edge inequality and is the remaining step.

## Monogamy of mutual information (MMI) — status and the mathematical obstruction

MMI, `I₃(A:B:C) = S_A+S_B+S_C − S_{AB}−S_{AC}−S_{BC}+S_{ABC} ≤ 0`, is the *sharp* holographic
inequality: true for min-cut/geometric entropies, false for general quantum states.

Unlike SSA, **MMI does not follow from a single pointwise (edge-by-edge) submodularity-style
inequality** applied to the three pairwise RT surfaces. Concretely: with `X, Y, Z` the min-cuts of
`AB, AC, BC`, the containments `A ⊆ X∩Y`, `B ⊆ X∩Z`, `C ⊆ Y∩Z`, `A∪B∪C ⊆ X∪Y∪Z` hold, but the
per-edge inequality
  `ind(X∩Y) + ind(X∩Z) + ind(Y∩Z) + ind(X∪Y∪Z) ≤ ind(X) + ind(Y) + ind(Z)`
is **FALSE** (e.g. an edge `(u,v)` with `u ∈ X∩Y∩Z`, `v ∈ X∩Y`, `v ∉ Z` gives LHS `= 2 > 1 =`
RHS). An exhaustive search over all boolean set-expressions in `X, Y, Z` respecting the containment
constraints confirms *no* fixed pointwise combination yields MMI. MMI genuinely requires the
*minimality* (optimality) of the pairwise cuts in a nested/contraction argument
(Hayden–Headrick–Maloney), not just the lattice combination that suffices for SSA. Formalizing that
nested-optimality argument is the remaining step for the full MMI result — it uses the *same* submodularity engine
(`cutCapacity_submodular`) proved here, applied inside a min-cut swapping argument. It is left as the
documented open step (no `sorry`): this file delivers the engine + SSA + a strict witness.
-/

@[expose] public section

namespace Physlib.CutSubmodularMMI

open Finset

/-!
## The bulk graph, cut capacity, admissible cuts, and RT entropy

These local definitions mirror `RTMinCut.lean` (which lives on a *different* branch and is
deliberately **not** imported here — this file is self-contained). `V` is a finite vertex set with
decidable equality; `w` is a nonnegative symmetric edge weight.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The capacity of the cut defined by a vertex set `S`: the total weight of edges crossing from
`S` to its complement. -/
def cutCapacity (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v

/-! ### Submodularity of the cut capacity (the engine)

We rewrite `cutCapacity` as a double sum over `univ × univ` of per-edge indicator contributions,
then bound it edge-by-edge. The crux is the boolean fact `edge_submodular`: for each ordered pair
`(u,v)`, the four indicator contributions satisfy the submodular inequality, provable by exhausting
the `16` membership cases. Multiplying by the nonnegative weight `w u v` and summing lifts it to the
capacity inequality.
-/

/-- `cutCapacity` written as a double sum over all ordered pairs with indicator weights.
An edge `(u,v)` contributes `w u v` to `cap S` exactly when `u ∈ S ∧ v ∈ Sᶜ`. -/
theorem cutCapacity_indicator (w : V → V → ℝ) (S : Finset V) :
    (∑ u, ∑ v, w u v * (if u ∈ S ∧ v ∈ Sᶜ then (1 : ℝ) else 0)) = cutCapacity w S := by
  unfold cutCapacity
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => u ∈ S)]
  have hnot : ∀ u ∈ Finset.univ.filter (fun u => ¬ u ∈ S),
      (∑ v, w u v * (if u ∈ S ∧ v ∈ Sᶜ then (1 : ℝ) else 0)) = 0 := by
    intro u hu
    simp only [Finset.mem_filter] at hu
    exact Finset.sum_eq_zero (fun v _ => by simp [hu.2])
  rw [Finset.sum_eq_zero hnot, add_zero]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u ∈ S := hu
  have hstep : ∀ v, w u v * (if u ∈ S ∧ v ∈ Sᶜ then (1 : ℝ) else 0)
      = (if v ∈ Sᶜ then w u v else 0) := by
    intro v; simp only [hu', true_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun v _ => hstep v)]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The per-edge boolean submodular inequality: for one ordered pair, the indicator contribution to
`cap(S∪T)` plus `cap(S∩T)` is at most that to `cap S` plus `cap T`. Here `a = u ∈ S`, `b = v ∈ S`,
`a' = u ∈ T`, `b' = v ∈ T`; an edge crosses `X` iff `u ∈ X ∧ v ∉ X`. Proved by exhausting the 16
membership cases. -/
theorem edge_submodular (a b : Prop) [Decidable a] [Decidable b]
    (a' b' : Prop) [Decidable a'] [Decidable b'] :
    ((if (a ∨ a') ∧ ¬(b ∨ b') then (1 : ℝ) else 0)
      + (if (a ∧ a') ∧ ¬(b ∧ b') then (1 : ℝ) else 0))
    ≤ (if a ∧ ¬b then (1 : ℝ) else 0) + (if a' ∧ ¬b' then (1 : ℝ) else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases ha' : a' <;> by_cases hb' : b' <;>
    simp_all

/-- **Cut submodularity (the engine).** For nonnegative weights, the cut-capacity function
is submodular:
  `cap(S ∪ T) + cap(S ∩ T) ≤ cap S + cap T`.
This is the geometric source of the holographic entropy inequalities. -/
theorem cutCapacity_submodular (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S T : Finset V) :
    cutCapacity w (S ∪ T) + cutCapacity w (S ∩ T) ≤ cutCapacity w S + cutCapacity w T := by
  rw [← cutCapacity_indicator w (S ∪ T), ← cutCapacity_indicator w (S ∩ T),
      ← cutCapacity_indicator w S, ← cutCapacity_indicator w T]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  have hbase := edge_submodular (u ∈ S) (v ∈ S) (u ∈ T) (v ∈ T)
  calc
    w u v * (if (u ∈ S ∨ u ∈ T) ∧ ¬(v ∈ S ∨ v ∈ T) then (1 : ℝ) else 0)
        + w u v * (if (u ∈ S ∧ u ∈ T) ∧ ¬(v ∈ S ∧ v ∈ T) then (1 : ℝ) else 0)
      = w u v * (((if (u ∈ S ∨ u ∈ T) ∧ ¬(v ∈ S ∨ v ∈ T) then (1 : ℝ) else 0)
          + (if (u ∈ S ∧ u ∈ T) ∧ ¬(v ∈ S ∧ v ∈ T) then (1 : ℝ) else 0))) := by ring
    _ ≤ w u v * (((if u ∈ S ∧ ¬ v ∈ S then (1 : ℝ) else 0)
          + (if u ∈ T ∧ ¬ v ∈ T then (1 : ℝ) else 0))) :=
        mul_le_mul_of_nonneg_left hbase (hw u v)
    _ = w u v * (if u ∈ S ∧ ¬ v ∈ S then (1 : ℝ) else 0)
          + w u v * (if u ∈ T ∧ ¬ v ∈ T then (1 : ℝ) else 0) := by ring

/-! ### RT entropy via anchored min-cuts

Following the anchored-sink design: a cut is *admissible* for region `A` (with a
distinguished `sink` region) when it contains `A` and stays disjoint from `sink`. Requiring the sink
in the complement is what keeps the min-cut from collapsing to `0` (taking `S = univ`). When
`Disjoint A sink`, `A` itself is admissible, so the set of admissible cuts is nonempty and the RT
entropy is a genuine minimum. -/

/-- The finite set of admissible cuts for region `A` with the given `sink`. -/
def admissibleCuts (A sink : Finset V) : Finset (Finset V) :=
  Finset.univ.filter (fun S => A ⊆ S ∧ sink ⊆ Sᶜ)

@[simp] theorem mem_admissibleCuts {A sink S : Finset V} :
    S ∈ admissibleCuts A sink ↔ (A ⊆ S ∧ sink ⊆ Sᶜ) := by simp [admissibleCuts]

/-- When `A` and the sink are disjoint, `A` itself is an admissible cut. -/
theorem A_mem_admissible {A sink : Finset V} (h : Disjoint A sink) :
    A ∈ admissibleCuts A sink := by
  rw [mem_admissibleCuts]
  exact ⟨subset_rfl, fun x hx => Finset.mem_compl.mpr
    (fun hxA => (Finset.disjoint_left.mp h hxA) hx)⟩

theorem admissibleCuts_nonempty {A sink : Finset V} (h : Disjoint A sink) :
    (admissibleCuts A sink).Nonempty := ⟨A, A_mem_admissible h⟩

/-- The **Ryu–Takayanagi min-cut entropy** of region `A` with the given `sink`: the minimum cut
capacity over admissible cuts (defaulting to `0` on the vacuous, sink-not-anchored case, which the
`Disjoint A sink` hypotheses below exclude). -/
noncomputable def rtEntropy (w : V → V → ℝ) (sink A : Finset V) : ℝ :=
  if h : ((admissibleCuts A sink).image (cutCapacity w)).Nonempty then
    ((admissibleCuts A sink).image (cutCapacity w)).min' h
  else 0

/-- The RT entropy is a lower bound of the capacity of *any* admissible cut (min ≤ each element). -/
theorem rtEntropy_le_cut (w : V → V → ℝ) {A sink S : Finset V}
    (h : Disjoint A sink) (hS : S ∈ admissibleCuts A sink) :
    rtEntropy w sink A ≤ cutCapacity w S := by
  have hne : ((admissibleCuts A sink).image (cutCapacity w)).Nonempty :=
    (admissibleCuts_nonempty h).image _
  simp only [rtEntropy, hne, dif_pos]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hS)

/-- There is an admissible cut whose capacity *achieves* the RT entropy (the RT surface). -/
theorem exists_min_cut (w : V → V → ℝ) {A sink : Finset V} (h : Disjoint A sink) :
    ∃ S ∈ admissibleCuts A sink, rtEntropy w sink A = cutCapacity w S := by
  have hne : ((admissibleCuts A sink).image (cutCapacity w)).Nonempty :=
    (admissibleCuts_nonempty h).image _
  have hmem := Finset.min'_mem _ hne
  simp only [Finset.mem_image] at hmem
  obtain ⟨S, hS, hSval⟩ := hmem
  exact ⟨S, hS, by simp only [rtEntropy, hne, dif_pos]; exact hSval.symm⟩

/-- If every admissible cut has capacity at least `c`, then so does the RT entropy (`c ≤ min`). -/
theorem le_rtEntropy (w : V → V → ℝ) {A sink : Finset V} (h : Disjoint A sink)
    {c : ℝ} (hc : ∀ S ∈ admissibleCuts A sink, c ≤ cutCapacity w S) :
    c ≤ rtEntropy w sink A := by
  have hne : ((admissibleCuts A sink).image (cutCapacity w)).Nonempty :=
    (admissibleCuts_nonempty h).image _
  simp only [rtEntropy, hne, dif_pos]
  apply Finset.le_min'
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  exact hc S hS

/-! ### Admissible-cut lattice operations

The union of admissible cuts of `A` and `A'` is an admissible cut of `A ∪ A'`; the intersection is
an admissible cut of `A ∩ A'`. Admissibility is monotone in the region. These let us combine the RT
surfaces of two regions into candidate cuts for their union and intersection — the geometric heart
of strong subadditivity. -/

theorem admissible_union {A A' sink S S' : Finset V}
    (hS : S ∈ admissibleCuts A sink) (hS' : S' ∈ admissibleCuts A' sink) :
    (S ∪ S') ∈ admissibleCuts (A ∪ A') sink := by
  rw [mem_admissibleCuts] at hS hS' ⊢
  refine ⟨Finset.union_subset_union hS.1 hS'.1, ?_⟩
  intro x hx
  simp only [Finset.mem_compl, Finset.mem_union, not_or]
  exact ⟨fun h => (Finset.mem_compl.mp (hS.2 hx)) h, fun h => (Finset.mem_compl.mp (hS'.2 hx)) h⟩

theorem admissible_inter {A A' sink S S' : Finset V}
    (hS : S ∈ admissibleCuts A sink) (hS' : S' ∈ admissibleCuts A' sink) :
    (S ∩ S') ∈ admissibleCuts (A ∩ A') sink := by
  rw [mem_admissibleCuts] at hS hS' ⊢
  refine ⟨Finset.inter_subset_inter hS.1 hS'.1, ?_⟩
  intro x hx
  simp only [Finset.mem_compl, Finset.mem_inter, not_and_or]
  left
  exact Finset.mem_compl.mp (hS.2 hx)

theorem admissible_mono {A A' sink S : Finset V} (hAA : A ⊆ A')
    (hS : S ∈ admissibleCuts A' sink) : S ∈ admissibleCuts A sink := by
  rw [mem_admissibleCuts] at hS ⊢
  exact ⟨hAA.trans hS.1, hS.2⟩

/-! ### Strong subadditivity (the headline holographic inequality)

Take the RT surfaces `S_AB ⊇ A∪B` and `S_BC ⊇ B∪C`. Their union covers `A∪B∪C` (admissible for the
triple) and their intersection covers `B` (admissible for `B`). Submodularity of the cut capacity on
these two surfaces then gives
  `cap(S_AB) + cap(S_BC) ≥ cap(S_AB ∪ S_BC) + cap(S_AB ∩ S_BC) ≥ S(A∪B∪C) + S(B)`,
i.e. `S(A∪B) + S(B∪C) ≥ S(A∪B∪C) + S(B)`. -/

/-- **Strong subadditivity of the RT min-cut entropy** (RT/geometric form):
  `S(A∪B) + S(B∪C) ≥ S(A∪B∪C) + S(B)`.
Derived from `cutCapacity_submodular` applied to the two pairwise RT surfaces. This is a headline
holographic entropy inequality. -/
theorem rtEntropy_strong_subadditive (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v)
    {A B C sink : Finset V}
    (hAB : Disjoint (A ∪ B) sink) (hBC : Disjoint (B ∪ C) sink)
    (hABC : Disjoint (A ∪ B ∪ C) sink) (hB : Disjoint B sink) :
    rtEntropy w sink (A ∪ B ∪ C) + rtEntropy w sink B
      ≤ rtEntropy w sink (A ∪ B) + rtEntropy w sink (B ∪ C) := by
  obtain ⟨Sab, hSab, hSabval⟩ := exists_min_cut w hAB
  obtain ⟨Sbc, hSbc, hSbcval⟩ := exists_min_cut w hBC
  -- `Sab ∪ Sbc` is admissible for `(A∪B) ∪ (B∪C) = A∪B∪C`.
  have hun : (Sab ∪ Sbc) ∈ admissibleCuts (A ∪ B ∪ C) sink := by
    have hset : ((A ∪ B) ∪ (B ∪ C)) = A ∪ B ∪ C := by
      ext x; simp only [Finset.mem_union]; tauto
    rw [← hset]
    exact admissible_union hSab hSbc
  -- `Sab ∩ Sbc` is admissible for `(A∪B) ∩ (B∪C) ⊇ B`, hence for `B`.
  have hinter : (Sab ∩ Sbc) ∈ admissibleCuts B sink := by
    apply admissible_mono (A' := (A ∪ B) ∩ (B ∪ C))
    · intro x hx; simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢; tauto
    · exact admissible_inter hSab hSbc
  have h1 : rtEntropy w sink (A ∪ B ∪ C) ≤ cutCapacity w (Sab ∪ Sbc) :=
    rtEntropy_le_cut w hABC hun
  have h2 : rtEntropy w sink B ≤ cutCapacity w (Sab ∩ Sbc) :=
    rtEntropy_le_cut w hB hinter
  have hsub := cutCapacity_submodular w hw Sab Sbc
  rw [hSabval, hSbcval]
  linarith [h1, h2, hsub]

/-! ## Anti-vacuity witness

A concrete 4-vertex weighted graph on which strong subadditivity is *strict*, with all four RT
min-cuts *positive* — certifying that the inequality carries genuine holographic content (not a
degenerate `0 ≤ 0`).

Vertices `Fin 4`: `sink = {0}`, `A = {1}`, `B = {2}`, `C = {3}`. Symmetric nonnegative weights:
`w(0,1)=2, w(0,2)=1, w(0,3)=2, w(1,3)=2` (all other pairs `0`). The min-cuts are
`S(AB)=S(BC)=S(ABC)=5` and `S(B)=1`, so `S(AB)+S(BC) = 10 > 6 = S(ABC)+S(B)`: SSA is strict. -/

/-- Witness graph: symmetric nonnegative weights on `Fin 4`. -/
def wG : Fin 4 → Fin 4 → ℝ := fun i j =>
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 2
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 2
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 2
  else 0

theorem wG_nonneg : ∀ u v, 0 ≤ wG u v := by
  intro u v; unfold wG
  split <;> [norm_num; skip]
  split <;> [norm_num; skip]
  split <;> [norm_num; skip]
  split <;> norm_num

/-- Evaluate a concrete cut capacity for `wG` via the indicator form and `Fin.sum_univ_four`. -/
theorem cutCapacity_eval (S : Finset (Fin 4)) :
    cutCapacity wG S = ∑ u : Fin 4, ∑ v : Fin 4, wG u v * (if u ∈ S ∧ v ∈ Sᶜ then (1 : ℝ) else 0) :=
  (cutCapacity_indicator wG S).symm

/-- Lower bound: every admissible cut for `AB = {1,2}` (sink `{0}`) has capacity ≥ 5, so
`S(AB) ≥ 5`. (The two admissible cuts are `{1,2}` and `{1,2,3}`, capacities `5` and `5`.) -/
theorem rtAB_ge : (5 : ℝ) ≤ rtEntropy wG {0} {1, 2} := by
  apply le_rtEntropy wG (by decide)
  intro S hS
  fin_cases hS <;>
    (rw [cutCapacity_eval]
     simp only [Fin.sum_univ_four, wG, Finset.mem_insert, Finset.mem_singleton,
       Finset.mem_compl, Fin.reduceEq, Fin.reduceFinMk, Fin.isValue]
     norm_num [Fin.ext_iff])

/-- Lower bound: `S(BC) ≥ 5`. -/
theorem rtBC_ge : (5 : ℝ) ≤ rtEntropy wG {0} {2, 3} := by
  apply le_rtEntropy wG (by decide)
  intro S hS
  fin_cases hS <;>
    (rw [cutCapacity_eval]
     simp only [Fin.sum_univ_four, wG, Finset.mem_insert, Finset.mem_singleton,
       Finset.mem_compl, Fin.reduceEq, Fin.reduceFinMk, Fin.isValue]
     norm_num [Fin.ext_iff])

/-- Upper bound: `S(ABC) ≤ 5` (the cut `{1,2,3}` is admissible with capacity `5`). -/
theorem rtABC_le : rtEntropy wG {0} {1, 2, 3} ≤ 5 := by
  have hadm : ({1, 2, 3} : Finset (Fin 4)) ∈ admissibleCuts {1, 2, 3} {0} := by decide
  have hle := rtEntropy_le_cut wG (by decide : Disjoint ({1, 2, 3} : Finset (Fin 4)) {0}) hadm
  refine hle.trans ?_
  rw [cutCapacity_eval]
  simp only [Fin.sum_univ_four, wG, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_compl, Fin.reduceEq, Fin.reduceFinMk, Fin.isValue]
  norm_num [Fin.ext_iff]

/-- Upper bound: `S(B) ≤ 1` (the cut `{2}` is admissible with capacity `1`). -/
theorem rtB_le : rtEntropy wG {0} {2} ≤ 1 := by
  have hadm : ({2} : Finset (Fin 4)) ∈ admissibleCuts {2} {0} := by decide
  have hle := rtEntropy_le_cut wG (by decide : Disjoint ({2} : Finset (Fin 4)) {0}) hadm
  refine hle.trans ?_
  rw [cutCapacity_eval]
  simp only [Fin.sum_univ_four, wG, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_compl, Fin.reduceEq, Fin.reduceFinMk, Fin.isValue]
  norm_num [Fin.ext_iff]

/-- **Anti-vacuity witness:** strong subadditivity is *strict* on `wG`:
  `S(ABC) + S(B) = 5 + 1 = 6 < 10 = 5 + 5 = S(AB) + S(BC)`,
with all four min-cuts positive. This certifies `rtEntropy_strong_subadditive` has genuine content
(not `0 ≤ 0`). -/
theorem ssa_strict_witness :
    rtEntropy wG {0} {1, 2, 3} + rtEntropy wG {0} {2}
      < rtEntropy wG {0} {1, 2} + rtEntropy wG {0} {2, 3} := by
  have h1 := rtAB_ge
  have h2 := rtBC_ge
  have h3 := rtABC_le
  have h4 := rtB_le
  linarith

/-- Positivity certificate for the witness min-cuts: each of the four RT entropies appearing in the
strict SSA witness is strictly positive. -/
theorem ssa_witness_mincuts_pos :
    0 < rtEntropy wG {0} {1, 2} ∧ 0 < rtEntropy wG {0} {2, 3} ∧
    0 < rtEntropy wG {0} {1, 2, 3} ∧ 0 < rtEntropy wG {0} {2} := by
  refine ⟨by linarith [rtAB_ge], by linarith [rtBC_ge], ?_, ?_⟩
  · -- S(ABC) ≥ 5 > 0 (same lower-bound argument as AB/BC)
    have : (5 : ℝ) ≤ rtEntropy wG {0} {1, 2, 3} := by
      apply le_rtEntropy wG (by decide)
      intro S hS
      fin_cases hS <;>
        (rw [cutCapacity_eval]
         simp only [Fin.sum_univ_four, wG, Finset.mem_insert, Finset.mem_singleton,
           Finset.mem_compl, Fin.reduceEq, Fin.reduceFinMk, Fin.isValue]
         norm_num [Fin.ext_iff])
    linarith
  · -- S(B) ≥ 1 > 0
    have : (1 : ℝ) ≤ rtEntropy wG {0} {2} := by
      apply le_rtEntropy wG (by decide)
      intro S hS
      fin_cases hS <;>
        (rw [cutCapacity_eval]
         simp only [Fin.sum_univ_four, wG, Finset.mem_insert, Finset.mem_singleton,
           Finset.mem_compl, Fin.reduceEq, Fin.reduceFinMk, Fin.isValue]
         norm_num [Fin.ext_iff])
    linarith

end Physlib.CutSubmodularMMI
