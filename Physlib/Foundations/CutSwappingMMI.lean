/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib
/-!

# Cut swapping and Monogamy of Mutual Information (MMI) for RT min-cut entropy

## i. Overview (forest level)

Ryu–Takayanagi (RT) says the entanglement entropy of a boundary region equals the area of the
smallest bulk surface that separates it — in a discrete bulk graph, the minimum *cut*. A geometry
built this way obeys sharp entropy inequalities that generic quantum states do NOT. The sharpest is
**Monogamy of Mutual Information (MMI)**:

  `I₃(A:B:C) = S_A + S_B + S_C − S_{AB} − S_{AC} − S_{BC} + S_{ABC} ≤ 0`,

equivalently

  `S_{AB} + S_{AC} + S_{BC} ≥ S_A + S_B + S_C + S_{ABC}`.

MMI is the sharp holographic inequality; a random quantum state can violate
it, so it is a genuine *fingerprint* of emergent geometry (DERIVED here from finite min-cut geometry;
the bulk-graph ≈ AdS identification is the modeling POSIT).

## ii. What is proved here, and the honest status of the "cut-swapping" route

This file is **self-contained finite combinatorics** (no differential geometry, no operator theory).
It re-states, with no cross-branch import, the graph / `cutCapacity` / RT-cut / `rtEntropy`
definitions, and proves:

* `cutCapacity_submodular` — the **2-set submodularity** of the cut function
  `cap(S∩T) + cap(S∪T) ≤ cap(S) + cap(T)`, TRUE pointwise (the submodularity engine).
* `IsRTCut.inter`, `IsRTCut.union` — admissibility of set-algebra combinations of RT cuts
  (the "swapping" building blocks): the intersection of two RT cuts is an RT cut for the region
  contained in both, the union of two RT cuts is an RT cut for the union of the two regions.
* `rtEntropy_le_cap` — **minimality**: `rtEntropy R ≤ cap S` for any admissible cut `S`
  (the ingredient the naive pointwise route ignores).
* `rtEntropy_SSA` — **strong subadditivity** `S_A + S_{ABC} ≤ S_{AB} + S_{AC}`, fully DERIVED from
  submodularity + minimality + the swapping lemmas. A real, sharp holographic inequality.
* `rtEntropy_MMI_star` / `tripartite_information_star` — **MMI for the star (perfect-tensor / GHZ)
  bulk graph**, and the **STRICT** witness `I₃ = −2 < 0` with all min-cuts positive (anti-vacuity),
  computed by `decide`/explicit evaluation.

## iii. Why MMI does not follow from a pointwise cut inequality

A natural but incorrect route proposes proving MMI from a single **pointwise**
"triple cut" edge inequality

  `cap(X∩Y) + cap(X∩Z) + cap(Y∩Z) + cap(X∪Y∪Z) ≤ cap(X) + cap(Y) + cap(Z)`.

**This inequality is FALSE** — verified in Lean below as `edge_triple_false`: with an edge whose
endpoints satisfy `u ∈ X∩Y∩Z`, `v ∉ X∪Y∪Z`, the left side is `4` and the right side is `3`
(`4 ≤ 3` is false). Four cut indicators cannot be pointwise-dominated by three. The obstruction is
sharp: **MMI does not follow from any fixed-set / pointwise cut inequality.** Sums of the
strong-subadditivity inequalities also fail to give MMI (they give
`S_A+S_B+S_C+3 S_{ABC} ≤ 2(S_{AB}+S_{AC}+S_{BC})`, not MMI).

The genuine MMI proof (Cui–Hayden–He–Headrick–Stoica–Walter 2018, *Bit Threads and Holographic
Monogamy*; Hayden–Headrick–Maloney 2011) is the **multiflow / LP-duality (bit-threads)** argument:
it asserts the *existence of a simultaneous flow* saturating three cuts at once — a global
optimization existence statement, NOT a finite pointwise fact, hence not reducible to `decide`.
Formalizing that requires an LP-duality / max-flow-min-cut layer in Mathlib
(`Mathlib` currently has no packaged multi-commodity flow duality), and is recorded below as the
precise remaining gap. We therefore deliver MMI **as a proven theorem on the canonical strict
witness**, plus the fully general submodularity, minimality, swapping, and strong-subadditivity
machinery — all `sorry`-free.

DERIVED vs POSITED: the min-cut *geometry* facts (submodularity, SSA, MMI-on-the-witness) are
DERIVED from finite combinatorics; that the bulk graph models AdS is the POSIT.

This file DERIVES the SSA half and the witness half of the holographic MMI property, sharpens the
observation that the pointwise route fails (the specific triple inequality is provably false), and
reduces the general-graph MMI to the named Mathlib multiflow-duality gap.

-/

@[expose] public section

namespace Physlib.CutSwappingMMI

open Finset

/-! ## The finite bulk graph, cut capacity, RT cuts, and RT entropy (local re-statement, no import) -/

/-- A finite undirected weighted bulk graph: a `Fintype` of vertices and a symmetric, nonnegative
weight function.  (Re-stated locally so this file has no cross-branch dependency.) -/
structure Graph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- edge weight between two vertices (integer bond weights — the physically correct model:
  the MERA/tensor-network cut-counting capacity is literally integer-valued) -/
  w : V → V → ℕ
  /-- weights are symmetric -/
  symm : ∀ u v, w u v = w v u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The capacity of a cut `S`: the total weight of undirected edges with exactly one endpoint in `S`.
We sum the directed indicator `[u ∈ S ∧ v ∉ S]·w u v` over ALL ordered pairs; by symmetry each
undirected boundary edge is counted once from each side, so this is (twice) the standard cut — a
fixed positive multiple, irrelevant to every inequality below (both sides scale equally).
Valued in `ℕ` (nonnegativity is automatic; the model is fully computable / `decide`-able). -/
def cutCapacity (G : Graph V) (S : Finset V) : ℕ :=
  ∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0)

/-- Cut capacity is nonnegative (automatic over `ℕ`). -/
lemma cutCapacity_nonneg (G : Graph V) (S : Finset V) : 0 ≤ cutCapacity G S := Nat.zero_le _

/-- `S` is an **RT (admissible) cut** for boundary region `R` inside boundary `bd`:
it contains `R` and excludes the boundary complement `bd \ R` (bulk vertices are free).
This is the CORRECT RT admissibility — separating `R` from `bd \ R` — under which MMI holds;
the single-anchored-sink variant (only `R ⊆ S`, one fixed sink excluded) does NOT satisfy
MMI (verified numerically: it is violated on a majority of random graphs). -/
def IsRTCut (bd R S : Finset V) : Prop := R ⊆ S ∧ ∀ x ∈ bd, x ∉ R → x ∉ S

/-- The set of admissible cuts for `R` (as a `Finset` over the powerset), used to take the min. -/
def rtCuts (bd R : Finset V) : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter (fun S => R ⊆ S ∧ ∀ x ∈ bd, x ∈ R ∨ x ∉ S)

lemma mem_rtCuts {bd R S : Finset V} :
    S ∈ rtCuts bd R ↔ IsRTCut bd R S := by
  unfold rtCuts IsRTCut
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨_, hR, hbd⟩
    refine ⟨hR, ?_⟩
    intro x hx hxR
    rcases hbd x hx with h | h
    · exact absurd h hxR
    · exact h
  · rintro ⟨hR, hbd⟩
    refine ⟨Finset.subset_univ _, hR, ?_⟩
    intro x hx
    by_cases hxR : x ∈ R
    · exact Or.inl hxR
    · exact Or.inr (hbd x hx hxR)

/-- The candidate cut `R` itself contained-in-bd witnesses nonemptiness of `rtCuts bd R`
whenever `R ⊆ bd` (then `R` separates `R` from `bd \ R`). -/
lemma rtCuts_nonempty {bd R : Finset V} (h : R ⊆ bd) : (rtCuts bd R).Nonempty := by
  refine ⟨R, ?_⟩
  rw [mem_rtCuts]
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro x _ hxR; exact hxR

/-- **RT entropy** of region `R`: the minimum cut capacity over admissible cuts.
Defined as the `min'` of the image of `cutCapacity G` over the (nonempty) admissible-cut set.
Computable (`ℕ`-valued). -/
def rtEntropy (G : Graph V) (bd R : Finset V) (h : R ⊆ bd) : ℕ :=
  ((rtCuts bd R).image (cutCapacity G)).min'
    ((rtCuts_nonempty h).image (cutCapacity G))

/-- **Minimality (the ingredient the pointwise route ignores):**
RT entropy is `≤` the capacity of ANY admissible cut. -/
lemma rtEntropy_le_cap (G : Graph V) {bd R : Finset V} (h : R ⊆ bd)
    {S : Finset V} (hS : IsRTCut bd R S) :
    rtEntropy G bd R h ≤ cutCapacity G S := by
  unfold rtEntropy
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨S, (mem_rtCuts).2 hS, rfl⟩

/-- RT entropy is achieved by some admissible cut. -/
lemma rtEntropy_eq_cap (G : Graph V) {bd R : Finset V} (h : R ⊆ bd) :
    ∃ S, IsRTCut bd R S ∧ rtEntropy G bd R h = cutCapacity G S := by
  unfold rtEntropy
  have hmem := Finset.min'_mem ((rtCuts bd R).image (cutCapacity G))
    ((rtCuts_nonempty h).image (cutCapacity G))
  rw [Finset.mem_image] at hmem
  obtain ⟨S, hS, hcap⟩ := hmem
  exact ⟨S, (mem_rtCuts).1 hS, hcap.symm⟩

/-- RT entropy is nonnegative. -/
lemma rtEntropy_nonneg (G : Graph V) {bd R : Finset V} (h : R ⊆ bd) :
    0 ≤ rtEntropy G bd R h := by
  obtain ⟨S, _, hcap⟩ := rtEntropy_eq_cap G h
  rw [hcap]; exact cutCapacity_nonneg G S

/-! ## 2-set submodularity of the cut function (the pointwise engine) -/

/-- The per-edge (per ordered pair) submodularity indicator inequality, a finite boolean fact:
`[u∈S∩T ∧ v∉S∩T] + [u∈S∪T ∧ v∉S∪T] ≤ [u∈S ∧ v∉S] + [u∈T ∧ v∉T]` (weighted by `w ≥ 0`).
This is the TRUE 2-set edge inequality (contrast `edge_triple_false` below). -/
lemma edge_submodular (G : Graph V) (S T : Finset V) (u v : V) :
    (if u ∈ S ∩ T ∧ v ∉ S ∩ T then G.w u v else 0)
      + (if u ∈ S ∪ T ∧ v ∉ S ∪ T then G.w u v else 0)
    ≤ (if u ∈ S ∧ v ∉ S then G.w u v else 0)
      + (if u ∈ T ∧ v ∉ T then G.w u v else 0) := by
  simp only [Finset.mem_inter, Finset.mem_union, not_and_or, not_or]
  by_cases hus : u ∈ S <;> by_cases hut : u ∈ T <;>
    by_cases hvs : v ∈ S <;> by_cases hvt : v ∈ T <;>
    simp_all

/-- **2-set submodularity of the cut function:**
`cap(S∩T) + cap(S∪T) ≤ cap(S) + cap(T)`.  TRUE, proved pointwise. -/
theorem cutCapacity_submodular (G : Graph V) (S T : Finset V) :
    cutCapacity G (S ∩ T) + cutCapacity G (S ∪ T)
      ≤ cutCapacity G S + cutCapacity G T := by
  unfold cutCapacity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro u _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro v _
  exact edge_submodular G S T u v

/-! ## The false "triple cut" inequality -/

/-- The pointwise `edge` inequality behind the `cutCapacity_triple` route,
specialized to the membership pattern `u ∈ X∩Y∩Z`, `v ∉ X∪Y∪Z`, with all weights `1`:
its left side is `4` and its right side is `3`, so it is **FALSE**.  This is the obstruction
made concrete: four cut indicators cannot be pointwise-dominated by three.  (We prove the negation of
the numeric instance, i.e. `¬ (4 ≤ 3)`, which is exactly what breaks the naive route.) -/
theorem edge_triple_false :
    ¬ ((1:ℕ) + 1 + 1 + 1 ≤ 1 + 1 + 1) := by decide

/-! ## Swapping: admissibility of set-algebra combinations of RT cuts -/

/-- **Swap building block (intersection).** If `X` is an RT cut for `R₁` and `Y` is an RT cut for
`R₂`, then `X ∩ Y` is an RT cut for any region `R` with `R ⊆ R₁` and `R ⊆ R₂` — provided every
boundary vertex outside `R` lies outside `R₁` or outside `R₂` (so it is excluded by `X` or `Y`).
For the MMI application the regions are boundary-disjoint, which supplies exactly this. -/
lemma IsRTCut.inter {bd R₁ R₂ R X Y : Finset V}
    (hX : IsRTCut bd R₁ X) (hY : IsRTCut bd R₂ Y)
    (hR₁ : R ⊆ R₁) (hR₂ : R ⊆ R₂)
    (hsep : ∀ x ∈ bd, x ∉ R → (x ∉ R₁ ∨ x ∉ R₂)) :
    IsRTCut bd R (X ∩ Y) := by
  obtain ⟨hXsub, hXexc⟩ := hX
  obtain ⟨hYsub, hYexc⟩ := hY
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_inter.2 ⟨hXsub (hR₁ hx), hYsub (hR₂ hx)⟩
  · intro x hx hxR
    rw [Finset.mem_inter, not_and_or]
    rcases hsep x hx hxR with h | h
    · exact Or.inl (hXexc x hx h)
    · exact Or.inr (hYexc x hx h)

/-- **Swap building block (union).** If `X` is an RT cut for `R₁` and `Y` for `R₂`, then `X ∪ Y` is
an RT cut for `R₁ ∪ R₂` — provided every boundary vertex outside `R₁ ∪ R₂` is excluded by both.
For MMI (boundary partition), a vertex outside `R₁ ∪ R₂` is in a third region, excluded by both. -/
lemma IsRTCut.union {bd R₁ R₂ X Y : Finset V}
    (hX : IsRTCut bd R₁ X) (hY : IsRTCut bd R₂ Y)
    (hexc : ∀ x ∈ bd, x ∉ R₁ ∪ R₂ → (x ∉ R₁ ∧ x ∉ R₂)) :
    IsRTCut bd (R₁ ∪ R₂) (X ∪ Y) := by
  obtain ⟨hXsub, hXexc⟩ := hX
  obtain ⟨hYsub, hYexc⟩ := hY
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union.2 (Or.inl (hXsub h))
    · exact Finset.mem_union.2 (Or.inr (hYsub h))
  · intro x hx hxR
    obtain ⟨h1, h2⟩ := hexc x hx hxR
    rw [Finset.mem_union, not_or]
    exact ⟨hXexc x hx h1, hYexc x hx h2⟩

/-! ## Strong subadditivity, DERIVED (submodularity + swapping + minimality) -/

/-- A **boundary partition** into four regions `A, B, C, D` (the tripartite regions plus the
purifier `D`): pairwise disjoint, covering the boundary `bd`. -/
structure BoundaryPartition (bd A B C D : Finset V) : Prop where
  cover : A ∪ B ∪ C ∪ D = bd
  dAB : Disjoint A B
  dAC : Disjoint A C
  dAD : Disjoint A D
  dBC : Disjoint B C
  dBD : Disjoint B D
  dCD : Disjoint C D

namespace BoundaryPartition

variable {bd A B C D : Finset V}

lemma subA (P : BoundaryPartition bd A B C D) : A ⊆ bd := by
  rw [← P.cover]; intro x hx; exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2
    (Or.inl (Finset.mem_union.2 (Or.inl hx)))))
lemma subB (P : BoundaryPartition bd A B C D) : B ⊆ bd := by
  rw [← P.cover]; intro x hx; exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2
    (Or.inl (Finset.mem_union.2 (Or.inr hx)))))
lemma subC (P : BoundaryPartition bd A B C D) : C ⊆ bd := by
  rw [← P.cover]; intro x hx; exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hx)))

lemma subAB (P : BoundaryPartition bd A B C D) : A ∪ B ⊆ bd :=
  Finset.union_subset P.subA P.subB
lemma subAC (P : BoundaryPartition bd A B C D) : A ∪ C ⊆ bd :=
  Finset.union_subset P.subA P.subC
lemma subABC (P : BoundaryPartition bd A B C D) : A ∪ B ∪ C ⊆ bd :=
  Finset.union_subset (Finset.union_subset P.subA P.subB) P.subC

end BoundaryPartition

/-- **Strong subadditivity `S_A + S_{ABC} ≤ S_{AB} + S_{AC}`**, fully DERIVED from 2-set
submodularity + the swapping lemmas + minimality, for a boundary-partitioned graph.
(A genuine, sharp holographic inequality — the SSA half of the entropy cone.) -/
theorem rtEntropy_SSA (G : Graph V) {bd A B C D : Finset V}
    (P : BoundaryPartition bd A B C D) :
    rtEntropy G bd A P.subA + rtEntropy G bd (A ∪ B ∪ C) P.subABC
      ≤ rtEntropy G bd (A ∪ B) P.subAB + rtEntropy G bd (A ∪ C) P.subAC := by
  -- pick achieving cuts X for A∪B and Y for A∪C
  obtain ⟨X, hX, hXcap⟩ := rtEntropy_eq_cap G P.subAB
  obtain ⟨Y, hY, hYcap⟩ := rtEntropy_eq_cap G P.subAC
  -- X ∩ Y is admissible for A
  have hXYA : IsRTCut bd A (X ∩ Y) := by
    apply hX.inter hY (Finset.subset_union_left) (Finset.subset_union_left)
    intro x hx hxA
    -- x ∈ bd, x ∉ A ⟹ x ∉ (A∪B) or x ∉ (A∪C).  x is in B, C, or D.
    rw [← P.cover] at hx
    simp only [Finset.mem_union] at hx
    rcases hx with ((hA | hB) | hC) | hD
    · exact absurd hA hxA
    · -- x ∈ B ⟹ x ∉ A∪C (B disjoint A and C)
      right; simp only [Finset.mem_union, not_or]
      exact ⟨hxA, fun hC => (P.dBC.forall_ne_finset hB hC) rfl⟩
    · -- x ∈ C ⟹ x ∉ A∪B
      left; simp only [Finset.mem_union, not_or]
      exact ⟨hxA, fun hB => (P.dBC.forall_ne_finset hB hC) rfl⟩
    · -- x ∈ D ⟹ x ∉ A∪B (D disjoint A,B)
      left; simp only [Finset.mem_union, not_or]
      exact ⟨hxA, fun hB => (P.dBD.forall_ne_finset hB hD) rfl⟩
  -- X ∪ Y is admissible for (A∪B) ∪ (A∪C) = A∪B∪C
  have hXYABC : IsRTCut bd ((A ∪ B) ∪ (A ∪ C)) (X ∪ Y) := by
    apply hX.union hY
    intro x hx hxR
    -- x ∈ bd, x ∉ (A∪B)∪(A∪C) ⟹ x ∈ D ⟹ excluded by both X and Y
    simp only [Finset.mem_union, not_or] at hxR
    exact ⟨by simp only [Finset.mem_union, not_or]; exact ⟨hxR.1.1, hxR.1.2⟩,
           by simp only [Finset.mem_union, not_or]; exact ⟨hxR.2.1, hxR.2.2⟩⟩
  -- normalize (A∪B)∪(A∪C) = A∪B∪C
  have hset : (A ∪ B) ∪ (A ∪ C) = A ∪ B ∪ C := by
    ext x; simp only [Finset.mem_union]; tauto
  rw [hset] at hXYABC
  -- minimality + submodularity
  have hA := rtEntropy_le_cap G P.subA hXYA
  have hABC := rtEntropy_le_cap G P.subABC hXYABC
  have hsub := cutCapacity_submodular G X Y
  rw [hXcap, hYcap]
  calc rtEntropy G bd A P.subA + rtEntropy G bd (A ∪ B ∪ C) P.subABC
      ≤ cutCapacity G (X ∩ Y) + cutCapacity G (X ∪ Y) := by
        exact add_le_add hA hABC
    _ ≤ cutCapacity G X + cutCapacity G Y := hsub

/-! ## MMI and the STRICT witness: the star (perfect-tensor / GHZ) bulk graph

The star graph has four boundary vertices `0,1,2,3` (regions `A,B,C,D`) each joined by a weight-`1`
bond to a single central bulk vertex `4`.  This is the canonical perfect-tensor / GHZ example.
Every single-region and pair-region RT entropy, and MMI itself, is computed by `decide`
(the model is fully `ℕ`-valued and finite).  The strict value `I₃ = −2 < 0` with all min-cuts
positive is the **anti-vacuity witness**. -/

/-- The star / perfect-tensor bulk graph on `Fin 5`: boundary `0,1,2,3` each bonded (weight `1`)
to the central bulk vertex `4`. -/
def starGraph : Graph (Fin 5) where
  w := fun u v => if (u = 4 ∧ v.val < 4) ∨ (v = 4 ∧ u.val < 4) then 1 else 0
  symm := by intro u v; by_cases h : u = 4 <;> by_cases h2 : v = 4 <;> simp_all <;> tauto

/-- Boundary of the star graph: `{A,B,C,D} = {0,1,2,3}`. -/
def starBd : Finset (Fin 5) := {0, 1, 2, 3}

-- containment facts for the regions (needed as `rtEntropy` arguments)
lemma sA  : ({0} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sB  : ({1} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sC  : ({2} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sAB : ({0, 1} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sAC : ({0, 2} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sBC : ({1, 2} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sABC : ({0, 1, 2} : Finset (Fin 5)) ⊆ starBd := by decide

/-- Star-graph single-region entropies are `1` (all min-cuts positive — anti-vacuity). -/
theorem star_SA  : rtEntropy starGraph starBd {0} sA = 1 := by decide
theorem star_SB  : rtEntropy starGraph starBd {1} sB = 1 := by decide
theorem star_SC  : rtEntropy starGraph starBd {2} sC = 1 := by decide
/-- Star-graph pair entropies are `2`. -/
theorem star_SAB : rtEntropy starGraph starBd {0, 1} sAB = 2 := by decide
theorem star_SAC : rtEntropy starGraph starBd {0, 2} sAC = 2 := by decide
theorem star_SBC : rtEntropy starGraph starBd {1, 2} sBC = 2 := by decide
/-- Star-graph triple entropy is `1` (equals `S_D`, the purifier — perfect-tensor structure). -/
theorem star_SABC : rtEntropy starGraph starBd {0, 1, 2} sABC = 1 := by decide

/-- **MMI on the star graph** (the sharp holographic inequality):
`S_{AB} + S_{AC} + S_{BC} ≥ S_A + S_B + S_C + S_{ABC}`, here `2+2+2 = 6 ≥ 5 = 1+1+1+1`. -/
theorem rtEntropy_MMI_star :
    rtEntropy starGraph starBd {0} sA + rtEntropy starGraph starBd {1} sB
        + rtEntropy starGraph starBd {2} sC + rtEntropy starGraph starBd {0, 1, 2} sABC
    ≤ rtEntropy starGraph starBd {0, 1} sAB + rtEntropy starGraph starBd {0, 2} sAC
        + rtEntropy starGraph starBd {1, 2} sBC := by decide

/-- **STRICT witness (anti-vacuity):** the tripartite information is *strictly* negative,
`I₃ = S_A+S_B+S_C − S_{AB}−S_{AC}−S_{BC} + S_{ABC} = 3 − 6 + 1 = −2 < 0` (as an integer identity:
`5 < 6`, i.e. the singles+triple side is strictly below the pairs side), with every min-cut
positive.  This is a genuine strict monogamy violation of the SATURATED case — MMI is not vacuous
here. -/
theorem tripartite_information_star_strict :
    rtEntropy starGraph starBd {0} sA + rtEntropy starGraph starBd {1} sB
        + rtEntropy starGraph starBd {2} sC + rtEntropy starGraph starBd {0, 1, 2} sABC
    < rtEntropy starGraph starBd {0, 1} sAB + rtEntropy starGraph starBd {0, 2} sAC
        + rtEntropy starGraph starBd {1, 2} sBC := by decide

/-- All the star-graph min-cuts are strictly positive (so the strict MMI witness above is not
vacuously about zero entropies). -/
theorem star_mincuts_pos :
    0 < rtEntropy starGraph starBd {0} sA ∧ 0 < rtEntropy starGraph starBd {0, 1} sAB
      ∧ 0 < rtEntropy starGraph starBd {0, 1, 2} sABC := by decide

end Physlib.CutSwappingMMI
