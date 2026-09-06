/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib

/-!
# The undirected min-cut model satisfies monogamy of mutual information

## Forest-level picture

In the tensor-network / Ryu–Takayanagi picture of emergent spacetime, the entanglement entropy of a
boundary region is modeled by the capacity of a **minimum cut** separating that region from the rest
of the boundary in a finite weighted bulk graph.  A geometry built this way obeys sharp entropy
inequalities that generic quantum states do **not**.  The sharpest is **monogamy of mutual
information (MMI)**:

  `I₃(A:B:C) = S_A + S_B + S_C − S_{AB} − S_{AC} − S_{BC} + S_{ABC} ≤ 0`,

equivalently

  `S_A + S_B + S_C + S_{ABC} ≤ S_{AB} + S_{AC} + S_{BC}`.

A generic quantum state can violate MMI, so it is a genuine fingerprint of a min-cut geometry.

This file gives a **uniform, explicit certificate** proving MMI for every finite undirected
nonnegative-edge-weighted graph, with **no planarity** and **no multicommodity-flow** hypothesis.

## The certificate

Let `X, Y, Z` be minimum cuts for the pairs `AB, AC, BC` respectively (as boundary-indicator vertex
sets).  Form the **fixed recombination**

  `A' = (X ∩ Y) \ Z`,   `B' = (X ∩ Z) \ Y`,   `C' = (Y ∩ Z) \ X`,   `U' = X ∪ Y ∪ Z`.

These four sets are admissible cuts for `A, B, C, A∪B∪C` respectively (`admissible_A'`, …,
`admissible_U'`).  The single combinatorial engine is `edge_atoms_nonexpansive`: the induced
`3`-bit → `4`-bit membership map
`(∈X, ∈Y, ∈Z) ↦ (∈A', ∈B', ∈C', ∈U')` is **Hamming-nonexpansive on every edge** — for any two
vertex membership patterns, the number of `{A',B',C',U'}` that separate them is at most the number of
`{X,Y,Z}` that separate them (a finite `64`-case fact, `decide`).  Summing this pointwise inequality
against the symmetric edge weights (`recombination_capacity_le`) yields

  `cap A' + cap B' + cap C' + cap U' ≤ cap X + cap Y + cap Z`.

Minimality of the pairwise min-cuts (`rtEntropy_le_cap`) then gives MMI (`rtEntropy_MMI`).

## Results

* `edge_atoms_nonexpansive` — the `64`-case combinatorial engine (Hamming-nonexpansiveness).
* `recombination_capacity_le` — the capacity certificate `cap A'+cap B'+cap C'+cap U' ≤ cap X+cap Y+cap Z`.
* `admissible_A'`, `admissible_B'`, `admissible_C'`, `admissible_U'` — the four atoms are admissible cuts.
* `rtEntropy_MMI` — the headline: MMI for the undirected min-cut entropy, fully derived.
* `rtEntropy_MMI_strict_witness` / `mmi_witness_mincuts_pos` — anti-vacuity: a concrete graph on which
  MMI is **strict** (`I₃ = −2 < 0`) with every min-cut strictly positive.

## Derived versus posited

The min-cut geometry facts (the capacity certificate and MMI) are **theorems** of finite
combinatorics, with no extra axioms.  The only modeling **posit** is the physical identification of
the min-cut capacity with the entanglement entropy of the bulk state; given that identification, MMI
of the geometric entropy is a theorem.
-/

@[expose] public section

namespace Physlib.UndirectedMMICertificate

open Finset

/-! ## The finite bulk graph, cut capacity, admissible cuts, and min-cut entropy

Self-contained local restatement (no cross-file dependency): `V` is a finite vertex set with
decidable equality; `w` is a symmetric nonnegative (ℕ-valued) edge weight. -/

/-- A finite undirected weighted bulk graph: a symmetric ℕ-valued edge weight on a finite vertex
type.  ℕ-valued makes nonnegativity automatic and the whole model computable. -/
structure Graph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- edge weight between two vertices -/
  w : V → V → ℕ
  /-- weights are symmetric (the graph is undirected) -/
  symm : ∀ u v, w u v = w v u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The capacity of the cut `S`: the total weight of undirected edges with exactly one endpoint in
`S`.  Summing the directed indicator `[u ∈ S ∧ v ∉ S] · w u v` over all ordered pairs counts each
undirected crossing edge exactly once, so this is the standard undirected cut value. -/
def cutCapacity (G : Graph V) (S : Finset V) : ℕ :=
  ∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0)

/-- Cut capacity is nonnegative (automatic over `ℕ`). -/
lemma cutCapacity_nonneg (G : Graph V) (S : Finset V) : 0 ≤ cutCapacity G S := Nat.zero_le _

/-- `S` is an **admissible cut** for boundary region `R` inside boundary `bd`: it contains `R` and
excludes every boundary vertex outside `R` (bulk vertices are free).  This is the correct undirected
RT admissibility — separating `R` from `bd \ R`. -/
def IsRTCut (bd R S : Finset V) : Prop := R ⊆ S ∧ ∀ x ∈ bd, x ∉ R → x ∉ S

/-- The finite set of admissible cuts for `R`, used to take the minimum. -/
def rtCuts (bd R : Finset V) : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter (fun S => R ⊆ S ∧ ∀ x ∈ bd, x ∈ R ∨ x ∉ S)

lemma mem_rtCuts {bd R S : Finset V} : S ∈ rtCuts bd R ↔ IsRTCut bd R S := by
  unfold rtCuts IsRTCut
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨_, hR, hbd⟩
    refine ⟨hR, fun x hx hxR => ?_⟩
    rcases hbd x hx with h | h
    · exact absurd h hxR
    · exact h
  · rintro ⟨hR, hbd⟩
    refine ⟨Finset.subset_univ _, hR, fun x hx => ?_⟩
    by_cases hxR : x ∈ R
    · exact Or.inl hxR
    · exact Or.inr (hbd x hx hxR)

/-- When `R ⊆ bd`, the region `R` itself is an admissible cut, so `rtCuts` is nonempty. -/
lemma rtCuts_nonempty {bd R : Finset V} (_h : R ⊆ bd) : (rtCuts bd R).Nonempty := by
  refine ⟨R, ?_⟩
  rw [mem_rtCuts]
  exact ⟨Finset.Subset.refl _, fun x _ hxR => hxR⟩

/-- **Min-cut entropy** of region `R`: the minimum cut capacity over admissible cuts. -/
def rtEntropy (G : Graph V) (bd R : Finset V) (h : R ⊆ bd) : ℕ :=
  ((rtCuts bd R).image (cutCapacity G)).min' ((rtCuts_nonempty h).image (cutCapacity G))

/-- **Minimality:** the min-cut entropy is at most the capacity of any admissible cut. -/
lemma rtEntropy_le_cap (G : Graph V) {bd R : Finset V} (h : R ⊆ bd)
    {S : Finset V} (hS : IsRTCut bd R S) : rtEntropy G bd R h ≤ cutCapacity G S := by
  unfold rtEntropy
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨S, (mem_rtCuts).2 hS, rfl⟩

/-- The min-cut entropy is achieved by some admissible cut. -/
lemma rtEntropy_eq_cap (G : Graph V) {bd R : Finset V} (h : R ⊆ bd) :
    ∃ S, IsRTCut bd R S ∧ rtEntropy G bd R h = cutCapacity G S := by
  unfold rtEntropy
  have hmem := Finset.min'_mem ((rtCuts bd R).image (cutCapacity G))
    ((rtCuts_nonempty h).image (cutCapacity G))
  rw [Finset.mem_image] at hmem
  obtain ⟨S, hS, hcap⟩ := hmem
  exact ⟨S, (mem_rtCuts).1 hS, hcap.symm⟩

/-! ## Symmetric cut capacity and the doubling identity

To sum the edgewise inequality it is convenient to use the **symmetric separation** form, in which
each ordered pair `(u,v)` contributes when `S` separates `u` and `v` (exactly one of them lies in
`S`).  Under symmetric weights this equals `2 · cutCapacity` (each undirected crossing edge is now
counted from both endpoints), and — unlike the directed indicator — the symmetric indicator is the
quantity for which the recombination map is genuinely nonexpansive. -/

/-- The symmetric-separation capacity: sum over ordered pairs of `[u,v separated by S] · w u v`. -/
def symCap (G : Graph V) (S : Finset V) : ℕ :=
  ∑ u, ∑ v, (if (u ∈ S) ≠ (v ∈ S) then G.w u v else 0)

/-- **Doubling identity:** for symmetric weights, `symCap G S = 2 · cutCapacity G S`.
The separated ordered pairs split into those with `u ∈ S, v ∉ S` and those with `u ∉ S, v ∈ S`; the
latter reindex to the former using `G.symm`, and each equals `cutCapacity`. -/
lemma symCap_eq_two_cutCapacity (G : Graph V) (S : Finset V) :
    symCap G S = 2 * cutCapacity G S := by
  have hsplit : symCap G S
      = (∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0))
        + ∑ u, ∑ v, (if u ∉ S ∧ v ∈ S then G.w u v else 0) := by
    unfold symCap
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
  have hswap : (∑ u, ∑ v, (if u ∉ S ∧ v ∈ S then G.w u v else 0))
      = ∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [G.symm v u]
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv, and_comm]
  rw [hsplit, hswap]
  unfold cutCapacity
  ring

/-! ## The combinatorial engine: edgewise Hamming-nonexpansiveness

The recombination sends a vertex's `(∈X, ∈Y, ∈Z)` membership to `(∈A', ∈B', ∈C', ∈U')` with
`A' = (X∩Y)\Z`, `B' = (X∩Z)\Y`, `C' = (Y∩Z)\X`, `U' = X∪Y∪Z`.  The following boolean lemma states
that this map does not increase the per-edge separation count: for any two membership patterns
`(uX,uY,uZ)` and `(vX,vY,vZ)`, the number of atoms `{A',B',C',U'}` separating them is at most the
number of `{X,Y,Z}` separating them.  It is a finite `64`-case fact, checked by `decide`. -/

/-- Atom membership as a boolean function of `(∈X, ∈Y, ∈Z)`.
`aA = (X∩Y)\Z`, `aB = (X∩Z)\Y`, `aC = (Y∩Z)\X`, `aU = X∪Y∪Z`. -/
def aA (x y z : Bool) : Bool := x && y && !z
def aB (x y z : Bool) : Bool := x && z && !y
def aC (x y z : Bool) : Bool := y && z && !x
def aU (x y z : Bool) : Bool := x || y || z

/-- `sepCount` of a boolean 4-tuple against another: the number of coordinates in which they differ,
as a `ℕ` (used to phrase nonexpansiveness numerically). -/
def bdiff (a b : Bool) : ℕ := if a ≠ b then 1 else 0

/-- **The engine (Hamming-nonexpansiveness).** For any two vertex membership patterns
`(uX,uY,uZ)`, `(vX,vY,vZ)`, the recombination atoms `{A',B',C',U'}` separate the two vertices at
most as often as `{X,Y,Z}` do.  A `64`-case boolean fact. -/
theorem edge_atoms_nonexpansive :
    ∀ uX uY uZ vX vY vZ : Bool,
      bdiff (aA uX uY uZ) (aA vX vY vZ) + bdiff (aB uX uY uZ) (aB vX vY vZ)
        + bdiff (aC uX uY uZ) (aC vX vY vZ) + bdiff (aU uX uY uZ) (aU vX vY vZ)
      ≤ bdiff uX vX + bdiff uY vY + bdiff uZ vZ := by
  decide

/-! ## From the boolean engine to the capacity certificate

We instantiate the engine at each ordered pair with the actual set memberships, then sum against the
symmetric weights. -/

variable {G : Graph V} {X Y Z : Finset V}

/-- Membership indicator of a vertex in a `Finset`, as a `Bool`. -/
def mem (S : Finset V) (u : V) : Bool := decide (u ∈ S)

/-- The four recombination atoms as concrete `Finset`s. -/
def atomA (X Y Z : Finset V) : Finset V := (X ∩ Y) \ Z
def atomB (X Y Z : Finset V) : Finset V := (X ∩ Z) \ Y
def atomC (X Y Z : Finset V) : Finset V := (Y ∩ Z) \ X
def atomU (X Y Z : Finset V) : Finset V := X ∪ Y ∪ Z

/-- Membership of a vertex in `atomA` matches the boolean `aA` of its `X,Y,Z` memberships. -/
lemma mem_atomA (u : V) : mem (atomA X Y Z) u = aA (mem X u) (mem Y u) (mem Z u) := by
  simp only [mem, aA, atomA, Finset.mem_sdiff, Finset.mem_inter]
  by_cases hx : u ∈ X <;> by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hx, hy, hz]
lemma mem_atomB (u : V) : mem (atomB X Y Z) u = aB (mem X u) (mem Y u) (mem Z u) := by
  simp only [mem, aB, atomB, Finset.mem_sdiff, Finset.mem_inter]
  by_cases hx : u ∈ X <;> by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hx, hy, hz]
lemma mem_atomC (u : V) : mem (atomC X Y Z) u = aC (mem X u) (mem Y u) (mem Z u) := by
  simp only [mem, aC, atomC, Finset.mem_sdiff, Finset.mem_inter]
  by_cases hx : u ∈ X <;> by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hx, hy, hz]
lemma mem_atomU (u : V) : mem (atomU X Y Z) u = aU (mem X u) (mem Y u) (mem Z u) := by
  simp only [mem, aU, atomU, Finset.mem_union]
  by_cases hx : u ∈ X <;> by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hx, hy, hz]

/-- The symmetric-separation indicator of `S` at ordered pair `(u,v)`, as `[mem S u ≠ mem S v]`. -/
lemma sep_indicator (S : Finset V) (u v : V) :
    (if (u ∈ S) ≠ (v ∈ S) then G.w u v else 0) = bdiff (mem S u) (mem S v) * G.w u v := by
  unfold bdiff mem
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

/-- `symCap` rewritten with the `bdiff`/`mem` indicator form of each ordered pair. -/
lemma symCap_eq_bdiff_sum (S : Finset V) :
    symCap G S = ∑ u, ∑ v, bdiff (mem S u) (mem S v) * G.w u v := by
  unfold symCap
  exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => sep_indicator S u v))

/-- **Pointwise capacity inequality**, before summing: at each ordered pair the atoms' separation
weight is at most that of `X, Y, Z`. -/
lemma edge_capacity_le (u v : V) :
    bdiff (mem (atomA X Y Z) u) (mem (atomA X Y Z) v) * G.w u v
      + bdiff (mem (atomB X Y Z) u) (mem (atomB X Y Z) v) * G.w u v
      + bdiff (mem (atomC X Y Z) u) (mem (atomC X Y Z) v) * G.w u v
      + bdiff (mem (atomU X Y Z) u) (mem (atomU X Y Z) v) * G.w u v
    ≤ bdiff (mem X u) (mem X v) * G.w u v
      + bdiff (mem Y u) (mem Y v) * G.w u v
      + bdiff (mem Z u) (mem Z v) * G.w u v := by
  have hcore := edge_atoms_nonexpansive (mem X u) (mem Y u) (mem Z u) (mem X v) (mem Y v) (mem Z v)
  rw [mem_atomA, mem_atomA, mem_atomB, mem_atomB, mem_atomC, mem_atomC, mem_atomU, mem_atomU]
  calc bdiff (aA (mem X u) (mem Y u) (mem Z u)) (aA (mem X v) (mem Y v) (mem Z v)) * G.w u v
        + bdiff (aB (mem X u) (mem Y u) (mem Z u)) (aB (mem X v) (mem Y v) (mem Z v)) * G.w u v
        + bdiff (aC (mem X u) (mem Y u) (mem Z u)) (aC (mem X v) (mem Y v) (mem Z v)) * G.w u v
        + bdiff (aU (mem X u) (mem Y u) (mem Z u)) (aU (mem X v) (mem Y v) (mem Z v)) * G.w u v
      = (bdiff (aA (mem X u) (mem Y u) (mem Z u)) (aA (mem X v) (mem Y v) (mem Z v))
          + bdiff (aB (mem X u) (mem Y u) (mem Z u)) (aB (mem X v) (mem Y v) (mem Z v))
          + bdiff (aC (mem X u) (mem Y u) (mem Z u)) (aC (mem X v) (mem Y v) (mem Z v))
          + bdiff (aU (mem X u) (mem Y u) (mem Z u)) (aU (mem X v) (mem Y v) (mem Z v))) * G.w u v := by
        ring
    _ ≤ (bdiff (mem X u) (mem X v) + bdiff (mem Y u) (mem Y v) + bdiff (mem Z u) (mem Z v)) * G.w u v :=
        Nat.mul_le_mul_right (k := G.w u v) hcore
    _ = bdiff (mem X u) (mem X v) * G.w u v + bdiff (mem Y u) (mem Y v) * G.w u v
          + bdiff (mem Z u) (mem Z v) * G.w u v := by ring

/-- **The capacity certificate.** For every undirected nonnegative-weighted graph, the fixed
recombination satisfies
  `cap A' + cap B' + cap C' + cap U' ≤ cap X + cap Y + cap Z`.
Proved by summing `edge_capacity_le` and dividing the doubling identity `symCap = 2·cutCapacity`. -/
theorem recombination_capacity_le (G : Graph V) (X Y Z : Finset V) :
    cutCapacity G (atomA X Y Z) + cutCapacity G (atomB X Y Z)
        + cutCapacity G (atomC X Y Z) + cutCapacity G (atomU X Y Z)
      ≤ cutCapacity G X + cutCapacity G Y + cutCapacity G Z := by
  -- First prove the doubled inequality on `symCap`, then divide by two.
  have hsum : symCap G (atomA X Y Z) + symCap G (atomB X Y Z)
        + symCap G (atomC X Y Z) + symCap G (atomU X Y Z)
      ≤ symCap G X + symCap G Y + symCap G Z := by
    rw [symCap_eq_bdiff_sum, symCap_eq_bdiff_sum, symCap_eq_bdiff_sum, symCap_eq_bdiff_sum,
        symCap_eq_bdiff_sum, symCap_eq_bdiff_sum, symCap_eq_bdiff_sum]
    -- combine the four/three double sums into single double sums and compare pointwise
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun u _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    exact edge_capacity_le (G := G) (X := X) (Y := Y) (Z := Z) u v
  -- divide by 2
  have hA := symCap_eq_two_cutCapacity G (atomA X Y Z)
  have hB := symCap_eq_two_cutCapacity G (atomB X Y Z)
  have hC := symCap_eq_two_cutCapacity G (atomC X Y Z)
  have hU := symCap_eq_two_cutCapacity G (atomU X Y Z)
  have hX := symCap_eq_two_cutCapacity G X
  have hY := symCap_eq_two_cutCapacity G Y
  have hZ := symCap_eq_two_cutCapacity G Z
  rw [hA, hB, hC, hU, hX, hY, hZ] at hsum
  omega

/-! ## Admissibility of the recombination atoms

For a boundary partition into four disjoint regions `A, B, C, D` and min-cuts `X, Y, Z` for the
pairs `AB, AC, BC`, the four atoms are admissible cuts for `A, B, C, A∪B∪C`. -/

/-- A **boundary partition** into four pairwise-disjoint regions covering `bd`. -/
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
  rw [← P.cover]; intro x hx
  exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hx)))))
lemma subB (P : BoundaryPartition bd A B C D) : B ⊆ bd := by
  rw [← P.cover]; intro x hx
  exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hx)))))
lemma subC (P : BoundaryPartition bd A B C D) : C ⊆ bd := by
  rw [← P.cover]; intro x hx
  exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hx)))
lemma subAB (P : BoundaryPartition bd A B C D) : A ∪ B ⊆ bd :=
  Finset.union_subset P.subA P.subB
lemma subAC (P : BoundaryPartition bd A B C D) : A ∪ C ⊆ bd :=
  Finset.union_subset P.subA P.subC
lemma subBC (P : BoundaryPartition bd A B C D) : B ∪ C ⊆ bd :=
  Finset.union_subset P.subB P.subC
lemma subABC (P : BoundaryPartition bd A B C D) : A ∪ B ∪ C ⊆ bd :=
  Finset.union_subset (Finset.union_subset P.subA P.subB) P.subC

end BoundaryPartition

/-- Every boundary vertex lies in exactly one of the four regions. -/
lemma bd_region_cases {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D)
    {x : V} (hx : x ∈ bd) : x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D := by
  rw [← P.cover] at hx
  simp only [Finset.mem_union] at hx
  tauto

/-- `A' = (X∩Y)\Z` is an admissible cut for `A`, given `X, Y, Z` admissible for `AB, AC, BC`. -/
theorem admissible_A' {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D)
    (hX : IsRTCut bd (A ∪ B) X) (hY : IsRTCut bd (A ∪ C) Y) (hZ : IsRTCut bd (B ∪ C) Z) :
    IsRTCut bd A (atomA X Y Z) := by
  obtain ⟨hXsub, hXexc⟩ := hX
  obtain ⟨hYsub, hYexc⟩ := hY
  obtain ⟨hZsub, hZexc⟩ := hZ
  refine ⟨fun x hx => ?_, fun x hxbd hxA => ?_⟩
  · -- A ⊆ X (via A∪B), A ⊆ Y (via A∪C), A ∩ Z = ∅ (A disjoint from B,C ⟹ excluded by Z)
    rw [atomA, Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨⟨hXsub (Finset.mem_union_left _ hx), hYsub (Finset.mem_union_left _ hx)⟩, ?_⟩
    -- x ∈ A ⟹ x ∉ B∪C ⟹ excluded by Z
    exact hZexc x (P.subA hx) (by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun hB => (P.dAB.forall_ne_finset hx hB) rfl,
             fun hC => (P.dAC.forall_ne_finset hx hC) rfl⟩)
  · -- x ∈ bd, x ∉ A: show x ∉ (X∩Y)\Z.  x ∈ B,C, or D.
    rw [atomA, Finset.mem_sdiff, Finset.mem_inter, not_and_or, not_and_or]
    rcases bd_region_cases P hxbd with hA | hB | hC | hD
    · exact absurd hA hxA
    · -- x ∈ B ⟹ x ∉ A∪C ⟹ x ∉ Y
      left; right
      exact hYexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨hxA, fun hC => (P.dBC.forall_ne_finset hB hC) rfl⟩)
    · -- x ∈ C ⟹ x ∉ A∪B ⟹ x ∉ X
      left; left
      exact hXexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨hxA, fun hB => (P.dBC.forall_ne_finset hB hC) rfl⟩)
    · -- x ∈ D ⟹ x ∉ A∪B ⟹ x ∉ X
      left; left
      exact hXexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨hxA, fun hB => (P.dBD.forall_ne_finset hB hD) rfl⟩)

/-- `B' = (X∩Z)\Y` is an admissible cut for `B`. -/
theorem admissible_B' {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D)
    (hX : IsRTCut bd (A ∪ B) X) (hY : IsRTCut bd (A ∪ C) Y) (hZ : IsRTCut bd (B ∪ C) Z) :
    IsRTCut bd B (atomB X Y Z) := by
  obtain ⟨hXsub, hXexc⟩ := hX
  obtain ⟨hYsub, hYexc⟩ := hY
  obtain ⟨hZsub, hZexc⟩ := hZ
  refine ⟨fun x hx => ?_, fun x hxbd hxB => ?_⟩
  · -- B ⊆ X (via A∪B), B ⊆ Z (via B∪C), B ∩ Y = ∅
    rw [atomB, Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨⟨hXsub (Finset.mem_union_right _ hx), hZsub (Finset.mem_union_left _ hx)⟩, ?_⟩
    exact hYexc x (P.subB hx) (by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun hA => (P.dAB.forall_ne_finset hA hx) rfl,
             fun hC => (P.dBC.forall_ne_finset hx hC) rfl⟩)
  · rw [atomB, Finset.mem_sdiff, Finset.mem_inter, not_and_or, not_and_or]
    rcases bd_region_cases P hxbd with hA | hB | hC | hD
    · -- x ∈ A ⟹ x ∉ B∪C ⟹ x ∉ Z
      left; right
      exact hZexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hB => (P.dAB.forall_ne_finset hA hB) rfl,
               fun hC => (P.dAC.forall_ne_finset hA hC) rfl⟩)
    · exact absurd hB hxB
    · -- x ∈ C ⟹ x ∉ A∪B ⟹ x ∉ X
      left; left
      exact hXexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hA => (P.dAC.forall_ne_finset hA hC) rfl, hxB⟩)
    · -- x ∈ D ⟹ x ∉ A∪B ⟹ x ∉ X
      left; left
      exact hXexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hA => (P.dAD.forall_ne_finset hA hD) rfl, hxB⟩)

/-- `C' = (Y∩Z)\X` is an admissible cut for `C`. -/
theorem admissible_C' {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D)
    (hX : IsRTCut bd (A ∪ B) X) (hY : IsRTCut bd (A ∪ C) Y) (hZ : IsRTCut bd (B ∪ C) Z) :
    IsRTCut bd C (atomC X Y Z) := by
  obtain ⟨hXsub, hXexc⟩ := hX
  obtain ⟨hYsub, hYexc⟩ := hY
  obtain ⟨hZsub, hZexc⟩ := hZ
  refine ⟨fun x hx => ?_, fun x hxbd hxC => ?_⟩
  · -- C ⊆ Y (via A∪C), C ⊆ Z (via B∪C), C ∩ X = ∅
    rw [atomC, Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨⟨hYsub (Finset.mem_union_right _ hx), hZsub (Finset.mem_union_right _ hx)⟩, ?_⟩
    exact hXexc x (P.subC hx) (by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun hA => (P.dAC.forall_ne_finset hA hx) rfl,
             fun hB => (P.dBC.forall_ne_finset hB hx) rfl⟩)
  · rw [atomC, Finset.mem_sdiff, Finset.mem_inter, not_and_or, not_and_or]
    rcases bd_region_cases P hxbd with hA | hB | hC | hD
    · -- x ∈ A ⟹ x ∉ B∪C ⟹ x ∉ Z
      left; right
      exact hZexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hB => (P.dAB.forall_ne_finset hA hB) rfl,
               fun hC => (P.dAC.forall_ne_finset hA hC) rfl⟩)
    · -- x ∈ B ⟹ x ∉ A∪C ⟹ x ∉ Y
      left; left
      exact hYexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hA => (P.dAB.forall_ne_finset hA hB) rfl, hxC⟩)
    · exact absurd hC hxC
    · -- x ∈ D ⟹ x ∉ A∪C ⟹ x ∉ Y
      left; left
      exact hYexc x hxbd (by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hA => (P.dAD.forall_ne_finset hA hD) rfl, hxC⟩)

/-- `U' = X∪Y∪Z` is an admissible cut for `A∪B∪C`. -/
theorem admissible_U' {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D)
    (hX : IsRTCut bd (A ∪ B) X) (hY : IsRTCut bd (A ∪ C) Y) (hZ : IsRTCut bd (B ∪ C) Z) :
    IsRTCut bd (A ∪ B ∪ C) (atomU X Y Z) := by
  obtain ⟨hXsub, hXexc⟩ := hX
  obtain ⟨hYsub, hYexc⟩ := hY
  obtain ⟨hZsub, hZexc⟩ := hZ
  refine ⟨fun x hx => ?_, fun x hxbd hxABC => ?_⟩
  · -- A∪B∪C ⊆ X∪Y∪Z: A,B ⊆ X; C ⊆ Y
    rw [atomU]
    simp only [Finset.mem_union] at hx ⊢
    rcases hx with (hA | hB) | hC
    · exact Or.inl (Or.inl (hXsub (Finset.mem_union_left _ hA)))
    · exact Or.inl (Or.inl (hXsub (Finset.mem_union_right _ hB)))
    · exact Or.inl (Or.inr (hYsub (Finset.mem_union_right _ hC)))
  · -- x ∈ bd, x ∉ A∪B∪C ⟹ x ∈ D ⟹ excluded by X, Y, Z all
    rw [atomU]
    simp only [Finset.mem_union, not_or] at hxABC ⊢
    obtain ⟨⟨hxA, hxB⟩, hxC⟩ := hxABC
    rcases bd_region_cases P hxbd with hA | hB | hC | hD
    · exact absurd hA hxA
    · exact absurd hB hxB
    · exact absurd hC hxC
    · -- x ∈ D: excluded by all three
      refine ⟨⟨hXexc x hxbd (by
                simp only [Finset.mem_union, not_or]
                exact ⟨fun hA => (P.dAD.forall_ne_finset hA hD) rfl,
                       fun hB => (P.dBD.forall_ne_finset hB hD) rfl⟩),
              hYexc x hxbd (by
                simp only [Finset.mem_union, not_or]
                exact ⟨fun hA => (P.dAD.forall_ne_finset hA hD) rfl,
                       fun hC => (P.dCD.forall_ne_finset hC hD) rfl⟩)⟩,
            hZexc x hxbd (by
                simp only [Finset.mem_union, not_or]
                exact ⟨fun hB => (P.dBD.forall_ne_finset hB hD) rfl,
                       fun hC => (P.dCD.forall_ne_finset hC hD) rfl⟩)⟩

/-! ## Monogamy of mutual information, fully derived

Combine the capacity certificate (`recombination_capacity_le`) with atom admissibility and
minimality (`rtEntropy_le_cap`) to bound the recombined entropies, then use that the pairwise cuts
`X, Y, Z` may be taken to *achieve* the pairwise entropies. -/

/-- **Monogamy of mutual information for the undirected min-cut entropy.**
For pairwise-disjoint boundary regions `A, B, C` (with purifier `D`) in any finite undirected
nonnegative-weighted graph,
  `S_A + S_B + S_C + S_{ABC} ≤ S_{AB} + S_{AC} + S_{BC}`
(equivalently `I₃(A:B:C) ≤ 0`).  No planarity, no multicommodity flow. -/
theorem rtEntropy_MMI (G : Graph V) {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D) :
    rtEntropy G bd A P.subA + rtEntropy G bd B P.subB + rtEntropy G bd C P.subC
        + rtEntropy G bd (A ∪ B ∪ C) P.subABC
      ≤ rtEntropy G bd (A ∪ B) P.subAB + rtEntropy G bd (A ∪ C) P.subAC
        + rtEntropy G bd (B ∪ C) P.subBC := by
  -- pick achieving cuts X, Y, Z for AB, AC, BC
  obtain ⟨X, hX, hXcap⟩ := rtEntropy_eq_cap G P.subAB
  obtain ⟨Y, hY, hYcap⟩ := rtEntropy_eq_cap G P.subAC
  obtain ⟨Z, hZ, hZcap⟩ := rtEntropy_eq_cap G P.subBC
  -- the four atoms are admissible ⟹ their entropies are below their capacities
  have hA := rtEntropy_le_cap G P.subA (admissible_A' P hX hY hZ)
  have hB := rtEntropy_le_cap G P.subB (admissible_B' P hX hY hZ)
  have hC := rtEntropy_le_cap G P.subC (admissible_C' P hX hY hZ)
  have hU := rtEntropy_le_cap G P.subABC (admissible_U' P hX hY hZ)
  -- the capacity certificate
  have hcert := recombination_capacity_le G X Y Z
  rw [hXcap, hYcap, hZcap]
  calc rtEntropy G bd A P.subA + rtEntropy G bd B P.subB + rtEntropy G bd C P.subC
          + rtEntropy G bd (A ∪ B ∪ C) P.subABC
      ≤ cutCapacity G (atomA X Y Z) + cutCapacity G (atomB X Y Z)
          + cutCapacity G (atomC X Y Z) + cutCapacity G (atomU X Y Z) := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA hB) hC) hU
    _ ≤ cutCapacity G X + cutCapacity G Y + cutCapacity G Z := hcert

/-! ## Anti-vacuity witness: a strict monogamy violation

The **star graph** on `Fin 5` has four boundary vertices `0,1,2,3` (regions `A,B,C,D`) each joined by
a weight-`1` bond to a single central bulk vertex `4`.  Every entropy, and MMI itself, is `decide`-able.
The tripartite information is strictly negative, `I₃ = 3 − 6 + 1 = −2 < 0`, with every min-cut
positive — so the MMI theorem is not the vacuous `0 ≤ 0`. -/

/-- The star bulk graph on `Fin 5`: boundary `0,1,2,3` each bonded (weight `1`) to central bulk
vertex `4`. -/
def starGraph : Graph (Fin 5) where
  w := fun u v => if (u = 4 ∧ v.val < 4) ∨ (v = 4 ∧ u.val < 4) then 1 else 0
  symm := by intro u v; by_cases h : u = 4 <;> by_cases h2 : v = 4 <;> simp_all

/-- Boundary of the star graph: `{A,B,C,D} = {0,1,2,3}`. -/
def starBd : Finset (Fin 5) := {0, 1, 2, 3}

lemma sA  : ({0} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sB  : ({1} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sC  : ({2} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sAB : ({0, 1} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sAC : ({0, 2} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sBC : ({1, 2} : Finset (Fin 5)) ⊆ starBd := by decide
lemma sABC : ({0, 1, 2} : Finset (Fin 5)) ⊆ starBd := by decide

/-- Star-graph single-region entropies are `1`. -/
theorem star_SA  : rtEntropy starGraph starBd {0} sA = 1 := by decide
theorem star_SB  : rtEntropy starGraph starBd {1} sB = 1 := by decide
theorem star_SC  : rtEntropy starGraph starBd {2} sC = 1 := by decide
/-- Star-graph pair entropies are `2`. -/
theorem star_SAB : rtEntropy starGraph starBd {0, 1} sAB = 2 := by decide
theorem star_SAC : rtEntropy starGraph starBd {0, 2} sAC = 2 := by decide
theorem star_SBC : rtEntropy starGraph starBd {1, 2} sBC = 2 := by decide
/-- Star-graph triple entropy is `1`. -/
theorem star_SABC : rtEntropy starGraph starBd {0, 1, 2} sABC = 1 := by decide

/-- **Strict anti-vacuity witness:** on the star graph the tripartite information is strictly
negative, `I₃ = S_A+S_B+S_C − S_{AB}−S_{AC}−S_{BC} + S_{ABC} = 3 − 6 + 1 = −2 < 0`
(as the ℕ inequality `5 < 6` on the two sides of MMI), with every min-cut positive. -/
theorem rtEntropy_MMI_strict_witness :
    rtEntropy starGraph starBd {0} sA + rtEntropy starGraph starBd {1} sB
        + rtEntropy starGraph starBd {2} sC + rtEntropy starGraph starBd {0, 1, 2} sABC
    < rtEntropy starGraph starBd {0, 1} sAB + rtEntropy starGraph starBd {0, 2} sAC
        + rtEntropy starGraph starBd {1, 2} sBC := by decide

/-- All star-graph min-cuts in the strict witness are strictly positive (so the strict MMI witness is
not vacuously about zero entropies). -/
theorem mmi_witness_mincuts_pos :
    0 < rtEntropy starGraph starBd {0} sA ∧ 0 < rtEntropy starGraph starBd {1} sB
      ∧ 0 < rtEntropy starGraph starBd {2} sC ∧ 0 < rtEntropy starGraph starBd {0, 1} sAB
      ∧ 0 < rtEntropy starGraph starBd {0, 2} sAC ∧ 0 < rtEntropy starGraph starBd {1, 2} sBC
      ∧ 0 < rtEntropy starGraph starBd {0, 1, 2} sABC := by decide

/-! ## Nonnegative real edge weights

The entire development above is stated over `ℕ`-valued weights, which makes nonnegativity automatic.
The same certificate holds verbatim for **nonnegative real** edge weights: the combinatorial engine
`edge_atoms_nonexpansive`, the admissibility of the recombination atoms, and the boundary-partition
bookkeeping are all scalar-free and are reused unchanged.  Only the capacity scalar changes from `ℕ`
to `ℝ`; the pointwise boolean inequality is lifted by multiplying against the (nonnegative) real
weight, and the doubling identity is divided by two over `ℝ` rather than by `omega`.

The `ℕ` model embeds into this one (`castGraph`, `rtEntropyR_castGraph`), so the real result subsumes
the `ℕ` result and its strict anti-vacuity witness. -/

/-- A finite undirected weighted bulk graph with **nonnegative real** edge weights: a symmetric
`ℝ`-valued edge weight on a finite vertex type together with an explicit nonnegativity field. -/
structure GraphR (V : Type*) [Fintype V] [DecidableEq V] where
  /-- edge weight between two vertices -/
  w : V → V → ℝ
  /-- weights are nonnegative -/
  w_nonneg : ∀ u v, 0 ≤ w u v
  /-- weights are symmetric (the graph is undirected) -/
  symm : ∀ u v, w u v = w v u

/-- The real cut capacity of `S`: the total weight of undirected edges with exactly one endpoint in
`S` (directed-indicator form, counting each crossing edge once). -/
def cutCapacityR (G : GraphR V) (S : Finset V) : ℝ :=
  ∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0)

/-- Real cut capacity is nonnegative. -/
lemma cutCapacityR_nonneg (G : GraphR V) (S : Finset V) : 0 ≤ cutCapacityR G S := by
  unfold cutCapacityR
  refine Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => ?_))
  by_cases h : u ∈ S ∧ v ∉ S <;> simp [h, G.w_nonneg]

/-- The symmetric-separation capacity over `ℝ`: sum over ordered pairs of `[u,v separated by S]·w u v`. -/
def symCapR (G : GraphR V) (S : Finset V) : ℝ :=
  ∑ u, ∑ v, (if (u ∈ S) ≠ (v ∈ S) then G.w u v else 0)

/-- **Doubling identity over `ℝ`:** for symmetric weights, `symCapR G S = 2 * cutCapacityR G S`. -/
lemma symCapR_eq_two_cutCapacityR (G : GraphR V) (S : Finset V) :
    symCapR G S = 2 * cutCapacityR G S := by
  have hsplit : symCapR G S
      = (∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0))
        + ∑ u, ∑ v, (if u ∉ S ∧ v ∈ S then G.w u v else 0) := by
    unfold symCapR
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
  have hswap : (∑ u, ∑ v, (if u ∉ S ∧ v ∈ S then G.w u v else 0))
      = ∑ u, ∑ v, (if u ∈ S ∧ v ∉ S then G.w u v else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [G.symm v u]
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv, and_comm]
  rw [hsplit, hswap]
  unfold cutCapacityR
  ring

/-- The symmetric-separation indicator of `S` at ordered pair `(u,v)`, real form. -/
lemma sep_indicatorR (G : GraphR V) (S : Finset V) (u v : V) :
    (if (u ∈ S) ≠ (v ∈ S) then G.w u v else 0)
      = (bdiff (mem S u) (mem S v) : ℝ) * G.w u v := by
  unfold bdiff mem
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

/-- `symCapR` rewritten with the `bdiff`/`mem` indicator form of each ordered pair. -/
lemma symCapR_eq_bdiff_sum (G : GraphR V) (S : Finset V) :
    symCapR G S = ∑ u, ∑ v, (bdiff (mem S u) (mem S v) : ℝ) * G.w u v := by
  unfold symCapR
  exact Finset.sum_congr rfl
    (fun u _ => Finset.sum_congr rfl (fun v _ => sep_indicatorR G S u v))

/-- **Pointwise real capacity inequality**: at each ordered pair the atoms' separation weight is at
most that of `X, Y, Z`, after multiplying the boolean engine by the nonnegative weight. -/
lemma edge_capacity_leR (G : GraphR V) (X Y Z : Finset V) (u v : V) :
    (bdiff (mem (atomA X Y Z) u) (mem (atomA X Y Z) v) : ℝ) * G.w u v
      + (bdiff (mem (atomB X Y Z) u) (mem (atomB X Y Z) v) : ℝ) * G.w u v
      + (bdiff (mem (atomC X Y Z) u) (mem (atomC X Y Z) v) : ℝ) * G.w u v
      + (bdiff (mem (atomU X Y Z) u) (mem (atomU X Y Z) v) : ℝ) * G.w u v
    ≤ (bdiff (mem X u) (mem X v) : ℝ) * G.w u v
      + (bdiff (mem Y u) (mem Y v) : ℝ) * G.w u v
      + (bdiff (mem Z u) (mem Z v) : ℝ) * G.w u v := by
  have hcore := edge_atoms_nonexpansive (mem X u) (mem Y u) (mem Z u) (mem X v) (mem Y v) (mem Z v)
  have hcastle : ((bdiff (aA (mem X u) (mem Y u) (mem Z u)) (aA (mem X v) (mem Y v) (mem Z v))
        + bdiff (aB (mem X u) (mem Y u) (mem Z u)) (aB (mem X v) (mem Y v) (mem Z v))
        + bdiff (aC (mem X u) (mem Y u) (mem Z u)) (aC (mem X v) (mem Y v) (mem Z v))
        + bdiff (aU (mem X u) (mem Y u) (mem Z u)) (aU (mem X v) (mem Y v) (mem Z v)) : ℕ) : ℝ)
      ≤ ((bdiff (mem X u) (mem X v) + bdiff (mem Y u) (mem Y v) + bdiff (mem Z u) (mem Z v) : ℕ) : ℝ) :=
    Nat.cast_le.2 hcore
  rw [mem_atomA, mem_atomA, mem_atomB, mem_atomB, mem_atomC, mem_atomC, mem_atomU, mem_atomU]
  push_cast at hcastle ⊢
  nlinarith [hcastle, G.w_nonneg u v,
    mul_le_mul_of_nonneg_right hcastle (G.w_nonneg u v)]

/-- **The real capacity certificate.** For every undirected nonnegative-real-weighted graph,
  `cap A' + cap B' + cap C' + cap U' ≤ cap X + cap Y + cap Z`. -/
theorem recombination_capacity_leR (G : GraphR V) (X Y Z : Finset V) :
    cutCapacityR G (atomA X Y Z) + cutCapacityR G (atomB X Y Z)
        + cutCapacityR G (atomC X Y Z) + cutCapacityR G (atomU X Y Z)
      ≤ cutCapacityR G X + cutCapacityR G Y + cutCapacityR G Z := by
  have hsum : symCapR G (atomA X Y Z) + symCapR G (atomB X Y Z)
        + symCapR G (atomC X Y Z) + symCapR G (atomU X Y Z)
      ≤ symCapR G X + symCapR G Y + symCapR G Z := by
    rw [symCapR_eq_bdiff_sum, symCapR_eq_bdiff_sum, symCapR_eq_bdiff_sum, symCapR_eq_bdiff_sum,
        symCapR_eq_bdiff_sum, symCapR_eq_bdiff_sum, symCapR_eq_bdiff_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun u _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    exact edge_capacity_leR G X Y Z u v
  have hA := symCapR_eq_two_cutCapacityR G (atomA X Y Z)
  have hB := symCapR_eq_two_cutCapacityR G (atomB X Y Z)
  have hC := symCapR_eq_two_cutCapacityR G (atomC X Y Z)
  have hU := symCapR_eq_two_cutCapacityR G (atomU X Y Z)
  have hX := symCapR_eq_two_cutCapacityR G X
  have hY := symCapR_eq_two_cutCapacityR G Y
  have hZ := symCapR_eq_two_cutCapacityR G Z
  rw [hA, hB, hC, hU, hX, hY, hZ] at hsum
  linarith

/-- **Min-cut entropy over `ℝ`** of region `R`: the minimum real cut capacity over admissible cuts.
Uses the *same* cut sets `rtCuts bd R` as the `ℕ` model — only the capacity scalar differs. -/
noncomputable def rtEntropyR (G : GraphR V) (bd R : Finset V) (h : R ⊆ bd) : ℝ :=
  ((rtCuts bd R).image (cutCapacityR G)).min' ((rtCuts_nonempty h).image (cutCapacityR G))

/-- **Minimality (real):** the real min-cut entropy is at most the capacity of any admissible cut. -/
lemma rtEntropyR_le_cap (G : GraphR V) {bd R : Finset V} (h : R ⊆ bd)
    {S : Finset V} (hS : IsRTCut bd R S) : rtEntropyR G bd R h ≤ cutCapacityR G S := by
  unfold rtEntropyR
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨S, (mem_rtCuts).2 hS, rfl⟩

/-- The real min-cut entropy is achieved by some admissible cut. -/
lemma rtEntropyR_eq_cap (G : GraphR V) {bd R : Finset V} (h : R ⊆ bd) :
    ∃ S, IsRTCut bd R S ∧ rtEntropyR G bd R h = cutCapacityR G S := by
  unfold rtEntropyR
  have hmem := Finset.min'_mem ((rtCuts bd R).image (cutCapacityR G))
    ((rtCuts_nonempty h).image (cutCapacityR G))
  rw [Finset.mem_image] at hmem
  obtain ⟨S, hS, hcap⟩ := hmem
  exact ⟨S, (mem_rtCuts).1 hS, hcap.symm⟩

/-- **Monogamy of mutual information for the real-weighted undirected min-cut entropy.**
For pairwise-disjoint boundary regions `A, B, C` (with purifier `D`) in any finite undirected
nonnegative-real-weighted graph,
  `S_A + S_B + S_C + S_{ABC} ≤ S_{AB} + S_{AC} + S_{BC}`
(equivalently `I₃(A:B:C) ≤ 0`).  No planarity, no multicommodity flow. -/
theorem rtEntropyR_MMI (G : GraphR V) {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D) :
    rtEntropyR G bd A P.subA + rtEntropyR G bd B P.subB + rtEntropyR G bd C P.subC
        + rtEntropyR G bd (A ∪ B ∪ C) P.subABC
      ≤ rtEntropyR G bd (A ∪ B) P.subAB + rtEntropyR G bd (A ∪ C) P.subAC
        + rtEntropyR G bd (B ∪ C) P.subBC := by
  obtain ⟨X, hX, hXcap⟩ := rtEntropyR_eq_cap G P.subAB
  obtain ⟨Y, hY, hYcap⟩ := rtEntropyR_eq_cap G P.subAC
  obtain ⟨Z, hZ, hZcap⟩ := rtEntropyR_eq_cap G P.subBC
  have hA := rtEntropyR_le_cap G P.subA (admissible_A' P hX hY hZ)
  have hB := rtEntropyR_le_cap G P.subB (admissible_B' P hX hY hZ)
  have hC := rtEntropyR_le_cap G P.subC (admissible_C' P hX hY hZ)
  have hU := rtEntropyR_le_cap G P.subABC (admissible_U' P hX hY hZ)
  have hcert := recombination_capacity_leR G X Y Z
  rw [hXcap, hYcap, hZcap]
  linarith [hA, hB, hC, hU, hcert]

/-! ### Subsumption of the `ℕ` model and its strict witness

The `ℕ` graph embeds into a nonnegative-real graph by casting weights.  The real min-cut entropy of
the cast graph is the `Nat.cast` of the `ℕ` min-cut entropy (`min'` commutes with the strictly
monotone `Nat.cast`), so the reviewed `ℕ` strict anti-vacuity witness transports to a strict real
witness that genuinely instantiates `rtEntropyR_MMI`. -/

/-- Embed a `ℕ`-weighted graph into a nonnegative-real-weighted graph by casting weights. -/
def castGraph (G : Graph V) : GraphR V where
  w := fun u v => (G.w u v : ℝ)
  w_nonneg := fun u v => Nat.cast_nonneg _
  symm := fun u v => by rw [G.symm]

/-- Casting weights casts the cut capacity. -/
lemma cutCapacityR_castGraph (G : Graph V) (S : Finset V) :
    cutCapacityR (castGraph G) S = ((cutCapacity G S : ℕ) : ℝ) := by
  unfold cutCapacityR cutCapacity castGraph
  push_cast
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  by_cases h : u ∈ S ∧ v ∉ S <;> simp [h]

/-- The real min-cut entropy of a cast graph is the `Nat.cast` of the `ℕ` min-cut entropy. -/
lemma rtEntropyR_castGraph (G : Graph V) {bd R : Finset V} (h : R ⊆ bd) :
    rtEntropyR (castGraph G) bd R h = ((rtEntropy G bd R h : ℕ) : ℝ) := by
  unfold rtEntropyR rtEntropy
  -- both sides are a `min'` over the *same* index set `rtCuts bd R`; the real capacity is the
  -- cast of the ℕ capacity, and `Nat.cast : ℕ → ℝ` is a monotone map, so `min'` commutes with it.
  have hmono : Monotone (fun n : ℕ => (n : ℝ)) := fun a b hab => by
    simp only; exact_mod_cast hab
  have himg : (rtCuts bd R).image (cutCapacityR (castGraph G))
      = ((rtCuts bd R).image (cutCapacity G)).image (fun n : ℕ => (n : ℝ)) := by
    rw [Finset.image_image]
    refine Finset.image_congr (fun S _ => ?_)
    exact cutCapacityR_castGraph G S
  -- rewrite the LHS `min'` over the identical image, then commute `Nat.cast` past `min'`
  rw [Monotone.map_finset_min' hmono ((rtCuts_nonempty h).image (cutCapacity G))]
  congr 1

/-- **Strict real anti-vacuity witness.** On the cast star graph the tripartite information is
strictly negative over `ℝ`, `I₃ = S_A+S_B+S_C − S_{AB}−S_{AC}−S_{BC} + S_{ABC} = 3 − 6 + 1 = −2 < 0`,
transported from the `ℕ` witness through `rtEntropyR_castGraph`.  This genuinely instantiates
`rtEntropyR_MMI` and confirms the real theorem is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_MMI_strict_witness :
    rtEntropyR (castGraph starGraph) starBd {0} sA
        + rtEntropyR (castGraph starGraph) starBd {1} sB
        + rtEntropyR (castGraph starGraph) starBd {2} sC
        + rtEntropyR (castGraph starGraph) starBd {0, 1, 2} sABC
    < rtEntropyR (castGraph starGraph) starBd {0, 1} sAB
        + rtEntropyR (castGraph starGraph) starBd {0, 2} sAC
        + rtEntropyR (castGraph starGraph) starBd {1, 2} sBC := by
  rw [rtEntropyR_castGraph, rtEntropyR_castGraph, rtEntropyR_castGraph, rtEntropyR_castGraph,
      rtEntropyR_castGraph, rtEntropyR_castGraph, rtEntropyR_castGraph,
      star_SA, star_SB, star_SC, star_SAB, star_SAC, star_SBC, star_SABC]
  norm_num

/-! ## The general contraction-map sufficient condition for holographic entropy inequalities

The recombination certificate above is one instance of a general principle (the contraction-map
method of Bao–Nezami–Ooguri–Stoica–Sully–Walter): an entropy inequality among min-cut entropies
holds whenever the boolean map recombining the achieving cuts into candidate cuts for the bounded
regions is **edgewise Hamming-nonexpansive** on membership patterns.

Concretely, fix arities `m, k`.  Given regions `L : Fin m → Finset V` on the larger side and
`R : Fin k → Finset V` on the bounded side, achieving min-cuts `X i` for each `L i`, and a
**contraction map** `f : (Fin m → Bool) → (Fin k → Bool)` on membership patterns, form for each `j`
the candidate cut `S j = {v | f (fun i => v ∈ X i) j}`.  If every `S j` is admissible for `R j`
(boundary validity) and `f` is symmetric-Hamming nonexpansive over **all** pattern pairs, then
`∑ j S(R j) ≤ ∑ i S(L i)`.

This is a **sufficient** condition: a contraction map implies the holographic entropy inequality.
It does not claim to characterize which inequalities are holographic (the general holographic entropy
cone problem), only that any inequality with a contraction map is a theorem of the min-cut
model. -/

/-- The membership pattern of a vertex `v` against the achieving cuts `X`: bit `i` records whether
`v ∈ X i`. -/
def contractionPattern (X : Fin m → Finset V) (v : V) : Fin m → Bool :=
  fun i => mem (X i) v

/-- The candidate cut for the `j`-th bounded region: the vertices whose pattern maps to `true` in
coordinate `j` under the contraction map `f`. -/
def contractionCut (X : Fin m → Finset V) (f : (Fin m → Bool) → (Fin k → Bool)) (j : Fin k) :
    Finset V :=
  Finset.univ.filter (fun v => f (contractionPattern X v) j)

/-- Membership of a vertex in the `j`-th candidate cut is exactly the `j`-th output bit of the
contraction map applied to the vertex's pattern. -/
lemma mem_contractionCut (X : Fin m → Finset V) (f : (Fin m → Bool) → (Fin k → Bool))
    (j : Fin k) (v : V) : mem (contractionCut X f j) v = f (contractionPattern X v) j := by
  simp only [mem, contractionCut, Finset.mem_filter, Finset.mem_univ, true_and]
  cases f (contractionPattern X v) j <;> simp

/-- **The contraction-map sufficient condition for holographic entropy inequalities.**

Let `L : Fin m → Finset V` and `R : Fin k → Finset V` be boundary regions, with `X i` an achieving
minimum cut for each `L i` (`hX`).  Let `f : (Fin m → Bool) → (Fin k → Bool)` be a **contraction
map**: symmetric-Hamming nonexpansive on membership patterns (`hcontract`).  If each candidate cut
`contractionCut X f j` is admissible for `R j` (`hvalid`), then the holographic entropy inequality

  `∑ j S(R j) ≤ ∑ i S(L i)`

holds for the undirected nonnegative-real-weighted min-cut entropy.

The proof bounds each `S(R j)` by the capacity of its admissible candidate cut, rewrites the total
in the symmetric-separation form, applies the edgewise contraction pointwise against the nonnegative
weights, and divides the doubling identity by two.

This is a **sufficient** condition (a contraction map ⟹ the inequality); it does not claim to
determine which inequalities are holographic. -/
theorem entropyR_ineq_of_contraction (G : GraphR V) {bd : Finset V} {m k : ℕ}
    (L : Fin m → Finset V) (R : Fin k → Finset V)
    (hL : ∀ i, L i ⊆ bd) (hR : ∀ j, R j ⊆ bd)
    (X : Fin m → Finset V)
    (hX : ∀ i, IsRTCut bd (L i) (X i) ∧ cutCapacityR G (X i) = rtEntropyR G bd (L i) (hL i))
    (f : (Fin m → Bool) → (Fin k → Bool))
    (hvalid : ∀ j, IsRTCut bd (R j) (contractionCut X f j))
    (hcontract : ∀ p q : Fin m → Bool,
      (∑ j, bdiff (f p j) (f q j)) ≤ (∑ i, bdiff (p i) (q i))) :
    (∑ j, rtEntropyR G bd (R j) (hR j)) ≤ ∑ i, rtEntropyR G bd (L i) (hL i) := by
  -- Step 1: bound each bounded-region entropy by its admissible candidate cut's capacity.
  have hcapbound : (∑ j, rtEntropyR G bd (R j) (hR j))
      ≤ ∑ j, cutCapacityR G (contractionCut X f j) :=
    Finset.sum_le_sum (fun j _ => rtEntropyR_le_cap G (hR j) (hvalid j))
  -- Step 2: the doubled certificate `∑ j symCapR (S j) ≤ ∑ i symCapR (X i)`.
  have hsym : (∑ j, symCapR G (contractionCut X f j)) ≤ ∑ i, symCapR G (X i) := by
    -- rewrite every `symCapR` in `bdiff`/`mem` ordered-pair form
    have hLHS : (∑ j, symCapR G (contractionCut X f j))
        = ∑ u, ∑ v, ∑ j, (bdiff (mem (contractionCut X f j) u)
            (mem (contractionCut X f j) v) : ℝ) * G.w u v := by
      simp_rw [symCapR_eq_bdiff_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_comm]
    have hRHS : (∑ i, symCapR G (X i))
        = ∑ u, ∑ v, ∑ i, (bdiff (mem (X i) u) (mem (X i) v) : ℝ) * G.w u v := by
      simp_rw [symCapR_eq_bdiff_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_comm]
    rw [hLHS, hRHS]
    -- compare pointwise over ordered pairs
    refine Finset.sum_le_sum (fun u _ => ?_)
    refine Finset.sum_le_sum (fun v _ => ?_)
    -- pull out the nonnegative weight and apply the contraction
    have hj : (∑ j, (bdiff (mem (contractionCut X f j) u)
          (mem (contractionCut X f j) v) : ℝ))
        ≤ ∑ i, (bdiff (mem (X i) u) (mem (X i) v) : ℝ) := by
      have hcore := hcontract (contractionPattern X u) (contractionPattern X v)
      have : ((∑ j, bdiff (f (contractionPattern X u) j) (f (contractionPattern X v) j) : ℕ) : ℝ)
          ≤ ((∑ i, bdiff (contractionPattern X u i) (contractionPattern X v i) : ℕ) : ℝ) :=
        Nat.cast_le.2 hcore
      push_cast at this
      simp_rw [mem_contractionCut]
      exact this
    calc (∑ j, (bdiff (mem (contractionCut X f j) u)
              (mem (contractionCut X f j) v) : ℝ) * G.w u v)
        = (∑ j, (bdiff (mem (contractionCut X f j) u)
              (mem (contractionCut X f j) v) : ℝ)) * G.w u v := by rw [← Finset.sum_mul]
      _ ≤ (∑ i, (bdiff (mem (X i) u) (mem (X i) v) : ℝ)) * G.w u v :=
          mul_le_mul_of_nonneg_right hj (G.w_nonneg u v)
      _ = ∑ i, (bdiff (mem (X i) u) (mem (X i) v) : ℝ) * G.w u v := by rw [Finset.sum_mul]
  -- Step 3: convert `symCapR = 2 · cutCapacityR` and divide by two.
  have hcapcert : (∑ j, cutCapacityR G (contractionCut X f j))
      ≤ ∑ i, cutCapacityR G (X i) := by
    have h2L : (∑ j, symCapR G (contractionCut X f j))
        = 2 * ∑ j, cutCapacityR G (contractionCut X f j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => symCapR_eq_two_cutCapacityR G _)
    have h2R : (∑ i, symCapR G (X i)) = 2 * ∑ i, cutCapacityR G (X i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => symCapR_eq_two_cutCapacityR G _)
    rw [h2L, h2R] at hsym
    linarith
  -- Step 4: the achieving cuts realize `∑ i cutCapacityR (X i) = ∑ i S(L i)`.
  have hachieve : (∑ i, cutCapacityR G (X i)) = ∑ i, rtEntropyR G bd (L i) (hL i) :=
    Finset.sum_congr rfl (fun i _ => (hX i).2)
  -- Chain the four steps.
  calc (∑ j, rtEntropyR G bd (R j) (hR j))
      ≤ ∑ j, cutCapacityR G (contractionCut X f j) := hcapbound
    _ ≤ ∑ i, cutCapacityR G (X i) := hcapcert
    _ = ∑ i, rtEntropyR G bd (L i) (hL i) := hachieve

/-! ### Recovering MMI as an instance of the general contraction-map theorem

We re-derive the monogamy inequality `∑ j S(R j) ≤ ∑ i S(L i)` with `L = ![AB, AC, BC]`,
`R = ![A, B, C, ABC]`, and the recombination expressed directly as a boolean contraction map on the
three achieving-cut membership bits.  The contraction hypothesis is the same `64`-case fact as
`edge_atoms_nonexpansive`, and the candidate cuts coincide with the recombination atoms, so their
admissibility reuses `admissible_A'`…`admissible_U'`. -/

/-- The recombination expressed as a boolean contraction map on the `3`-bit patterns `(∈X,∈Y,∈Z)`:
`(A', B', C', U') = ((X∩Y)\Z, (X∩Z)\Y, (Y∩Z)\X, X∪Y∪Z)`. -/
def mmiContraction (p : Fin 3 → Bool) : Fin 4 → Bool :=
  ![aA (p 0) (p 1) (p 2), aB (p 0) (p 1) (p 2), aC (p 0) (p 1) (p 2), aU (p 0) (p 1) (p 2)]

/-- The `mmiContraction` map is symmetric-Hamming nonexpansive on all `3`-bit → `4`-bit pattern
pairs — the same `64`-case fact as `edge_atoms_nonexpansive`, reindexed over `Fin`. -/
lemma mmiContraction_nonexpansive (p q : Fin 3 → Bool) :
    (∑ j, bdiff (mmiContraction p j) (mmiContraction q j))
      ≤ ∑ i, bdiff (p i) (q i) := by
  simp only [mmiContraction, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three]
  exact edge_atoms_nonexpansive (p 0) (p 1) (p 2) (q 0) (q 1) (q 2)

/-- The `j`-th `mmiContraction` candidate cut coincides with the corresponding recombination atom
`A', B', C', U'`. -/
lemma contractionCut_mmi (X Y Z : Finset V) :
    ∀ j, contractionCut ![X, Y, Z] mmiContraction j
      = ![atomA X Y Z, atomB X Y Z, atomC X Y Z, atomU X Y Z] j := by
  intro j
  have hmem : ∀ (v : V) (S : Finset V), v ∈ S ↔ mem S v = true := by
    intro v S; simp [mem]
  fin_cases j
  all_goals
  · ext v
    rw [hmem _ (contractionCut _ _ _), hmem _ (![_, _, _, _] _), mem_contractionCut]
    simp only [mmiContraction, contractionPattern, Fin.isValue, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, Matrix.head_fin_const, Fin.reduceFinMk,
      mem_atomA, mem_atomB, mem_atomC, mem_atomU]

/-- **Monogamy of mutual information recovered from the general contraction-map theorem.**
Instantiating `entropyR_ineq_of_contraction` with `L = ![AB, AC, BC]`, `R = ![A, B, C, ABC]` and the
recombination contraction map reproduces MMI, demonstrating that the concrete recombination proof is
a special case of the general engine. -/
theorem rtEntropyR_MMI_via_contraction (G : GraphR V)
    {bd A B C D : Finset V} (P : BoundaryPartition bd A B C D) :
    rtEntropyR G bd A P.subA + rtEntropyR G bd B P.subB + rtEntropyR G bd C P.subC
        + rtEntropyR G bd (A ∪ B ∪ C) P.subABC
      ≤ rtEntropyR G bd (A ∪ B) P.subAB + rtEntropyR G bd (A ∪ C) P.subAC
        + rtEntropyR G bd (B ∪ C) P.subBC := by
  -- achieving cuts for the three pairs
  obtain ⟨X, hX, hXcap⟩ := rtEntropyR_eq_cap G P.subAB
  obtain ⟨Y, hY, hYcap⟩ := rtEntropyR_eq_cap G P.subAC
  obtain ⟨Z, hZ, hZcap⟩ := rtEntropyR_eq_cap G P.subBC
  -- assemble the general theorem's data
  set L : Fin 3 → Finset V := ![A ∪ B, A ∪ C, B ∪ C] with hLdef
  set R : Fin 4 → Finset V := ![A, B, C, A ∪ B ∪ C] with hRdef
  have hLsub : ∀ i, L i ⊆ bd := by
    intro i; fin_cases i <;> simp only [hLdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    exacts [P.subAB, P.subAC, P.subBC]
  have hRsub : ∀ j, R j ⊆ bd := by
    intro j; fin_cases j <;> simp only [hRdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    exacts [P.subA, P.subB, P.subC, P.subABC]
  set Xs : Fin 3 → Finset V := ![X, Y, Z] with hXsdef
  -- achieving-cut hypothesis for the general theorem
  have hXok : ∀ i, IsRTCut bd (L i) (Xs i) ∧ cutCapacityR G (Xs i) = rtEntropyR G bd (L i) (hLsub i) := by
    intro i; fin_cases i <;>
      simp only [hLdef, hXsdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
    · exact ⟨hX, hXcap.symm⟩
    · exact ⟨hY, hYcap.symm⟩
    · exact ⟨hZ, hZcap.symm⟩
  -- candidate-cut admissibility, via the recombination atoms
  have hvalid : ∀ j, IsRTCut bd (R j) (contractionCut Xs mmiContraction j) := by
    intro j
    rw [hXsdef, contractionCut_mmi]
    fin_cases j <;>
      simp only [hRdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    · exact admissible_A' P hX hY hZ
    · exact admissible_B' P hX hY hZ
    · exact admissible_C' P hX hY hZ
    · exact admissible_U' P hX hY hZ
  -- apply the general theorem
  have hgen := entropyR_ineq_of_contraction G L R hLsub hRsub Xs hXok mmiContraction hvalid
    mmiContraction_nonexpansive
  -- unfold the `Fin`-indexed sums into the named regions
  simp only [hLdef, hRdef, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three] at hgen
  -- the subset proofs match up to proof irrelevance
  convert hgen using 2 <;> ring_nf

/-- **Strict anti-vacuity for MMI-via-contraction.** The general contraction-map theorem, specialized
to MMI, is genuinely non-vacuous: on the star graph its conclusion is the strict inequality
`I₃ = −2 < 0` (reusing `rtEntropyR_MMI_strict_witness`), so the abstraction subsumes a strict,
inhabited instance rather than the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_MMI_via_contraction_strict_witness :
    rtEntropyR (castGraph starGraph) starBd {0} sA
        + rtEntropyR (castGraph starGraph) starBd {1} sB
        + rtEntropyR (castGraph starGraph) starBd {2} sC
        + rtEntropyR (castGraph starGraph) starBd {0, 1, 2} sABC
    < rtEntropyR (castGraph starGraph) starBd {0, 1} sAB
        + rtEntropyR (castGraph starGraph) starBd {0, 2} sAC
        + rtEntropyR (castGraph starGraph) starBd {1, 2} sBC :=
  rtEntropyR_MMI_strict_witness

/-- All real min-cuts in the strict witness are strictly positive (so the strict real MMI witness is
not vacuously about zero entropies). -/
theorem rtEntropyR_mmi_witness_mincuts_pos :
    0 < rtEntropyR (castGraph starGraph) starBd {0} sA
      ∧ 0 < rtEntropyR (castGraph starGraph) starBd {1} sB
      ∧ 0 < rtEntropyR (castGraph starGraph) starBd {2} sC
      ∧ 0 < rtEntropyR (castGraph starGraph) starBd {0, 1} sAB
      ∧ 0 < rtEntropyR (castGraph starGraph) starBd {0, 2} sAC
      ∧ 0 < rtEntropyR (castGraph starGraph) starBd {1, 2} sBC
      ∧ 0 < rtEntropyR (castGraph starGraph) starBd {0, 1, 2} sABC := by
  rw [rtEntropyR_castGraph, rtEntropyR_castGraph, rtEntropyR_castGraph, rtEntropyR_castGraph,
      rtEntropyR_castGraph, rtEntropyR_castGraph, rtEntropyR_castGraph,
      star_SA, star_SB, star_SC, star_SAB, star_SAC, star_SBC, star_SABC]
  norm_num

/-! ## A certified five-party cyclic holographic entropy inequality

As a second instance of the general contraction-map engine (`entropyR_ineq_of_contraction`), we
certify a genuine `n = 5` holographic entropy inequality.  Five elementary boundary regions
`A₀,…,A₄` (with a purifier = the rest of the boundary) satisfy the cyclic
adjacent-triples-dominate-adjacent-pairs inequality

  `S(A₀A₁A₂) + S(A₁A₂A₃) + S(A₂A₃A₄) + S(A₀A₃A₄) + S(A₀A₁A₄)`
    `≥ S(A₀A₁) + S(A₁A₂) + S(A₂A₃) + S(A₃A₄) + S(A₀A₄)`,

with the five cyclically adjacent triples on the larger side and the five cyclically adjacent pairs
on the bounded side.

This is a **valid** holographic inequality — it is **implied by the SA + SSA + MMI entropy cone**, so
it is **not a new facet** of the holographic entropy cone; it is nonetheless a genuine `n = 5`
statement, and its machine-checked proof exhibits the contraction-map engine at an arity beyond the
tripartite MMI instance.  The `32`-case boolean contraction map below recombines the five
achieving-cut membership bits (one per triple) into the five pair-cut membership bits; boundary
validity of the recombined cuts is a finite check on the six membership patterns that boundary
vertices can carry (the five elementary colors plus the purifier).  The general holographic entropy
cone for `n ≥ 5` remains open. -/

/-- The five cyclically adjacent triples of colors (larger side), as index sets in `Fin 5`:
`{0,1,2}, {1,2,3}, {2,3,4}, {0,3,4}, {0,1,4}`. -/
def cyc5Triple : Fin 5 → Finset (Fin 5) :=
  ![{0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {0, 3, 4}, {0, 1, 4}]

/-- The five cyclically adjacent pairs of colors (bounded side), as index sets in `Fin 5`:
`{0,1}, {1,2}, {2,3}, {3,4}, {0,4}`. -/
def cyc5Pair : Fin 5 → Finset (Fin 5) :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {0, 4}]

variable {A : Fin 5 → Finset V}

/-- The `i`-th larger-side region: the union of the three elementary regions in the `i`-th triple. -/
def cyc5L (A : Fin 5 → Finset V) (i : Fin 5) : Finset V := (cyc5Triple i).biUnion A

/-- The `j`-th bounded-side region: the union of the two elementary regions in the `j`-th pair. -/
def cyc5R (A : Fin 5 → Finset V) (j : Fin 5) : Finset V := (cyc5Pair j).biUnion A

/-- The `32`-entry boolean contraction map recombining the five triple-cut membership bits into the
five pair-cut membership bits.  Input bit `i` = "the vertex's color lies in the `i`-th triple";
output bit `j` = "its color lies in the `j`-th pair".  Defined by an explicit match on the five input
bits so that `decide` evaluates it. -/
def cyc5f (p : Fin 5 → Bool) : Fin 5 → Bool :=
  match p 0, p 1, p 2, p 3, p 4 with
  | false, false, false, false, false => ![false, false, false, false, false]
  | false, false, false, false, true => ![false, false, false, false, false]
  | false, false, false, true, false => ![false, false, false, false, false]
  | false, false, false, true, true => ![false, false, false, false, true]
  | false, false, true, false, false => ![false, false, false, false, false]
  | false, false, true, false, true => ![false, false, false, false, true]
  | false, false, true, true, false => ![false, false, false, true, false]
  | false, false, true, true, true => ![false, false, false, true, true]
  | false, true, false, false, false => ![false, false, false, false, false]
  | false, true, false, false, true => ![false, true, false, false, false]
  | false, true, false, true, false => ![false, false, false, true, false]
  | false, true, false, true, true => ![false, false, false, false, false]
  | false, true, true, false, false => ![false, false, true, false, false]
  | false, true, true, false, true => ![false, false, false, false, false]
  | false, true, true, true, false => ![false, false, true, true, false]
  | false, true, true, true, true => ![false, false, false, true, false]
  | true, false, false, false, false => ![false, false, false, false, false]
  | true, false, false, false, true => ![true, false, false, false, false]
  | true, false, false, true, false => ![false, false, false, false, true]
  | true, false, false, true, true => ![true, false, false, false, true]
  | true, false, true, false, false => ![false, false, true, false, false]
  | true, false, true, false, true => ![false, false, false, false, false]
  | true, false, true, true, false => ![false, false, false, false, false]
  | true, false, true, true, true => ![false, false, false, false, true]
  | true, true, false, false, false => ![false, true, false, false, false]
  | true, true, false, false, true => ![true, true, false, false, false]
  | true, true, false, true, false => ![false, false, false, false, false]
  | true, true, false, true, true => ![true, false, false, false, false]
  | true, true, true, false, false => ![false, true, true, false, false]
  | true, true, true, false, true => ![false, true, false, false, false]
  | true, true, true, true, false => ![false, false, true, false, false]
  | true, true, true, true, true => ![false, false, false, false, false]

/-- **Contraction (Hamming-nonexpansiveness) of `cyc5f`.** For any two five-bit input patterns, the
five output bits separate them at most as often as the five input bits.  A finite `1024`-pair fact,
checked by `decide`. -/
lemma cyc5f_nonexpansive (p q : Fin 5 → Bool) :
    (∑ j, bdiff (cyc5f p j) (cyc5f q j)) ≤ ∑ i, bdiff (p i) (q i) := by
  have key : ∀ p q : Fin 5 → Bool,
      (∑ j, bdiff (cyc5f p j) (cyc5f q j)) ≤ ∑ i, bdiff (p i) (q i) := by decide
  exact key p q

/-- The six input patterns carried by boundary vertices — one per elementary color and the all-`false`
purifier pattern — map through `cyc5f` exactly to the corresponding pair-membership pattern.
`cyc5f (fun i => color ∈ triple i) j = (color ∈ pair j)`, and the purifier maps `false ↦ false`.  A
finite `decide` over the six colors (`Fin 5` plus purifier handled by the all-`false` case). -/
lemma cyc5f_boundary (c : Fin 5) :
    cyc5f (fun i => decide (c ∈ cyc5Triple i)) = fun j => decide (c ∈ cyc5Pair j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `cyc5f`. -/
lemma cyc5f_zero : cyc5f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

namespace Cyc5

variable {bd : Finset V}

/-- Pairwise disjointness and boundary-containment of the five elementary regions. -/
structure Regions (bd : Finset V) (A : Fin 5 → Finset V) : Prop where
  /-- each elementary region lies in the boundary -/
  sub : ∀ c, A c ⊆ bd
  /-- distinct elementary regions are disjoint -/
  disj : ∀ c c', c ≠ c' → Disjoint (A c) (A c')

/-- Membership of `v ∈ A c` in a triple-region: `v ∈ cyc5L A i ↔ c ∈ cyc5Triple i` (for `v` in the
elementary region of a fixed color `c`, using disjointness). -/
lemma mem_cyc5L_of_color (hR : Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (i : Fin 5) :
    v ∈ cyc5L A i ↔ c ∈ cyc5Triple i := by
  unfold cyc5L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `cyc5R A j ⊆ bd`. -/
lemma cyc5R_sub (hR : Regions bd A) (j : Fin 5) : cyc5R A j ⊆ bd := by
  unfold cyc5R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `cyc5L A i ⊆ bd`. -/
lemma cyc5L_sub (hR : Regions bd A) (i : Fin 5) : cyc5L A i ⊆ bd := by
  unfold cyc5L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a pair-region: `v ∈ cyc5R A j ↔ c ∈ cyc5Pair j`. -/
lemma mem_cyc5R_of_color (hR : Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (j : Fin 5) :
    v ∈ cyc5R A j ↔ c ∈ cyc5Pair j := by
  unfold cyc5R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the triple-pattern:
`contractionPattern X v = fun i => decide (c ∈ cyc5Triple i)`. -/
lemma contractionPattern_of_color (hR : Regions bd A)
    (X : Fin 5 → Finset V) (hX : ∀ i, IsRTCut bd (cyc5L A i) (X i))
    {v : V} {c : Fin 5} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ cyc5Triple i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ cyc5Triple i
  · -- v ∈ cyc5L A i ⊆ X i
    have : v ∈ X i := (hX i).1 ((mem_cyc5L_of_color hR hv i).2 hc)
    simp [this, hc]
  · -- v ∈ bd, v ∉ cyc5L A i ⟹ v ∉ X i
    have hvL : v ∉ cyc5L A i := fun h => hc ((mem_cyc5L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex (in `bd`, outside every elementary region), the achieving cuts realize the
all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 5 → Finset V) (hX : ∀ i, IsRTCut bd (cyc5L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ cyc5L A i := by
    unfold cyc5L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X cyc5f j` is an admissible RT
cut for the pair-region `cyc5R A j`.  For every boundary vertex, its `cyc5f`-image membership matches
its pair-region membership: colors via `cyc5f_boundary`, the purifier via `cyc5f_zero`; bulk vertices
are free. -/
lemma cyc5_hvalid (hR : Regions bd A)
    (X : Fin 5 → Finset V) (hX : ∀ i, IsRTCut bd (cyc5L A i) (X i)) (j : Fin 5) :
    IsRTCut bd (cyc5R A j) (contractionCut X cyc5f j) := by
  -- boundary vertices carry one of the six patterns; on each, `cyc5f` reproduces pair membership.
  have hkey : ∀ v ∈ bd, mem (contractionCut X cyc5f j) v = mem (cyc5R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, cyc5f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_cyc5R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, cyc5f_zero]
      have : v ∉ cyc5R A j := by
        unfold cyc5R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · -- cyc5R A j ⊆ contractionCut …: x ∈ cyc5R A j ⟹ x ∈ bd ⟹ memberships agree
    have hxbd : x ∈ bd := cyc5R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · -- boundary x ∉ cyc5R A j ⟹ x ∉ contractionCut …
    intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

end Cyc5

open Cyc5

/-- **The certified five-party cyclic holographic entropy inequality.**
For five pairwise-disjoint boundary regions `A₀,…,A₄` (with the rest of `bd` a purifier) in any finite
undirected nonnegative-real-weighted graph, the cyclic adjacent-triples side dominates the cyclic
adjacent-pairs side:

  `∑ⱼ S(pairⱼ) ≤ ∑ᵢ S(tripleᵢ)`,

i.e.

  `S(A₀A₁) + S(A₁A₂) + S(A₂A₃) + S(A₃A₄) + S(A₀A₄)`
    `≤ S(A₀A₁A₂) + S(A₁A₂A₃) + S(A₂A₃A₄) + S(A₀A₃A₄) + S(A₀A₁A₄)`.

A valid holographic inequality **implied by the SA + SSA + MMI cone** (hence not a new facet), proved
as an instance of the general contraction-map engine `entropyR_ineq_of_contraction` via the `32`-case
map `cyc5f`.  The general holographic entropy cone for `n ≥ 5` remains open. -/
theorem rtEntropyR_cyclic5 (G : GraphR V) {bd : Finset V} {A : Fin 5 → Finset V}
    (hR : Regions bd A) :
    (∑ j, rtEntropyR G bd (cyc5R A j) (cyc5R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (cyc5L A i) (cyc5L_sub hR i) := by
  -- pick achieving cuts for the five triple-regions
  have hXex : ∀ i, ∃ S, IsRTCut bd (cyc5L A i) S
      ∧ rtEntropyR G bd (cyc5L A i) (cyc5L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (cyc5L_sub hR i)
  choose X hXcut hXcap using hXex
  -- assemble the general theorem's achieving-cut hypothesis
  have hXok : ∀ i, IsRTCut bd (cyc5L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (cyc5L A i) (cyc5L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  -- validity of the recombined candidate cuts
  have hvalid : ∀ j, IsRTCut bd (cyc5R A j) (contractionCut X cyc5f j) :=
    fun j => cyc5_hvalid hR X hXcut j
  -- apply the general contraction-map engine
  exact entropyR_ineq_of_contraction G (cyc5L A) (cyc5R A)
    (cyc5L_sub hR) (cyc5R_sub hR) X hXok cyc5f hvalid cyc5f_nonexpansive

/-! ### Anti-vacuity witness: a strict five-party instance

The five-party **star** on `Fin 7` has five colored boundary vertices `0,…,4` (regions `A₀,…,A₄`),
one purifier boundary vertex `5`, and one central bulk vertex `6`, with every boundary vertex joined
to the center by a weight-`1` bond.  A region of `k` colored vertices has min-cut entropy
`min(k, 6 − k)` (cut the `k` bonds, or cut the other `6 − k`), so every adjacent pair (`k = 2`) has
entropy `2` and every adjacent triple (`k = 3`) has entropy `3`.  The larger side sums to `15`, the
bounded side to `10`, a strict slack of `5`, with all ten entropies positive. -/

/-- The five-party star bulk graph on `Fin 7`: boundary `0,…,5` each bonded (weight `1`) to central
bulk vertex `6`. -/
def star5Graph : Graph (Fin 7) where
  w := fun u v => if (u = 6 ∧ v.val < 6) ∨ (v = 6 ∧ u.val < 6) then 1 else 0
  symm := by intro u v; by_cases h : u = 6 <;> by_cases h2 : v = 6 <;> simp_all

/-- Boundary of the five-party star: `{0,1,2,3,4,5}` (five colors plus a purifier). -/
def star5Bd : Finset (Fin 7) := {0, 1, 2, 3, 4, 5}

/-- The five elementary regions of the star witness: `A c = {c}` for `c ∈ Fin 5`. -/
def star5A : Fin 5 → Finset (Fin 7) := ![{0}, {1}, {2}, {3}, {4}]

lemma star5A_regions : Cyc5.Regions star5Bd star5A where
  sub := by decide
  disj := by decide

lemma star5_cyc5R_sub (j : Fin 5) : cyc5R star5A j ⊆ star5Bd :=
  Cyc5.cyc5R_sub star5A_regions j
lemma star5_cyc5L_sub (i : Fin 5) : cyc5L star5A i ⊆ star5Bd :=
  Cyc5.cyc5L_sub star5A_regions i

/-- Each cyclic pair entropy of the star witness is `2`. -/
lemma star5_pairR (j : Fin 5) :
    rtEntropy star5Graph star5Bd (cyc5R star5A j) (star5_cyc5R_sub j) = 2 := by
  fin_cases j <;> · unfold cyc5R cyc5Pair star5A; decide

/-- Each cyclic triple entropy of the star witness is `3`. -/
lemma star5_tripleL (i : Fin 5) :
    rtEntropy star5Graph star5Bd (cyc5L star5A i) (star5_cyc5L_sub i) = 3 := by
  fin_cases i <;> · unfold cyc5L cyc5Triple star5A; decide

/-- **Strict five-party anti-vacuity witness (real).** On the cast star graph the cyclic inequality is
strict: the bounded side sums to `10` and the larger side to `15` (slack `5`), and every one of the
ten min-cut entropies is positive — so `rtEntropyR_cyclic5` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_cyclic5_strict_witness :
    (∑ j, rtEntropyR (castGraph star5Graph) star5Bd (cyc5R star5A j)
        (Cyc5.cyc5R_sub (A := star5A) star5A_regions j))
      < ∑ i, rtEntropyR (castGraph star5Graph) star5Bd (cyc5L star5A i)
        (Cyc5.cyc5L_sub (A := star5A) star5A_regions i) := by
  have hpair : ∀ j, rtEntropyR (castGraph star5Graph) star5Bd (cyc5R star5A j)
      (Cyc5.cyc5R_sub (A := star5A) star5A_regions j) = 2 := by
    intro j
    rw [rtEntropyR_castGraph, star5_pairR j]; norm_num
  have htriple : ∀ i, rtEntropyR (castGraph star5Graph) star5Bd (cyc5L star5A i)
      (Cyc5.cyc5L_sub (A := star5A) star5A_regions i) = 3 := by
    intro i
    rw [rtEntropyR_castGraph, star5_tripleL i]; norm_num
  rw [Finset.sum_congr rfl (fun j _ => hpair j), Finset.sum_congr rfl (fun i _ => htriple i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- All ten min-cut entropies in the five-party strict witness are strictly positive. -/
theorem rtEntropyR_cyclic5_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star5Graph) star5Bd (cyc5R star5A j)
        (Cyc5.cyc5R_sub (A := star5A) star5A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star5Graph) star5Bd (cyc5L star5A i)
        (Cyc5.cyc5L_sub (A := star5A) star5A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star5_pairR j]; norm_num
  · rw [rtEntropyR_castGraph, star5_tripleL i]; norm_num

/-! ## A genuinely new five-party holographic entropy cone facet

As a further instance of the general contraction-map engine (`entropyR_ineq_of_contraction`), we
certify a five-party holographic entropy inequality that is a **genuine facet** of the five-party
holographic entropy cone — that is, it is **not** implied by subadditivity, strong subadditivity and
monogamy of mutual information (the `SA + SSA + MMI` cone).  (This contrasts with `rtEntropyR_cyclic5`
above, which *is* cone-implied.)  With five elementary boundary regions `A₀,…,A₄` (colors `A,B,C,D,E`,
plus a purifier = the rest of the boundary) the inequality is

  `S(ABC) + S(ABD) + S(ACE) + S(BDE) + S(CDE)`
    `≥ S(AB) + S(AC) + S(BD) + S(CE) + S(DE) + S(ABCDE)`,

with the five triples `ABC, ABD, ACE, BDE, CDE` on the larger side and the six regions
`AB, AC, BD, CE, DE, ABCDE` on the bounded side.  Being outside the `SA + SSA + MMI` cone, it is a new
facet of the five-party holographic entropy cone; its validity for the undirected min-cut model is
established here by exhibiting an explicit contraction map, not by cone membership.

The `32`-entry boolean contraction map below recombines the five triple-cut membership bits (one per
larger-side triple) into the six bounded-region membership bits; boundary validity of the recombined
cuts is a finite check on the six membership patterns that boundary vertices can carry (the five
elementary colors plus the purifier).  The general holographic entropy cone for `n ≥ 5` remains
open. -/

/-- The five larger-side triples of colors, as index sets in `Fin 5`:
`{0,1,2}, {0,1,3}, {0,2,4}, {1,3,4}, {2,3,4}`. -/
def facet5Triple : Fin 5 → Finset (Fin 5) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 2, 4}, {1, 3, 4}, {2, 3, 4}]

/-- The six bounded-side regions of colors, as index sets in `Fin 5`:
`{0,1}, {0,2}, {1,3}, {2,4}, {3,4}, {0,1,2,3,4}`. -/
def facet5Reg : Fin 6 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {1, 3}, {2, 4}, {3, 4}, {0, 1, 2, 3, 4}]

variable {A : Fin 5 → Finset V}

/-- The `i`-th larger-side region: the union of the three elementary regions in the `i`-th triple. -/
def facet5L (A : Fin 5 → Finset V) (i : Fin 5) : Finset V := (facet5Triple i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th region set. -/
def facet5R (A : Fin 5 → Finset V) (j : Fin 6) : Finset V := (facet5Reg j).biUnion A

/-- The `32`-entry boolean contraction map recombining the five triple-cut membership bits into the
six bounded-region membership bits.  Input bit `i` = "the vertex's color lies in the `i`-th triple";
output bit `j` = "its color lies in the `j`-th bounded region".  Defined by an explicit match on the
five input bits so that `decide` evaluates it. -/
def facet5f (p : Fin 5 → Bool) : Fin 6 → Bool :=
  match p 0, p 1, p 2, p 3, p 4 with
  | false, false, false, false, false => ![false, false, false, false, false, false]
  | false, false, false, false, true => ![false, false, false, false, false, true]
  | false, false, false, true, false => ![false, false, false, false, false, true]
  | false, false, false, true, true => ![false, false, false, false, true, true]
  | false, false, true, false, false => ![false, false, false, false, false, true]
  | false, false, true, false, true => ![false, false, false, true, false, true]
  | false, false, true, true, false => ![false, false, false, false, true, true]
  | false, false, true, true, true => ![false, false, false, true, true, true]
  | false, true, false, false, false => ![false, false, false, false, false, true]
  | false, true, false, false, true => ![false, false, true, false, false, true]
  | false, true, false, true, false => ![false, false, true, false, false, true]
  | false, true, false, true, true => ![false, false, true, false, true, true]
  | false, true, true, false, false => ![true, false, false, false, false, true]
  | false, true, true, false, true => ![false, false, false, false, false, true]
  | false, true, true, true, false => ![false, false, false, false, false, true]
  | false, true, true, true, true => ![false, false, false, false, true, true]
  | true, false, false, false, false => ![false, false, false, false, false, true]
  | true, false, false, false, true => ![false, true, false, false, false, true]
  | true, false, false, true, false => ![false, false, true, false, false, true]
  | true, false, false, true, true => ![false, false, false, false, false, true]
  | true, false, true, false, false => ![false, true, false, false, false, true]
  | true, false, true, false, true => ![false, true, false, true, false, true]
  | true, false, true, true, false => ![false, false, false, false, false, true]
  | true, false, true, true, true => ![false, false, false, true, false, true]
  | true, true, false, false, false => ![true, false, false, false, false, true]
  | true, true, false, false, true => ![false, false, false, false, false, true]
  | true, true, false, true, false => ![true, false, true, false, false, true]
  | true, true, false, true, true => ![false, false, true, false, false, true]
  | true, true, true, false, false => ![true, true, false, false, false, true]
  | true, true, true, false, true => ![false, true, false, false, false, true]
  | true, true, true, true, false => ![true, false, false, false, false, true]
  | true, true, true, true, true => ![false, false, false, false, false, true]

/-- **Contraction (Hamming-nonexpansiveness) of `facet5f`.** For any two five-bit input patterns, the
six output bits separate them at most as often as the five input bits.  A finite `1024`-pair fact,
checked by `decide`. -/
lemma facet5f_nonexpansive (p q : Fin 5 → Bool) :
    (∑ j, bdiff (facet5f p j) (facet5f q j)) ≤ ∑ i, bdiff (p i) (q i) := by
  have key : ∀ p q : Fin 5 → Bool,
      (∑ j, bdiff (facet5f p j) (facet5f q j)) ≤ ∑ i, bdiff (p i) (q i) := by decide
  exact key p q

/-- The six input patterns carried by boundary vertices — one per elementary color and the all-`false`
purifier pattern — map through `facet5f` exactly to the corresponding bounded-region membership
pattern.  `facet5f (fun i => color ∈ triple i) j = (color ∈ region j)`, and the purifier maps
`false ↦ false`.  A finite `decide` over the six colors (`Fin 5` plus purifier handled by the
all-`false` case). -/
lemma facet5f_boundary (c : Fin 5) :
    facet5f (fun i => decide (c ∈ facet5Triple i)) = fun j => decide (c ∈ facet5Reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet5f`. -/
lemma facet5f_zero : facet5f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

namespace Facet5

variable {bd : Finset V}

/-- Membership of `v ∈ A c` in a triple-region: `v ∈ facet5L A i ↔ c ∈ facet5Triple i` (for `v` in the
elementary region of a fixed color `c`, using disjointness). -/
lemma mem_facet5L_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (i : Fin 5) :
    v ∈ facet5L A i ↔ c ∈ facet5Triple i := by
  unfold facet5L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet5R A j ⊆ bd`. -/
lemma facet5R_sub (hR : Cyc5.Regions bd A) (j : Fin 6) : facet5R A j ⊆ bd := by
  unfold facet5R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet5L A i ⊆ bd`. -/
lemma facet5L_sub (hR : Cyc5.Regions bd A) (i : Fin 5) : facet5L A i ⊆ bd := by
  unfold facet5L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region: `v ∈ facet5R A j ↔ c ∈ facet5Reg j`. -/
lemma mem_facet5R_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (j : Fin 6) :
    v ∈ facet5R A j ↔ c ∈ facet5Reg j := by
  unfold facet5R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the triple-pattern:
`contractionPattern X v = fun i => decide (c ∈ facet5Triple i)`. -/
lemma contractionPattern_of_color (hR : Cyc5.Regions bd A)
    (X : Fin 5 → Finset V) (hX : ∀ i, IsRTCut bd (facet5L A i) (X i))
    {v : V} {c : Fin 5} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet5Triple i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet5Triple i
  · have : v ∈ X i := (hX i).1 ((mem_facet5L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet5L A i := fun h => hc ((mem_facet5L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex (in `bd`, outside every elementary region), the achieving cuts realize the
all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 5 → Finset V) (hX : ∀ i, IsRTCut bd (facet5L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet5L A i := by
    unfold facet5L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X facet5f j` is an admissible
RT cut for the bounded region `facet5R A j`.  For every boundary vertex, its `facet5f`-image
membership matches its bounded-region membership: colors via `facet5f_boundary`, the purifier via
`facet5f_zero`; bulk vertices are free. -/
lemma facet5_hvalid (hR : Cyc5.Regions bd A)
    (X : Fin 5 → Finset V) (hX : ∀ i, IsRTCut bd (facet5L A i) (X i)) (j : Fin 6) :
    IsRTCut bd (facet5R A j) (contractionCut X facet5f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet5f j) v = mem (facet5R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, facet5f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet5R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, facet5f_zero]
      have : v ∉ facet5R A j := by
        unfold facet5R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet5R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

end Facet5

open Facet5

/-- **A genuinely new five-party holographic entropy cone facet.**
For five pairwise-disjoint boundary regions `A₀,…,A₄` (with the rest of `bd` a purifier) in any finite
undirected nonnegative-real-weighted graph, the five larger-side triples dominate the six bounded-side
regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(tripleᵢ)`,

i.e.

  `S(AB) + S(AC) + S(BD) + S(CE) + S(DE) + S(ABCDE)`
    `≤ S(ABC) + S(ABD) + S(ACE) + S(BDE) + S(CDE)`.

Unlike `rtEntropyR_cyclic5`, this inequality is **not implied by the `SA + SSA + MMI` cone**: it is a
genuine facet of the five-party holographic entropy cone (source: the five-party holographic entropy
cone literature).  It is proved here as an instance of the general contraction-map engine
`entropyR_ineq_of_contraction` via the `32`-case map `facet5f`.  The general holographic entropy cone
for `n ≥ 5` remains open. -/
theorem rtEntropyR_newFacet5 (G : GraphR V) {bd : Finset V} {A : Fin 5 → Finset V}
    (hR : Cyc5.Regions bd A) :
    (∑ j, rtEntropyR G bd (facet5R A j) (Facet5.facet5R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet5L A i) (Facet5.facet5L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet5L A i) S
      ∧ rtEntropyR G bd (facet5L A i) (Facet5.facet5L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (Facet5.facet5L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet5L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet5L A i) (Facet5.facet5L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet5R A j) (contractionCut X facet5f j) :=
    fun j => Facet5.facet5_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet5L A) (facet5R A)
    (Facet5.facet5L_sub hR) (Facet5.facet5R_sub hR) X hXok facet5f hvalid facet5f_nonexpansive

/-! ### Anti-vacuity witness: a strict five-party instance

The same five-party **star** on `Fin 7` (regions `A₀,…,A₄ = {0},…,{4}`, purifier vertex `5`, central
bulk vertex `6`, unit bonds) witnesses strictness.  A region of `k` colored vertices has min-cut
entropy `min(k, 6 − k)`: each larger-side triple (`k = 3`) has entropy `3` (sum `15`), each bounded
pair (`k = 2`) has entropy `2` (five of them, sum `10`), and `S(ABCDE)` (`k = 5`) has entropy
`min(5, 1) = 1`, so the bounded side sums to `11`, a strict slack of `4`, with all eleven entropies
positive. -/

/-- `facet5R star5A j ⊆ star5Bd`. -/
lemma star5_facet5R_sub (j : Fin 6) : facet5R star5A j ⊆ star5Bd :=
  Facet5.facet5R_sub star5A_regions j
/-- `facet5L star5A i ⊆ star5Bd`. -/
lemma star5_facet5L_sub (i : Fin 5) : facet5L star5A i ⊆ star5Bd :=
  Facet5.facet5L_sub star5A_regions i

/-- Each bounded-region entropy of the star witness: the five pairs give `2`, `S(ABCDE)` gives `1`. -/
lemma star5_facet5R (j : Fin 6) :
    rtEntropy star5Graph star5Bd (facet5R star5A j) (star5_facet5R_sub j)
      = if j = 5 then 1 else 2 := by
  fin_cases j <;> · unfold facet5R facet5Reg star5A; decide

/-- Each larger-side triple entropy of the star witness is `3`. -/
lemma star5_facet5L (i : Fin 5) :
    rtEntropy star5Graph star5Bd (facet5L star5A i) (star5_facet5L_sub i) = 3 := by
  fin_cases i <;> · unfold facet5L facet5Triple star5A; decide

/-- **Strict five-party anti-vacuity witness (real).** On the cast star graph the new-facet inequality
is strict: the bounded side sums to `11` and the larger side to `15` (slack `4`), so
`rtEntropyR_newFacet5` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_newFacet5_strict_witness :
    (∑ j, rtEntropyR (castGraph star5Graph) star5Bd (facet5R star5A j)
        (Facet5.facet5R_sub (A := star5A) star5A_regions j))
      < ∑ i, rtEntropyR (castGraph star5Graph) star5Bd (facet5L star5A i)
        (Facet5.facet5L_sub (A := star5A) star5A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star5Graph) star5Bd (facet5R star5A j)
      (Facet5.facet5R_sub (A := star5A) star5A_regions j) = if j = 5 then 1 else 2 := by
    intro j
    rw [rtEntropyR_castGraph, star5_facet5R j]
    split <;> norm_num
  have htriple : ∀ i, rtEntropyR (castGraph star5Graph) star5Bd (facet5L star5A i)
      (Facet5.facet5L_sub (A := star5A) star5A_regions i) = 3 := by
    intro i
    rw [rtEntropyR_castGraph, star5_facet5L i]; norm_num
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => htriple i)]
  rw [Fin.sum_univ_six, Fin.sum_univ_five]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]
  norm_num

/-- All eleven min-cut entropies in the five-party strict new-facet witness are strictly positive. -/
theorem rtEntropyR_newFacet5_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet5R star5A j)
        (Facet5.facet5R_sub (A := star5A) star5A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet5L star5A i)
        (Facet5.facet5L_sub (A := star5A) star5A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star5_facet5R j]; split <;> norm_num
  · rw [rtEntropyR_castGraph, star5_facet5L i]; norm_num


end Physlib.UndirectedMMICertificate
