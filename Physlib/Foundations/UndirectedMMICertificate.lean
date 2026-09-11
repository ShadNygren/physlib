/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib
public import Physlib.Foundations.Facet6Map
public import Physlib.Foundations.Facet6Base
public import Physlib.Foundations.Facet6Lip0
public import Physlib.Foundations.Facet6Lip1
public import Physlib.Foundations.Facet6Lip2
public import Physlib.Foundations.Facet6Lip3
public import Physlib.Foundations.Facet6Lip4
public import Physlib.Foundations.Facet6Lip5
public import Physlib.Foundations.Facet6Lip6
public import Physlib.Foundations.Facet6Lip7
public import Physlib.Foundations.Facet6Lip8
public import Physlib.Foundations.Facet6Lip9
public import Physlib.Foundations.FacetN61411Lip
public import Physlib.Foundations.FacetN612982Lip
public import Physlib.Foundations.FacetN67451Lip
public import Physlib.Foundations.FacetN61234Lip0
public import Physlib.Foundations.FacetN61234Lip1
public import Physlib.Foundations.FacetN61234Lip2
public import Physlib.Foundations.FacetN61234Lip3
public import Physlib.Foundations.FacetN61234Lip4
public import Physlib.Foundations.FacetN61234Lip5
public import Physlib.Foundations.FacetN61234Lip6
public import Physlib.Foundations.FacetN61234Lip7
public import Physlib.Foundations.FacetN61234Lip8
public import Physlib.Foundations.FacetN61234Lip9
public import Physlib.Foundations.FacetN61234Lip10
public import Physlib.Foundations.FacetN614Lip0
public import Physlib.Foundations.FacetN614Lip1
public import Physlib.Foundations.FacetN614Lip2
public import Physlib.Foundations.FacetN614Lip3
public import Physlib.Foundations.FacetN614Lip4
public import Physlib.Foundations.FacetN614Lip5
public import Physlib.Foundations.FacetN614Lip6
public import Physlib.Foundations.FacetN614Lip7
public import Physlib.Foundations.FacetN614Lip8
public import Physlib.Foundations.FacetN614Lip9
public import Physlib.Foundations.FacetN614Lip10
public import Physlib.Foundations.FacetN614Lip11

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

/-- **The engine (Hamming-nonexpansiveness).** For any two vertex membership patterns
`(uX,uY,uZ)`, `(vX,vY,vZ)`, the recombination atoms `{A',B',C',U'}` separate the two vertices at
most as often as `{X,Y,Z}` do.  A `64`-case boolean fact. -/
theorem edge_atoms_nonexpansive :
    ∀ uX uY uZ vX vY vZ : Bool,
      bdiff (aA uX uY uZ) (aA vX vY vZ) + bdiff (aB uX uY uZ) (aB vX vY vZ)
        + bdiff (aC uX uY uZ) (aC vX vY vZ) + bdiff (aU uX uY uZ) (aU vX vY vZ)
      ≤ bdiff uX vX + bdiff uY vY + bdiff uZ vZ := by
  decide

/-! ## Edge-nonexpansiveness implies global nonexpansiveness

A boolean map on the hypercube that changes its output by at most one Hamming unit whenever a
single input coordinate is flipped is Hamming-nonexpansive on *every* pair of inputs.  This is a
path-metric argument: any two inputs are joined by a path of single-coordinate flips of length equal
to their Hamming distance, and nonexpansiveness accumulates along the path by the triangle
inequality.  The reduction is quantitatively useful: it discharges the global `2ᵐ × 2ᵐ` pair
obligation from just the `m · 2ᵐ` single-flip edge cases. -/

/-- Triangle inequality for the boolean Hamming indicator `bdiff`. -/
theorem bdiff_triangle (a b c : Bool) : bdiff a c ≤ bdiff a b + bdiff b c := by
  unfold bdiff; revert a b c; decide

@[simp] theorem bdiff_self (a : Bool) : bdiff a a = 0 := by
  unfold bdiff; simp

/-- Summed triangle inequality: the Hamming distance between two boolean vectors is bounded by the
distances through any intermediate vector. -/
theorem hdist_triangle {ι : Type*} [Fintype ι] (A B C : ι → Bool) :
    (∑ j, bdiff (A j) (C j)) ≤ (∑ j, bdiff (A j) (B j)) + (∑ j, bdiff (B j) (C j)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => bdiff_triangle (A j) (B j) (C j))

/-- The Hamming distance between two patterns is zero iff they coincide. -/
theorem sum_bdiff_eq_zero_iff {m : ℕ} (p q : Fin m → Bool) :
    (∑ i, bdiff (p i) (q i)) = 0 ↔ p = q := by
  constructor
  · intro h
    funext i
    have hi : bdiff (p i) (q i) = 0 := by
      by_contra hne
      have : 0 < ∑ i, bdiff (p i) (q i) :=
        Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i, Finset.mem_univ i, Nat.pos_of_ne_zero hne⟩
      omega
    unfold bdiff at hi
    by_contra hpq
    simp [hpq] at hi
  · intro h; subst h; simp

/-- Overwriting coordinate `i` of `p` with `q i` (where they differ) decrements the Hamming distance
to `q` by exactly one. -/
theorem sum_bdiff_update {m : ℕ} (p q : Fin m → Bool) (i : Fin m) (hi : p i ≠ q i) :
    (∑ x, bdiff (Function.update p i (q i) x) (q x)) + 1 = ∑ x, bdiff (p x) (q x) := by
  have hsplit : ∀ (f : Fin m → ℕ), ∑ x, f x = f i + ∑ x ∈ Finset.univ.erase i, f x := by
    intro f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]; ring
  rw [hsplit (fun x => bdiff (Function.update p i (q i) x) (q x)),
      hsplit (fun x => bdiff (p x) (q x))]
  simp only [Function.update_self]
  rw [bdiff_self]
  have herase : ∑ x ∈ Finset.univ.erase i, bdiff (Function.update p i (q i) x) (q x)
      = ∑ x ∈ Finset.univ.erase i, bdiff (p x) (q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [herase]
  have hbi : bdiff (p i) (q i) = 1 := by unfold bdiff; simp [hi]
  rw [hbi]; ring

/-- **Edge-nonexpansiveness implies global nonexpansiveness.** If a boolean map `f` is
Hamming-nonexpansive across every hypercube edge — flipping any single input coordinate changes the
output by at most one Hamming unit — then `f` is Hamming-nonexpansive on every pair of inputs.

The proof is strong induction on the input Hamming distance `n`.  At `n = 0` the inputs coincide.
Otherwise pick a differing coordinate `i`, overwrite it in `p` to match `q` (obtaining `p'` at
distance `n - 1`, handled by the induction hypothesis), and note the single flip `p → p'` costs at
most one output unit by hypothesis; the triangle inequality chains the two bounds. -/
theorem nonexpansive_of_singleFlip {m k : ℕ} (f : (Fin m → Bool) → (Fin k → Bool))
    (h : ∀ (p : Fin m → Bool) (i : Fin m),
           (∑ j, bdiff (f p j) (f (Function.update p i (!(p i))) j)) ≤ 1) :
    ∀ (p q : Fin m → Bool),
      (∑ j, bdiff (f p j) (f q j)) ≤ (∑ i, bdiff (p i) (q i)) := by
  suffices H : ∀ (n : ℕ) (p q : Fin m → Bool), (∑ i, bdiff (p i) (q i)) = n →
      (∑ j, bdiff (f p j) (f q j)) ≤ n by
    intro p q; exact H _ p q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q hn
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hpq : p = q := (sum_bdiff_eq_zero_iff p q).1 hn
      subst hpq; simp
    · have hne : (Finset.univ.filter (fun i => p i ≠ q i)).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hall : ∀ i, p i = q i := by
          intro i
          by_contra hne
          have hmem : i ∈ Finset.univ.filter (fun i => p i ≠ q i) := by simp [hne]
          rw [hempty] at hmem; simp at hmem
        have : p = q := funext hall
        subst this; simp at hn; omega
      obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter] at hi
      have hpqi : p i ≠ q i := hi.2
      set p' := Function.update p i (q i) with hp'
      have hdec : (∑ x, bdiff (p' x) (q x)) + 1 = ∑ x, bdiff (p x) (q x) :=
        sum_bdiff_update p q i hpqi
      have hn' : (∑ x, bdiff (p' x) (q x)) = n - 1 := by omega
      have hflip : q i = !(p i) := by cases hpi : p i <;> cases hqi : q i <;> simp_all
      have hupdate : p' = Function.update p i (!(p i)) := by rw [hp', hflip]
      have hih : (∑ j, bdiff (f p' j) (f q j)) ≤ n - 1 := ih (n - 1) (by omega) p' q hn'
      have hedge : (∑ j, bdiff (f p j) (f p' j)) ≤ 1 := by rw [hupdate]; exact h p i
      calc (∑ j, bdiff (f p j) (f q j))
          ≤ (∑ j, bdiff (f p j) (f p' j)) + (∑ j, bdiff (f p' j) (f q j)) :=
            hdist_triangle (f p) (f p') (f q)
        _ ≤ 1 + (n - 1) := Nat.add_le_add hedge hih
        _ = n := by omega

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

/-- **Single-flip (edge) nonexpansiveness of `facet5f`.** Flipping any one of the five input
coordinates changes the six-bit output by at most one Hamming unit — the `5 · 2⁵ = 160` edge cases,
checked by `decide`. -/
theorem facet5f_singleFlip :
    ∀ (p : Fin 5 → Bool) (i : Fin 5),
      (∑ j, bdiff (facet5f p j) (facet5f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide

/-- **Global nonexpansiveness of `facet5f`, re-derived from the single-flip reduction.** Identical in
statement to `facet5f_nonexpansive`, but obtained from `nonexpansive_of_singleFlip` by discharging
only the `160` single-flip edge cases (via `facet5f_singleFlip`) rather than the `1024` input pairs.
This validates the edge-to-global reduction inside the kernel. -/
theorem facet5f_nonexpansive_via_singleFlip (p q : Fin 5 → Bool) :
    (∑ j, bdiff (facet5f p j) (facet5f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet5f facet5f_singleFlip p q

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


/-! ### A second genuinely-new five-party holographic entropy cone facet

As a further instance of the general contraction-map engine (`entropyR_ineq_of_contraction`), we
certify a second five-party holographic entropy inequality that is a **genuine facet** of the
five-party holographic entropy cone — that is, it is **not** implied by subadditivity, strong
subadditivity and monogamy of mutual information (the `SA + SSA + MMI` cone).  With five elementary
boundary regions `A₀,…,A₄` (colors `A,B,C,D,E`, plus a purifier = the rest of the boundary) the
inequality is

  `S(AD) + S(BC) + S(ABE) + S(ACE) + S(ADE) + S(BDE) + S(CDE)`
    `≥ S(A) + S(B) + S(C) + S(D) + S(AE) + S(DE) + S(BCE) + S(ABDE) + S(ACDE)`,

with the seven larger-side regions `AD, BC, ABE, ACE, ADE, BDE, CDE` and the nine bounded-side regions
`A, B, C, D, AE, DE, BCE, ABDE, ACDE`.  Being outside the `SA + SSA + MMI` cone, it is a new facet of
the five-party holographic entropy cone (source: the five-party holographic entropy cone literature);
its validity for the undirected min-cut model is established here by exhibiting an explicit contraction
map, not by cone membership.

The `128`-entry boolean contraction map below recombines the seven larger-side cut membership bits
(one per larger-side region) into the nine bounded-region membership bits; boundary validity of the
recombined cuts is a finite check on the membership patterns that boundary vertices can carry (the
five elementary colors plus the purifier).  The general holographic entropy cone for `n ≥ 5` remains
open. -/

/-- The seven larger-side regions of colors, as index sets in `Fin 5`:
`{0,3}, {1,2}, {0,1,4}, {0,2,4}, {0,3,4}, {1,3,4}, {2,3,4}`. -/
def facet8Sev : Fin 7 → Finset (Fin 5) :=
  ![{0, 3}, {1, 2}, {0, 1, 4}, {0, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}]

/-- The nine bounded-side regions of colors, as index sets in `Fin 5`:
`{0}, {1}, {2}, {3}, {0,4}, {3,4}, {1,2,4}, {0,1,3,4}, {0,2,3,4}`. -/
def facet8Reg : Fin 9 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {0, 4}, {3, 4}, {1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}]

variable {A : Fin 5 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th larger set. -/
def facet8L (A : Fin 5 → Finset V) (i : Fin 7) : Finset V := (facet8Sev i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th region set. -/
def facet8R (A : Fin 5 → Finset V) (j : Fin 9) : Finset V := (facet8Reg j).biUnion A

/-- The `128`-entry boolean contraction map recombining the seven larger-side cut membership bits into
the nine bounded-region membership bits.  Input bit `i` = "the vertex's color lies in the `i`-th
larger-side region"; output bit `j` = "its color lies in the `j`-th bounded region".  Defined by an
explicit match on the seven input bits so that `decide` evaluates it. -/
def facet8f (p : Fin 7 → Bool) : Fin 9 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6 with
  | false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false]
  | false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, true, true, true, false, false => ![false, false, false, false, true, false, false, true, true]
  | false, false, true, true, true, false, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, true, true, true, true, false => ![false, false, false, false, true, false, true, true, true]
  | false, false, true, true, true, true, true => ![false, false, false, false, true, true, true, true, true]
  | false, true, false, false, false, false, false => ![false, false, false, false, false, false, true, false, false]
  | false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, false, true]
  | false, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | false, true, false, true, false, false, true => ![false, false, true, false, false, false, true, false, true]
  | false, true, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, true, true => ![false, false, true, false, false, false, true, true, true]
  | false, true, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, true => ![false, false, true, false, false, false, true, true, true]
  | false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false => ![false, true, false, false, false, false, true, true, false]
  | false, true, true, false, false, true, true => ![false, false, false, false, false, false, true, true, false]
  | false, true, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, true => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, true => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, true, true, false, true => ![false, false, true, false, true, false, true, true, true]
  | false, true, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, true, false, true => ![false, false, false, true, false, false, false, true, true]
  | true, false, false, false, true, true, false => ![false, false, false, true, false, false, false, true, true]
  | true, false, false, false, true, true, true => ![false, false, false, true, false, true, false, true, true]
  | true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, false, false => ![false, false, false, false, true, false, false, true, true]
  | true, false, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, true, false, false, false, false => ![true, false, false, false, false, false, false, true, false]
  | true, false, true, false, false, false, true => ![true, false, false, false, false, false, false, true, true]
  | true, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | true, false, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, false, false => ![true, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true]
  | true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, true, false, true, true => ![false, false, false, false, true, false, false, true, true]
  | true, false, true, true, true, false, false => ![true, false, false, false, true, false, false, true, true]
  | true, false, true, true, true, false, true => ![false, false, false, false, true, false, false, true, true]
  | true, false, true, true, true, true, false => ![false, false, false, false, true, false, false, true, true]
  | true, false, true, true, true, true, true => ![false, false, false, false, true, true, false, true, true]
  | true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false]
  | true, true, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | true, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | true, true, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, true, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, true, false, true, false, false, true => ![false, false, true, false, false, false, false, false, true]
  | true, true, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, true, true => ![false, false, true, false, false, false, false, true, true]
  | true, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, true, false, true => ![false, false, true, false, false, false, false, true, true]
  | true, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | true, true, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, false, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | true, true, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, false, true, false, true => ![false, false, true, false, false, false, false, true, true]
  | true, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, true, false, false, true => ![false, false, true, false, false, false, false, true, true]
  | true, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, true, true, false, false => ![false, false, false, false, true, false, false, true, true]
  | true, true, true, true, true, false, true => ![false, false, true, false, true, false, false, true, true]
  | true, true, true, true, true, true, false => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, true, true, true, true => ![false, false, false, false, true, false, false, true, true]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Contraction (Hamming-nonexpansiveness) of `facet8f`.** For any two seven-bit input patterns, the
nine output bits separate them at most as often as the seven input bits.  A finite `16384`-pair fact,
checked by the kernel evaluator (`decide +kernel`, with the recursion depth and heartbeat budget
raised to accommodate the seven-bit case tree). -/
lemma facet8f_nonexpansive (p q : Fin 7 → Bool) :
    (∑ j, bdiff (facet8f p j) (facet8f q j)) ≤ ∑ i, bdiff (p i) (q i) := by
  have key : ∀ p q : Fin 7 → Bool,
      (∑ j, bdiff (facet8f p j) (facet8f q j)) ≤ ∑ i, bdiff (p i) (q i) := by decide +kernel
  exact key p q

/-- The six input patterns carried by boundary vertices — one per elementary color and the all-`false`
purifier pattern — map through `facet8f` exactly to the corresponding bounded-region membership
pattern.  `facet8f (fun i => color ∈ region i) j = (color ∈ region j)`, and the purifier maps
`false ↦ false`.  A finite `decide` over the five colors. -/
lemma facet8f_boundary (c : Fin 5) :
    facet8f (fun i => decide (c ∈ facet8Sev i)) = fun j => decide (c ∈ facet8Reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet8f`. -/
lemma facet8f_zero : facet8f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

namespace Facet8

variable {bd : Finset V}

/-- Membership of `v ∈ A c` in a larger-side region: `v ∈ facet8L A i ↔ c ∈ facet8Sev i`. -/
lemma mem_facet8L_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (i : Fin 7) :
    v ∈ facet8L A i ↔ c ∈ facet8Sev i := by
  unfold facet8L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet8R A j ⊆ bd`. -/
lemma facet8R_sub (hR : Cyc5.Regions bd A) (j : Fin 9) : facet8R A j ⊆ bd := by
  unfold facet8R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet8L A i ⊆ bd`. -/
lemma facet8L_sub (hR : Cyc5.Regions bd A) (i : Fin 7) : facet8L A i ⊆ bd := by
  unfold facet8L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region: `v ∈ facet8R A j ↔ c ∈ facet8Reg j`. -/
lemma mem_facet8R_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (j : Fin 9) :
    v ∈ facet8R A j ↔ c ∈ facet8Reg j := by
  unfold facet8R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern:
`contractionPattern X v = fun i => decide (c ∈ facet8Sev i)`. -/
lemma contractionPattern_of_color (hR : Cyc5.Regions bd A)
    (X : Fin 7 → Finset V) (hX : ∀ i, IsRTCut bd (facet8L A i) (X i))
    {v : V} {c : Fin 5} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet8Sev i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet8Sev i
  · have : v ∈ X i := (hX i).1 ((mem_facet8L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet8L A i := fun h => hc ((mem_facet8L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex (in `bd`, outside every elementary region), the achieving cuts realize the
all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 7 → Finset V) (hX : ∀ i, IsRTCut bd (facet8L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet8L A i := by
    unfold facet8L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X facet8f j` is an admissible
RT cut for the bounded region `facet8R A j`.  For every boundary vertex, its `facet8f`-image
membership matches its bounded-region membership: colors via `facet8f_boundary`, the purifier via
`facet8f_zero`; bulk vertices are free. -/
lemma facet8_hvalid (hR : Cyc5.Regions bd A)
    (X : Fin 7 → Finset V) (hX : ∀ i, IsRTCut bd (facet8L A i) (X i)) (j : Fin 9) :
    IsRTCut bd (facet8R A j) (contractionCut X facet8f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet8f j) v = mem (facet8R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, facet8f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet8R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, facet8f_zero]
      have : v ∉ facet8R A j := by
        unfold facet8R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet8R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

end Facet8

open Facet8

/-- **A second genuinely new five-party holographic entropy cone facet.**
For five pairwise-disjoint boundary regions `A₀,…,A₄` (with the rest of `bd` a purifier) in any finite
undirected nonnegative-real-weighted graph, the seven larger-side regions dominate the nine
bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(largerᵢ)`,

i.e.

  `S(A) + S(B) + S(C) + S(D) + S(AE) + S(DE) + S(BCE) + S(ABDE) + S(ACDE)`
    `≤ S(AD) + S(BC) + S(ABE) + S(ACE) + S(ADE) + S(BDE) + S(CDE)`.

Like `rtEntropyR_newFacet5` (and unlike `rtEntropyR_cyclic5`), this inequality is **not implied by the
`SA + SSA + MMI` cone**: it is a second genuine facet of the five-party holographic entropy cone
(source: the five-party holographic entropy cone literature).  It is proved here as an instance of the
general contraction-map engine `entropyR_ineq_of_contraction` via the `128`-case map `facet8f`.  The
general holographic entropy cone for `n ≥ 5` remains open. -/
theorem rtEntropyR_newFacet8 (G : GraphR V) {bd : Finset V} {A : Fin 5 → Finset V}
    (hR : Cyc5.Regions bd A) :
    (∑ j, rtEntropyR G bd (facet8R A j) (Facet8.facet8R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet8L A i) (Facet8.facet8L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet8L A i) S
      ∧ rtEntropyR G bd (facet8L A i) (Facet8.facet8L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (Facet8.facet8L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet8L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet8L A i) (Facet8.facet8L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet8R A j) (contractionCut X facet8f j) :=
    fun j => Facet8.facet8_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet8L A) (facet8R A)
    (Facet8.facet8L_sub hR) (Facet8.facet8R_sub hR) X hXok facet8f hvalid facet8f_nonexpansive

/-! ### Anti-vacuity witness: a strict five-party instance

The same five-party **star** on `Fin 7` (regions `A₀,…,A₄ = {0},…,{4}`, purifier vertex `5`, central
bulk vertex `6`, unit bonds) witnesses strictness.  A region of `k` colored vertices has min-cut
entropy `min(k, 6 − k)`: the larger-side regions have cardinalities `[2,2,3,3,3,3,3]` (entropies
`[2,2,3,3,3,3,3]`, sum `19`); the bounded-side regions have cardinalities `[1,1,1,1,2,2,3,4,4]`
(entropies `[1,1,1,1,2,2,3,2,2]`, sum `15`), a strict slack of `4`, with all sixteen entropies
positive. -/

/-- `facet8R star5A j ⊆ star5Bd`. -/
lemma star5_facet8R_sub (j : Fin 9) : facet8R star5A j ⊆ star5Bd :=
  Facet8.facet8R_sub star5A_regions j
/-- `facet8L star5A i ⊆ star5Bd`. -/
lemma star5_facet8L_sub (i : Fin 7) : facet8L star5A i ⊆ star5Bd :=
  Facet8.facet8L_sub star5A_regions i

/-- Each bounded-region entropy of the star witness, as the vector `![1,1,1,1,2,2,3,2,2]`. -/
lemma star5_facet8R (j : Fin 9) :
    rtEntropy star5Graph star5Bd (facet8R star5A j) (star5_facet8R_sub j)
      = ![1, 1, 1, 1, 2, 2, 3, 2, 2] j := by
  fin_cases j <;> · unfold facet8R facet8Reg star5A; decide

/-- Each larger-side entropy of the star witness, as the vector `![2,2,3,3,3,3,3]`. -/
lemma star5_facet8L (i : Fin 7) :
    rtEntropy star5Graph star5Bd (facet8L star5A i) (star5_facet8L_sub i)
      = ![2, 2, 3, 3, 3, 3, 3] i := by
  fin_cases i <;> · unfold facet8L facet8Sev star5A; decide

/-- **Strict five-party anti-vacuity witness (real).** On the cast star graph the second new-facet
inequality is strict: the bounded side sums to `15` and the larger side to `19` (slack `4`), so
`rtEntropyR_newFacet8` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_newFacet8_strict_witness :
    (∑ j, rtEntropyR (castGraph star5Graph) star5Bd (facet8R star5A j)
        (Facet8.facet8R_sub (A := star5A) star5A_regions j))
      < ∑ i, rtEntropyR (castGraph star5Graph) star5Bd (facet8L star5A i)
        (Facet8.facet8L_sub (A := star5A) star5A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star5Graph) star5Bd (facet8R star5A j)
      (Facet8.facet8R_sub (A := star5A) star5A_regions j)
        = ((![1, 1, 1, 1, 2, 2, 3, 2, 2] : Fin 9 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star5_facet8R j]
  have hlar : ∀ i, rtEntropyR (castGraph star5Graph) star5Bd (facet8L star5A i)
      (Facet8.facet8L_sub (A := star5A) star5A_regions i)
        = ((![2, 2, 3, 3, 3, 3, 3] : Fin 7 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star5_facet8L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All sixteen min-cut entropies in the second five-party strict new-facet witness are strictly
positive. -/
theorem rtEntropyR_newFacet8_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet8R star5A j)
        (Facet8.facet8R_sub (A := star5A) star5A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet8L star5A i)
        (Facet8.facet8L_sub (A := star5A) star5A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star5_facet8R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star5_facet8L i]; fin_cases i <;> norm_num



/-! ### A genuinely-new five-party holographic entropy cone facet (bounded side 9 terms)

A further instance of the general contraction-map engine (`entropyR_ineq_of_contraction`): a
five-party holographic entropy inequality that is a **genuine facet** of the five-party holographic
entropy cone — **not** implied by subadditivity, strong subadditivity and monogamy of mutual
information (the `SA + SSA + MMI` cone).  With five elementary boundary regions `A₀,…,A₄` (colors
`A,B,C,D,E`, plus a purifier = the rest of the boundary), the 8 larger-side regions dominate the
9 bounded-side regions.  Being outside the `SA + SSA + MMI` cone it is a new facet of the
five-party holographic entropy cone (source: the five-region holographic entropy cone literature);
its validity for the undirected min-cut model is established here by exhibiting an explicit
contraction map, not by cone membership.

The `256`-entry boolean contraction map below recombines the 8 larger-side cut membership bits
into the 9 bounded-region membership bits.  Its Hamming-nonexpansiveness is discharged through the
single-flip edge-case reduction (`nonexpansive_of_singleFlip`): only the `2048` hypercube-edge
checks are evaluated, rather than the `256²` input pairs.  Boundary validity of the recombined
cuts is a finite check on the membership patterns that boundary vertices can carry (the five
elementary colors plus the purifier).  The general holographic entropy cone for `n ≥ 5` remains
open. -/

/-- The 8 larger-side regions of colors, as index sets in `Fin 5`. -/
def facet7L_reg : Fin 8 → Finset (Fin 5) :=
  ![{0, 1, 2}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 3, 4}, {1, 2, 4}, {1, 3, 4}]

/-- The 9 bounded-side regions of colors, as index sets in `Fin 5`. -/
def facet7R_reg : Fin 9 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 4}, {3, 4}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}]

variable {A : Fin 5 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th larger set. -/
def facet7L (A : Fin 5 → Finset V) (i : Fin 8) : Finset V := (facet7L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th region set. -/
def facet7R (A : Fin 5 → Finset V) (j : Fin 9) : Finset V := (facet7R_reg j).biUnion A

/-- The `256`-entry boolean contraction map recombining the 8 larger-side cut membership bits
into the 9 bounded-region membership bits.  Input bit `i` = "the vertex's color lies in the `i`-th
larger-side region"; output bit `j` = "its color lies in the `j`-th bounded region".  Defined by an
explicit match on the 8 input bits so that `decide` evaluates it. -/
def facet7f (p : Fin 8 → Bool) : Fin 9 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7 with
  | false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false]
  | true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, false, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, false, false => ![true, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, true, false, false]
  | true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | true, true, false, false, true, false, false, false => ![false, true, false, false, false, false, true, true, false]
  | false, false, true, false, true, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, false, false => ![false, true, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | true, false, false, true, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, false, false => ![false, true, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, false => ![true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, false => ![true, true, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, false, false => ![false, false, true, false, false, false, false, true, true]
  | false, true, false, true, false, true, false, false => ![false, false, true, false, false, false, false, true, true]
  | true, true, false, true, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, false => ![true, false, true, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, false, false => ![false, true, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, false => ![false, false, true, false, false, false, true, false, true]
  | true, false, true, false, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, false => ![true, false, true, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, false => ![true, true, true, false, false, false, true, true, true]
  | false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | true, true, false, false, false, false, true, false => ![false, false, false, true, false, false, true, true, false]
  | false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, true, false => ![false, false, false, true, false, false, true, true, true]
  | false, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, true, false => ![false, false, false, true, false, false, true, true, true]
  | false, false, true, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, false => ![true, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, true, false => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, true, false => ![true, false, false, true, false, false, true, true, true]
  | false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | true, false, false, false, true, false, true, false => ![false, true, false, false, false, false, true, true, false]
  | false, true, false, false, true, false, true, false => ![false, true, false, false, false, false, true, true, false]
  | true, true, false, false, true, false, true, false => ![false, true, false, true, false, false, true, true, false]
  | false, false, true, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, false => ![false, true, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, true, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, false => ![false, true, false, true, false, false, true, true, true]
  | false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, true, false => ![false, true, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, true, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, false => ![false, true, false, true, false, false, true, true, true]
  | false, false, true, true, true, false, true, false => ![true, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, false => ![true, true, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, false => ![true, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, false => ![true, true, false, true, false, false, true, true, true]
  | false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, true, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, false]
  | true, true, false, false, false, true, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, true, false => ![false, false, false, false, false, true, false, true, true]
  | true, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, true, false => ![false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, false => ![true, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, true, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, false]
  | true, true, false, false, true, true, true, false => ![false, true, false, false, false, false, true, true, false]
  | false, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, false => ![true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, false => ![true, true, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, false, false, true => ![false, false, false, false, true, false, false, true, true]
  | false, true, false, true, false, false, false, true => ![false, false, false, false, true, false, false, true, true]
  | true, true, false, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, true, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, true, false, false, false, true => ![true, false, false, false, true, false, true, true, true]
  | false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, false, true => ![false, true, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, false, true => ![false, false, false, false, false, true, true, false, true]
  | true, false, true, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, true, true, false, true, false, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, true => ![true, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, false, true => ![false, false, false, false, false, true, false, false, true]
  | true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, true, false, false, false, true, false, true => ![false, false, false, false, false, true, false, true, true]
  | true, true, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, true, false, true => ![false, false, false, false, false, true, true, false, true]
  | true, false, true, false, false, true, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, true, true, false, false, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, true => ![true, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, true => ![false, false, false, false, false, true, true, false, true]
  | true, false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, true, false, false, true, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, true => ![false, false, true, false, false, true, true, false, true]
  | true, false, true, false, true, true, false, true => ![false, false, true, false, false, false, true, false, true]
  | false, true, true, false, true, true, false, true => ![false, false, true, false, false, true, true, true, true]
  | true, true, true, false, true, true, false, true => ![false, false, true, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, true => ![false, false, true, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, true => ![false, false, true, false, false, true, true, true, true]
  | true, false, true, true, true, true, false, true => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, true => ![false, false, true, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, true => ![true, false, true, false, false, false, true, true, true]
  | false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, false, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, false, false, false, true, true => ![false, false, false, true, true, false, true, true, true]
  | false, false, false, true, false, false, true, true => ![false, false, false, false, true, false, false, true, true]
  | true, false, false, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, false, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, false, true, false, false, true, true => ![false, false, false, true, true, false, true, true, true]
  | false, false, true, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, false, true, true, false, false, true, true => ![true, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, false, true, true => ![true, false, false, false, true, false, true, true, true]
  | true, true, true, true, false, false, true, true => ![true, false, false, true, true, false, true, true, true]
  | false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true => ![false, true, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, true, true => ![false, true, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, true, true => ![false, true, false, true, false, false, true, true, true]
  | false, false, true, false, true, false, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, true, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true => ![true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, true => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, true => ![true, false, false, true, false, false, true, true, true]
  | false, false, false, false, false, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, false, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, false, true, false, true, true, true => ![false, false, false, false, true, true, false, true, true]
  | true, false, false, true, false, true, true, true => ![false, false, false, false, true, false, false, true, true]
  | false, true, false, true, false, true, true, true => ![false, false, false, false, true, false, false, true, true]
  | true, true, false, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, true, true, false, true, true, true => ![false, false, false, false, true, true, true, true, true]
  | true, false, true, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, true, false, true, true, true => ![true, false, false, false, true, false, true, true, true]
  | false, false, false, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, true => ![false, true, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, true => ![false, false, false, false, false, true, true, false, true]
  | true, false, true, false, true, true, true, true => ![false, false, false, false, false, false, true, false, true]
  | false, true, true, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, true => ![true, false, false, false, false, false, true, true, true]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Single-flip (edge) nonexpansiveness of `facet7f`.** Flipping any one of the 8 input
coordinates changes the 9-bit output by at most one Hamming unit — the `2048` edge cases,
checked by the kernel evaluator (`decide +kernel`, with recursion depth and heartbeat budget raised
to accommodate the case tree). -/
theorem facet7f_singleFlip :
    ∀ (p : Fin 8 → Bool) (i : Fin 8),
      (∑ j, bdiff (facet7f p j) (facet7f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide +kernel

/-- **Global nonexpansiveness of `facet7f`, derived from the single-flip reduction.** Obtained from
`nonexpansive_of_singleFlip` by discharging only the `2048` single-flip edge cases (via
`facet7f_singleFlip`) rather than the `256²` input pairs. -/
theorem facet7f_nonexpansive (p q : Fin 8 → Bool) :
    (∑ j, bdiff (facet7f p j) (facet7f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet7f facet7f_singleFlip p q

/-- The five color input patterns map through the contraction to the corresponding bounded-region
membership pattern.  A finite `decide` over the five colors. -/
lemma facet7f_boundary (c : Fin 5) :
    facet7f (fun i => decide (c ∈ facet7L_reg i)) = fun j => decide (c ∈ facet7R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet7f`. -/
lemma facet7f_zero : facet7f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

namespace Facet7

variable {bd : Finset V}

/-- Membership of `v ∈ A c` in a larger-side region: `v ∈ facet7L A i ↔ c ∈ facet7L_reg i`. -/
lemma mem_facet7L_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (i : Fin 8) :
    v ∈ facet7L A i ↔ c ∈ facet7L_reg i := by
  unfold facet7L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet7R A j ⊆ bd`. -/
lemma facet7R_sub (hR : Cyc5.Regions bd A) (j : Fin 9) : facet7R A j ⊆ bd := by
  unfold facet7R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet7L A i ⊆ bd`. -/
lemma facet7L_sub (hR : Cyc5.Regions bd A) (i : Fin 8) : facet7L A i ⊆ bd := by
  unfold facet7L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region: `v ∈ facet7R A j ↔ c ∈ facet7R_reg j`. -/
lemma mem_facet7R_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (j : Fin 9) :
    v ∈ facet7R A j ↔ c ∈ facet7R_reg j := by
  unfold facet7R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color (hR : Cyc5.Regions bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet7L A i) (X i))
    {v : V} {c : Fin 5} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet7L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet7L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet7L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet7L A i := fun h => hc ((mem_facet7L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet7L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet7L A i := by
    unfold facet7L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X facet7f j` is an admissible
RT cut for the bounded region `facet7R A j`. -/
lemma facet7_hvalid (hR : Cyc5.Regions bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet7L A i) (X i)) (j : Fin 9) :
    IsRTCut bd (facet7R A j) (contractionCut X facet7f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet7f j) v = mem (facet7R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, facet7f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet7R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, facet7f_zero]
      have : v ∉ facet7R A j := by
        unfold facet7R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet7R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

end Facet7

open Facet7

/-- **A genuinely new five-party holographic entropy cone facet (9-term bounded side).**
For five pairwise-disjoint boundary regions `A₀,…,A₄` (with the rest of `bd` a purifier) in any
finite undirected nonnegative-real-weighted graph, the 8 larger-side regions dominate the 9
bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(largerᵢ)`.

This inequality is **not implied by the `SA + SSA + MMI` cone**: it is a genuine facet of the
five-party holographic entropy cone (source: the five-region holographic entropy cone literature).
It is proved as an instance of the general contraction-map engine `entropyR_ineq_of_contraction`
via the `256`-case map `facet7f`, whose nonexpansiveness comes through the single-flip edge-case
reduction.  The general holographic entropy cone for `n ≥ 5` remains open. -/
theorem rtEntropyR_newFacet7 (G : GraphR V) {bd : Finset V} {A : Fin 5 → Finset V}
    (hR : Cyc5.Regions bd A) :
    (∑ j, rtEntropyR G bd (facet7R A j) (Facet7.facet7R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet7L A i) (Facet7.facet7L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet7L A i) S
      ∧ rtEntropyR G bd (facet7L A i) (Facet7.facet7L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (Facet7.facet7L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet7L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet7L A i) (Facet7.facet7L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet7R A j) (contractionCut X facet7f j) :=
    fun j => Facet7.facet7_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet7L A) (facet7R A)
    (Facet7.facet7L_sub hR) (Facet7.facet7R_sub hR) X hXok facet7f hvalid facet7f_nonexpansive

/-! #### Anti-vacuity witness: a strict five-party instance

The five-party **star** on `Fin 7` (regions `A₀,…,A₄ = {0},…,{4}`, purifier vertex `5`, central
bulk vertex `6`, unit bonds) witnesses strictness.  A region of `k` colored vertices has min-cut
entropy `min(k, 6 − k)`: the larger-side regions have entropies `![3, 3, 3, 3, 3, 3, 3, 3]` (sum `24`); the
bounded-side regions have entropies `![2, 2, 2, 2, 2, 2, 2, 2, 2]` (sum `18`), a strict slack of `6`, all
entropies positive. -/

/-- `facet7R star5A j ⊆ star5Bd`. -/
lemma star5_facet7R_sub (j : Fin 9) : facet7R star5A j ⊆ star5Bd :=
  Facet7.facet7R_sub star5A_regions j
/-- `facet7L star5A i ⊆ star5Bd`. -/
lemma star5_facet7L_sub (i : Fin 8) : facet7L star5A i ⊆ star5Bd :=
  Facet7.facet7L_sub star5A_regions i

/-- Each bounded-region entropy of the star witness, as `![2, 2, 2, 2, 2, 2, 2, 2, 2]`. -/
lemma star5_facet7R (j : Fin 9) :
    rtEntropy star5Graph star5Bd (facet7R star5A j) (star5_facet7R_sub j)
      = (![2, 2, 2, 2, 2, 2, 2, 2, 2] : Fin 9 → ℕ) j := by
  fin_cases j <;> · unfold facet7R facet7R_reg star5A; decide

/-- Each larger-side entropy of the star witness, as `![3, 3, 3, 3, 3, 3, 3, 3]`. -/
lemma star5_facet7L (i : Fin 8) :
    rtEntropy star5Graph star5Bd (facet7L star5A i) (star5_facet7L_sub i)
      = (![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i := by
  fin_cases i <;> · unfold facet7L facet7L_reg star5A; decide

/-- **Strict five-party anti-vacuity witness (real).** On the cast star graph this new-facet
inequality is strict: the bounded side sums to `18` and the larger side to `24` (slack
`6`), so `rtEntropyR_newFacet7` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_newFacet7_strict_witness :
    (∑ j, rtEntropyR (castGraph star5Graph) star5Bd (facet7R star5A j)
        (Facet7.facet7R_sub (A := star5A) star5A_regions j))
      < ∑ i, rtEntropyR (castGraph star5Graph) star5Bd (facet7L star5A i)
        (Facet7.facet7L_sub (A := star5A) star5A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star5Graph) star5Bd (facet7R star5A j)
      (Facet7.facet7R_sub (A := star5A) star5A_regions j)
        = ((![2, 2, 2, 2, 2, 2, 2, 2, 2] : Fin 9 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star5_facet7R j]
  have hlar : ∀ i, rtEntropyR (castGraph star5Graph) star5Bd (facet7L star5A i)
      (Facet7.facet7L_sub (A := star5A) star5A_regions i)
        = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star5_facet7L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in this five-party strict new-facet witness are strictly positive. -/
theorem rtEntropyR_newFacet7_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet7R star5A j)
        (Facet7.facet7R_sub (A := star5A) star5A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet7L star5A i)
        (Facet7.facet7L_sub (A := star5A) star5A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star5_facet7R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star5_facet7L i]; fin_cases i <;> norm_num

/-! ### A genuinely-new five-party holographic entropy cone facet (bounded side 10 terms)

A further instance of the general contraction-map engine (`entropyR_ineq_of_contraction`): a
five-party holographic entropy inequality that is a **genuine facet** of the five-party holographic
entropy cone — **not** implied by subadditivity, strong subadditivity and monogamy of mutual
information (the `SA + SSA + MMI` cone).  With five elementary boundary regions `A₀,…,A₄` (colors
`A,B,C,D,E`, plus a purifier = the rest of the boundary), the 9 larger-side regions dominate the
10 bounded-side regions.  Being outside the `SA + SSA + MMI` cone it is a new facet of the
five-party holographic entropy cone (source: the five-region holographic entropy cone literature);
its validity for the undirected min-cut model is established here by exhibiting an explicit
contraction map, not by cone membership.

The `512`-entry boolean contraction map below recombines the 9 larger-side cut membership bits
into the 10 bounded-region membership bits.  Its Hamming-nonexpansiveness is discharged through the
single-flip edge-case reduction (`nonexpansive_of_singleFlip`): only the `4608` hypercube-edge
checks are evaluated, rather than the `512²` input pairs.  Boundary validity of the recombined
cuts is a finite check on the membership patterns that boundary vertices can carry (the five
elementary colors plus the purifier).  The general holographic entropy cone for `n ≥ 5` remains
open. -/

/-- The 9 larger-side regions of colors, as index sets in `Fin 5`. -/
def facet5bL_reg : Fin 9 → Finset (Fin 5) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}]

/-- The 10 bounded-side regions of colors, as index sets in `Fin 5`. -/
def facet5bR_reg : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 4}, {2, 4}, {3, 4}, {1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}]

variable {A : Fin 5 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th larger set. -/
def facet5bL (A : Fin 5 → Finset V) (i : Fin 9) : Finset V := (facet5bL_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th region set. -/
def facet5bR (A : Fin 5 → Finset V) (j : Fin 10) : Finset V := (facet5bR_reg j).biUnion A

/-- The `512`-entry boolean contraction map recombining the 9 larger-side cut membership bits
into the 10 bounded-region membership bits.  Input bit `i` = "the vertex's color lies in the `i`-th
larger-side region"; output bit `j` = "its color lies in the `j`-th bounded region".  Defined by an
explicit match on the 9 input bits so that `decide` evaluates it. -/
def facet5bf (p : Fin 9 → Bool) : Fin 10 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8 with
  | false, false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, false]
  | true, false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | false, true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, false]
  | true, true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | true, false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, true, true, false, false, false, false, false, false => ![true, false, false, false, false, false, false, true, true, false]
  | false, false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | true, false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | true, false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, true, false, false, false, false => ![false, true, false, false, false, false, false, true, false, true]
  | false, true, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, false, false, false => ![false, true, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, false, false => ![false, true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, false, false => ![true, true, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, false]
  | true, false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, true, false, false, false => ![false, false, true, false, false, false, false, false, true, true]
  | true, true, false, true, false, true, false, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, false, false => ![true, false, true, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, false, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, false, false => ![true, false, true, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, false, false, false => ![false, true, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, false, false => ![false, true, true, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, false, false => ![true, true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, false, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, false, false => ![true, true, true, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | true, false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, true, true, false, false]
  | false, true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, false, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, true, false, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, true, true, false, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true, false]
  | true, true, true, false, false, false, true, false, false => ![true, false, false, false, false, false, true, true, true, false]
  | false, false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, true, false, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, true, false, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, true, false, false => ![false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, true, false, true, false, false => ![false, true, false, false, false, false, true, true, false, true]
  | false, true, false, true, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, true, false, false => ![false, true, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, false, true, false, false => ![false, true, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, true, false, false => ![true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, false, false => ![true, true, false, false, false, false, true, true, true, true]
  | false, false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, true, false, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, false, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, true, false, false => ![false, true, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, true, false, false => ![false, true, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, false, false => ![false, true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, false, false => ![true, true, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, false]
  | true, false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, true, false, true, false]
  | true, true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, true, true, false, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | true, true, true, false, false, false, false, true, false => ![true, false, false, false, false, false, true, true, true, false]
  | false, false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, false, true, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | true, true, false, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, false, true, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, true, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, false, true, false => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, false, true, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, true, false, true, false => ![false, false, false, false, false, false, true, false, true, true]
  | true, false, false, true, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, false, true, false => ![false, false, true, false, false, false, true, false, true, true]
  | true, true, false, true, false, true, false, true, false => ![false, false, true, false, false, false, true, true, true, true]
  | false, false, true, true, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, true, false, true, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, false, true, false => ![false, false, true, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, false, true, false => ![true, false, true, false, false, false, true, true, true, true]
  | false, false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, true, false => ![false, false, true, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, true, false => ![true, false, true, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | true, true, false, false, false, false, true, true, false => ![false, false, false, true, false, false, true, true, true, false]
  | false, false, true, false, false, false, true, true, false => ![false, false, false, true, false, false, false, true, true, false]
  | true, false, true, false, false, false, true, true, false => ![false, false, false, true, false, false, true, true, true, false]
  | false, true, true, false, false, false, true, true, false => ![false, false, false, true, false, false, true, true, true, false]
  | true, true, true, false, false, false, true, true, false => ![true, false, false, true, false, false, true, true, true, false]
  | false, false, false, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, false, true, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, true, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | false, true, true, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true, false]
  | true, true, true, true, false, false, true, true, false => ![true, false, false, false, false, false, true, true, true, false]
  | false, false, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, true, false => ![false, false, false, true, false, false, true, true, true, true]
  | false, false, true, false, true, false, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, true, false => ![false, false, false, true, false, false, true, true, true, true]
  | false, true, true, false, true, false, true, true, false => ![false, false, false, true, false, false, true, true, true, true]
  | true, true, true, false, true, false, true, true, false => ![true, false, false, true, false, false, true, true, true, true]
  | false, false, false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, true, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, true, true, true, false => ![false, false, false, true, false, false, true, true, true, true]
  | false, false, true, false, false, true, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, true, false => ![false, false, false, true, false, false, true, true, true, true]
  | false, true, true, false, false, true, true, true, false => ![false, false, false, true, false, false, true, true, true, true]
  | true, true, true, false, false, true, true, true, false => ![true, false, false, true, false, false, true, true, true, true]
  | false, false, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, true, true, false => ![true, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, true, false => ![false, false, false, true, false, true, false, true, true, true]
  | true, false, true, false, true, true, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, true, false => ![true, false, false, true, false, false, false, true, true, true]
  | false, false, false, true, true, true, true, true, false => ![false, false, false, false, false, true, true, true, true, true]
  | true, false, false, true, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | true, false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, false, false, true]
  | true, false, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | true, false, true, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, true, false, false, false, true => ![false, true, false, false, false, false, true, true, false, true]
  | false, true, false, true, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, false, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, false, false, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, false, true => ![false, true, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, false, false, true => ![false, false, true, false, false, false, true, false, true, true]
  | true, true, false, true, false, true, false, false, true => ![false, false, true, false, false, false, true, true, true, true]
  | false, false, true, true, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, false, true => ![false, false, true, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, false, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, false, false, true => ![false, false, true, false, false, false, true, true, true, true]
  | false, false, true, false, true, true, false, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, false, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, false, false, true => ![false, false, true, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, false, false, true => ![false, true, true, false, false, false, true, true, true, true]
  | false, false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, false, true => ![false, true, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, false, true => ![false, true, true, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, false, false, true, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, false]
  | false, false, false, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, false, false, true, false, true => ![false, true, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, false, true, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, false, true, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, false, true, false, true => ![false, false, false, false, true, false, false, true, false, true]
  | true, false, false, false, true, false, true, false, true => ![false, false, false, false, true, false, true, true, false, true]
  | false, true, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, true, false, false, true, false, true, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, false, true, false, true, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, true, false, true, false, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, true, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, true, false, true => ![false, false, false, false, true, false, true, true, false, true]
  | true, false, false, true, true, false, true, false, true => ![false, true, false, false, true, false, true, true, false, true]
  | false, true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, false, true, false, true => ![false, true, false, false, false, false, true, true, false, true]
  | false, false, true, true, true, false, true, false, true => ![false, false, false, false, true, false, true, true, true, true]
  | true, false, true, true, true, false, true, false, true => ![false, true, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, false, false, false, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, true, true, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, false, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, true, false, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, true, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, false, true, true, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, false, true => ![false, true, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, false, false, true, true, true, false, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, false, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, true, true, false, true => ![false, false, false, false, true, true, false, true, true, true]
  | true, false, true, false, true, true, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, true, true, true, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, true, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, true, false, true => ![false, false, false, false, true, false, true, true, true, true]
  | true, false, false, true, true, true, true, false, true => ![false, true, false, false, true, false, true, true, true, true]
  | false, true, false, true, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, true, false, true => ![false, true, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, true, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, true, true, true, true, false, true => ![false, true, false, false, true, false, false, true, true, true]
  | false, true, true, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, false, true => ![false, true, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, false]
  | false, false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, false, true, true => ![false, false, false, false, false, true, true, false, true, true]
  | true, true, false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, true, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, false, false, true, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, false, false, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, true, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, true, false, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, false, false, true, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, true, false, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, false, true, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, false, true, true => ![false, false, false, false, false, true, false, false, true, true]
  | true, false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, false, true, true => ![false, false, false, false, false, true, true, false, true, true]
  | true, true, false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, true, false, false, true, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, false, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, true, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, true, false, true, true => ![false, false, false, false, false, true, true, false, true, true]
  | true, false, false, true, false, true, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, true, false, true, false, true, false, true, true => ![false, false, true, false, false, true, true, false, true, true]
  | true, true, false, true, false, true, false, true, true => ![false, false, true, false, false, false, true, false, true, true]
  | false, false, true, true, false, true, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, false, true, true, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, false, true, true => ![false, false, true, false, false, true, true, true, true, true]
  | true, true, true, true, false, true, false, true, true => ![false, false, true, false, false, false, true, true, true, true]
  | false, false, false, false, true, true, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, false, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, true, false, true, true => ![false, false, false, false, true, true, false, true, true, true]
  | true, false, true, false, true, true, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, true, true, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, true, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, false, true, true => ![false, false, true, false, false, true, true, true, true, true]
  | true, true, false, true, true, true, false, true, true => ![false, false, true, false, false, false, true, true, true, true]
  | false, false, true, true, true, true, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, true, true => ![false, false, true, false, false, true, false, true, true, true]
  | true, true, true, true, true, true, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | false, false, false, false, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, false, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | false, false, true, false, false, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | false, true, true, false, false, false, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | true, true, true, false, false, false, true, true, true => ![false, false, false, true, false, false, true, true, true, false]
  | false, false, false, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, true, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, true, false, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true, false]
  | false, false, false, false, true, false, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, false, false, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, true, false, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | true, false, true, false, true, false, true, true, true => ![false, false, false, true, true, false, true, true, true, true]
  | false, true, true, false, true, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | false, false, false, true, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true, true]
  | true, false, false, true, true, false, true, true, true => ![false, false, false, false, true, false, true, true, false, true]
  | false, true, false, true, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, true, true, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, false, true, true, true, false, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, true, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, false, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, false, false, false, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, false, false, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, true, true, true, true => ![false, false, false, true, false, true, false, true, true, true]
  | true, false, true, false, false, true, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, false, false, true, true, true, true => ![false, false, false, true, false, true, true, true, true, true]
  | true, true, true, false, false, true, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | false, false, false, true, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, false, false, true, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, true, true => ![false, false, false, false, false, true, true, false, true, true]
  | true, true, false, true, false, true, true, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, true, true, false, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, true, true, false, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, true, true, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, true, true, true, true => ![false, false, false, false, true, true, false, true, true, true]
  | true, false, false, false, true, true, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, false, false, true, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, false, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, true, true => ![false, false, false, true, true, true, false, true, true, true]
  | true, false, true, false, true, true, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | false, true, true, false, true, true, true, true, true => ![false, false, false, true, false, true, false, true, true, true]
  | true, true, true, false, true, true, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, false, false, true, true, true, true, true, true => ![false, false, false, false, true, true, true, true, true, true]
  | true, false, false, true, true, true, true, true, true => ![false, false, false, false, true, false, true, true, true, true]
  | false, true, false, true, true, true, true, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | true, true, false, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, true, true, true, true => ![false, false, false, false, true, true, false, true, true, true]
  | true, false, true, true, true, true, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, true, true, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, true, true, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Single-flip (edge) nonexpansiveness of `facet5bf`.** Flipping any one of the 9 input
coordinates changes the 10-bit output by at most one Hamming unit — the `4608` edge cases,
checked by the kernel evaluator (`decide +kernel`, with recursion depth and heartbeat budget raised
to accommodate the case tree). -/
theorem facet5bf_singleFlip :
    ∀ (p : Fin 9 → Bool) (i : Fin 9),
      (∑ j, bdiff (facet5bf p j) (facet5bf (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide +kernel

/-- **Global nonexpansiveness of `facet5bf`, derived from the single-flip reduction.** Obtained from
`nonexpansive_of_singleFlip` by discharging only the `4608` single-flip edge cases (via
`facet5bf_singleFlip`) rather than the `512²` input pairs. -/
theorem facet5bf_nonexpansive (p q : Fin 9 → Bool) :
    (∑ j, bdiff (facet5bf p j) (facet5bf q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet5bf facet5bf_singleFlip p q

/-- The five color input patterns map through the contraction to the corresponding bounded-region
membership pattern.  A finite `decide` over the five colors. -/
lemma facet5bf_boundary (c : Fin 5) :
    facet5bf (fun i => decide (c ∈ facet5bL_reg i)) = fun j => decide (c ∈ facet5bR_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet5bf`. -/
lemma facet5bf_zero : facet5bf (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

namespace Facet5B

variable {bd : Finset V}

/-- Membership of `v ∈ A c` in a larger-side region: `v ∈ facet5bL A i ↔ c ∈ facet5bL_reg i`. -/
lemma mem_facet5bL_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (i : Fin 9) :
    v ∈ facet5bL A i ↔ c ∈ facet5bL_reg i := by
  unfold facet5bL
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet5bR A j ⊆ bd`. -/
lemma facet5bR_sub (hR : Cyc5.Regions bd A) (j : Fin 10) : facet5bR A j ⊆ bd := by
  unfold facet5bR
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet5bL A i ⊆ bd`. -/
lemma facet5bL_sub (hR : Cyc5.Regions bd A) (i : Fin 9) : facet5bL A i ⊆ bd := by
  unfold facet5bL
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region: `v ∈ facet5bR A j ↔ c ∈ facet5bR_reg j`. -/
lemma mem_facet5bR_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (j : Fin 10) :
    v ∈ facet5bR A j ↔ c ∈ facet5bR_reg j := by
  unfold facet5bR
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color (hR : Cyc5.Regions bd A)
    (X : Fin 9 → Finset V) (hX : ∀ i, IsRTCut bd (facet5bL A i) (X i))
    {v : V} {c : Fin 5} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet5bL_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet5bL_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet5bL_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet5bL A i := fun h => hc ((mem_facet5bL_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 9 → Finset V) (hX : ∀ i, IsRTCut bd (facet5bL A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet5bL A i := by
    unfold facet5bL
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X facet5bf j` is an admissible
RT cut for the bounded region `facet5bR A j`. -/
lemma facet5_hvalid (hR : Cyc5.Regions bd A)
    (X : Fin 9 → Finset V) (hX : ∀ i, IsRTCut bd (facet5bL A i) (X i)) (j : Fin 10) :
    IsRTCut bd (facet5bR A j) (contractionCut X facet5bf j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet5bf j) v = mem (facet5bR A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, facet5bf_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet5bR_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, facet5bf_zero]
      have : v ∉ facet5bR A j := by
        unfold facet5bR
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet5bR_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

end Facet5B

open Facet5B

/-- **A genuinely new five-party holographic entropy cone facet (10-term bounded side).**
For five pairwise-disjoint boundary regions `A₀,…,A₄` (with the rest of `bd` a purifier) in any
finite undirected nonnegative-real-weighted graph, the 9 larger-side regions dominate the 10
bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(largerᵢ)`.

This inequality is **not implied by the `SA + SSA + MMI` cone**: it is a genuine facet of the
five-party holographic entropy cone (source: the five-region holographic entropy cone literature).
It is proved as an instance of the general contraction-map engine `entropyR_ineq_of_contraction`
via the `512`-case map `facet5bf`, whose nonexpansiveness comes through the single-flip edge-case
reduction.  The general holographic entropy cone for `n ≥ 5` remains open. -/
theorem rtEntropyR_newFacet5b (G : GraphR V) {bd : Finset V} {A : Fin 5 → Finset V}
    (hR : Cyc5.Regions bd A) :
    (∑ j, rtEntropyR G bd (facet5bR A j) (Facet5B.facet5bR_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet5bL A i) (Facet5B.facet5bL_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet5bL A i) S
      ∧ rtEntropyR G bd (facet5bL A i) (Facet5B.facet5bL_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (Facet5B.facet5bL_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet5bL A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet5bL A i) (Facet5B.facet5bL_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet5bR A j) (contractionCut X facet5bf j) :=
    fun j => Facet5B.facet5_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet5bL A) (facet5bR A)
    (Facet5B.facet5bL_sub hR) (Facet5B.facet5bR_sub hR) X hXok facet5bf hvalid facet5bf_nonexpansive

/-! #### Anti-vacuity witness: a strict five-party instance

The five-party **star** on `Fin 7` (regions `A₀,…,A₄ = {0},…,{4}`, purifier vertex `5`, central
bulk vertex `6`, unit bonds) witnesses strictness.  A region of `k` colored vertices has min-cut
entropy `min(k, 6 − k)`: the larger-side regions have entropies `![3, 3, 3, 3, 3, 3, 3, 3, 3]` (sum `27`); the
bounded-side regions have entropies `![2, 2, 2, 2, 2, 2, 3, 2, 2, 2]` (sum `21`), a strict slack of `6`, all
entropies positive. -/

/-- `facet5bR star5A j ⊆ star5Bd`. -/
lemma star5_facet5bR_sub (j : Fin 10) : facet5bR star5A j ⊆ star5Bd :=
  Facet5B.facet5bR_sub star5A_regions j
/-- `facet5bL star5A i ⊆ star5Bd`. -/
lemma star5_facet5bL_sub (i : Fin 9) : facet5bL star5A i ⊆ star5Bd :=
  Facet5B.facet5bL_sub star5A_regions i

/-- Each bounded-region entropy of the star witness, as `![2, 2, 2, 2, 2, 2, 3, 2, 2, 2]`. -/
lemma star5_facet5bR (j : Fin 10) :
    rtEntropy star5Graph star5Bd (facet5bR star5A j) (star5_facet5bR_sub j)
      = (![2, 2, 2, 2, 2, 2, 3, 2, 2, 2] : Fin 10 → ℕ) j := by
  fin_cases j <;> · unfold facet5bR facet5bR_reg star5A; decide

/-- Each larger-side entropy of the star witness, as `![3, 3, 3, 3, 3, 3, 3, 3, 3]`. -/
lemma star5_facet5bL (i : Fin 9) :
    rtEntropy star5Graph star5Bd (facet5bL star5A i) (star5_facet5bL_sub i)
      = (![3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 9 → ℕ) i := by
  fin_cases i <;> · unfold facet5bL facet5bL_reg star5A; decide

/-- **Strict five-party anti-vacuity witness (real).** On the cast star graph this new-facet
inequality is strict: the bounded side sums to `21` and the larger side to `27` (slack
`6`), so `rtEntropyR_newFacet5b` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_newFacet5b_strict_witness :
    (∑ j, rtEntropyR (castGraph star5Graph) star5Bd (facet5bR star5A j)
        (Facet5B.facet5bR_sub (A := star5A) star5A_regions j))
      < ∑ i, rtEntropyR (castGraph star5Graph) star5Bd (facet5bL star5A i)
        (Facet5B.facet5bL_sub (A := star5A) star5A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star5Graph) star5Bd (facet5bR star5A j)
      (Facet5B.facet5bR_sub (A := star5A) star5A_regions j)
        = ((![2, 2, 2, 2, 2, 2, 3, 2, 2, 2] : Fin 10 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star5_facet5bR j]
  have hlar : ∀ i, rtEntropyR (castGraph star5Graph) star5Bd (facet5bL star5A i)
      (Facet5B.facet5bL_sub (A := star5A) star5A_regions i)
        = ((![3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 9 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star5_facet5bL i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in this five-party strict new-facet witness are strictly positive. -/
theorem rtEntropyR_newFacet5b_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet5bR star5A j)
        (Facet5B.facet5bR_sub (A := star5A) star5A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet5bL star5A i)
        (Facet5B.facet5bL_sub (A := star5A) star5A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star5_facet5bR j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star5_facet5bL i]; fin_cases i <;> norm_num


/-! ### A fifth genuinely-new five-party holographic entropy cone facet (16 → 18, count-lattice)

A further instance of the general contraction-map engine (`entropyR_ineq_of_contraction`): a
five-party holographic entropy inequality that is a **genuine facet** of the five-party holographic
entropy cone — **not** implied by subadditivity, strong subadditivity and monogamy of mutual
information (the `SA + SSA + MMI` cone).  With five elementary boundary regions `A₀,…,A₄` (colors
`A,B,C,D,E`, plus a purifier = the rest of the boundary), the 16 larger-side regions dominate the
18 bounded-side regions.

The `{0,1}^16 → {0,1}^18` contraction map is large, so it is handled by a *count-lattice*
factorisation, isolated in `Physlib.Foundations.Facet6Map`.  The 16 larger-side terms fall into
10 blocks of equal regions (multiplicities `[3,3,1,1,3,1,1,1,1,1]`), and the map depends only on
each block's popcount: `facet6f = facet6G ∘ blockPopcounts`.  On the count-lattice
`∏_b {0..coef_b}`, `facet6G` is 1-Lipschitz along lattice edges (adjacent popcounts differ by at
most one output bit), checked block-by-block.  A single input-bit flip moves exactly one block
popcount by `±1` — one lattice edge — so single-flip nonexpansiveness of `facet6f` follows
structurally, and Hamming-nonexpansiveness then follows from the single-flip reduction
(`nonexpansive_of_singleFlip`).  Boundary validity of the recombined cuts is the usual finite
check on the six membership patterns boundary vertices can carry.  The general holographic entropy
cone for `n ≥ 5` remains open. -/

/-- The 16 larger-side regions of colors (multiplicity-unrolled distinct regions), as index sets
in `Fin 5`. -/
def facet6Sev : Fin 16 → Finset (Fin 5) :=
  ![{0, 1, 2}, {0, 1, 2}, {0, 1, 2}, {0, 1, 3}, {0, 1, 3}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 2, 4}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}]

/-- The 18 bounded-side regions of colors, as index sets in `Fin 5`. -/
def facet6Reg : Fin 18 → Finset (Fin 5) :=
  ![{0, 1}, {0, 1}, {0, 2}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 3}, {2, 4}, {2, 4}, {3, 4}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}]

variable {A : Fin 5 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th larger set. -/
def facet6L (A : Fin 5 → Finset V) (i : Fin 16) : Finset V := (facet6Sev i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th region set. -/
def facet6R (A : Fin 5 → Finset V) (j : Fin 18) : Finset V := (facet6Reg j).biUnion A

/-! The 10 block-popcount coordinates of `Facet6.blockPopcounts`, as definitional (`rfl`) accessors
that give the block-Lipschitz rewrites a handle. -/
@[simp] lemma bp0 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 0 = Facet6.bit p 0 + Facet6.bit p 1 + Facet6.bit p 2 := rfl
@[simp] lemma bp1 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 1 = Facet6.bit p 3 + Facet6.bit p 4 + Facet6.bit p 5 := rfl
@[simp] lemma bp2 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 2 = Facet6.bit p 6 := rfl
@[simp] lemma bp3 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 3 = Facet6.bit p 7 := rfl
@[simp] lemma bp4 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 4 = Facet6.bit p 8 + Facet6.bit p 9 + Facet6.bit p 10 := rfl
@[simp] lemma bp5 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 5 = Facet6.bit p 11 := rfl
@[simp] lemma bp6 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 6 = Facet6.bit p 12 := rfl
@[simp] lemma bp7 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 7 = Facet6.bit p 13 := rfl
@[simp] lemma bp8 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 8 = Facet6.bit p 14 := rfl
@[simp] lemma bp9 (p : Fin 16 → Bool) : Facet6.blockPopcounts p 9 = Facet6.bit p 15 := rfl

/-- `facet6f p` as the explicit `facet6G` application on the ten block popcounts. -/
lemma facet6f_eq (p : Fin 16 → Bool) :
    Facet6.facet6f p = Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1)
      (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4)
      (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7)
      (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) := rfl

/-! **Block-popcount bounds.** A single input bit contributes `0` or `1`, so each block popcount is
`≤ coefs b`; and if the flipped input bit is `false`, its block's popcount is strictly below `coefs b`
(so `≤ coefs b − 1`). These feed the bounded-quantifier `facet6G_lip_b` lemmas: the plain
`∀ n ≤ k, …` form needs a `Decidable` instance, and `Nat.decidableBallLE` does not chain past ~6
nested binders — so the lip lemmas `intro` the ten `≤` bounds, `interval_cases` each, and `decide`
the ground leaf; the single-flip proof then supplies each popcount value together with its bound. -/
lemma Facet6.bit_le_one (p : Fin 16 → Bool) (i : Fin 16) : Facet6.bit p i ≤ 1 := by
  unfold Facet6.bit; split_ifs <;> omega

lemma Facet6.bit_eq_zero_of_false (p : Fin 16 → Bool) (i : Fin 16) (hp : p i = false) :
    Facet6.bit p i = 0 := by
  unfold Facet6.bit; rw [hp]; simp

/-- Discharge a **loose** block-popcount bound `Facet6.blockPopcounts x c ≤ coefs c`: unfold via the
`bpᵢ` accessors, load `Facet6.bit x i ≤ 1` for every bit, then `omega`. -/
macro "bpLoose" x:term : tactic =>
  `(tactic|
    (simp only [bp0, bp1, bp2, bp3, bp4, bp5, bp6, bp7, bp8, bp9]
     have _hb0 := Facet6.bit_le_one $x 0; have _hb1 := Facet6.bit_le_one $x 1
     have _hb2 := Facet6.bit_le_one $x 2; have _hb3 := Facet6.bit_le_one $x 3
     have _hb4 := Facet6.bit_le_one $x 4; have _hb5 := Facet6.bit_le_one $x 5
     have _hb6 := Facet6.bit_le_one $x 6; have _hb7 := Facet6.bit_le_one $x 7
     have _hb8 := Facet6.bit_le_one $x 8; have _hb9 := Facet6.bit_le_one $x 9
     have _hb10 := Facet6.bit_le_one $x 10; have _hb11 := Facet6.bit_le_one $x 11
     have _hb12 := Facet6.bit_le_one $x 12; have _hb13 := Facet6.bit_le_one $x 13
     have _hb14 := Facet6.bit_le_one $x 14; have _hb15 := Facet6.bit_le_one $x 15
     omega))

/-- Discharge a **strict** flipped-block bound `Facet6.blockPopcounts x b ≤ coefs b − 1`, given a
hypothesis `h : x i = false` for the flipped bit `i` in block `b`: as `bpLoose`, plus rewriting the
flipped bit's contribution to `0`. -/
macro "bpStrict" x:term "," h:ident : tactic =>
  `(tactic|
    (simp only [bp0, bp1, bp2, bp3, bp4, bp5, bp6, bp7, bp8, bp9,
       Facet6.bit_eq_zero_of_false $x _ $h]
     have _hb0 := Facet6.bit_le_one $x 0; have _hb1 := Facet6.bit_le_one $x 1
     have _hb2 := Facet6.bit_le_one $x 2; have _hb3 := Facet6.bit_le_one $x 3
     have _hb4 := Facet6.bit_le_one $x 4; have _hb5 := Facet6.bit_le_one $x 5
     have _hb8 := Facet6.bit_le_one $x 8; have _hb9 := Facet6.bit_le_one $x 9
     have _hb10 := Facet6.bit_le_one $x 10
     omega))

/-! **Per-block count-lattice Lipschitz.** For each block `b`, bumping the `b`-th popcount
coordinate by `1` (a lattice edge) changes at most one of the 18 output bits.  Each is a finite
`decide` over the count-lattice; the block coordinate ranges over `0 .. coef_b − 1`, the others over
their full ranges.  These `decide`s reduce the big `facet6G` map and are the heaviest
compile here — so the ten lemmas `facet6G_lip_0 … facet6G_lip_9` live in ten **separate** modules
`Physlib.Foundations.Facet6Lip0 … Facet6Lip9` (imported above), each with **unlimited heartbeats**.
`lake build` compiles them in parallel over the cached `Facet6Map` `.olean`, so the wall-clock is
one lemma's time rather than the sum of ten.  Each is `public` in this same namespace, so the
references below (in `facet6f_singleFlip`) resolve unqualified exactly as before. -/

set_option maxHeartbeats 2000000 in
/-- **Single-flip (edge) nonexpansiveness of `facet6f`.** Flipping any one of the 16 input bits
changes exactly one block popcount by `±1` (one lattice edge), so at most one output bit changes.
Proved structurally from the per-block lattice-Lipschitz lemmas via `Facet6.blockPopcounts`; no
`2^16`-scale `decide`. -/
theorem facet6f_singleFlip :
    ∀ (p : Fin 16 → Bool) (i : Fin 16),
      (∑ j, bdiff (Facet6.facet6f p j) (Facet6.facet6f (Function.update p i (!(p i))) j)) ≤ 1 := by
  intro p i
  fin_cases i
  · -- flip input bit 0 (block 0)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 0 (!(p 0))) j)) ≤ 1
    set q := Function.update p 0 (!(p 0)) with hq
    have hother : ∀ b : Fin 16, b ≠ 0 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 0 with
    | false =>
      have hqi : q 0 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp0, Facet6.bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp0, Facet6.bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_0 (Facet6.blockPopcounts p 0) (by bpStrict p, hpi) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 0 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : Facet6.blockPopcounts q 0 + 1 = Facet6.blockPopcounts p 0 := by
        first
        | (simp only [bp0, Facet6.bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp0, Facet6.bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts q 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts q 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet6G_lip_0 (Facet6.blockPopcounts q 0) (by bpStrict q, hqi) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 1 (block 0)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 1 (!(p 1))) j)) ≤ 1
    set q := Function.update p 1 (!(p 1)) with hq
    have hother : ∀ b : Fin 16, b ≠ 1 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 1 with
    | false =>
      have hqi : q 1 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp0, Facet6.bit, hother 0 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp0, Facet6.bit, hother 0 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_0 (Facet6.blockPopcounts p 0) (by bpStrict p, hpi) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 1 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : Facet6.blockPopcounts q 0 + 1 = Facet6.blockPopcounts p 0 := by
        first
        | (simp only [bp0, Facet6.bit, hother 0 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp0, Facet6.bit, hother 0 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts q 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts q 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet6G_lip_0 (Facet6.blockPopcounts q 0) (by bpStrict q, hqi) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 2 (block 0)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 2 (!(p 2))) j)) ≤ 1
    set q := Function.update p 2 (!(p 2)) with hq
    have hother : ∀ b : Fin 16, b ≠ 2 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 2 with
    | false =>
      have hqi : q 2 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_0 (Facet6.blockPopcounts p 0) (by bpStrict p, hpi) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 2 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : Facet6.blockPopcounts q 0 + 1 = Facet6.blockPopcounts p 0 := by
        first
        | (simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts q 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts q 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet6G_lip_0 (Facet6.blockPopcounts q 0) (by bpStrict q, hqi) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 3 (block 1)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 3 (!(p 3))) j)) ≤ 1
    set q := Function.update p 3 (!(p 3)) with hq
    have hother : ∀ b : Fin 16, b ≠ 3 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 3 with
    | false =>
      have hqi : q 3 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1, Facet6.bit, hother 4 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1, Facet6.bit, hother 4 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_1 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpStrict p, hpi) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 3 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : Facet6.blockPopcounts q 1 + 1 = Facet6.blockPopcounts p 1 := by
        first
        | (simp only [bp1, Facet6.bit, hother 4 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1, Facet6.bit, hother 4 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts q 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts q 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet6G_lip_1 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts q 1) (by bpStrict q, hqi) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 4 (block 1)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 4 (!(p 4))) j)) ≤ 1
    set q := Function.update p 4 (!(p 4)) with hq
    have hother : ∀ b : Fin 16, b ≠ 4 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 4 with
    | false =>
      have hqi : q 4 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1, Facet6.bit, hother 3 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1, Facet6.bit, hother 3 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_1 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpStrict p, hpi) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 4 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : Facet6.blockPopcounts q 1 + 1 = Facet6.blockPopcounts p 1 := by
        first
        | (simp only [bp1, Facet6.bit, hother 3 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1, Facet6.bit, hother 3 (by decide), hother 5 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts q 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts q 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet6G_lip_1 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts q 1) (by bpStrict q, hqi) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 5 (block 1)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 5 (!(p 5))) j)) ≤ 1
    set q := Function.update p 5 (!(p 5)) with hq
    have hother : ∀ b : Fin 16, b ≠ 5 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 5 with
    | false =>
      have hqi : q 5 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_1 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpStrict p, hpi) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 5 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : Facet6.blockPopcounts q 1 + 1 = Facet6.blockPopcounts p 1 := by
        first
        | (simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts q 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts q 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet6G_lip_1 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts q 1) (by bpStrict q, hqi) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 6 (block 2)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 6 (!(p 6))) j)) ≤ 1
    set q := Function.update p 6 (!(p 6)) with hq
    have hother : ∀ b : Fin 16, b ≠ 6 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 6 with
    | false =>
      have hqi : q 6 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 + 1 := by
        first
        | (simp only [bp2, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp2, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_2 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpStrict p, hpi) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 6 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : Facet6.blockPopcounts q 2 + 1 = Facet6.blockPopcounts p 2 := by
        first
        | (simp only [bp2, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp2, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts q 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts q 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e2]
      exact facet6G_lip_2 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts q 2) (by bpStrict q, hqi) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 7 (block 3)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 7 (!(p 7))) j)) ≤ 1
    set q := Function.update p 7 (!(p 7)) with hq
    have hother : ∀ b : Fin 16, b ≠ 7 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 7 with
    | false =>
      have hqi : q 7 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 + 1 := by
        first
        | (simp only [bp3, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp3, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_3 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpStrict p, hpi) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 7 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : Facet6.blockPopcounts q 3 + 1 = Facet6.blockPopcounts p 3 := by
        first
        | (simp only [bp3, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp3, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts q 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts q 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e3]
      exact facet6G_lip_3 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts q 3) (by bpStrict q, hqi) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 8 (block 4)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 8 (!(p 8))) j)) ≤ 1
    set q := Function.update p 8 (!(p 8)) with hq
    have hother : ∀ b : Fin 16, b ≠ 8 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 8 with
    | false =>
      have hqi : q 8 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp4, Facet6.bit, hother 9 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp4, Facet6.bit, hother 9 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_4 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpStrict p, hpi) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 8 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : Facet6.blockPopcounts q 4 + 1 = Facet6.blockPopcounts p 4 := by
        first
        | (simp only [bp4, Facet6.bit, hother 9 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp4, Facet6.bit, hother 9 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts q 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts q 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet6G_lip_4 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts q 4) (by bpStrict q, hqi) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 9 (block 4)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 9 (!(p 9))) j)) ≤ 1
    set q := Function.update p 9 (!(p 9)) with hq
    have hother : ∀ b : Fin 16, b ≠ 9 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 9 with
    | false =>
      have hqi : q 9 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp4, Facet6.bit, hother 8 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp4, Facet6.bit, hother 8 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_4 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpStrict p, hpi) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 9 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : Facet6.blockPopcounts q 4 + 1 = Facet6.blockPopcounts p 4 := by
        first
        | (simp only [bp4, Facet6.bit, hother 8 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp4, Facet6.bit, hother 8 (by decide), hother 10 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts q 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts q 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet6G_lip_4 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts q 4) (by bpStrict q, hqi) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 10 (block 4)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 10 (!(p 10))) j)) ≤ 1
    set q := Function.update p 10 (!(p 10)) with hq
    have hother : ∀ b : Fin 16, b ≠ 10 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 10 with
    | false =>
      have hqi : q 10 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_4 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpStrict p, hpi) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 10 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : Facet6.blockPopcounts q 4 + 1 = Facet6.blockPopcounts p 4 := by
        first
        | (simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts q 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts q 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet6G_lip_4 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts q 4) (by bpStrict q, hqi) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 11 (block 5)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 11 (!(p 11))) j)) ≤ 1
    set q := Function.update p 11 (!(p 11)) with hq
    have hother : ∀ b : Fin 16, b ≠ 11 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 11 with
    | false =>
      have hqi : q 11 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp5, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp5, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_5 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpStrict p, hpi) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 11 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : Facet6.blockPopcounts q 5 + 1 = Facet6.blockPopcounts p 5 := by
        first
        | (simp only [bp5, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp5, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts q 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts q 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet6G_lip_5 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts q 5) (by bpStrict q, hqi) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 12 (block 6)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 12 (!(p 12))) j)) ≤ 1
    set q := Function.update p 12 (!(p 12)) with hq
    have hother : ∀ b : Fin 16, b ≠ 12 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 12 with
    | false =>
      have hqi : q 12 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp6, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp6, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_6 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpStrict p, hpi) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 12 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : Facet6.blockPopcounts q 6 + 1 = Facet6.blockPopcounts p 6 := by
        first
        | (simp only [bp6, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp6, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e7, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts q 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts q 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet6G_lip_6 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts q 6) (by bpStrict q, hqi) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 13 (block 7)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 13 (!(p 13))) j)) ≤ 1
    set q := Function.update p 13 (!(p 13)) with hq
    have hother : ∀ b : Fin 16, b ≠ 13 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 13 with
    | false =>
      have hqi : q 13 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 + 1 := by
        first
        | (simp only [bp7, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_7 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpStrict p, hpi) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 13 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : Facet6.blockPopcounts q 7 + 1 = Facet6.blockPopcounts p 7 := by
        first
        | (simp only [bp7, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e8, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts q 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts q 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e7]
      exact facet6G_lip_7 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts q 7) (by bpStrict q, hqi) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 14 (block 8)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 14 (!(p 14))) j)) ≤ 1
    set q := Function.update p 14 (!(p 14)) with hq
    have hother : ∀ b : Fin 16, b ≠ 14 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 := by
      simp only [bp9, Facet6.bit, hother 15 (by decide)]
    cases hpi : p 14 with
    | false =>
      have hqi : q 14 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp8, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp8, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_8 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpStrict p, hpi) (Facet6.blockPopcounts p 9) (by bpLoose p)
    | true =>
      have hqi : q 14 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : Facet6.blockPopcounts q 8 + 1 = Facet6.blockPopcounts p 8 := by
        first
        | (simp only [bp8, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp8, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e9]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts q 8) (Facet6.blockPopcounts p 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts q 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet6G_lip_8 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts q 8) (by bpStrict q, hqi) (Facet6.blockPopcounts p 9) (by bpLoose p)
  · -- flip input bit 15 (block 9)
    show (∑ j, bdiff (Facet6.facet6f p j)
          (Facet6.facet6f (Function.update p 15 (!(p 15))) j)) ≤ 1
    set q := Function.update p 15 (!(p 15)) with hq
    have hother : ∀ b : Fin 16, b ≠ 15 → q b = p b :=
      fun b hb => Function.update_of_ne hb _ _
    have e0 : Facet6.blockPopcounts q 0 = Facet6.blockPopcounts p 0 := by
      simp only [bp0, Facet6.bit, hother 0 (by decide), hother 1 (by decide), hother 2 (by decide)]
    have e1 : Facet6.blockPopcounts q 1 = Facet6.blockPopcounts p 1 := by
      simp only [bp1, Facet6.bit, hother 3 (by decide), hother 4 (by decide), hother 5 (by decide)]
    have e2 : Facet6.blockPopcounts q 2 = Facet6.blockPopcounts p 2 := by
      simp only [bp2, Facet6.bit, hother 6 (by decide)]
    have e3 : Facet6.blockPopcounts q 3 = Facet6.blockPopcounts p 3 := by
      simp only [bp3, Facet6.bit, hother 7 (by decide)]
    have e4 : Facet6.blockPopcounts q 4 = Facet6.blockPopcounts p 4 := by
      simp only [bp4, Facet6.bit, hother 8 (by decide), hother 9 (by decide), hother 10 (by decide)]
    have e5 : Facet6.blockPopcounts q 5 = Facet6.blockPopcounts p 5 := by
      simp only [bp5, Facet6.bit, hother 11 (by decide)]
    have e6 : Facet6.blockPopcounts q 6 = Facet6.blockPopcounts p 6 := by
      simp only [bp6, Facet6.bit, hother 12 (by decide)]
    have e7 : Facet6.blockPopcounts q 7 = Facet6.blockPopcounts p 7 := by
      simp only [bp7, Facet6.bit, hother 13 (by decide)]
    have e8 : Facet6.blockPopcounts q 8 = Facet6.blockPopcounts p 8 := by
      simp only [bp8, Facet6.bit, hother 14 (by decide)]
    cases hpi : p 15 with
    | false =>
      have hqi : q 15 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : Facet6.blockPopcounts q 9 = Facet6.blockPopcounts p 9 + 1 := by
        first
        | (simp only [bp9, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp9, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet6G_lip_9 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts p 9) (by bpStrict p, hpi)
    | true =>
      have hqi : q 15 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : Facet6.blockPopcounts q 9 + 1 = Facet6.blockPopcounts p 9 := by
        first
        | (simp only [bp9, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp9, Facet6.bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet6f_eq p, facet6f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts q 9) j))
          = ∑ j, bdiff (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts q 9) j) (Facet6.facet6G (Facet6.blockPopcounts p 0) (Facet6.blockPopcounts p 1) (Facet6.blockPopcounts p 2) (Facet6.blockPopcounts p 3) (Facet6.blockPopcounts p 4) (Facet6.blockPopcounts p 5) (Facet6.blockPopcounts p 6) (Facet6.blockPopcounts p 7) (Facet6.blockPopcounts p 8) (Facet6.blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e9]
      exact facet6G_lip_9 (Facet6.blockPopcounts p 0) (by bpLoose p) (Facet6.blockPopcounts p 1) (by bpLoose p) (Facet6.blockPopcounts p 2) (by bpLoose p) (Facet6.blockPopcounts p 3) (by bpLoose p) (Facet6.blockPopcounts p 4) (by bpLoose p) (Facet6.blockPopcounts p 5) (by bpLoose p) (Facet6.blockPopcounts p 6) (by bpLoose p) (Facet6.blockPopcounts p 7) (by bpLoose p) (Facet6.blockPopcounts p 8) (by bpLoose p) (Facet6.blockPopcounts q 9) (by bpStrict q, hqi)

/-- **Contraction (Hamming-nonexpansiveness) of `facet6f`.** Obtained from the single-flip
reduction (`nonexpansive_of_singleFlip`): the 18 output bits separate any two 16-bit patterns at
most as often as the 16 input bits. -/
theorem facet6f_nonexpansive (p q : Fin 16 → Bool) :
    (∑ j, bdiff (Facet6.facet6f p j) (Facet6.facet6f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip Facet6.facet6f facet6f_singleFlip p q

/-- The six input patterns carried by boundary vertices — one per elementary color and the
all-`false` purifier pattern — map through `facet6f` exactly to the corresponding bounded-region
membership pattern. -/
lemma facet6f_boundary (c : Fin 5) :
    Facet6.facet6f (fun i => decide (c ∈ facet6Sev i)) = fun j => decide (c ∈ facet6Reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet6f`. -/
lemma facet6f_zero : Facet6.facet6f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

namespace Facet6Cert

variable {bd : Finset V}

/-- Membership of `v ∈ A c` in a larger-side region: `v ∈ facet6L A i ↔ c ∈ facet6Sev i`. -/
lemma mem_facet6L_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (i : Fin 16) :
    v ∈ facet6L A i ↔ c ∈ facet6Sev i := by
  unfold facet6L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet6R A j ⊆ bd`. -/
lemma facet6R_sub (hR : Cyc5.Regions bd A) (j : Fin 18) : facet6R A j ⊆ bd := by
  unfold facet6R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet6L A i ⊆ bd`. -/
lemma facet6L_sub (hR : Cyc5.Regions bd A) (i : Fin 16) : facet6L A i ⊆ bd := by
  unfold facet6L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region: `v ∈ facet6R A j ↔ c ∈ facet6Reg j`. -/
lemma mem_facet6R_of_color (hR : Cyc5.Regions bd A) {v : V} {c : Fin 5} (hv : v ∈ A c) (j : Fin 18) :
    v ∈ facet6R A j ↔ c ∈ facet6Reg j := by
  unfold facet6R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color (hR : Cyc5.Regions bd A)
    (X : Fin 16 → Finset V) (hX : ∀ i, IsRTCut bd (facet6L A i) (X i))
    {v : V} {c : Fin 5} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet6Sev i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet6Sev i
  · have : v ∈ X i := (hX i).1 ((mem_facet6L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet6L A i := fun h => hc ((mem_facet6L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 16 → Finset V) (hX : ∀ i, IsRTCut bd (facet6L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet6L A i := by
    unfold facet6L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X facet6f j` is an
admissible RT cut for the bounded region `facet6R A j`. -/
lemma facet6_hvalid (hR : Cyc5.Regions bd A)
    (X : Fin 16 → Finset V) (hX : ∀ i, IsRTCut bd (facet6L A i) (X i)) (j : Fin 18) :
    IsRTCut bd (facet6R A j) (contractionCut X Facet6.facet6f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X Facet6.facet6f j) v = mem (facet6R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, facet6f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet6R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, facet6f_zero]
      have : v ∉ facet6R A j := by
        unfold facet6R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet6R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

end Facet6Cert

open Facet6Cert

/-- **A fifth genuinely new five-party holographic entropy cone facet.**
For five pairwise-disjoint boundary regions `A₀,…,A₄` (with the rest of `bd` a purifier) in any
finite undirected nonnegative-real-weighted graph, the 16 larger-side regions dominate the 18
bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(largerᵢ)`.

Being outside the `SA + SSA + MMI` cone, this is a genuine facet of the five-party holographic
entropy cone (source: the five-party holographic entropy cone database).  It is proved here as an
instance of the general contraction-map engine `entropyR_ineq_of_contraction` via the count-lattice
map `facet6f` (whose Hamming-nonexpansiveness comes from the single-flip reduction over the
block-popcount lattice).  The general holographic entropy cone for `n ≥ 5` remains open. -/
theorem rtEntropyR_newFacet6 (G : GraphR V) {bd : Finset V} {A : Fin 5 → Finset V}
    (hR : Cyc5.Regions bd A) :
    (∑ j, rtEntropyR G bd (facet6R A j) (Facet6Cert.facet6R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet6L A i) (Facet6Cert.facet6L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet6L A i) S
      ∧ rtEntropyR G bd (facet6L A i) (Facet6Cert.facet6L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (Facet6Cert.facet6L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet6L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet6L A i) (Facet6Cert.facet6L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet6R A j) (contractionCut X Facet6.facet6f j) :=
    fun j => Facet6Cert.facet6_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet6L A) (facet6R A)
    (Facet6Cert.facet6L_sub hR) (Facet6Cert.facet6R_sub hR) X hXok Facet6.facet6f hvalid
    facet6f_nonexpansive

/-! ### Anti-vacuity witness: a strict five-party instance

The five-party **star** on `Fin 7` (regions `A₀,…,A₄ = {0},…,{4}`, purifier vertex `5`, central
bulk vertex `6`, unit bonds) witnesses strictness.  A region of `k` colored vertices has min-cut
entropy `min(k, 6 − k)`: every larger-side region is a triple (entropy `3`, sum `48`); every
bounded-side region is a pair or a 4-set (entropy `2`, sum `36`), a strict slack of `12`, with all
`34` entropies positive. -/

/-- `facet6R star5A j ⊆ star5Bd`. -/
lemma star5_facet6R_sub (j : Fin 18) : facet6R star5A j ⊆ star5Bd :=
  Facet6Cert.facet6R_sub star5A_regions j
/-- `facet6L star5A i ⊆ star5Bd`. -/
lemma star5_facet6L_sub (i : Fin 16) : facet6L star5A i ⊆ star5Bd :=
  Facet6Cert.facet6L_sub star5A_regions i

/-- Each bounded-region entropy of the star witness is `2`. -/
lemma star5_facet6R (j : Fin 18) :
    rtEntropy star5Graph star5Bd (facet6R star5A j) (star5_facet6R_sub j) = 2 := by
  fin_cases j <;> · unfold facet6R facet6Reg star5A; decide

/-- Each larger-side entropy of the star witness is `3`. -/
lemma star5_facet6L (i : Fin 16) :
    rtEntropy star5Graph star5Bd (facet6L star5A i) (star5_facet6L_sub i) = 3 := by
  fin_cases i <;> · unfold facet6L facet6Sev star5A; decide

/-- **Strict five-party anti-vacuity witness (real).** On the cast star graph the new-facet
inequality is strict: the bounded side sums to `36` and the larger side to `48` (slack `12`), so
`rtEntropyR_newFacet6` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_newFacet6_strict_witness :
    (∑ j, rtEntropyR (castGraph star5Graph) star5Bd (facet6R star5A j)
        (Facet6Cert.facet6R_sub (A := star5A) star5A_regions j))
      < ∑ i, rtEntropyR (castGraph star5Graph) star5Bd (facet6L star5A i)
        (Facet6Cert.facet6L_sub (A := star5A) star5A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star5Graph) star5Bd (facet6R star5A j)
      (Facet6Cert.facet6R_sub (A := star5A) star5A_regions j) = (2 : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star5_facet6R j]; norm_num
  have hlar : ∀ i, rtEntropyR (castGraph star5Graph) star5Bd (facet6L star5A i)
      (Facet6Cert.facet6L_sub (A := star5A) star5A_regions i) = (3 : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star5_facet6L i]; norm_num
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp
  norm_num

/-- All `34` min-cut entropies in the five-party strict new-facet witness are strictly positive. -/
theorem rtEntropyR_newFacet6_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet6R star5A j)
        (Facet6Cert.facet6R_sub (A := star5A) star5A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star5Graph) star5Bd (facet6L star5A i)
        (Facet6Cert.facet6L_sub (A := star5A) star5A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star5_facet6R j]; norm_num
  · rw [rtEntropyR_castGraph, star5_facet6L i]; norm_num

/-! ### A genuinely new six-party holographic entropy cone facet

As a further instance of the general contraction-map engine (`entropyR_ineq_of_contraction`), we
certify a six-party holographic entropy inequality that is a **genuine facet** of the six-party
holographic entropy cone — not implied by subadditivity, strong subadditivity and monogamy of mutual
information.  With six elementary boundary regions `A₀,…,A₅` (colors `A,B,C,D,E,F`, plus a purifier =
the rest of the boundary) the inequality is

  `S(ABC) + S(ABD) + S(ABE) + S(ACD) + S(ACF) + S(BCEF)`
    `≥ S(AB) + S(AC) + S(AD) + S(BE) + S(CF) + S(ABCD) + S(ABCEF)`,

with the six larger-side regions `ABC, ABD, ABE, ACD, ACF, BCEF` and the seven bounded-side regions
`AB, AC, AD, BE, CF, ABCD, ABCEF` (source: the six-party holographic entropy cone / Hernández-Cuenca
holographic entropy cone database).  Its validity for the undirected min-cut model is established
here by exhibiting an explicit `64`-entry boolean contraction map, not by cone membership. -/

namespace Facet6n174

-- LHS regions (Fin 6 color-sets), bit order i=0..5:  bit l = [color in LHS[l]]; LHS order as listed (size-lex)
def facet6n174L_reg : Fin 6 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 5}, {1, 2, 4, 5}]
-- RHS regions (Fin 6 color-sets), bit order j=0..6:  bit r = [color in RHS[r]]; RHS order as listed (size-lex)
def facet6n174R_reg : Fin 7 → Finset (Fin 6) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 4}, {2, 5}, {0, 1, 2, 3}, {0, 1, 2, 4, 5}]

def facet6n174f (p : Fin 6 → Bool) : Fin 7 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5 with
  | false, false, false, false, false, false => ![false, false, false, false, false, false, false]
  | false, false, false, false, false, true => ![false, false, false, false, false, false, true]
  | false, false, false, false, true, false => ![false, false, false, false, false, false, true]
  | false, false, false, false, true, true => ![false, false, false, false, true, false, true]
  | false, false, false, true, false, false => ![false, false, false, false, false, true, false]
  | false, false, false, true, false, true => ![false, false, false, false, false, true, true]
  | false, false, false, true, true, false => ![false, false, false, false, false, true, true]
  | false, false, false, true, true, true => ![false, false, false, false, true, true, true]
  | false, false, true, false, false, false => ![false, false, false, false, false, false, true]
  | false, false, true, false, false, true => ![false, false, false, true, false, false, true]
  | false, false, true, false, true, false => ![false, false, false, false, false, true, true]
  | false, false, true, false, true, true => ![false, false, false, false, false, false, true]
  | false, false, true, true, false, false => ![false, false, false, false, false, true, true]
  | false, false, true, true, false, true => ![false, false, false, false, false, false, true]
  | false, false, true, true, true, false => ![false, false, true, false, false, true, true]
  | false, false, true, true, true, true => ![false, false, false, false, false, true, true]
  | false, true, false, false, false, false => ![false, false, false, false, false, true, false]
  | false, true, false, false, false, true => ![false, false, false, false, false, true, true]
  | false, true, false, false, true, false => ![false, false, false, false, false, true, true]
  | false, true, false, false, true, true => ![false, false, false, false, false, false, true]
  | false, true, false, true, false, false => ![false, false, true, false, false, true, false]
  | false, true, false, true, false, true => ![false, false, false, false, false, true, false]
  | false, true, false, true, true, false => ![false, false, true, false, false, true, true]
  | false, true, false, true, true, true => ![false, false, false, false, false, true, true]
  | false, true, true, false, false, false => ![false, false, false, false, false, true, true]
  | false, true, true, false, false, true => ![false, false, false, true, false, true, true]
  | false, true, true, false, true, false => ![false, false, true, false, false, true, true]
  | false, true, true, false, true, true => ![false, false, false, false, false, true, true]
  | false, true, true, true, false, false => ![false, false, true, false, false, true, true]
  | false, true, true, true, false, true => ![false, false, false, false, false, true, true]
  | false, true, true, true, true, false => ![false, true, true, false, false, true, true]
  | false, true, true, true, true, true => ![false, true, false, false, false, true, true]
  | true, false, false, false, false, false => ![false, false, false, false, false, false, true]
  | true, false, false, false, false, true => ![false, false, false, false, false, true, true]
  | true, false, false, false, true, false => ![false, false, false, false, false, true, true]
  | true, false, false, false, true, true => ![false, false, false, false, true, true, true]
  | true, false, false, true, false, false => ![false, false, false, false, false, true, true]
  | true, false, false, true, false, true => ![false, false, false, false, true, true, true]
  | true, false, false, true, true, false => ![false, true, false, false, false, true, true]
  | true, false, false, true, true, true => ![false, true, false, false, true, true, true]
  | true, false, true, false, false, false => ![false, false, false, false, false, true, true]
  | true, false, true, false, false, true => ![false, false, false, true, false, true, true]
  | true, false, true, false, true, false => ![false, false, true, false, false, true, true]
  | true, false, true, false, true, true => ![false, false, false, false, false, true, true]
  | true, false, true, true, false, false => ![false, false, true, false, false, true, true]
  | true, false, true, true, false, true => ![false, false, false, false, false, true, true]
  | true, false, true, true, true, false => ![false, true, true, false, false, true, true]
  | true, false, true, true, true, true => ![false, true, false, false, false, true, true]
  | true, true, false, false, false, false => ![false, false, false, false, false, true, true]
  | true, true, false, false, false, true => ![false, false, false, true, false, true, true]
  | true, true, false, false, true, false => ![false, false, true, false, false, true, true]
  | true, true, false, false, true, true => ![false, false, false, false, false, true, true]
  | true, true, false, true, false, false => ![false, false, true, false, false, true, true]
  | true, true, false, true, false, true => ![false, false, false, false, false, true, true]
  | true, true, false, true, true, false => ![false, true, true, false, false, true, true]
  | true, true, false, true, true, true => ![false, true, false, false, false, true, true]
  | true, true, true, false, false, false => ![true, false, false, false, false, true, true]
  | true, true, true, false, false, true => ![true, false, false, true, false, true, true]
  | true, true, true, false, true, false => ![true, false, true, false, false, true, true]
  | true, true, true, false, true, true => ![true, false, false, false, false, true, true]
  | true, true, true, true, false, false => ![true, false, true, false, false, true, true]
  | true, true, true, true, false, true => ![true, false, false, false, false, true, true]
  | true, true, true, true, true, false => ![true, true, true, false, false, true, true]
  | true, true, true, true, true, true => ![true, true, false, false, false, true, true]

variable {bd : Finset V}

/-- Pairwise disjointness and boundary-containment of the six elementary regions. -/
structure Regions6 (bd : Finset V) (A : Fin 6 → Finset V) : Prop where
  /-- each elementary region lies in the boundary -/
  sub : ∀ c, A c ⊆ bd
  /-- distinct elementary regions are disjoint -/
  disj : ∀ c c', c ≠ c' → Disjoint (A c) (A c')

variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th color set. -/
def facet6n174L (A : Fin 6 → Finset V) (i : Fin 6) : Finset V := (facet6n174L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th color set. -/
def facet6n174R (A : Fin 6 → Finset V) (j : Fin 7) : Finset V := (facet6n174R_reg j).biUnion A

set_option maxHeartbeats 0 in
/-- **Single-flip (edge) nonexpansiveness of `facet6n174f`.** Flipping any one of the six input
coordinates changes the seven-bit output by at most one Hamming unit — the `6 · 2⁶ = 384` edge cases,
checked by `decide`. -/
theorem facet6n174f_singleFlip :
    ∀ (p : Fin 6 → Bool) (i : Fin 6),
      (∑ j, bdiff (facet6n174f p j) (facet6n174f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide

/-- **Global nonexpansiveness of `facet6n174f`, derived from the single-flip reduction.** The seven
output bits separate any two six-bit inputs at most as often as the six input bits, obtained from
`nonexpansive_of_singleFlip` by discharging only the `384` single-flip edge cases. -/
theorem facet6n174f_nonexpansive_via_singleFlip (p q : Fin 6 → Bool) :
    (∑ j, bdiff (facet6n174f p j) (facet6n174f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet6n174f facet6n174f_singleFlip p q

/-- The seven input patterns carried by boundary vertices — one per elementary color and the
all-`false` purifier pattern — map through `facet6n174f` exactly to the corresponding bounded-region
membership pattern. -/
lemma facet6n174f_boundary (c : Fin 6) :
    facet6n174f (fun i => decide (c ∈ facet6n174L_reg i)) = fun j => decide (c ∈ facet6n174R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet6n174f`. -/
lemma facet6n174f_zero : facet6n174f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region: `v ∈ facet6n174L A i ↔ c ∈ facet6n174L_reg i`. -/
lemma mem_facet6n174L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 6) :
    v ∈ facet6n174L A i ↔ c ∈ facet6n174L_reg i := by
  unfold facet6n174L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet6n174R A j ⊆ bd`. -/
lemma facet6n174R_sub (hR : Regions6 bd A) (j : Fin 7) : facet6n174R A j ⊆ bd := by
  unfold facet6n174R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet6n174L A i ⊆ bd`. -/
lemma facet6n174L_sub (hR : Regions6 bd A) (i : Fin 6) : facet6n174L A i ⊆ bd := by
  unfold facet6n174L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region: `v ∈ facet6n174R A j ↔ c ∈ facet6n174R_reg j`. -/
lemma mem_facet6n174R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 7) :
    v ∈ facet6n174R A j ↔ c ∈ facet6n174R_reg j := by
  unfold facet6n174R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern:
`contractionPattern X v = fun i => decide (c ∈ facet6n174L_reg i)`. -/
lemma contractionPattern_of_color (hR : Regions6 bd A)
    (X : Fin 6 → Finset V) (hX : ∀ i, IsRTCut bd (facet6n174L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet6n174L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet6n174L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet6n174L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet6n174L A i := fun h => hc ((mem_facet6n174L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex (in `bd`, outside every elementary region), the achieving cuts realize the
all-`false` pattern. -/
lemma contractionPattern_of_purifier
    (X : Fin 6 → Finset V) (hX : ∀ i, IsRTCut bd (facet6n174L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet6n174L A i := by
    unfold facet6n174L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** Each `contractionCut X facet6n174f j` is an
admissible RT cut for the bounded region `facet6n174R A j`. -/
lemma facet6n174_hvalid (hR : Regions6 bd A)
    (X : Fin 6 → Finset V) (hX : ∀ i, IsRTCut bd (facet6n174L A i) (X i)) (j : Fin 7) :
    IsRTCut bd (facet6n174R A j) (contractionCut X facet6n174f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet6n174f j) v = mem (facet6n174R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color hR X hX hvc, facet6n174f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet6n174R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier X hX hvbd hcolor, facet6n174f_zero]
      have : v ∉ facet6n174R A j := by
        unfold facet6n174R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet6n174R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A genuinely new six-party holographic entropy cone facet.**
For six pairwise-disjoint boundary regions `A₀,…,A₅` (with the rest of `bd` a purifier) in any finite
undirected nonnegative-real-weighted graph, the six larger-side regions dominate the seven bounded-side
regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(larger-regionᵢ)`,

i.e.

  `S(AB) + S(AC) + S(AD) + S(BE) + S(CF) + S(ABCD) + S(ABCEF)`
    `≤ S(ABC) + S(ABD) + S(ABE) + S(ACD) + S(ACF) + S(BCEF)`.

This inequality is a genuine facet of the six-party holographic entropy cone (source: the six-party
holographic entropy cone / Hernández-Cuenca holographic entropy cone database), not implied by the
`SA + SSA + MMI` cone.  It is proved here as an instance of the general contraction-map engine
`entropyR_ineq_of_contraction` via the `64`-case map `facet6n174f`. -/
theorem rtEntropyR_newFacet_n6_59174 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet6n174R A j) (facet6n174R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet6n174L A i) (facet6n174L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet6n174L A i) S
      ∧ rtEntropyR G bd (facet6n174L A i) (facet6n174L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet6n174L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet6n174L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet6n174L A i) (facet6n174L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet6n174R A j) (contractionCut X facet6n174f j) :=
    fun j => facet6n174_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet6n174L A) (facet6n174R A)
    (facet6n174L_sub hR) (facet6n174R_sub hR) X hXok facet6n174f hvalid
    facet6n174f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance

The six-party **star** on `Fin 8` has six colored boundary vertices `0,…,5` (regions `A₀,…,A₅`), one
purifier boundary vertex `6`, and one central bulk vertex `7`, with every boundary vertex joined to the
center by a weight-`1` bond.  A region of `k` colored vertices among the `7` boundary vertices has
min-cut entropy `min(k, 7 − k)`.  Each larger-side region here has entropy `3` (the five triples with
`k = 3`, and `BCEF` with `k = 4`, `min(4, 3) = 3`), so the larger side sums to `18`; the bounded side
gives `AB, AC, AD, BE, CF = 2`, `ABCD = min(4, 3) = 3`, `ABCEF = min(5, 2) = 2`, summing to `15`, a
strict slack of `3`, with all thirteen entropies positive. -/

/-- The six-party star bulk graph on `Fin 8`: boundary `0,…,6` each bonded (weight `1`) to central
bulk vertex `7`. -/
def star6Graph : Graph (Fin 8) where
  w := fun u v => if (u = 7 ∧ v.val < 7) ∨ (v = 7 ∧ u.val < 7) then 1 else 0
  symm := by intro u v; by_cases h : u = 7 <;> by_cases h2 : v = 7 <;> simp_all

/-- Boundary of the six-party star: `{0,1,2,3,4,5,6}` (six colors plus a purifier). -/
def star6Bd : Finset (Fin 8) := {0, 1, 2, 3, 4, 5, 6}

/-- The six elementary regions of the star witness: `A c = {c}` for `c ∈ Fin 6`. -/
def star6A : Fin 6 → Finset (Fin 8) := ![{0}, {1}, {2}, {3}, {4}, {5}]

lemma star6A_regions : Regions6 star6Bd star6A where
  sub := by decide
  disj := by decide

/-- `facet6n174R star6A j ⊆ star6Bd`. -/
lemma star6_facet6n174R_sub (j : Fin 7) : facet6n174R star6A j ⊆ star6Bd :=
  facet6n174R_sub star6A_regions j
/-- `facet6n174L star6A i ⊆ star6Bd`. -/
lemma star6_facet6n174L_sub (i : Fin 6) : facet6n174L star6A i ⊆ star6Bd :=
  facet6n174L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness: `AB, AC, AD, BE, CF = 2`, `ABCD = 3`,
`ABCEF = 2`. -/
lemma star6_facet6n174R (j : Fin 7) :
    rtEntropy star6Graph star6Bd (facet6n174R star6A j) (star6_facet6n174R_sub j)
      = if j = 5 then 3 else 2 := by
  fin_cases j <;> · unfold facet6n174R facet6n174R_reg star6A; decide

/-- Each larger-side region entropy of the star witness is `3`. -/
lemma star6_facet6n174L (i : Fin 6) :
    rtEntropy star6Graph star6Bd (facet6n174L star6A i) (star6_facet6n174L_sub i) = 3 := by
  fin_cases i <;> · unfold facet6n174L facet6n174L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness (real).** On the cast star graph the new-facet inequality
is strict: the bounded side sums to `15` and the larger side to `18` (slack `3`), so
`rtEntropyR_newFacet_n6_59174` is not the vacuous `0 ≤ 0`. -/
theorem rtEntropyR_newFacet_n6_59174_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet6n174R star6A j)
        (facet6n174R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet6n174L star6A i)
        (facet6n174L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet6n174R star6A j)
      (facet6n174R_sub (A := star6A) star6A_regions j) = if j = 5 then (3 : ℝ) else 2 := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet6n174R j]
    split <;> norm_num
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet6n174L star6A i)
      (facet6n174L_sub (A := star6A) star6A_regions i) = (3 : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet6n174L i]; norm_num
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  rw [Fin.sum_univ_seven, Fin.sum_univ_six]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide), if_neg (by decide)]
  norm_num

/-- All thirteen min-cut entropies in the six-party strict new-facet witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_59174_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet6n174R star6A j)
        (facet6n174R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet6n174L star6A i)
        (facet6n174L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet6n174R j]; split <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet6n174L i]; norm_num

end Facet6n174

/-! ### A six-party holographic entropy cone facet (database index 18024)

A direct boolean contraction map with 7 larger-side regions and 9 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n18024

open Physlib.UndirectedMMICertificate.Facet6n174

-- facet 18024 (DIRECT): L=7 R=9, 6-party colors 0..5
def facet18024L_reg : Fin 7 → Finset (Fin 6) :=
  ![{1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 3, 5}, {1, 3, 5}, {1, 2, 3, 4}]
def facet18024R_reg : Fin 9 → Finset (Fin 6) :=
  ![{0}, {1}, {2}, {0, 3}, {1, 4}, {3, 5}, {1, 2, 3}, {0, 1, 3, 5}, {0, 1, 2, 3, 4}]
def facet18024f (p : Fin 7 → Bool) : Fin 9 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6 with
  | false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false]
  | false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, true, false => ![false, false, false, false, false, true, false, true, false]
  | false, false, false, false, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false => ![false, false, false, false, false, true, false, true, true]
  | false, false, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, false, true, false, false, false, true => ![false, false, false, false, true, false, false, false, true]
  | false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, true, true => ![false, false, false, false, true, false, false, true, true]
  | false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true]
  | false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, true, false, false => ![false, false, false, true, false, false, false, true, true]
  | false, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, true, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false => ![false, false, false, false, false, true, false, true, true]
  | false, true, false, false, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, true, false => ![false, false, false, false, false, true, false, true, true]
  | false, true, false, true, false, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, false => ![false, false, false, true, false, false, false, true, true]
  | false, true, false, true, true, false, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, false, true, true, true, false => ![false, false, false, true, false, true, false, true, true]
  | false, true, false, true, true, true, true => ![false, false, false, true, false, true, true, true, true]
  | false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, false, false, false, true => ![false, false, false, false, true, false, false, true, true]
  | false, true, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, false, true, false, false => ![false, false, false, true, false, false, false, true, true]
  | false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, false => ![false, false, false, true, false, false, false, true, true]
  | false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false => ![true, false, false, true, false, false, false, true, true]
  | false, true, true, true, true, false, true => ![false, false, false, true, false, false, false, true, true]
  | false, true, true, true, true, true, false => ![false, false, false, true, false, false, false, true, true]
  | false, true, true, true, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, false, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, false]
  | true, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, false]
  | true, false, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, false, true => ![false, false, true, false, false, false, true, false, true]
  | true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, true, false, true, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, true, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, true, true, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, false, false, true => ![false, false, false, false, true, false, true, false, true]
  | true, false, true, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, false, true, false, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, true, false, true, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, true, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, true, true, false, true => ![false, false, false, false, false, false, false, false, true]
  | true, false, true, true, true, true, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, true, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, true, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, true, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, false => ![false, false, false, false, false, true, false, true, true]
  | true, true, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, false, false, true, false => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, false, false, true, true => ![false, true, false, false, true, false, true, true, true]
  | true, true, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, true, true, false, false => ![false, false, false, true, false, false, false, true, true]
  | true, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true]

variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th color set. -/
def facet18024L (A : Fin 6 → Finset V) (i : Fin 7) : Finset V := (facet18024L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th color set. -/
def facet18024R (A : Fin 6 → Finset V) (j : Fin 9) : Finset V := (facet18024R_reg j).biUnion A

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Single-flip (edge) nonexpansiveness of `facet18024f`.** Flipping any one of the 7 input
coordinates changes the 9-bit output by at most one Hamming unit, checked over all single-flip
edge cases. -/
theorem facet18024f_singleFlip :
    ∀ (p : Fin 7 → Bool) (i : Fin 7),
      (∑ j, bdiff (facet18024f p j) (facet18024f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide

/-- **Global nonexpansiveness of `facet18024f`, derived from the single-flip reduction.** -/
theorem facet18024f_nonexpansive_via_singleFlip (p q : Fin 7 → Bool) :
    (∑ j, bdiff (facet18024f p j) (facet18024f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet18024f facet18024f_singleFlip p q

/-- The boundary input patterns map through `facet18024f` exactly to the bounded-region membership
pattern. -/
lemma facet18024f_boundary (c : Fin 6) :
    facet18024f (fun i => decide (c ∈ facet18024L_reg i)) = fun j => decide (c ∈ facet18024R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet18024f`. -/
lemma facet18024f_zero : facet18024f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet18024L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 7) :
    v ∈ facet18024L A i ↔ c ∈ facet18024L_reg i := by
  unfold facet18024L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet18024R A j ⊆ bd`. -/
lemma facet18024R_sub (hR : Regions6 bd A) (j : Fin 9) : facet18024R A j ⊆ bd := by
  unfold facet18024R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet18024L A i ⊆ bd`. -/
lemma facet18024L_sub (hR : Regions6 bd A) (i : Fin 7) : facet18024L A i ⊆ bd := by
  unfold facet18024L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet18024R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 9) :
    v ∈ facet18024R A j ↔ c ∈ facet18024R_reg j := by
  unfold facet18024R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_18024 (hR : Regions6 bd A)
    (X : Fin 7 → Finset V) (hX : ∀ i, IsRTCut bd (facet18024L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet18024L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet18024L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet18024L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet18024L A i := fun h => hc ((mem_facet18024L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_18024
    (X : Fin 7 → Finset V) (hX : ∀ i, IsRTCut bd (facet18024L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet18024L A i := by
    unfold facet18024L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet18024_hvalid (hR : Regions6 bd A)
    (X : Fin 7 → Finset V) (hX : ∀ i, IsRTCut bd (facet18024L A i) (X i)) (j : Fin 9) :
    IsRTCut bd (facet18024R A j) (contractionCut X facet18024f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet18024f j) v = mem (facet18024R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_18024 hR X hX hvc, facet18024f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet18024R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_18024 X hX hvbd hcolor, facet18024f_zero]
      have : v ∉ facet18024R A j := by
        unfold facet18024R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet18024R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 18024).**
For six pairwise-disjoint boundary regions `A₀,…,A₅` in any finite undirected
nonnegative-real-weighted graph, the 7 larger-side regions dominate the 9 bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(larger-regionᵢ)`.

This inequality is a facet of the six-party holographic entropy cone (source: the six-party
holographic entropy cone / Hernández-Cuenca holographic entropy cone database), proved here as an
instance of the general contraction-map engine `entropyR_ineq_of_contraction`. -/
theorem rtEntropyR_newFacet_n6_18024 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet18024R A j) (facet18024R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet18024L A i) (facet18024L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet18024L A i) S
      ∧ rtEntropyR G bd (facet18024L A i) (facet18024L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet18024L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet18024L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet18024L A i) (facet18024L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet18024R A j) (contractionCut X facet18024f j) :=
    fun j => facet18024_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet18024L A) (facet18024R A)
    (facet18024L_sub hR) (facet18024R_sub hR) X hXok facet18024f hvalid
    facet18024f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet18024R star6A j ⊆ star6Bd`. -/
lemma star6_facet18024R_sub (j : Fin 9) : facet18024R star6A j ⊆ star6Bd :=
  facet18024R_sub star6A_regions j
/-- `facet18024L star6A i ⊆ star6Bd`. -/
lemma star6_facet18024L_sub (i : Fin 7) : facet18024L star6A i ⊆ star6Bd :=
  facet18024L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet18024R (j : Fin 9) :
    rtEntropy star6Graph star6Bd (facet18024R star6A j) (star6_facet18024R_sub j)
      = ((![1, 1, 1, 2, 2, 2, 3, 3, 2] : Fin 9 → ℕ) j) := by
  fin_cases j <;> · unfold facet18024R facet18024R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet18024L (i : Fin 7) :
    rtEntropy star6Graph star6Bd (facet18024L star6A i) (star6_facet18024L_sub i)
      = ((![2, 3, 3, 3, 3, 3, 3] : Fin 7 → ℕ) i) := by
  fin_cases i <;> · unfold facet18024L facet18024L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to `17` and the larger side to `20` (slack `3`). -/
theorem rtEntropyR_newFacet_n6_18024_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet18024R star6A j)
        (facet18024R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet18024L star6A i)
        (facet18024L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet18024R star6A j)
      (facet18024R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 2, 2, 2, 3, 3, 2] : Fin 9 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet18024R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet18024L star6A i)
      (facet18024L_sub (A := star6A) star6A_regions i) = ((![2, 3, 3, 3, 3, 3, 3] : Fin 7 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet18024L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_18024_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet18024R star6A j)
        (facet18024R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet18024L star6A i)
        (facet18024L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet18024R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet18024L i]; fin_cases i <;> norm_num

end Facet6n18024

/-! ### A six-party holographic entropy cone facet (database index 59172)

A direct boolean contraction map with 8 larger-side regions and 9 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n59172

open Physlib.UndirectedMMICertificate.Facet6n174

-- facet 59172 (DIRECT 256-arm): L=8 R=9, 6-party colors 0..5
def facet59172L_reg : Fin 8 → Finset (Fin 6) := ![{0, 1, 2}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 5}, {1, 2, 4}, {1, 2, 5}]
def facet59172R_reg : Fin 9 → Finset (Fin 6) := ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 4}, {2, 5}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5}]
def facet59172f (p : Fin 8 → Bool) : Fin 9 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7 with
  | false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false]
  | false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, true, false, true => ![false, false, false, false, false, true, false, false, true]
  | false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, true, true, true => ![false, false, false, false, false, true, false, true, true]
  | false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, true, false, false]
  | false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, true, false, true]
  | false, false, false, false, true, true, false, true => ![false, false, false, false, false, true, true, false, true]
  | false, false, false, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, false, false, true, false => ![false, false, false, false, true, false, false, true, false]
  | false, false, false, true, false, false, true, true => ![false, false, false, false, true, false, false, true, true]
  | false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, false]
  | false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, false, false, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, true, false, false]
  | false, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, false, true]
  | false, false, true, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true]
  | false, false, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, false, false, false => ![false, false, true, false, false, false, true, false, false]
  | false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, true, false, false]
  | false, false, true, false, true, false, true, false => ![false, false, false, false, false, false, true, false, false]
  | false, false, true, false, true, false, true, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, true, false, true, true, false, false => ![false, false, true, false, false, false, true, false, true]
  | false, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, false, true]
  | false, false, true, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, true, false => ![false, false, false, false, true, false, true, true, false]
  | false, false, true, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, false, true, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, false => ![false, false, true, false, false, false, true, true, false]
  | false, false, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, false]
  | false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, false, true => ![false, false, false, false, false, true, false, true, true]
  | false, true, false, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, true, true => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, true, false => ![false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, true, true => ![false, false, false, true, false, true, true, true, true]
  | false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, false, true, false => ![false, false, false, false, true, false, false, true, true]
  | false, true, false, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, false, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, false, true => ![true, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | false, true, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, false => ![false, true, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | false, true, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | false, true, true, false, false, true, true, false => ![true, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, false, false => ![false, false, true, false, false, false, true, false, true]
  | false, true, true, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | false, true, true, false, true, false, true, false => ![false, false, false, false, false, false, true, false, true]
  | false, true, true, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, false, true, false => ![false, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, false, true, true => ![false, false, false, true, true, false, true, true, true]
  | false, true, true, true, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, true, true, true, false, false, false => ![false, false, true, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | false, true, true, true, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, true => ![false, true, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, true => ![false, true, false, true, false, false, true, true, true]
  | true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true]
  | true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, false, true => ![false, false, false, false, false, true, false, true, true]
  | true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, true, true, false => ![false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, true, true, true => ![false, false, false, true, false, true, true, true, true]
  | true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, false => ![false, false, false, false, true, false, false, true, true]
  | true, false, false, true, false, false, true, true => ![false, false, false, false, true, false, true, true, true]
  | true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, false, true => ![true, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, false, false => ![false, true, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true]
  | true, false, true, false, false, true, true, false => ![true, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, false => ![false, false, true, false, false, false, true, false, true]
  | true, false, true, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, true, false, true, false => ![false, false, false, false, false, false, true, false, true]
  | true, false, true, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, false, true, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | true, false, true, true, false, false, true, false => ![false, false, false, false, true, false, true, true, true]
  | true, false, true, true, false, false, true, true => ![false, false, false, true, true, false, true, true, true]
  | true, false, true, true, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, false, true, true, true, false, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, false, true, true, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, true => ![false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, true => ![false, true, false, true, false, false, true, true, true]
  | true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true]
  | true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, true, false, false, false, true, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, true, true, false => ![false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, true, true, true => ![false, false, false, true, false, true, true, true, true]
  | true, true, false, false, true, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, false, true => ![false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, false => ![false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, true => ![false, false, false, true, false, true, true, true, true]
  | true, true, false, false, true, true, false, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, false, true => ![false, true, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, true, false => ![false, true, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, true, true => ![false, true, false, true, false, true, true, true, true]
  | true, true, false, true, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, false, true, false, false, true, false => ![false, false, false, false, true, false, true, true, true]
  | true, true, false, true, false, false, true, true => ![false, false, false, true, true, false, true, true, true]
  | true, true, false, true, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, false, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, true, false, true, true, false, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, true, false, true, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, true => ![false, true, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, true, true => ![false, true, false, true, false, false, true, true, true]
  | true, true, true, false, false, false, false, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, false, true => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, false, false, false, true, false => ![false, false, false, false, true, false, true, true, true]
  | true, true, true, false, false, false, true, true => ![false, false, false, true, true, false, true, true, true]
  | true, true, true, false, false, true, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, true, false, false, true, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, true, true, false, true, false, false, false => ![false, false, true, false, false, false, true, true, true]
  | true, true, true, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, false => ![false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, true => ![false, false, false, true, false, false, true, true, true]
  | true, true, true, false, true, true, false, false => ![false, true, true, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, true => ![false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, false => ![false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, true => ![false, true, false, true, false, false, true, true, true]
  | true, true, true, true, false, false, false, false => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, false, true => ![true, false, false, false, true, false, true, true, true]
  | true, true, true, true, false, false, true, false => ![true, false, false, false, true, false, true, true, true]
  | true, true, true, true, false, false, true, true => ![true, false, false, true, true, false, true, true, true]
  | true, true, true, true, false, true, false, false => ![true, false, true, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, true => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, false => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, true => ![true, false, false, true, false, false, true, true, true]
  | true, true, true, true, true, false, false, false => ![true, false, true, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, true => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, false => ![true, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, true => ![true, false, false, true, false, false, true, true, true]
  | true, true, true, true, true, true, false, false => ![true, true, true, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, true => ![true, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, false => ![true, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, true => ![true, true, false, true, false, false, true, true, true]

variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th color set. -/
def facet59172L (A : Fin 6 → Finset V) (i : Fin 8) : Finset V := (facet59172L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th color set. -/
def facet59172R (A : Fin 6 → Finset V) (j : Fin 9) : Finset V := (facet59172R_reg j).biUnion A

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Single-flip (edge) nonexpansiveness of `facet59172f`.** Flipping any one of the 8 input
coordinates changes the 9-bit output by at most one Hamming unit, checked over all single-flip
edge cases. -/
theorem facet59172f_singleFlip :
    ∀ (p : Fin 8 → Bool) (i : Fin 8),
      (∑ j, bdiff (facet59172f p j) (facet59172f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide +kernel

/-- **Global nonexpansiveness of `facet59172f`, derived from the single-flip reduction.** -/
theorem facet59172f_nonexpansive_via_singleFlip (p q : Fin 8 → Bool) :
    (∑ j, bdiff (facet59172f p j) (facet59172f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet59172f facet59172f_singleFlip p q

/-- The boundary input patterns map through `facet59172f` exactly to the bounded-region membership
pattern. -/
lemma facet59172f_boundary (c : Fin 6) :
    facet59172f (fun i => decide (c ∈ facet59172L_reg i)) = fun j => decide (c ∈ facet59172R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet59172f`. -/
lemma facet59172f_zero : facet59172f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet59172L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 8) :
    v ∈ facet59172L A i ↔ c ∈ facet59172L_reg i := by
  unfold facet59172L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet59172R A j ⊆ bd`. -/
lemma facet59172R_sub (hR : Regions6 bd A) (j : Fin 9) : facet59172R A j ⊆ bd := by
  unfold facet59172R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet59172L A i ⊆ bd`. -/
lemma facet59172L_sub (hR : Regions6 bd A) (i : Fin 8) : facet59172L A i ⊆ bd := by
  unfold facet59172L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet59172R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 9) :
    v ∈ facet59172R A j ↔ c ∈ facet59172R_reg j := by
  unfold facet59172R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_59172 (hR : Regions6 bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet59172L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet59172L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet59172L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet59172L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet59172L A i := fun h => hc ((mem_facet59172L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_59172
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet59172L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet59172L A i := by
    unfold facet59172L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet59172_hvalid (hR : Regions6 bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet59172L A i) (X i)) (j : Fin 9) :
    IsRTCut bd (facet59172R A j) (contractionCut X facet59172f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet59172f j) v = mem (facet59172R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_59172 hR X hX hvc, facet59172f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet59172R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_59172 X hX hvbd hcolor, facet59172f_zero]
      have : v ∉ facet59172R A j := by
        unfold facet59172R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet59172R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 59172).**
For six pairwise-disjoint boundary regions `A₀,…,A₅` in any finite undirected
nonnegative-real-weighted graph, the 8 larger-side regions dominate the 9 bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(larger-regionᵢ)`.

This inequality is a facet of the six-party holographic entropy cone (source: the six-party
holographic entropy cone / Hernández-Cuenca holographic entropy cone database), proved here as an
instance of the general contraction-map engine `entropyR_ineq_of_contraction`. -/
theorem rtEntropyR_newFacet_n6_59172 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet59172R A j) (facet59172R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet59172L A i) (facet59172L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet59172L A i) S
      ∧ rtEntropyR G bd (facet59172L A i) (facet59172L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet59172L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet59172L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet59172L A i) (facet59172L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet59172R A j) (contractionCut X facet59172f j) :=
    fun j => facet59172_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet59172L A) (facet59172R A)
    (facet59172L_sub hR) (facet59172R_sub hR) X hXok facet59172f hvalid
    facet59172f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet59172R star6A j ⊆ star6Bd`. -/
lemma star6_facet59172R_sub (j : Fin 9) : facet59172R star6A j ⊆ star6Bd :=
  facet59172R_sub star6A_regions j
/-- `facet59172L star6A i ⊆ star6Bd`. -/
lemma star6_facet59172L_sub (i : Fin 8) : facet59172L star6A i ⊆ star6Bd :=
  facet59172L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet59172R (j : Fin 9) :
    rtEntropy star6Graph star6Bd (facet59172R star6A j) (star6_facet59172R_sub j)
      = ((![2, 2, 2, 2, 2, 2, 3, 3, 3] : Fin 9 → ℕ) j) := by
  fin_cases j <;> · unfold facet59172R facet59172R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet59172L (i : Fin 8) :
    rtEntropy star6Graph star6Bd (facet59172L star6A i) (star6_facet59172L_sub i)
      = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i) := by
  fin_cases i <;> · unfold facet59172L facet59172L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to `21` and the larger side to `24` (slack `3`). -/
theorem rtEntropyR_newFacet_n6_59172_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet59172R star6A j)
        (facet59172R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet59172L star6A i)
        (facet59172L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet59172R star6A j)
      (facet59172R_sub (A := star6A) star6A_regions j) = ((![2, 2, 2, 2, 2, 2, 3, 3, 3] : Fin 9 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet59172R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet59172L star6A i)
      (facet59172L_sub (A := star6A) star6A_regions i) = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet59172L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_59172_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet59172R star6A j)
        (facet59172R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet59172L star6A i)
        (facet59172L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet59172R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet59172L i]; fin_cases i <;> norm_num

end Facet6n59172

/-! ### A six-party holographic entropy cone facet (database index 6402)

A direct boolean contraction map with 8 larger-side regions and 10 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n6402

open Physlib.UndirectedMMICertificate.Facet6n174

-- facet 6402 (DIRECT 256-arm): L=8 R=10, 6-party colors 0..5
def facet6402L_reg : Fin 8 → Finset (Fin 6) := ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 5}, {1, 2, 3}, {1, 2, 3}, {1, 2, 4, 5}]
def facet6402R_reg : Fin 10 → Finset (Fin 6) := ![{0}, {0}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 5}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 4, 5}]
def facet6402f (p : Fin 8 → Bool) : Fin 10 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7 with
  | false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, false]
  | false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, false, true]
  | false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, true, false => ![false, false, false, false, false, true, false, true, true, false]
  | false, false, false, true, false, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, false, false, true, true, true, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, true, false, false, false, false, true => ![false, false, false, false, true, false, false, false, false, true]
  | false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, false, true, true => ![false, false, false, false, true, false, false, false, true, true]
  | false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, true, false, true => ![false, false, false, false, true, false, false, false, true, true]
  | false, false, true, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, false, true, false, true, false, false, false => ![true, false, false, false, false, false, false, false, false, true]
  | false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, true, false, true, false, true, false => ![true, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, true, false, false => ![true, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, true, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, true, true, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, false, true, true, false, false, false, true => ![false, false, false, false, true, false, false, true, false, true]
  | false, false, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, false, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, false, true, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, false => ![true, false, false, false, false, false, false, true, false, true]
  | false, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, false, true, true, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, true, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, true, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, true, false => ![false, false, false, true, false, false, false, true, true, false]
  | false, true, false, false, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, false, false, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, false, true, false => ![false, false, false, false, false, true, false, true, true, false]
  | false, true, false, true, false, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, true, false, true, false, false => ![false, false, false, false, false, true, false, true, true, false]
  | false, true, false, true, false, true, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, true, false, true, true, false => ![false, false, false, true, false, true, false, true, true, false]
  | false, true, false, true, false, true, true, true => ![false, false, false, true, false, true, false, true, true, true]
  | false, true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, false, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, true, true, false => ![false, false, false, true, false, true, false, true, true, true]
  | false, true, false, true, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, true, false, false, false, false, true => ![false, false, false, false, true, false, false, true, false, true]
  | false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, false, false, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | false, true, true, false, true, false, false, false => ![true, false, false, false, false, false, false, true, false, true]
  | false, true, true, false, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, true, false, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, true, false, false, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, false => ![false, false, false, true, false, true, false, true, true, true]
  | false, true, true, true, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, true => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, true => ![true, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, false]
  | true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, true, false, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | true, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, false, true, true, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, true, true => ![false, false, true, false, false, false, true, true, true, true]
  | true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, false, false, true, false, true, true, true => ![false, false, true, false, false, true, false, true, true, true]
  | true, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, true, true => ![false, false, true, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, false, true => ![false, false, true, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, true, false => ![false, false, true, false, false, true, false, true, true, true]
  | true, false, false, true, true, true, true, true => ![false, false, true, false, false, true, true, true, true, true]
  | true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, true, false, false, false, false, true => ![false, false, false, false, true, false, false, false, true, true]
  | true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, true, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, true => ![false, false, true, false, true, false, false, true, true, true]
  | true, false, true, false, true, false, false, false => ![true, false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, true, false, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, true => ![false, false, true, false, false, true, false, true, true, true]
  | true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | true, true, false, false, false, true, true, true => ![false, false, true, true, false, false, false, true, true, true]
  | true, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, false, true, false, false, true, true => ![false, false, true, false, false, true, false, true, true, true]
  | true, true, false, true, false, true, false, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, false, true, false, true, false, true => ![false, false, true, false, false, true, false, true, true, true]
  | true, true, false, true, false, true, true, false => ![false, false, false, true, false, true, false, true, true, true]
  | true, true, false, true, false, true, true, true => ![false, false, true, true, false, true, false, true, true, true]
  | true, true, false, true, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | true, true, false, true, true, true, true, true => ![false, false, true, false, false, true, false, true, true, true]
  | true, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, true, false, false, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, true, true => ![false, false, true, false, true, false, false, true, true, true]
  | true, true, true, false, false, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, false, true => ![false, false, true, false, true, false, false, true, true, true]
  | true, true, true, false, false, true, true, false => ![false, false, true, true, false, false, false, true, true, true]
  | true, true, true, false, false, true, true, true => ![false, false, true, true, true, false, false, true, true, true]
  | true, true, true, false, true, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, true, true => ![false, false, true, true, false, false, false, true, true, true]
  | true, true, true, true, false, false, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, false => ![false, false, false, true, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, true => ![false, false, true, true, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, false => ![true, true, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, true => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, true => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, false => ![true, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, true => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, true => ![false, false, true, false, false, false, false, true, true, true]

variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th color set. -/
def facet6402L (A : Fin 6 → Finset V) (i : Fin 8) : Finset V := (facet6402L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th color set. -/
def facet6402R (A : Fin 6 → Finset V) (j : Fin 10) : Finset V := (facet6402R_reg j).biUnion A

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Single-flip (edge) nonexpansiveness of `facet6402f`.** Flipping any one of the 8 input
coordinates changes the 10-bit output by at most one Hamming unit, checked over all single-flip
edge cases. -/
theorem facet6402f_singleFlip :
    ∀ (p : Fin 8 → Bool) (i : Fin 8),
      (∑ j, bdiff (facet6402f p j) (facet6402f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide +kernel

/-- **Global nonexpansiveness of `facet6402f`, derived from the single-flip reduction.** -/
theorem facet6402f_nonexpansive_via_singleFlip (p q : Fin 8 → Bool) :
    (∑ j, bdiff (facet6402f p j) (facet6402f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet6402f facet6402f_singleFlip p q

/-- The boundary input patterns map through `facet6402f` exactly to the bounded-region membership
pattern. -/
lemma facet6402f_boundary (c : Fin 6) :
    facet6402f (fun i => decide (c ∈ facet6402L_reg i)) = fun j => decide (c ∈ facet6402R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet6402f`. -/
lemma facet6402f_zero : facet6402f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet6402L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 8) :
    v ∈ facet6402L A i ↔ c ∈ facet6402L_reg i := by
  unfold facet6402L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet6402R A j ⊆ bd`. -/
lemma facet6402R_sub (hR : Regions6 bd A) (j : Fin 10) : facet6402R A j ⊆ bd := by
  unfold facet6402R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet6402L A i ⊆ bd`. -/
lemma facet6402L_sub (hR : Regions6 bd A) (i : Fin 8) : facet6402L A i ⊆ bd := by
  unfold facet6402L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet6402R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 10) :
    v ∈ facet6402R A j ↔ c ∈ facet6402R_reg j := by
  unfold facet6402R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_6402 (hR : Regions6 bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet6402L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet6402L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet6402L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet6402L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet6402L A i := fun h => hc ((mem_facet6402L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_6402
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet6402L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet6402L A i := by
    unfold facet6402L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet6402_hvalid (hR : Regions6 bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet6402L A i) (X i)) (j : Fin 10) :
    IsRTCut bd (facet6402R A j) (contractionCut X facet6402f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet6402f j) v = mem (facet6402R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_6402 hR X hX hvc, facet6402f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet6402R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_6402 X hX hvbd hcolor, facet6402f_zero]
      have : v ∉ facet6402R A j := by
        unfold facet6402R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet6402R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 6402).**
For six pairwise-disjoint boundary regions `A₀,…,A₅` in any finite undirected
nonnegative-real-weighted graph, the 8 larger-side regions dominate the 10 bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(larger-regionᵢ)`.

This inequality is a facet of the six-party holographic entropy cone (source: the six-party
holographic entropy cone / Hernández-Cuenca holographic entropy cone database), proved here as an
instance of the general contraction-map engine `entropyR_ineq_of_contraction`. -/
theorem rtEntropyR_newFacet_n6_6402 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet6402R A j) (facet6402R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet6402L A i) (facet6402L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet6402L A i) S
      ∧ rtEntropyR G bd (facet6402L A i) (facet6402L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet6402L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet6402L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet6402L A i) (facet6402L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet6402R A j) (contractionCut X facet6402f j) :=
    fun j => facet6402_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet6402L A) (facet6402R A)
    (facet6402L_sub hR) (facet6402R_sub hR) X hXok facet6402f hvalid
    facet6402f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet6402R star6A j ⊆ star6Bd`. -/
lemma star6_facet6402R_sub (j : Fin 10) : facet6402R star6A j ⊆ star6Bd :=
  facet6402R_sub star6A_regions j
/-- `facet6402L star6A i ⊆ star6Bd`. -/
lemma star6_facet6402L_sub (i : Fin 8) : facet6402L star6A i ⊆ star6Bd :=
  facet6402L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet6402R (j : Fin 10) :
    rtEntropy star6Graph star6Bd (facet6402R star6A j) (star6_facet6402R_sub j)
      = ((![1, 1, 2, 2, 2, 2, 2, 3, 3, 2] : Fin 10 → ℕ) j) := by
  fin_cases j <;> · unfold facet6402R facet6402R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet6402L (i : Fin 8) :
    rtEntropy star6Graph star6Bd (facet6402L star6A i) (star6_facet6402L_sub i)
      = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i) := by
  fin_cases i <;> · unfold facet6402L facet6402L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to `20` and the larger side to `24` (slack `4`). -/
theorem rtEntropyR_newFacet_n6_6402_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet6402R star6A j)
        (facet6402R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet6402L star6A i)
        (facet6402L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet6402R star6A j)
      (facet6402R_sub (A := star6A) star6A_regions j) = ((![1, 1, 2, 2, 2, 2, 2, 3, 3, 2] : Fin 10 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet6402R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet6402L star6A i)
      (facet6402L_sub (A := star6A) star6A_regions i) = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet6402L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_6402_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet6402R star6A j)
        (facet6402R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet6402L star6A i)
        (facet6402L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet6402R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet6402L i]; fin_cases i <;> norm_num

end Facet6n6402

/-! ### A six-party holographic entropy cone facet (database index 35246)

A direct boolean contraction map with 8 larger-side regions and 10 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n35246

open Physlib.UndirectedMMICertificate.Facet6n174

-- facet 35246 (DIRECT 256-arm): L=8 R=10, 6-party colors 0..5
def facet35246L_reg : Fin 8 → Finset (Fin 6) := ![{0, 1, 2}, {0, 2, 3}, {0, 2, 4}, {0, 3, 5}, {1, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3, 5}]
def facet35246R_reg : Fin 10 → Finset (Fin 6) := ![{0}, {1}, {0, 2}, {2, 3}, {2, 4}, {3, 4}, {3, 5}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 5}]
def facet35246f (p : Fin 8 → Bool) : Fin 10 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7 with
  | false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, false]
  | false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, false, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, false]
  | false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, false, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, false => ![false, false, false, false, false, true, false, true, true, false]
  | false, false, false, false, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, true, false, false, true]
  | false, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, true, false, false, true, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, true, false, true, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, true, false, true, true]
  | false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, false, false, true, true, true, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, false]
  | false, false, true, false, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, false => ![false, false, false, false, true, false, false, true, true, false]
  | false, false, true, false, false, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, true, false => ![false, false, false, false, true, false, false, true, true, false]
  | false, false, true, false, true, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, false, true, false, true, true, false, false => ![false, false, false, false, true, false, false, true, true, false]
  | false, false, true, false, true, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, false, true, false, true, true, true, false => ![false, false, false, false, true, true, false, true, true, false]
  | false, false, true, false, true, true, true, true => ![false, false, false, false, true, true, false, true, true, true]
  | false, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, false, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | false, false, true, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | false, false, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, false]
  | false, false, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, false]
  | false, false, true, true, true, true, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, true, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, false, true, true, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, false, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, false, false, true, true, true, true => ![false, false, false, true, false, true, false, true, true, true]
  | false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, false, true, false, false, false, true => ![false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, false, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | false, true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, false, true, true, false, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, true, true => ![false, false, false, false, false, true, true, true, true, true]
  | false, true, false, true, true, true, false, false => ![false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, false, true => ![false, false, false, false, false, true, true, true, true, true]
  | false, true, false, true, true, true, true, false => ![false, false, false, false, false, true, true, true, true, true]
  | false, true, false, true, true, true, true, true => ![false, false, false, true, false, true, true, true, true, true]
  | false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, true, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, true, true, false => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, false, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | false, true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, false, true, false, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, false, true, false, true, false => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, true, false, true, true => ![false, false, false, false, true, true, false, true, true, true]
  | false, true, true, false, true, true, false, false => ![false, false, false, false, true, false, false, true, true, true]
  | false, true, true, false, true, true, false, true => ![false, false, false, false, true, true, false, true, true, true]
  | false, true, true, false, true, true, true, false => ![false, false, false, false, true, true, false, true, true, true]
  | false, true, true, false, true, true, true, true => ![false, false, false, true, true, true, false, true, true, true]
  | false, true, true, true, false, false, false, false => ![false, false, true, false, false, false, false, true, false, true]
  | false, true, true, true, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, true, true, false, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | false, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | false, true, true, true, true, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, false, true, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | false, true, true, true, true, true, false, true => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, true, true, true, true, false => ![false, false, false, false, false, true, false, true, true, true]
  | false, true, true, true, true, true, true, true => ![false, false, false, true, false, true, false, true, true, true]
  | true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, false, true, false, false, true => ![false, true, false, false, false, false, false, false, true, true]
  | true, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true => ![false, true, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, true => ![false, true, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, false, false, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | true, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | true, false, false, true, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, true, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, true, true, false => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, false, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | true, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, true, false, true, false, true, false => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, false => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, false => ![false, false, false, false, true, false, false, true, true, false]
  | true, false, true, false, true, true, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, false, true, true, false, false, false, false => ![false, false, true, false, false, false, false, true, false, true]
  | true, false, true, true, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, true, true, false, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true]
  | true, false, true, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, true, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, false, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, false]
  | true, false, true, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, false, false, false, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, false, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, false, false, false, true, true, false => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, false, false, false, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | true, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true]
  | true, true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true]
  | true, true, false, false, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, false, true, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | true, true, false, true, false, false, false, false => ![false, false, true, false, false, false, false, true, false, true]
  | true, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, true, false, true, false, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, false, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, false, true, false, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, false, true, true, true => ![false, false, false, true, false, false, false, true, true, true]
  | true, true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, false, true, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, false, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, true, false => ![false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, true, true => ![false, false, false, true, false, false, true, true, true, true]
  | true, true, true, false, false, false, false, false => ![false, false, true, false, false, false, false, true, false, true]
  | true, true, true, false, false, false, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, false, false, true, true => ![false, false, true, false, true, false, false, true, true, true]
  | true, true, true, false, false, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, false, false, true, false, true => ![false, false, true, false, true, false, false, true, true, true]
  | true, true, true, false, false, true, true, false => ![false, false, true, false, true, false, false, true, true, true]
  | true, true, true, false, false, true, true, true => ![false, false, true, true, true, false, false, true, true, true]
  | true, true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, true, false, true]
  | true, true, true, false, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, false, true, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, true, false, true, true, false, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, false, true, true, false, true => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, true, false, true, true, true, false => ![false, false, false, false, true, false, false, true, true, true]
  | true, true, true, false, true, true, true, true => ![false, false, false, true, true, false, false, true, true, true]
  | true, true, true, true, false, false, false, false => ![true, false, true, false, false, false, false, true, false, true]
  | true, true, true, true, false, false, false, true => ![false, false, true, false, false, false, false, true, false, true]
  | true, true, true, true, false, false, true, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, false, true, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, false => ![true, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, false, true => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, false, true, true, true => ![false, false, true, true, false, false, false, true, true, true]
  | true, true, true, true, true, false, false, false => ![false, false, true, false, false, false, false, true, false, true]
  | true, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true]
  | true, true, true, true, true, false, true, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, false => ![false, false, true, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, true, true, true]
  | true, true, true, true, true, true, true, true => ![false, false, false, true, false, false, false, true, true, true]

variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th color set. -/
def facet35246L (A : Fin 6 → Finset V) (i : Fin 8) : Finset V := (facet35246L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th color set. -/
def facet35246R (A : Fin 6 → Finset V) (j : Fin 10) : Finset V := (facet35246R_reg j).biUnion A

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Single-flip (edge) nonexpansiveness of `facet35246f`.** Flipping any one of the 8 input
coordinates changes the 10-bit output by at most one Hamming unit, checked over all single-flip
edge cases. -/
theorem facet35246f_singleFlip :
    ∀ (p : Fin 8 → Bool) (i : Fin 8),
      (∑ j, bdiff (facet35246f p j) (facet35246f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide +kernel

/-- **Global nonexpansiveness of `facet35246f`, derived from the single-flip reduction.** -/
theorem facet35246f_nonexpansive_via_singleFlip (p q : Fin 8 → Bool) :
    (∑ j, bdiff (facet35246f p j) (facet35246f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet35246f facet35246f_singleFlip p q

/-- The boundary input patterns map through `facet35246f` exactly to the bounded-region membership
pattern. -/
lemma facet35246f_boundary (c : Fin 6) :
    facet35246f (fun i => decide (c ∈ facet35246L_reg i)) = fun j => decide (c ∈ facet35246R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet35246f`. -/
lemma facet35246f_zero : facet35246f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet35246L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 8) :
    v ∈ facet35246L A i ↔ c ∈ facet35246L_reg i := by
  unfold facet35246L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet35246R A j ⊆ bd`. -/
lemma facet35246R_sub (hR : Regions6 bd A) (j : Fin 10) : facet35246R A j ⊆ bd := by
  unfold facet35246R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet35246L A i ⊆ bd`. -/
lemma facet35246L_sub (hR : Regions6 bd A) (i : Fin 8) : facet35246L A i ⊆ bd := by
  unfold facet35246L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet35246R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 10) :
    v ∈ facet35246R A j ↔ c ∈ facet35246R_reg j := by
  unfold facet35246R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_35246 (hR : Regions6 bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet35246L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet35246L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet35246L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet35246L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet35246L A i := fun h => hc ((mem_facet35246L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_35246
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet35246L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet35246L A i := by
    unfold facet35246L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet35246_hvalid (hR : Regions6 bd A)
    (X : Fin 8 → Finset V) (hX : ∀ i, IsRTCut bd (facet35246L A i) (X i)) (j : Fin 10) :
    IsRTCut bd (facet35246R A j) (contractionCut X facet35246f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet35246f j) v = mem (facet35246R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_35246 hR X hX hvc, facet35246f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet35246R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_35246 X hX hvbd hcolor, facet35246f_zero]
      have : v ∉ facet35246R A j := by
        unfold facet35246R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet35246R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 35246).**
For six pairwise-disjoint boundary regions `A₀,…,A₅` in any finite undirected
nonnegative-real-weighted graph, the 8 larger-side regions dominate the 10 bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(larger-regionᵢ)`.

This inequality is a facet of the six-party holographic entropy cone (source: the six-party
holographic entropy cone / Hernández-Cuenca holographic entropy cone database), proved here as an
instance of the general contraction-map engine `entropyR_ineq_of_contraction`. -/
theorem rtEntropyR_newFacet_n6_35246 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet35246R A j) (facet35246R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet35246L A i) (facet35246L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet35246L A i) S
      ∧ rtEntropyR G bd (facet35246L A i) (facet35246L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet35246L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet35246L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet35246L A i) (facet35246L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet35246R A j) (contractionCut X facet35246f j) :=
    fun j => facet35246_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet35246L A) (facet35246R A)
    (facet35246L_sub hR) (facet35246R_sub hR) X hXok facet35246f hvalid
    facet35246f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet35246R star6A j ⊆ star6Bd`. -/
lemma star6_facet35246R_sub (j : Fin 10) : facet35246R star6A j ⊆ star6Bd :=
  facet35246R_sub star6A_regions j
/-- `facet35246L star6A i ⊆ star6Bd`. -/
lemma star6_facet35246L_sub (i : Fin 8) : facet35246L star6A i ⊆ star6Bd :=
  facet35246L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet35246R (j : Fin 10) :
    rtEntropy star6Graph star6Bd (facet35246R star6A j) (star6_facet35246R_sub j)
      = ((![1, 1, 2, 2, 2, 2, 2, 3, 3, 2] : Fin 10 → ℕ) j) := by
  fin_cases j <;> · unfold facet35246R facet35246R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet35246L (i : Fin 8) :
    rtEntropy star6Graph star6Bd (facet35246L star6A i) (star6_facet35246L_sub i)
      = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i) := by
  fin_cases i <;> · unfold facet35246L facet35246L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to `20` and the larger side to `24` (slack `4`). -/
theorem rtEntropyR_newFacet_n6_35246_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet35246R star6A j)
        (facet35246R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet35246L star6A i)
        (facet35246L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet35246R star6A j)
      (facet35246R_sub (A := star6A) star6A_regions j) = ((![1, 1, 2, 2, 2, 2, 2, 3, 3, 2] : Fin 10 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet35246R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet35246L star6A i)
      (facet35246L_sub (A := star6A) star6A_regions i) = ((![3, 3, 3, 3, 3, 3, 3, 3] : Fin 8 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet35246L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_35246_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet35246R star6A j)
        (facet35246R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet35246L star6A i)
        (facet35246L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet35246R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet35246L i]; fin_cases i <;> norm_num

end Facet6n35246




/-! ### A six-party holographic entropy cone facet (database index 1160)

A direct boolean contraction map with 9 larger-side regions and 12 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n1160

open Physlib.UndirectedMMICertificate.Facet6n174

def facet1160L_reg : Fin 9 → Finset (Fin 6) := ![{0, 3}, {0, 4}, {1, 2}, {0, 1, 5}, {0, 3, 5}, {1, 3, 5}, {1, 4, 5}, {0, 2, 4, 5}, {2, 3, 4, 5}]
def facet1160R_reg : Fin 12 → Finset (Fin 6) := ![{0}, {0}, {1}, {2}, {3}, {4}, {1, 5}, {3, 5}, {0, 4, 5}, {0, 1, 3, 5}, {1, 2, 4, 5}, {0, 2, 3, 4, 5}]
def facet1160f (p : Fin 9 → Bool) : Fin 12 → Bool :=
  match p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8 with
  | false, false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, false, false, false]
  | false, false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, false, false, false, true]
  | false, false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, false, false, true, false]
  | false, false, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, false, false, false, true, true]
  | false, false, false, false, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, false, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, false]
  | false, false, false, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, false, false, false, true, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, false, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, false]
  | false, false, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true, false, true]
  | false, false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | false, false, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | false, false, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, false, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, false]
  | false, false, false, true, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, false, true, false, false, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, false, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, false, true, true, false, false => ![false, false, false, false, false, false, true, false, false, true, true, false]
  | false, false, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, false, true, false, true, true, true, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, false, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | false, false, false, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, false, false, true, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, false, true, false, true => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, false, true, true, false, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, false, true, true, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, false, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | false, false, false, true, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, false, false, true, true, true, true, false, false => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, false, true, true, true, true, false, true => ![false, false, false, false, false, false, true, true, false, true, true, true]
  | false, false, false, true, true, true, true, true, false => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, false, false, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true, true, true]
  | false, false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, false, true, false]
  | false, false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, false, false, true, true => ![false, false, false, true, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, false, true, false, false => ![false, false, true, false, false, false, false, false, false, false, true, false]
  | false, false, true, false, false, false, true, false, true => ![false, false, true, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, false, true, true, false => ![false, false, true, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, false, true, true, true => ![false, false, false, false, false, false, false, false, false, false, true, true]
  | false, false, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, false, true, true => ![false, false, false, true, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, false, true, true, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, false, true, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, false, true, true => ![false, false, false, true, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, false]
  | false, false, true, false, true, false, true, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, true, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, false, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | false, false, true, false, true, true, false, true, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | false, false, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | false, false, true, true, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, false, true, true => ![false, false, false, true, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, false]
  | false, false, true, true, false, false, true, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, true, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, false, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, false, false => ![false, false, true, false, false, false, false, false, false, true, true, false]
  | false, false, true, true, false, true, false, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, false, true, true, false, false => ![false, false, true, false, false, false, true, false, false, true, true, false]
  | false, false, true, true, false, true, true, false, true => ![false, false, true, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, false, true, true, true, false => ![false, false, true, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, false, true, true, true, true => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, false, true => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, false, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, false, true, true, true => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, true, true, false, false, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | false, false, true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | false, false, true, true, true, true, true, false, false => ![false, false, true, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, true, true, true, false, true => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, true, true, true, true, false => ![false, false, false, false, false, false, true, false, false, true, true, true]
  | false, false, true, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, false, true, true, true]
  | false, true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, false, false, false]
  | false, true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, false, false, true]
  | false, true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, false, false, true]
  | false, true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, false, true, false]
  | false, true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, true, false, false, false, false, true, true, true => ![false, false, false, false, false, true, false, false, true, false, true, true]
  | false, true, false, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, false]
  | false, true, false, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, false, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, false, false, false, true, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, false, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, false, true, true, true, true => ![false, false, false, false, false, true, false, false, true, true, true, true]
  | false, true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, false]
  | false, true, false, false, true, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, true, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, false, false, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, false, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, false, true, true, true => ![false, false, false, false, false, true, false, false, true, true, true, true]
  | false, true, false, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true, false, true]
  | false, true, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, true, false, false, true, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, true, false, false, true, true, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, false, true, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, false]
  | false, true, false, true, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, false, true, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, false, true, true, true => ![false, false, false, false, false, true, false, false, true, true, true, true]
  | false, true, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, false, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, false, true, true, false, false => ![false, false, false, false, false, false, true, false, true, true, true, false]
  | false, true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, false, true, false, true, true, true, false => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, false, true, false, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | false, true, false, true, true, false, false, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, false, true, true, false, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, true, false, true, true, true, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, false, true, true, true, true, false, false => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, false, true, true, true, true, false, true => ![false, false, false, false, false, false, true, true, true, true, true, true]
  | false, true, false, true, true, true, true, true, false => ![true, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, false, true, true, true, true, true, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, false, true, false]
  | false, true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, true, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, true, true, false, false, false, false, true, true => ![false, false, false, true, false, false, false, false, true, false, true, true]
  | false, true, true, false, false, false, true, false, false => ![false, false, true, false, false, false, false, false, true, false, true, false]
  | false, true, true, false, false, false, true, false, true => ![false, false, true, false, false, false, false, false, true, false, true, true]
  | false, true, true, false, false, false, true, true, false => ![false, false, true, false, false, false, false, false, true, false, true, true]
  | false, true, true, false, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, false, true, true]
  | false, true, true, false, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, true, false, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, false, true, true => ![false, false, false, true, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, false]
  | false, true, true, false, false, true, true, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, true, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, false, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, true, false, true, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, false, true, true => ![false, false, false, true, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, false]
  | false, true, true, false, true, false, true, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, true, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, true, true, false, true, true, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, true, true, true, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | false, true, true, true, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, false, true, true => ![false, false, false, true, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, false]
  | false, true, true, true, false, false, true, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, true, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, false, false, false => ![false, false, true, false, false, false, false, false, true, true, true, false]
  | false, true, true, true, false, true, false, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, false, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, false, true, true, false, false => ![false, false, true, false, false, false, true, false, true, true, true, false]
  | false, true, true, true, false, true, true, false, true => ![false, false, true, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, false, true, true, true, false => ![false, false, true, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, false, true, true, true, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, false, false, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, false, true, true, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, true, false, false, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | false, true, true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | false, true, true, true, true, true, true, false, false => ![false, false, true, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, true, true, false, true => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, true, true, true, false => ![false, false, false, false, false, false, true, false, true, true, true, true]
  | false, true, true, true, true, true, true, true, true => ![false, false, false, false, false, false, true, true, true, true, true, true]
  | true, false, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, false]
  | true, false, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | true, false, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, false, false, false, true, false, false, false => ![false, false, false, false, true, false, false, false, false, true, false, false]
  | true, false, false, false, false, true, false, false, true => ![false, false, false, false, true, false, false, false, false, true, false, true]
  | true, false, false, false, false, true, false, true, false => ![false, false, false, false, true, false, false, false, false, true, false, true]
  | true, false, false, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, false, true, true, false, false => ![false, false, false, false, true, false, false, false, false, true, true, false]
  | true, false, false, false, false, true, true, false, true => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, true, false => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, false, false, false, true, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, false, false, true => ![false, false, false, false, true, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, false, true, false => ![true, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, false, true => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, false, false, false => ![false, false, false, false, true, false, false, false, false, true, false, true]
  | true, false, false, false, true, true, false, false, true => ![false, false, false, false, true, false, false, true, false, true, false, true]
  | true, false, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, false, true, false, true]
  | true, false, false, false, true, true, true, false, false => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, true, false, true => ![false, false, false, false, true, false, false, true, false, true, true, true]
  | true, false, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | true, false, false, true, false, false, false, false, false => ![true, false, false, false, false, false, false, false, false, true, false, false]
  | true, false, false, true, false, false, false, false, true => ![true, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, false, false, true, false => ![true, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, false, true, false, false => ![true, false, false, false, false, false, false, false, false, true, true, false]
  | true, false, false, true, false, false, true, false, true => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, true, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, false, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, false]
  | true, false, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, false, true, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | true, false, false, true, false, true, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, false, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, false, false, false, false => ![true, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, true, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, true, false, true, false, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, false, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, false, true]
  | true, false, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true, false, true]
  | true, false, false, true, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, false, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, false, true]
  | true, false, false, true, true, true, true, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, false, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | true, false, false, true, true, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, false, true, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | true, false, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | true, false, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, false, true, true => ![false, false, false, true, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, false]
  | true, false, true, false, false, false, true, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, false, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, false, false => ![false, false, false, false, true, false, false, false, false, true, true, false]
  | true, false, true, false, false, true, false, false, true => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, true, false => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, false, false => ![false, false, true, false, true, false, false, false, false, true, true, false]
  | true, false, true, false, false, true, true, false, true => ![false, false, true, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, true, false => ![false, false, true, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, false, true, true, true, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, false, true => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, true, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, false, true => ![false, false, true, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, true, false => ![true, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, false, true, true, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, false, false => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, false, true => ![false, false, false, false, true, false, false, true, false, true, true, true]
  | true, false, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | true, false, true, false, true, true, true, false, false => ![false, false, true, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, false, true => ![false, false, false, false, true, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, false, true, true, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, false, false => ![true, false, false, false, false, false, false, false, false, true, true, false]
  | true, false, true, true, false, false, false, false, true => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, true, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, false, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, false, false => ![true, false, true, false, false, false, false, false, false, true, true, false]
  | true, false, true, true, false, false, true, false, true => ![true, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, true, false => ![true, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, false, true, true, true => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, false]
  | true, false, true, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, false, true, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, false]
  | true, false, true, true, false, true, true, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, true, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, false, true, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, false, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, false, true, false, false => ![true, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, false, true => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true, false => ![true, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, false, true, true, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, false, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | true, false, true, true, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, false, true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | true, false, true, true, true, true, true, false, false => ![false, false, true, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, false, true => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, false, false, true, true, true]
  | true, false, true, true, true, true, true, true, true => ![false, false, false, false, false, false, false, true, false, true, true, true]
  | true, true, false, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, false]
  | true, true, false, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | true, true, false, false, false, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, false, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, false, false, true, true, true => ![false, false, false, false, false, true, false, false, true, true, true, true]
  | true, true, false, false, false, true, false, false, false => ![false, false, false, false, true, false, false, false, true, true, false, false]
  | true, true, false, false, false, true, false, false, true => ![false, false, false, false, true, false, false, false, true, true, false, true]
  | true, true, false, false, false, true, false, true, false => ![false, false, false, false, true, false, false, false, true, true, false, true]
  | true, true, false, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, false, true, true, false, false => ![false, false, false, false, true, false, false, false, true, true, true, false]
  | true, true, false, false, false, true, true, false, true => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, false, false, false, true, true, true, false => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, false, false, false, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, true, false, false, false, true => ![false, false, false, false, true, false, false, false, true, true, false, true]
  | true, true, false, false, true, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, true, false, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, false, true => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, false, false, false => ![false, false, false, false, true, false, false, false, true, true, false, true]
  | true, true, false, false, true, true, false, false, true => ![false, false, false, false, true, false, false, true, true, true, false, true]
  | true, true, false, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, false, true]
  | true, true, false, false, true, true, true, false, false => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, true, false, true => ![false, false, false, false, true, false, false, true, true, true, true, true]
  | true, true, false, false, true, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, false, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | true, true, false, true, false, false, false, false, false => ![true, false, false, false, false, false, false, false, true, true, false, false]
  | true, true, false, true, false, false, false, false, true => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, false, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, false, false, true, false, false => ![true, false, false, false, false, false, false, false, true, true, true, false]
  | true, true, false, true, false, false, true, false, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, false, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, false]
  | true, true, false, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, false, true, false, true, true => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, false, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | true, true, false, true, false, true, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, false, true, true, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, false, false, false => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, false, false, true, false => ![true, true, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, false, false, true, true => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, false, true, false, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, true, true, false => ![true, true, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, false, true, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true, false, true]
  | true, true, false, true, true, true, false, true, false => ![true, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, false, true]
  | true, true, false, true, true, true, true, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, true, false, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | true, true, false, true, true, true, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, false, true, true, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | true, true, true, false, false, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, false, true, true => ![false, false, false, true, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, false]
  | true, true, true, false, false, false, true, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, true, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, false, false, false => ![false, false, false, false, true, false, false, false, true, true, true, false]
  | true, true, true, false, false, true, false, false, true => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, false, true, false => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, true, false, false => ![false, false, true, false, true, false, false, false, true, true, true, false]
  | true, true, true, false, false, true, true, false, true => ![false, false, true, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, true, true, false => ![false, false, true, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, false, true, true, true, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, false, false, true => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, true, false, true => ![false, false, true, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, true, true, false => ![true, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, false, true, true, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, false, false, false => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, false, false, true => ![false, false, false, false, true, false, false, true, true, true, true, true]
  | true, true, true, false, true, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, false, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | true, true, true, false, true, true, true, false, false => ![false, false, true, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, true, false, true => ![false, false, false, false, true, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, true, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, false, true, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, false, false, false => ![true, false, false, false, false, false, false, false, true, true, true, false]
  | true, true, true, true, false, false, false, false, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, true, false, false => ![true, false, true, false, false, false, false, false, true, true, true, false]
  | true, true, true, true, false, false, true, false, true => ![true, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, true, true, false => ![true, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, false, true, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, false]
  | true, true, true, true, false, true, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, false, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, false, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, false]
  | true, true, true, true, false, true, true, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, true, true, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, false, true, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, false, false, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, false, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, false, true, false => ![true, true, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, false, true, true => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, false, false => ![true, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, false, true => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, false, true, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, false, false, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, false, false, true => ![false, false, false, false, false, false, false, true, true, true, true, true]
  | true, true, true, true, true, true, false, true, false => ![true, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, false, true, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, true, false, false => ![false, false, true, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, true, false, true => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, true, true, false => ![false, false, false, false, false, false, false, false, true, true, true, true]
  | true, true, true, true, true, true, true, true, true => ![false, false, false, false, false, false, false, true, true, true, true, true]

variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region: the union of the elementary regions in the `i`-th color set. -/
def facet1160L (A : Fin 6 → Finset V) (i : Fin 9) : Finset V := (facet1160L_reg i).biUnion A

/-- The `j`-th bounded-side region: the union of the elementary regions in the `j`-th color set. -/
def facet1160R (A : Fin 6 → Finset V) (j : Fin 12) : Finset V := (facet1160R_reg j).biUnion A

set_option maxHeartbeats 0 in
/-- **Single-flip (edge) nonexpansiveness of `facet1160f`.** Flipping any one of the 9 input
coordinates changes the 12-bit output by at most one Hamming unit, checked over all single-flip
edge cases. -/
theorem facet1160f_singleFlip :
    ∀ (p : Fin 9 → Bool) (i : Fin 9),
      (∑ j, bdiff (facet1160f p j) (facet1160f (Function.update p i (!(p i))) j)) ≤ 1 := by
  decide +kernel

/-- **Global nonexpansiveness of `facet1160f`, derived from the single-flip reduction.** -/
theorem facet1160f_nonexpansive_via_singleFlip (p q : Fin 9 → Bool) :
    (∑ j, bdiff (facet1160f p j) (facet1160f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet1160f facet1160f_singleFlip p q

/-- The boundary input patterns map through `facet1160f` exactly to the bounded-region membership
pattern. -/
lemma facet1160f_boundary (c : Fin 6) :
    facet1160f (fun i => decide (c ∈ facet1160L_reg i)) = fun j => decide (c ∈ facet1160R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern (all `false`) maps to all `false` under `facet1160f`. -/
lemma facet1160f_zero : facet1160f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet1160L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 9) :
    v ∈ facet1160L A i ↔ c ∈ facet1160L_reg i := by
  unfold facet1160L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet1160R A j ⊆ bd`. -/
lemma facet1160R_sub (hR : Regions6 bd A) (j : Fin 12) : facet1160R A j ⊆ bd := by
  unfold facet1160R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet1160L A i ⊆ bd`. -/
lemma facet1160L_sub (hR : Regions6 bd A) (i : Fin 9) : facet1160L A i ⊆ bd := by
  unfold facet1160L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet1160R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 12) :
    v ∈ facet1160R A j ↔ c ∈ facet1160R_reg j := by
  unfold facet1160R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_1160 (hR : Regions6 bd A)
    (X : Fin 9 → Finset V) (hX : ∀ i, IsRTCut bd (facet1160L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet1160L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet1160L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet1160L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet1160L A i := fun h => hc ((mem_facet1160L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_1160
    (X : Fin 9 → Finset V) (hX : ∀ i, IsRTCut bd (facet1160L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet1160L A i := by
    unfold facet1160L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet1160_hvalid (hR : Regions6 bd A)
    (X : Fin 9 → Finset V) (hX : ∀ i, IsRTCut bd (facet1160L A i) (X i)) (j : Fin 12) :
    IsRTCut bd (facet1160R A j) (contractionCut X facet1160f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet1160f j) v = mem (facet1160R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_1160 hR X hX hvc, facet1160f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet1160R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_1160 X hX hvbd hcolor, facet1160f_zero]
      have : v ∉ facet1160R A j := by
        unfold facet1160R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet1160R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 1160).**
For six pairwise-disjoint boundary regions `A₀,…,A₅` in any finite undirected
nonnegative-real-weighted graph, the 9 larger-side regions dominate the 12 bounded-side regions:

  `∑ⱼ S(regionⱼ) ≤ ∑ᵢ S(larger-regionᵢ)`.

This inequality is a facet of the six-party holographic entropy cone (source: the six-party
holographic entropy cone / Hernández-Cuenca holographic entropy cone database), proved here as an
instance of the general contraction-map engine `entropyR_ineq_of_contraction`. -/
theorem rtEntropyR_newFacet_n6_1160 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet1160R A j) (facet1160R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet1160L A i) (facet1160L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet1160L A i) S
      ∧ rtEntropyR G bd (facet1160L A i) (facet1160L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet1160L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet1160L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet1160L A i) (facet1160L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet1160R A j) (contractionCut X facet1160f j) :=
    fun j => facet1160_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet1160L A) (facet1160R A)
    (facet1160L_sub hR) (facet1160R_sub hR) X hXok facet1160f hvalid
    facet1160f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet1160R star6A j ⊆ star6Bd`. -/
lemma star6_facet1160R_sub (j : Fin 12) : facet1160R star6A j ⊆ star6Bd :=
  facet1160R_sub star6A_regions j
/-- `facet1160L star6A i ⊆ star6Bd`. -/
lemma star6_facet1160L_sub (i : Fin 9) : facet1160L star6A i ⊆ star6Bd :=
  facet1160L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet1160R (j : Fin 12) :
    rtEntropy star6Graph star6Bd (facet1160R star6A j) (star6_facet1160R_sub j)
      = ((![1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2] : Fin 12 → ℕ) j) := by
  fin_cases j <;> · unfold facet1160R facet1160R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet1160L (i : Fin 9) :
    rtEntropy star6Graph star6Bd (facet1160L star6A i) (star6_facet1160L_sub i)
      = ((![2, 2, 2, 3, 3, 3, 3, 3, 3] : Fin 9 → ℕ) i) := by
  fin_cases i <;> · unfold facet1160L facet1160L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to `21` and the larger side to `24` (slack `3`). -/
theorem rtEntropyR_newFacet_n6_1160_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet1160R star6A j)
        (facet1160R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet1160L star6A i)
        (facet1160L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet1160R star6A j)
      (facet1160R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2] : Fin 12 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet1160R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet1160L star6A i)
      (facet1160L_sub (A := star6A) star6A_regions i) = ((![2, 2, 2, 3, 3, 3, 3, 3, 3] : Fin 9 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet1160L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_1160_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet1160R star6A j)
        (facet1160R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet1160L star6A i)
        (facet1160L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet1160R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet1160L i]; fin_cases i <;> norm_num

end Facet6n1160

/-! ### A six-party holographic entropy cone facet (database index 1411)

A count-lattice boolean contraction map with 10 larger-side regions and 13 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n1411

open Physlib.UndirectedMMICertificate.Facet6n174

def facet1411L_reg : Fin 10 → Finset (Fin 6) := ![{0, 3}, {1, 2}, {0, 1, 4}, {0, 1, 5}, {1, 3, 4}, {0, 1, 2, 3}, {0, 2, 3, 4}, {0, 2, 3, 5}, {1, 2, 3, 5}, {1, 2, 3, 5}]
def facet1411R_reg : Fin 13 → Finset (Fin 6) := ![{0}, {0}, {1}, {2}, {3}, {1, 4}, {1, 5}, {0, 3, 4}, {1, 2, 3}, {2, 3, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 5}]

/-! Block-popcount accessors (definitional). -/
@[simp] lemma bp1411_0 (p : Fin 10 → Bool) : facet1411blockPopcounts p 0 = facet1411bit p 0 := rfl
@[simp] lemma bp1411_1 (p : Fin 10 → Bool) : facet1411blockPopcounts p 1 = facet1411bit p 1 := rfl
@[simp] lemma bp1411_2 (p : Fin 10 → Bool) : facet1411blockPopcounts p 2 = facet1411bit p 2 := rfl
@[simp] lemma bp1411_3 (p : Fin 10 → Bool) : facet1411blockPopcounts p 3 = facet1411bit p 3 := rfl
@[simp] lemma bp1411_4 (p : Fin 10 → Bool) : facet1411blockPopcounts p 4 = facet1411bit p 4 := rfl
@[simp] lemma bp1411_5 (p : Fin 10 → Bool) : facet1411blockPopcounts p 5 = facet1411bit p 5 := rfl
@[simp] lemma bp1411_6 (p : Fin 10 → Bool) : facet1411blockPopcounts p 6 = facet1411bit p 6 := rfl
@[simp] lemma bp1411_7 (p : Fin 10 → Bool) : facet1411blockPopcounts p 7 = facet1411bit p 7 := rfl
@[simp] lemma bp1411_8 (p : Fin 10 → Bool) : facet1411blockPopcounts p 8 = facet1411bit p 8 + facet1411bit p 9 := rfl

lemma facet1411f_eq (p : Fin 10 → Bool) :
    facet1411f p = facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) := rfl

lemma facet1411bit_le_one (p : Fin 10 → Bool) (i : Fin 10) : facet1411bit p i ≤ 1 := by
  unfold facet1411bit; split_ifs <;> omega
lemma facet1411bit_eq_zero_of_false (p : Fin 10 → Bool) (i : Fin 10) (hp : p i = false) :
    facet1411bit p i = 0 := by
  unfold facet1411bit; rw [hp]; simp

macro "bpLoose1411" x:term : tactic =>
  `(tactic|
    (simp only [bp1411_0, bp1411_1, bp1411_2, bp1411_3, bp1411_4, bp1411_5, bp1411_6, bp1411_7, bp1411_8]
     have _hb0 := facet1411bit_le_one $x 0
     have _hb1 := facet1411bit_le_one $x 1
     have _hb2 := facet1411bit_le_one $x 2
     have _hb3 := facet1411bit_le_one $x 3
     have _hb4 := facet1411bit_le_one $x 4
     have _hb5 := facet1411bit_le_one $x 5
     have _hb6 := facet1411bit_le_one $x 6
     have _hb7 := facet1411bit_le_one $x 7
     have _hb8 := facet1411bit_le_one $x 8
     have _hb9 := facet1411bit_le_one $x 9
     omega))
macro "bpStrict1411" x:term "," h:ident : tactic =>
  `(tactic|
    (simp only [bp1411_0, bp1411_1, bp1411_2, bp1411_3, bp1411_4, bp1411_5, bp1411_6, bp1411_7, bp1411_8,
       facet1411bit_eq_zero_of_false $x _ $h]
     have _hb0 := facet1411bit_le_one $x 0
     have _hb1 := facet1411bit_le_one $x 1
     have _hb2 := facet1411bit_le_one $x 2
     have _hb3 := facet1411bit_le_one $x 3
     have _hb4 := facet1411bit_le_one $x 4
     have _hb5 := facet1411bit_le_one $x 5
     have _hb6 := facet1411bit_le_one $x 6
     have _hb7 := facet1411bit_le_one $x 7
     have _hb8 := facet1411bit_le_one $x 8
     have _hb9 := facet1411bit_le_one $x 9
     omega))

set_option maxHeartbeats 2000000 in
/-- **Single-flip (edge) nonexpansiveness of `facet1411f`.** -/
theorem facet1411f_singleFlip :
    ∀ (p : Fin 10 → Bool) (i : Fin 10),
      (∑ j, bdiff (facet1411f p j) (facet1411f (Function.update p i (!(p i))) j)) ≤ 1 := by
  intro p i
  fin_cases i
  · -- flip input bit 0 (block 0)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 0 (!(p 0))) j)) ≤ 1
    set q := Function.update p 0 (!(p 0)) with hq
    have hother : ∀ x : Fin 10, x ≠ 0 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 0 with
    | false =>
      have hqi : q 0 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp1411_0, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_0, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_0 (facet1411blockPopcounts p 0) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 0 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet1411blockPopcounts q 0 + 1 = facet1411blockPopcounts p 0 := by
        first
        | (simp only [bp1411_0, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_0, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e1, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts q 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts q 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet1411G_lip_0 (facet1411blockPopcounts q 0) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 1 (block 1)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 1 (!(p 1))) j)) ≤ 1
    set q := Function.update p 1 (!(p 1)) with hq
    have hother : ∀ x : Fin 10, x ≠ 1 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 1 with
    | false =>
      have hqi : q 1 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1411_1, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_1, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_1 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 1 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1411blockPopcounts q 1 + 1 = facet1411blockPopcounts p 1 := by
        first
        | (simp only [bp1411_1, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_1, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts q 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts q 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet1411G_lip_1 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts q 1) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 2 (block 2)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 2 (!(p 2))) j)) ≤ 1
    set q := Function.update p 2 (!(p 2)) with hq
    have hother : ∀ x : Fin 10, x ≠ 2 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 2 with
    | false =>
      have hqi : q 2 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 + 1 := by
        first
        | (simp only [bp1411_2, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_2, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_2 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 2 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet1411blockPopcounts q 2 + 1 = facet1411blockPopcounts p 2 := by
        first
        | (simp only [bp1411_2, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_2, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts q 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts q 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e2]
      exact facet1411G_lip_2 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts q 2) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 3 (block 3)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 3 (!(p 3))) j)) ≤ 1
    set q := Function.update p 3 (!(p 3)) with hq
    have hother : ∀ x : Fin 10, x ≠ 3 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 3 with
    | false =>
      have hqi : q 3 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 + 1 := by
        first
        | (simp only [bp1411_3, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_3, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_3 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 3 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet1411blockPopcounts q 3 + 1 = facet1411blockPopcounts p 3 := by
        first
        | (simp only [bp1411_3, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_3, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts q 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts q 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e3]
      exact facet1411G_lip_3 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts q 3) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 4 (block 4)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 4 (!(p 4))) j)) ≤ 1
    set q := Function.update p 4 (!(p 4)) with hq
    have hother : ∀ x : Fin 10, x ≠ 4 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 4 with
    | false =>
      have hqi : q 4 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp1411_4, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_4, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_4 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 4 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet1411blockPopcounts q 4 + 1 = facet1411blockPopcounts p 4 := by
        first
        | (simp only [bp1411_4, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_4, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts q 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts q 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet1411G_lip_4 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts q 4) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 5 (block 5)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 5 (!(p 5))) j)) ≤ 1
    set q := Function.update p 5 (!(p 5)) with hq
    have hother : ∀ x : Fin 10, x ≠ 5 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 5 with
    | false =>
      have hqi : q 5 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp1411_5, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_5, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_5 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 5 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet1411blockPopcounts q 5 + 1 = facet1411blockPopcounts p 5 := by
        first
        | (simp only [bp1411_5, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_5, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e6, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts q 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts q 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet1411G_lip_5 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts q 5) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 6 (block 6)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 6 (!(p 6))) j)) ≤ 1
    set q := Function.update p 6 (!(p 6)) with hq
    have hother : ∀ x : Fin 10, x ≠ 6 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 6 with
    | false =>
      have hqi : q 6 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp1411_6, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_6, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_6 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 6 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet1411blockPopcounts q 6 + 1 = facet1411blockPopcounts p 6 := by
        first
        | (simp only [bp1411_6, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_6, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e7, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts q 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts q 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet1411G_lip_6 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts q 6) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 7 (block 7)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 7 (!(p 7))) j)) ≤ 1
    set q := Function.update p 7 (!(p 7)) with hq
    have hother : ∀ x : Fin 10, x ≠ 7 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 := by
      simp only [bp1411_8, facet1411bit, hother 8 (by decide), hother 9 (by decide)]
    cases hpi : p 7 with
    | false =>
      have hqi : q 7 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 + 1 := by
        first
        | (simp only [bp1411_7, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_7, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_7 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpStrict1411 p, hpi) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
    | true =>
      have hqi : q 7 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet1411blockPopcounts q 7 + 1 = facet1411blockPopcounts p 7 := by
        first
        | (simp only [bp1411_7, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_7, facet1411bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e8]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts q 7) (facet1411blockPopcounts p 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts q 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e7]
      exact facet1411G_lip_7 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts q 7) (by bpStrict1411 q, hqi) (facet1411blockPopcounts p 8) (by bpLoose1411 p)
  · -- flip input bit 8 (block 8)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 8 (!(p 8))) j)) ≤ 1
    set q := Function.update p 8 (!(p 8)) with hq
    have hother : ∀ x : Fin 10, x ≠ 8 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    cases hpi : p 8 with
    | false =>
      have hqi : q 8 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp1411_8, facet1411bit, hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_8, facet1411bit, hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_8 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpStrict1411 p, hpi)
    | true =>
      have hqi : q 8 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet1411blockPopcounts q 8 + 1 = facet1411blockPopcounts p 8 := by
        first
        | (simp only [bp1411_8, facet1411bit, hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_8, facet1411bit, hother 9 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts q 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts q 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet1411G_lip_8 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts q 8) (by bpStrict1411 q, hqi)
  · -- flip input bit 9 (block 8)
    show (∑ j, bdiff (facet1411f p j)
          (facet1411f (Function.update p 9 (!(p 9))) j)) ≤ 1
    set q := Function.update p 9 (!(p 9)) with hq
    have hother : ∀ x : Fin 10, x ≠ 9 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1411blockPopcounts q 0 = facet1411blockPopcounts p 0 := by
      simp only [bp1411_0, facet1411bit, hother 0 (by decide)]
    have e1 : facet1411blockPopcounts q 1 = facet1411blockPopcounts p 1 := by
      simp only [bp1411_1, facet1411bit, hother 1 (by decide)]
    have e2 : facet1411blockPopcounts q 2 = facet1411blockPopcounts p 2 := by
      simp only [bp1411_2, facet1411bit, hother 2 (by decide)]
    have e3 : facet1411blockPopcounts q 3 = facet1411blockPopcounts p 3 := by
      simp only [bp1411_3, facet1411bit, hother 3 (by decide)]
    have e4 : facet1411blockPopcounts q 4 = facet1411blockPopcounts p 4 := by
      simp only [bp1411_4, facet1411bit, hother 4 (by decide)]
    have e5 : facet1411blockPopcounts q 5 = facet1411blockPopcounts p 5 := by
      simp only [bp1411_5, facet1411bit, hother 5 (by decide)]
    have e6 : facet1411blockPopcounts q 6 = facet1411blockPopcounts p 6 := by
      simp only [bp1411_6, facet1411bit, hother 6 (by decide)]
    have e7 : facet1411blockPopcounts q 7 = facet1411blockPopcounts p 7 := by
      simp only [bp1411_7, facet1411bit, hother 7 (by decide)]
    cases hpi : p 9 with
    | false =>
      have hqi : q 9 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet1411blockPopcounts q 8 = facet1411blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp1411_8, facet1411bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_8, facet1411bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet1411G_lip_8 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts p 8) (by bpStrict1411 p, hpi)
    | true =>
      have hqi : q 9 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet1411blockPopcounts q 8 + 1 = facet1411blockPopcounts p 8 := by
        first
        | (simp only [bp1411_8, facet1411bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1411_8, facet1411bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1411f_eq p, facet1411f_eq q, e0, e1, e2, e3, e4, e5, e6, e7]
      rw [show (∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts q 8) j))
          = ∑ j, bdiff (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts q 8) j) (facet1411G (facet1411blockPopcounts p 0) (facet1411blockPopcounts p 1) (facet1411blockPopcounts p 2) (facet1411blockPopcounts p 3) (facet1411blockPopcounts p 4) (facet1411blockPopcounts p 5) (facet1411blockPopcounts p 6) (facet1411blockPopcounts p 7) (facet1411blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet1411G_lip_8 (facet1411blockPopcounts p 0) (by bpLoose1411 p) (facet1411blockPopcounts p 1) (by bpLoose1411 p) (facet1411blockPopcounts p 2) (by bpLoose1411 p) (facet1411blockPopcounts p 3) (by bpLoose1411 p) (facet1411blockPopcounts p 4) (by bpLoose1411 p) (facet1411blockPopcounts p 5) (by bpLoose1411 p) (facet1411blockPopcounts p 6) (by bpLoose1411 p) (facet1411blockPopcounts p 7) (by bpLoose1411 p) (facet1411blockPopcounts q 8) (by bpStrict1411 q, hqi)


variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region. -/
def facet1411L (A : Fin 6 → Finset V) (i : Fin 10) : Finset V := (facet1411L_reg i).biUnion A

/-- The `j`-th bounded-side region. -/
def facet1411R (A : Fin 6 → Finset V) (j : Fin 13) : Finset V := (facet1411R_reg j).biUnion A

/-- **Global nonexpansiveness of `facet1411f`, derived from the single-flip reduction.** -/
theorem facet1411f_nonexpansive_via_singleFlip (p q : Fin 10 → Bool) :
    (∑ j, bdiff (facet1411f p j) (facet1411f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet1411f facet1411f_singleFlip p q

/-- The boundary input patterns map through `facet1411f` exactly to the bounded-region pattern. -/
lemma facet1411f_boundary (c : Fin 6) :
    facet1411f (fun i => decide (c ∈ facet1411L_reg i)) = fun j => decide (c ∈ facet1411R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern maps to all `false`. -/
lemma facet1411f_zero : facet1411f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet1411L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 10) :
    v ∈ facet1411L A i ↔ c ∈ facet1411L_reg i := by
  unfold facet1411L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet1411R A j ⊆ bd`. -/
lemma facet1411R_sub (hR : Regions6 bd A) (j : Fin 13) : facet1411R A j ⊆ bd := by
  unfold facet1411R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet1411L A i ⊆ bd`. -/
lemma facet1411L_sub (hR : Regions6 bd A) (i : Fin 10) : facet1411L A i ⊆ bd := by
  unfold facet1411L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet1411R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 13) :
    v ∈ facet1411R A j ↔ c ∈ facet1411R_reg j := by
  unfold facet1411R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_1411 (hR : Regions6 bd A)
    (X : Fin 10 → Finset V) (hX : ∀ i, IsRTCut bd (facet1411L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet1411L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet1411L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet1411L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet1411L A i := fun h => hc ((mem_facet1411L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_1411
    (X : Fin 10 → Finset V) (hX : ∀ i, IsRTCut bd (facet1411L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet1411L A i := by
    unfold facet1411L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet1411_hvalid (hR : Regions6 bd A)
    (X : Fin 10 → Finset V) (hX : ∀ i, IsRTCut bd (facet1411L A i) (X i)) (j : Fin 13) :
    IsRTCut bd (facet1411R A j) (contractionCut X facet1411f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet1411f j) v = mem (facet1411R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_1411 hR X hX hvc, facet1411f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet1411R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_1411 X hX hvbd hcolor, facet1411f_zero]
      have : v ∉ facet1411R A j := by
        unfold facet1411R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet1411R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 1411).**
For six pairwise-disjoint boundary regions in any finite undirected nonnegative-real-weighted
graph, the 10 larger-side regions dominate the 13 bounded-side regions. Source: the six-party
holographic entropy cone / Hernandez-Cuenca holographic entropy cone database. The contraction map
is handled by a count-lattice factorisation (`facet1411f = facet1411G ∘ facet1411blockPopcounts`);
its Hamming-nonexpansiveness comes from the single-flip reduction over the block-popcount lattice. -/
theorem rtEntropyR_newFacet_n6_1411 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet1411R A j) (facet1411R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet1411L A i) (facet1411L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet1411L A i) S
      ∧ rtEntropyR G bd (facet1411L A i) (facet1411L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet1411L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet1411L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet1411L A i) (facet1411L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet1411R A j) (contractionCut X facet1411f j) :=
    fun j => facet1411_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet1411L A) (facet1411R A)
    (facet1411L_sub hR) (facet1411R_sub hR) X hXok facet1411f hvalid
    facet1411f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet1411R star6A j ⊆ star6Bd`. -/
lemma star6_facet1411R_sub (j : Fin 13) : facet1411R star6A j ⊆ star6Bd :=
  facet1411R_sub star6A_regions j
/-- `facet1411L star6A i ⊆ star6Bd`. -/
lemma star6_facet1411L_sub (i : Fin 10) : facet1411L star6A i ⊆ star6Bd :=
  facet1411L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet1411R (j : Fin 13) :
    rtEntropy star6Graph star6Bd (facet1411R star6A j) (star6_facet1411R_sub j)
      = ((![1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2] : Fin 13 → ℕ) j) := by
  fin_cases j <;> · unfold facet1411R facet1411R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet1411L (i : Fin 10) :
    rtEntropy star6Graph star6Bd (facet1411L star6A i) (star6_facet1411L_sub i)
      = ((![2, 2, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 10 → ℕ) i) := by
  fin_cases i <;> · unfold facet1411L facet1411L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to 24 and the larger side to 28 (slack 4). -/
theorem rtEntropyR_newFacet_n6_1411_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet1411R star6A j)
        (facet1411R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet1411L star6A i)
        (facet1411L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet1411R star6A j)
      (facet1411R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2] : Fin 13 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet1411R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet1411L star6A i)
      (facet1411L_sub (A := star6A) star6A_regions i) = ((![2, 2, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 10 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet1411L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_1411_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet1411R star6A j)
        (facet1411R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet1411L star6A i)
        (facet1411L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet1411R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet1411L i]; fin_cases i <;> norm_num

end Facet6n1411


/-! ### A six-party holographic entropy cone facet (database index 12982)

A count-lattice boolean contraction map with 12 larger-side regions and 15 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n12982

open Physlib.UndirectedMMICertificate.Facet6n174

def facet12982L_reg : Fin 12 → Finset (Fin 6) := ![{0, 1, 3}, {0, 1, 3}, {0, 3, 4}, {0, 3, 4}, {0, 4, 5}, {1, 4, 5}, {2, 3, 5}, {3, 4, 5}, {3, 4, 5}, {0, 1, 2, 4}, {0, 2, 4, 5}, {1, 2, 3, 4}]
def facet12982R_reg : Fin 15 → Finset (Fin 6) := ![{0}, {1}, {2}, {0, 3}, {0, 4}, {1, 3}, {3, 4}, {3, 5}, {4, 5}, {4, 5}, {0, 1, 3, 4}, {0, 3, 4, 5}, {2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 4, 5}]

/-! Block-popcount accessors (definitional). -/
@[simp] lemma bp12982_0 (p : Fin 12 → Bool) : facet12982blockPopcounts p 0 = facet12982bit p 0 + facet12982bit p 1 := rfl
@[simp] lemma bp12982_1 (p : Fin 12 → Bool) : facet12982blockPopcounts p 1 = facet12982bit p 2 + facet12982bit p 3 := rfl
@[simp] lemma bp12982_2 (p : Fin 12 → Bool) : facet12982blockPopcounts p 2 = facet12982bit p 4 := rfl
@[simp] lemma bp12982_3 (p : Fin 12 → Bool) : facet12982blockPopcounts p 3 = facet12982bit p 5 := rfl
@[simp] lemma bp12982_4 (p : Fin 12 → Bool) : facet12982blockPopcounts p 4 = facet12982bit p 6 := rfl
@[simp] lemma bp12982_5 (p : Fin 12 → Bool) : facet12982blockPopcounts p 5 = facet12982bit p 7 + facet12982bit p 8 := rfl
@[simp] lemma bp12982_6 (p : Fin 12 → Bool) : facet12982blockPopcounts p 6 = facet12982bit p 9 := rfl
@[simp] lemma bp12982_7 (p : Fin 12 → Bool) : facet12982blockPopcounts p 7 = facet12982bit p 10 := rfl
@[simp] lemma bp12982_8 (p : Fin 12 → Bool) : facet12982blockPopcounts p 8 = facet12982bit p 11 := rfl

lemma facet12982f_eq (p : Fin 12 → Bool) :
    facet12982f p = facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) := rfl

lemma facet12982bit_le_one (p : Fin 12 → Bool) (i : Fin 12) : facet12982bit p i ≤ 1 := by
  unfold facet12982bit; split_ifs <;> omega
lemma facet12982bit_eq_zero_of_false (p : Fin 12 → Bool) (i : Fin 12) (hp : p i = false) :
    facet12982bit p i = 0 := by
  unfold facet12982bit; rw [hp]; simp

macro "bpLoose12982" x:term : tactic =>
  `(tactic|
    (simp only [bp12982_0, bp12982_1, bp12982_2, bp12982_3, bp12982_4, bp12982_5, bp12982_6, bp12982_7, bp12982_8]
     have _hb0 := facet12982bit_le_one $x 0
     have _hb1 := facet12982bit_le_one $x 1
     have _hb2 := facet12982bit_le_one $x 2
     have _hb3 := facet12982bit_le_one $x 3
     have _hb4 := facet12982bit_le_one $x 4
     have _hb5 := facet12982bit_le_one $x 5
     have _hb6 := facet12982bit_le_one $x 6
     have _hb7 := facet12982bit_le_one $x 7
     have _hb8 := facet12982bit_le_one $x 8
     have _hb9 := facet12982bit_le_one $x 9
     have _hb10 := facet12982bit_le_one $x 10
     have _hb11 := facet12982bit_le_one $x 11
     omega))
macro "bpStrict12982" x:term "," h:ident : tactic =>
  `(tactic|
    (simp only [bp12982_0, bp12982_1, bp12982_2, bp12982_3, bp12982_4, bp12982_5, bp12982_6, bp12982_7, bp12982_8,
       facet12982bit_eq_zero_of_false $x _ $h]
     have _hb0 := facet12982bit_le_one $x 0
     have _hb1 := facet12982bit_le_one $x 1
     have _hb2 := facet12982bit_le_one $x 2
     have _hb3 := facet12982bit_le_one $x 3
     have _hb4 := facet12982bit_le_one $x 4
     have _hb5 := facet12982bit_le_one $x 5
     have _hb6 := facet12982bit_le_one $x 6
     have _hb7 := facet12982bit_le_one $x 7
     have _hb8 := facet12982bit_le_one $x 8
     have _hb9 := facet12982bit_le_one $x 9
     have _hb10 := facet12982bit_le_one $x 10
     have _hb11 := facet12982bit_le_one $x 11
     omega))

set_option maxHeartbeats 2000000 in
/-- **Single-flip (edge) nonexpansiveness of `facet12982f`.** -/
theorem facet12982f_singleFlip :
    ∀ (p : Fin 12 → Bool) (i : Fin 12),
      (∑ j, bdiff (facet12982f p j) (facet12982f (Function.update p i (!(p i))) j)) ≤ 1 := by
  intro p i
  fin_cases i
  · -- flip input bit 0 (block 0)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 0 (!(p 0))) j)) ≤ 1
    set q := Function.update p 0 (!(p 0)) with hq
    have hother : ∀ x : Fin 12, x ≠ 0 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 0 with
    | false =>
      have hqi : q 0 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp12982_0, facet12982bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_0, facet12982bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_0 (facet12982blockPopcounts p 0) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 0 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet12982blockPopcounts q 0 + 1 = facet12982blockPopcounts p 0 := by
        first
        | (simp only [bp12982_0, facet12982bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_0, facet12982bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e1, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts q 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts q 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet12982G_lip_0 (facet12982blockPopcounts q 0) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 1 (block 0)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 1 (!(p 1))) j)) ≤ 1
    set q := Function.update p 1 (!(p 1)) with hq
    have hother : ∀ x : Fin 12, x ≠ 1 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 1 with
    | false =>
      have hqi : q 1 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp12982_0, facet12982bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_0, facet12982bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_0 (facet12982blockPopcounts p 0) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 1 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet12982blockPopcounts q 0 + 1 = facet12982blockPopcounts p 0 := by
        first
        | (simp only [bp12982_0, facet12982bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_0, facet12982bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e1, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts q 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts q 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet12982G_lip_0 (facet12982blockPopcounts q 0) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 2 (block 1)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 2 (!(p 2))) j)) ≤ 1
    set q := Function.update p 2 (!(p 2)) with hq
    have hother : ∀ x : Fin 12, x ≠ 2 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 2 with
    | false =>
      have hqi : q 2 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp12982_1, facet12982bit, hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_1, facet12982bit, hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_1 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 2 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet12982blockPopcounts q 1 + 1 = facet12982blockPopcounts p 1 := by
        first
        | (simp only [bp12982_1, facet12982bit, hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_1, facet12982bit, hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts q 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts q 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet12982G_lip_1 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts q 1) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 3 (block 1)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 3 (!(p 3))) j)) ≤ 1
    set q := Function.update p 3 (!(p 3)) with hq
    have hother : ∀ x : Fin 12, x ≠ 3 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 3 with
    | false =>
      have hqi : q 3 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp12982_1, facet12982bit, hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_1, facet12982bit, hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_1 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 3 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet12982blockPopcounts q 1 + 1 = facet12982blockPopcounts p 1 := by
        first
        | (simp only [bp12982_1, facet12982bit, hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_1, facet12982bit, hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts q 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts q 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet12982G_lip_1 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts q 1) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 4 (block 2)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 4 (!(p 4))) j)) ≤ 1
    set q := Function.update p 4 (!(p 4)) with hq
    have hother : ∀ x : Fin 12, x ≠ 4 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 4 with
    | false =>
      have hqi : q 4 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 + 1 := by
        first
        | (simp only [bp12982_2, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_2, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_2 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 4 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet12982blockPopcounts q 2 + 1 = facet12982blockPopcounts p 2 := by
        first
        | (simp only [bp12982_2, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_2, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts q 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts q 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e2]
      exact facet12982G_lip_2 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts q 2) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 5 (block 3)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 5 (!(p 5))) j)) ≤ 1
    set q := Function.update p 5 (!(p 5)) with hq
    have hother : ∀ x : Fin 12, x ≠ 5 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 5 with
    | false =>
      have hqi : q 5 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 + 1 := by
        first
        | (simp only [bp12982_3, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_3, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_3 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 5 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet12982blockPopcounts q 3 + 1 = facet12982blockPopcounts p 3 := by
        first
        | (simp only [bp12982_3, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_3, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts q 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts q 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e3]
      exact facet12982G_lip_3 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts q 3) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 6 (block 4)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 6 (!(p 6))) j)) ≤ 1
    set q := Function.update p 6 (!(p 6)) with hq
    have hother : ∀ x : Fin 12, x ≠ 6 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 6 with
    | false =>
      have hqi : q 6 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp12982_4, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_4, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_4 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 6 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet12982blockPopcounts q 4 + 1 = facet12982blockPopcounts p 4 := by
        first
        | (simp only [bp12982_4, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_4, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts q 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts q 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet12982G_lip_4 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts q 4) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 7 (block 5)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 7 (!(p 7))) j)) ≤ 1
    set q := Function.update p 7 (!(p 7)) with hq
    have hother : ∀ x : Fin 12, x ≠ 7 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 7 with
    | false =>
      have hqi : q 7 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp12982_5, facet12982bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_5, facet12982bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_5 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 7 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet12982blockPopcounts q 5 + 1 = facet12982blockPopcounts p 5 := by
        first
        | (simp only [bp12982_5, facet12982bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_5, facet12982bit, hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts q 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts q 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet12982G_lip_5 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts q 5) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 8 (block 5)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 8 (!(p 8))) j)) ≤ 1
    set q := Function.update p 8 (!(p 8)) with hq
    have hother : ∀ x : Fin 12, x ≠ 8 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 8 with
    | false =>
      have hqi : q 8 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp12982_5, facet12982bit, hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_5, facet12982bit, hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_5 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 8 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet12982blockPopcounts q 5 + 1 = facet12982blockPopcounts p 5 := by
        first
        | (simp only [bp12982_5, facet12982bit, hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_5, facet12982bit, hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e6, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts q 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts q 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet12982G_lip_5 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts q 5) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 9 (block 6)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 9 (!(p 9))) j)) ≤ 1
    set q := Function.update p 9 (!(p 9)) with hq
    have hother : ∀ x : Fin 12, x ≠ 9 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 9 with
    | false =>
      have hqi : q 9 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp12982_6, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_6, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_6 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 9 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet12982blockPopcounts q 6 + 1 = facet12982blockPopcounts p 6 := by
        first
        | (simp only [bp12982_6, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_6, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e7, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts q 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts q 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet12982G_lip_6 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts q 6) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 10 (block 7)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 10 (!(p 10))) j)) ≤ 1
    set q := Function.update p 10 (!(p 10)) with hq
    have hother : ∀ x : Fin 12, x ≠ 10 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 := by
      simp only [bp12982_8, facet12982bit, hother 11 (by decide)]
    cases hpi : p 10 with
    | false =>
      have hqi : q 10 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 + 1 := by
        first
        | (simp only [bp12982_7, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_7, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_7 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpStrict12982 p, hpi) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
    | true =>
      have hqi : q 10 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet12982blockPopcounts q 7 + 1 = facet12982blockPopcounts p 7 := by
        first
        | (simp only [bp12982_7, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_7, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e8]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts q 7) (facet12982blockPopcounts p 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts q 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e7]
      exact facet12982G_lip_7 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts q 7) (by bpStrict12982 q, hqi) (facet12982blockPopcounts p 8) (by bpLoose12982 p)
  · -- flip input bit 11 (block 8)
    show (∑ j, bdiff (facet12982f p j)
          (facet12982f (Function.update p 11 (!(p 11))) j)) ≤ 1
    set q := Function.update p 11 (!(p 11)) with hq
    have hother : ∀ x : Fin 12, x ≠ 11 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet12982blockPopcounts q 0 = facet12982blockPopcounts p 0 := by
      simp only [bp12982_0, facet12982bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet12982blockPopcounts q 1 = facet12982blockPopcounts p 1 := by
      simp only [bp12982_1, facet12982bit, hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet12982blockPopcounts q 2 = facet12982blockPopcounts p 2 := by
      simp only [bp12982_2, facet12982bit, hother 4 (by decide)]
    have e3 : facet12982blockPopcounts q 3 = facet12982blockPopcounts p 3 := by
      simp only [bp12982_3, facet12982bit, hother 5 (by decide)]
    have e4 : facet12982blockPopcounts q 4 = facet12982blockPopcounts p 4 := by
      simp only [bp12982_4, facet12982bit, hother 6 (by decide)]
    have e5 : facet12982blockPopcounts q 5 = facet12982blockPopcounts p 5 := by
      simp only [bp12982_5, facet12982bit, hother 7 (by decide), hother 8 (by decide)]
    have e6 : facet12982blockPopcounts q 6 = facet12982blockPopcounts p 6 := by
      simp only [bp12982_6, facet12982bit, hother 9 (by decide)]
    have e7 : facet12982blockPopcounts q 7 = facet12982blockPopcounts p 7 := by
      simp only [bp12982_7, facet12982bit, hother 10 (by decide)]
    cases hpi : p 11 with
    | false =>
      have hqi : q 11 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet12982blockPopcounts q 8 = facet12982blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp12982_8, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_8, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact facet12982G_lip_8 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts p 8) (by bpStrict12982 p, hpi)
    | true =>
      have hqi : q 11 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet12982blockPopcounts q 8 + 1 = facet12982blockPopcounts p 8 := by
        first
        | (simp only [bp12982_8, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp12982_8, facet12982bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet12982f_eq p, facet12982f_eq q, e0, e1, e2, e3, e4, e5, e6, e7]
      rw [show (∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts q 8) j))
          = ∑ j, bdiff (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts q 8) j) (facet12982G (facet12982blockPopcounts p 0) (facet12982blockPopcounts p 1) (facet12982blockPopcounts p 2) (facet12982blockPopcounts p 3) (facet12982blockPopcounts p 4) (facet12982blockPopcounts p 5) (facet12982blockPopcounts p 6) (facet12982blockPopcounts p 7) (facet12982blockPopcounts p 8) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet12982G_lip_8 (facet12982blockPopcounts p 0) (by bpLoose12982 p) (facet12982blockPopcounts p 1) (by bpLoose12982 p) (facet12982blockPopcounts p 2) (by bpLoose12982 p) (facet12982blockPopcounts p 3) (by bpLoose12982 p) (facet12982blockPopcounts p 4) (by bpLoose12982 p) (facet12982blockPopcounts p 5) (by bpLoose12982 p) (facet12982blockPopcounts p 6) (by bpLoose12982 p) (facet12982blockPopcounts p 7) (by bpLoose12982 p) (facet12982blockPopcounts q 8) (by bpStrict12982 q, hqi)


variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region. -/
def facet12982L (A : Fin 6 → Finset V) (i : Fin 12) : Finset V := (facet12982L_reg i).biUnion A

/-- The `j`-th bounded-side region. -/
def facet12982R (A : Fin 6 → Finset V) (j : Fin 15) : Finset V := (facet12982R_reg j).biUnion A

/-- **Global nonexpansiveness of `facet12982f`, derived from the single-flip reduction.** -/
theorem facet12982f_nonexpansive_via_singleFlip (p q : Fin 12 → Bool) :
    (∑ j, bdiff (facet12982f p j) (facet12982f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet12982f facet12982f_singleFlip p q

/-- The boundary input patterns map through `facet12982f` exactly to the bounded-region pattern. -/
lemma facet12982f_boundary (c : Fin 6) :
    facet12982f (fun i => decide (c ∈ facet12982L_reg i)) = fun j => decide (c ∈ facet12982R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern maps to all `false`. -/
lemma facet12982f_zero : facet12982f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet12982L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 12) :
    v ∈ facet12982L A i ↔ c ∈ facet12982L_reg i := by
  unfold facet12982L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet12982R A j ⊆ bd`. -/
lemma facet12982R_sub (hR : Regions6 bd A) (j : Fin 15) : facet12982R A j ⊆ bd := by
  unfold facet12982R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet12982L A i ⊆ bd`. -/
lemma facet12982L_sub (hR : Regions6 bd A) (i : Fin 12) : facet12982L A i ⊆ bd := by
  unfold facet12982L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet12982R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 15) :
    v ∈ facet12982R A j ↔ c ∈ facet12982R_reg j := by
  unfold facet12982R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_12982 (hR : Regions6 bd A)
    (X : Fin 12 → Finset V) (hX : ∀ i, IsRTCut bd (facet12982L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet12982L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet12982L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet12982L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet12982L A i := fun h => hc ((mem_facet12982L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_12982
    (X : Fin 12 → Finset V) (hX : ∀ i, IsRTCut bd (facet12982L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet12982L A i := by
    unfold facet12982L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet12982_hvalid (hR : Regions6 bd A)
    (X : Fin 12 → Finset V) (hX : ∀ i, IsRTCut bd (facet12982L A i) (X i)) (j : Fin 15) :
    IsRTCut bd (facet12982R A j) (contractionCut X facet12982f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet12982f j) v = mem (facet12982R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_12982 hR X hX hvc, facet12982f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet12982R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_12982 X hX hvbd hcolor, facet12982f_zero]
      have : v ∉ facet12982R A j := by
        unfold facet12982R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet12982R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 12982).**
For six pairwise-disjoint boundary regions in any finite undirected nonnegative-real-weighted
graph, the 12 larger-side regions dominate the 15 bounded-side regions. Source: the six-party
holographic entropy cone / Hernandez-Cuenca holographic entropy cone database. The contraction map
is handled by a count-lattice factorisation (`facet12982f = facet12982G ∘ facet12982blockPopcounts`);
its Hamming-nonexpansiveness comes from the single-flip reduction over the block-popcount lattice. -/
theorem rtEntropyR_newFacet_n6_12982 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet12982R A j) (facet12982R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet12982L A i) (facet12982L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet12982L A i) S
      ∧ rtEntropyR G bd (facet12982L A i) (facet12982L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet12982L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet12982L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet12982L A i) (facet12982L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet12982R A j) (contractionCut X facet12982f j) :=
    fun j => facet12982_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet12982L A) (facet12982R A)
    (facet12982L_sub hR) (facet12982R_sub hR) X hXok facet12982f hvalid
    facet12982f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet12982R star6A j ⊆ star6Bd`. -/
lemma star6_facet12982R_sub (j : Fin 15) : facet12982R star6A j ⊆ star6Bd :=
  facet12982R_sub star6A_regions j
/-- `facet12982L star6A i ⊆ star6Bd`. -/
lemma star6_facet12982L_sub (i : Fin 12) : facet12982L star6A i ⊆ star6Bd :=
  facet12982L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet12982R (j : Fin 15) :
    rtEntropy star6Graph star6Bd (facet12982R star6A j) (star6_facet12982R_sub j)
      = ((![1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 2, 2] : Fin 15 → ℕ) j) := by
  fin_cases j <;> · unfold facet12982R facet12982R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet12982L (i : Fin 12) :
    rtEntropy star6Graph star6Bd (facet12982L star6A i) (star6_facet12982L_sub i)
      = ((![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 12 → ℕ) i) := by
  fin_cases i <;> · unfold facet12982L facet12982L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to 30 and the larger side to 36 (slack 6). -/
theorem rtEntropyR_newFacet_n6_12982_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet12982R star6A j)
        (facet12982R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet12982L star6A i)
        (facet12982L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet12982R star6A j)
      (facet12982R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 2, 2] : Fin 15 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet12982R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet12982L star6A i)
      (facet12982L_sub (A := star6A) star6A_regions i) = ((![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 12 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet12982L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_12982_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet12982R star6A j)
        (facet12982R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet12982L star6A i)
        (facet12982L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet12982R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet12982L i]; fin_cases i <;> norm_num

end Facet6n12982


/-! ### A six-party holographic entropy cone facet (database index 7451)

A count-lattice boolean contraction map with 12 larger-side regions and 15 bounded-side regions,
drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone
database, realized in the undirected min-cut model. -/
namespace Facet6n7451

open Physlib.UndirectedMMICertificate.Facet6n174

def facet7451L_reg : Fin 12 → Finset (Fin 6) := ![{2, 3}, {0, 2, 4}, {0, 4, 5}, {1, 2, 4}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {2, 4, 5}, {2, 4, 5}, {3, 4, 5}, {0, 1, 2, 5}, {0, 1, 3, 5}]
def facet7451R_reg : Fin 15 → Finset (Fin 6) := ![{0}, {1}, {2}, {3}, {2, 4}, {2, 4}, {2, 5}, {3, 5}, {4, 5}, {4, 5}, {0, 1, 4, 5}, {0, 2, 4, 5}, {1, 2, 4, 5}, {2, 3, 4, 5}, {0, 1, 2, 3, 5}]

/-! Block-popcount accessors (definitional). -/
@[simp] lemma bp7451_0 (p : Fin 12 → Bool) : facet7451blockPopcounts p 0 = facet7451bit p 0 := rfl
@[simp] lemma bp7451_1 (p : Fin 12 → Bool) : facet7451blockPopcounts p 1 = facet7451bit p 1 := rfl
@[simp] lemma bp7451_2 (p : Fin 12 → Bool) : facet7451blockPopcounts p 2 = facet7451bit p 2 := rfl
@[simp] lemma bp7451_3 (p : Fin 12 → Bool) : facet7451blockPopcounts p 3 = facet7451bit p 3 := rfl
@[simp] lemma bp7451_4 (p : Fin 12 → Bool) : facet7451blockPopcounts p 4 = facet7451bit p 4 := rfl
@[simp] lemma bp7451_5 (p : Fin 12 → Bool) : facet7451blockPopcounts p 5 = facet7451bit p 5 := rfl
@[simp] lemma bp7451_6 (p : Fin 12 → Bool) : facet7451blockPopcounts p 6 = facet7451bit p 6 + facet7451bit p 7 + facet7451bit p 8 := rfl
@[simp] lemma bp7451_7 (p : Fin 12 → Bool) : facet7451blockPopcounts p 7 = facet7451bit p 9 := rfl
@[simp] lemma bp7451_8 (p : Fin 12 → Bool) : facet7451blockPopcounts p 8 = facet7451bit p 10 := rfl
@[simp] lemma bp7451_9 (p : Fin 12 → Bool) : facet7451blockPopcounts p 9 = facet7451bit p 11 := rfl

lemma facet7451f_eq (p : Fin 12 → Bool) :
    facet7451f p = facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) := rfl

lemma facet7451bit_le_one (p : Fin 12 → Bool) (i : Fin 12) : facet7451bit p i ≤ 1 := by
  unfold facet7451bit; split_ifs <;> omega
lemma facet7451bit_eq_zero_of_false (p : Fin 12 → Bool) (i : Fin 12) (hp : p i = false) :
    facet7451bit p i = 0 := by
  unfold facet7451bit; rw [hp]; simp

macro "bpLoose7451" x:term : tactic =>
  `(tactic|
    (simp only [bp7451_0, bp7451_1, bp7451_2, bp7451_3, bp7451_4, bp7451_5, bp7451_6, bp7451_7, bp7451_8, bp7451_9]
     have _hb0 := facet7451bit_le_one $x 0
     have _hb1 := facet7451bit_le_one $x 1
     have _hb2 := facet7451bit_le_one $x 2
     have _hb3 := facet7451bit_le_one $x 3
     have _hb4 := facet7451bit_le_one $x 4
     have _hb5 := facet7451bit_le_one $x 5
     have _hb6 := facet7451bit_le_one $x 6
     have _hb7 := facet7451bit_le_one $x 7
     have _hb8 := facet7451bit_le_one $x 8
     have _hb9 := facet7451bit_le_one $x 9
     have _hb10 := facet7451bit_le_one $x 10
     have _hb11 := facet7451bit_le_one $x 11
     omega))
macro "bpStrict7451" x:term "," h:ident : tactic =>
  `(tactic|
    (simp only [bp7451_0, bp7451_1, bp7451_2, bp7451_3, bp7451_4, bp7451_5, bp7451_6, bp7451_7, bp7451_8, bp7451_9,
       facet7451bit_eq_zero_of_false $x _ $h]
     have _hb0 := facet7451bit_le_one $x 0
     have _hb1 := facet7451bit_le_one $x 1
     have _hb2 := facet7451bit_le_one $x 2
     have _hb3 := facet7451bit_le_one $x 3
     have _hb4 := facet7451bit_le_one $x 4
     have _hb5 := facet7451bit_le_one $x 5
     have _hb6 := facet7451bit_le_one $x 6
     have _hb7 := facet7451bit_le_one $x 7
     have _hb8 := facet7451bit_le_one $x 8
     have _hb9 := facet7451bit_le_one $x 9
     have _hb10 := facet7451bit_le_one $x 10
     have _hb11 := facet7451bit_le_one $x 11
     omega))

set_option maxHeartbeats 2000000 in
/-- **Single-flip (edge) nonexpansiveness of `facet7451f`.** -/
theorem facet7451f_singleFlip :
    ∀ (p : Fin 12 → Bool) (i : Fin 12),
      (∑ j, bdiff (facet7451f p j) (facet7451f (Function.update p i (!(p i))) j)) ≤ 1 := by
  intro p i
  fin_cases i
  · -- flip input bit 0 (block 0)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 0 (!(p 0))) j)) ≤ 1
    set q := Function.update p 0 (!(p 0)) with hq
    have hother : ∀ x : Fin 12, x ≠ 0 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 0 with
    | false =>
      have hqi : q 0 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp7451_0, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_0, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_0 (facet7451blockPopcounts p 0) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 0 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet7451blockPopcounts q 0 + 1 = facet7451blockPopcounts p 0 := by
        first
        | (simp only [bp7451_0, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_0, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts q 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts q 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet7451G_lip_0 (facet7451blockPopcounts q 0) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 1 (block 1)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 1 (!(p 1))) j)) ≤ 1
    set q := Function.update p 1 (!(p 1)) with hq
    have hother : ∀ x : Fin 12, x ≠ 1 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 1 with
    | false =>
      have hqi : q 1 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp7451_1, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_1, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_1 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 1 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet7451blockPopcounts q 1 + 1 = facet7451blockPopcounts p 1 := by
        first
        | (simp only [bp7451_1, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_1, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts q 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts q 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet7451G_lip_1 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts q 1) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 2 (block 2)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 2 (!(p 2))) j)) ≤ 1
    set q := Function.update p 2 (!(p 2)) with hq
    have hother : ∀ x : Fin 12, x ≠ 2 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 2 with
    | false =>
      have hqi : q 2 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 + 1 := by
        first
        | (simp only [bp7451_2, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_2, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_2 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 2 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet7451blockPopcounts q 2 + 1 = facet7451blockPopcounts p 2 := by
        first
        | (simp only [bp7451_2, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_2, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts q 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts q 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e2]
      exact facet7451G_lip_2 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts q 2) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 3 (block 3)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 3 (!(p 3))) j)) ≤ 1
    set q := Function.update p 3 (!(p 3)) with hq
    have hother : ∀ x : Fin 12, x ≠ 3 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 3 with
    | false =>
      have hqi : q 3 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 + 1 := by
        first
        | (simp only [bp7451_3, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_3, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_3 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 3 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet7451blockPopcounts q 3 + 1 = facet7451blockPopcounts p 3 := by
        first
        | (simp only [bp7451_3, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_3, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts q 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts q 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e3]
      exact facet7451G_lip_3 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts q 3) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 4 (block 4)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 4 (!(p 4))) j)) ≤ 1
    set q := Function.update p 4 (!(p 4)) with hq
    have hother : ∀ x : Fin 12, x ≠ 4 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 4 with
    | false =>
      have hqi : q 4 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp7451_4, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_4, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_4 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 4 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet7451blockPopcounts q 4 + 1 = facet7451blockPopcounts p 4 := by
        first
        | (simp only [bp7451_4, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_4, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts q 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts q 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet7451G_lip_4 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts q 4) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 5 (block 5)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 5 (!(p 5))) j)) ≤ 1
    set q := Function.update p 5 (!(p 5)) with hq
    have hother : ∀ x : Fin 12, x ≠ 5 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 5 with
    | false =>
      have hqi : q 5 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp7451_5, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_5, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_5 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 5 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet7451blockPopcounts q 5 + 1 = facet7451blockPopcounts p 5 := by
        first
        | (simp only [bp7451_5, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_5, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts q 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts q 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet7451G_lip_5 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts q 5) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 6 (block 6)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 6 (!(p 6))) j)) ≤ 1
    set q := Function.update p 6 (!(p 6)) with hq
    have hother : ∀ x : Fin 12, x ≠ 6 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 6 with
    | false =>
      have hqi : q 6 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp7451_6, facet7451bit, hother 7 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_6, facet7451bit, hother 7 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_6 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 6 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet7451blockPopcounts q 6 + 1 = facet7451blockPopcounts p 6 := by
        first
        | (simp only [bp7451_6, facet7451bit, hother 7 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_6, facet7451bit, hother 7 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts q 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts q 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet7451G_lip_6 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts q 6) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 7 (block 6)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 7 (!(p 7))) j)) ≤ 1
    set q := Function.update p 7 (!(p 7)) with hq
    have hother : ∀ x : Fin 12, x ≠ 7 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 7 with
    | false =>
      have hqi : q 7 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_6 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 7 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet7451blockPopcounts q 6 + 1 = facet7451blockPopcounts p 6 := by
        first
        | (simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 8 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts q 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts q 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet7451G_lip_6 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts q 6) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 8 (block 6)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 8 (!(p 8))) j)) ≤ 1
    set q := Function.update p 8 (!(p 8)) with hq
    have hother : ∀ x : Fin 12, x ≠ 8 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 8 with
    | false =>
      have hqi : q 8 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_6 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 8 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet7451blockPopcounts q 6 + 1 = facet7451blockPopcounts p 6 := by
        first
        | (simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e7, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts q 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts q 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet7451G_lip_6 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts q 6) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 9 (block 7)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 9 (!(p 9))) j)) ≤ 1
    set q := Function.update p 9 (!(p 9)) with hq
    have hother : ∀ x : Fin 12, x ≠ 9 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 9 with
    | false =>
      have hqi : q 9 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 + 1 := by
        first
        | (simp only [bp7451_7, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_7, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_7 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 9 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet7451blockPopcounts q 7 + 1 = facet7451blockPopcounts p 7 := by
        first
        | (simp only [bp7451_7, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_7, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e8, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts q 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts q 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e7]
      exact facet7451G_lip_7 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts q 7) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 10 (block 8)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 10 (!(p 10))) j)) ≤ 1
    set q := Function.update p 10 (!(p 10)) with hq
    have hother : ∀ x : Fin 12, x ≠ 10 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 := by
      simp only [bp7451_9, facet7451bit, hother 11 (by decide)]
    cases hpi : p 10 with
    | false =>
      have hqi : q 10 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp7451_8, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_8, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_8 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpStrict7451 p, hpi) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
    | true =>
      have hqi : q 10 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet7451blockPopcounts q 8 + 1 = facet7451blockPopcounts p 8 := by
        first
        | (simp only [bp7451_8, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_8, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e9]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts q 8) (facet7451blockPopcounts p 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts q 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet7451G_lip_8 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts q 8) (by bpStrict7451 q, hqi) (facet7451blockPopcounts p 9) (by bpLoose7451 p)
  · -- flip input bit 11 (block 9)
    show (∑ j, bdiff (facet7451f p j)
          (facet7451f (Function.update p 11 (!(p 11))) j)) ≤ 1
    set q := Function.update p 11 (!(p 11)) with hq
    have hother : ∀ x : Fin 12, x ≠ 11 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet7451blockPopcounts q 0 = facet7451blockPopcounts p 0 := by
      simp only [bp7451_0, facet7451bit, hother 0 (by decide)]
    have e1 : facet7451blockPopcounts q 1 = facet7451blockPopcounts p 1 := by
      simp only [bp7451_1, facet7451bit, hother 1 (by decide)]
    have e2 : facet7451blockPopcounts q 2 = facet7451blockPopcounts p 2 := by
      simp only [bp7451_2, facet7451bit, hother 2 (by decide)]
    have e3 : facet7451blockPopcounts q 3 = facet7451blockPopcounts p 3 := by
      simp only [bp7451_3, facet7451bit, hother 3 (by decide)]
    have e4 : facet7451blockPopcounts q 4 = facet7451blockPopcounts p 4 := by
      simp only [bp7451_4, facet7451bit, hother 4 (by decide)]
    have e5 : facet7451blockPopcounts q 5 = facet7451blockPopcounts p 5 := by
      simp only [bp7451_5, facet7451bit, hother 5 (by decide)]
    have e6 : facet7451blockPopcounts q 6 = facet7451blockPopcounts p 6 := by
      simp only [bp7451_6, facet7451bit, hother 6 (by decide), hother 7 (by decide), hother 8 (by decide)]
    have e7 : facet7451blockPopcounts q 7 = facet7451blockPopcounts p 7 := by
      simp only [bp7451_7, facet7451bit, hother 9 (by decide)]
    have e8 : facet7451blockPopcounts q 8 = facet7451blockPopcounts p 8 := by
      simp only [bp7451_8, facet7451bit, hother 10 (by decide)]
    cases hpi : p 11 with
    | false =>
      have hqi : q 11 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : facet7451blockPopcounts q 9 = facet7451blockPopcounts p 9 + 1 := by
        first
        | (simp only [bp7451_9, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_9, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact facet7451G_lip_9 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts p 9) (by bpStrict7451 p, hpi)
    | true =>
      have hqi : q 11 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : facet7451blockPopcounts q 9 + 1 = facet7451blockPopcounts p 9 := by
        first
        | (simp only [bp7451_9, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp7451_9, facet7451bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet7451f_eq p, facet7451f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8]
      rw [show (∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts q 9) j))
          = ∑ j, bdiff (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts q 9) j) (facet7451G (facet7451blockPopcounts p 0) (facet7451blockPopcounts p 1) (facet7451blockPopcounts p 2) (facet7451blockPopcounts p 3) (facet7451blockPopcounts p 4) (facet7451blockPopcounts p 5) (facet7451blockPopcounts p 6) (facet7451blockPopcounts p 7) (facet7451blockPopcounts p 8) (facet7451blockPopcounts p 9) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e9]
      exact facet7451G_lip_9 (facet7451blockPopcounts p 0) (by bpLoose7451 p) (facet7451blockPopcounts p 1) (by bpLoose7451 p) (facet7451blockPopcounts p 2) (by bpLoose7451 p) (facet7451blockPopcounts p 3) (by bpLoose7451 p) (facet7451blockPopcounts p 4) (by bpLoose7451 p) (facet7451blockPopcounts p 5) (by bpLoose7451 p) (facet7451blockPopcounts p 6) (by bpLoose7451 p) (facet7451blockPopcounts p 7) (by bpLoose7451 p) (facet7451blockPopcounts p 8) (by bpLoose7451 p) (facet7451blockPopcounts q 9) (by bpStrict7451 q, hqi)


variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region. -/
def facet7451L (A : Fin 6 → Finset V) (i : Fin 12) : Finset V := (facet7451L_reg i).biUnion A

/-- The `j`-th bounded-side region. -/
def facet7451R (A : Fin 6 → Finset V) (j : Fin 15) : Finset V := (facet7451R_reg j).biUnion A

/-- **Global nonexpansiveness of `facet7451f`, derived from the single-flip reduction.** -/
theorem facet7451f_nonexpansive_via_singleFlip (p q : Fin 12 → Bool) :
    (∑ j, bdiff (facet7451f p j) (facet7451f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet7451f facet7451f_singleFlip p q

/-- The boundary input patterns map through `facet7451f` exactly to the bounded-region pattern. -/
lemma facet7451f_boundary (c : Fin 6) :
    facet7451f (fun i => decide (c ∈ facet7451L_reg i)) = fun j => decide (c ∈ facet7451R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern maps to all `false`. -/
lemma facet7451f_zero : facet7451f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet7451L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 12) :
    v ∈ facet7451L A i ↔ c ∈ facet7451L_reg i := by
  unfold facet7451L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet7451R A j ⊆ bd`. -/
lemma facet7451R_sub (hR : Regions6 bd A) (j : Fin 15) : facet7451R A j ⊆ bd := by
  unfold facet7451R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet7451L A i ⊆ bd`. -/
lemma facet7451L_sub (hR : Regions6 bd A) (i : Fin 12) : facet7451L A i ⊆ bd := by
  unfold facet7451L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet7451R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 15) :
    v ∈ facet7451R A j ↔ c ∈ facet7451R_reg j := by
  unfold facet7451R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_7451 (hR : Regions6 bd A)
    (X : Fin 12 → Finset V) (hX : ∀ i, IsRTCut bd (facet7451L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet7451L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet7451L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet7451L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet7451L A i := fun h => hc ((mem_facet7451L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_7451
    (X : Fin 12 → Finset V) (hX : ∀ i, IsRTCut bd (facet7451L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet7451L A i := by
    unfold facet7451L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet7451_hvalid (hR : Regions6 bd A)
    (X : Fin 12 → Finset V) (hX : ∀ i, IsRTCut bd (facet7451L A i) (X i)) (j : Fin 15) :
    IsRTCut bd (facet7451R A j) (contractionCut X facet7451f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet7451f j) v = mem (facet7451R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_7451 hR X hX hvc, facet7451f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet7451R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_7451 X hX hvbd hcolor, facet7451f_zero]
      have : v ∉ facet7451R A j := by
        unfold facet7451R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet7451R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 7451).**
For six pairwise-disjoint boundary regions in any finite undirected nonnegative-real-weighted
graph, the 12 larger-side regions dominate the 15 bounded-side regions. Source: the six-party
holographic entropy cone / Hernandez-Cuenca holographic entropy cone database. The contraction map
is handled by a count-lattice factorisation (`facet7451f = facet7451G ∘ facet7451blockPopcounts`);
its Hamming-nonexpansiveness comes from the single-flip reduction over the block-popcount lattice. -/
theorem rtEntropyR_newFacet_n6_7451 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet7451R A j) (facet7451R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet7451L A i) (facet7451L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet7451L A i) S
      ∧ rtEntropyR G bd (facet7451L A i) (facet7451L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet7451L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet7451L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet7451L A i) (facet7451L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet7451R A j) (contractionCut X facet7451f j) :=
    fun j => facet7451_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet7451L A) (facet7451R A)
    (facet7451L_sub hR) (facet7451R_sub hR) X hXok facet7451f hvalid
    facet7451f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet7451R star6A j ⊆ star6Bd`. -/
lemma star6_facet7451R_sub (j : Fin 15) : facet7451R star6A j ⊆ star6Bd :=
  facet7451R_sub star6A_regions j
/-- `facet7451L star6A i ⊆ star6Bd`. -/
lemma star6_facet7451L_sub (i : Fin 12) : facet7451L star6A i ⊆ star6Bd :=
  facet7451L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet7451R (j : Fin 15) :
    rtEntropy star6Graph star6Bd (facet7451R star6A j) (star6_facet7451R_sub j)
      = ((![1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 2] : Fin 15 → ℕ) j) := by
  fin_cases j <;> · unfold facet7451R facet7451R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet7451L (i : Fin 12) :
    rtEntropy star6Graph star6Bd (facet7451L star6A i) (star6_facet7451L_sub i)
      = ((![2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 12 → ℕ) i) := by
  fin_cases i <;> · unfold facet7451L facet7451L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to 30 and the larger side to 35 (slack 5). -/
theorem rtEntropyR_newFacet_n6_7451_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet7451R star6A j)
        (facet7451R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet7451L star6A i)
        (facet7451L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet7451R star6A j)
      (facet7451R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 2] : Fin 15 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet7451R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet7451L star6A i)
      (facet7451L_sub (A := star6A) star6A_regions i) = ((![2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 12 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet7451L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_7451_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet7451R star6A j)
        (facet7451R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet7451L star6A i)
        (facet7451L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet7451R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet7451L i]; fin_cases i <;> norm_num

end Facet6n7451


/-! ### A six-party holographic entropy cone facet (database index 1234)

A count-lattice boolean contraction map with 13 larger-side regions and 17 bounded-side
regions, drawn from the six-party holographic entropy cone / Hernández-Cuenca holographic entropy
cone database, realized in the undirected min-cut model.  The larger-side regions fall into 11
equal-region blocks (one of multiplicity three), so the contraction map factors through the
block popcounts. -/
namespace Facet6n1234

open Physlib.UndirectedMMICertificate.Facet6n174

def facet1234L_reg : Fin 13 → Finset (Fin 6) := ![{0, 1, 2}, {0, 1, 4}, {0, 1, 4}, {0, 1, 4}, {0, 2, 5}, {1, 2, 5}, {1, 4, 5}, {2, 3, 5}, {0, 1, 3, 5}, {0, 2, 3, 4}, {0, 2, 4, 5}, {1, 2, 3, 4}, {1, 2, 4, 5}]
def facet1234R_reg : Fin 17 → Finset (Fin 6) := ![{0}, {0}, {1}, {2}, {3}, {0, 4}, {1, 4}, {1, 4}, {1, 5}, {2, 5}, {2, 5}, {0, 1, 2, 4}, {0, 1, 4, 5}, {2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 4, 5}]

/-! Block-popcount accessors (definitional). -/
@[simp] lemma bp1234_0 (p : Fin 13 → Bool) : facet1234blockPopcounts p 0 = facet1234bit p 0 := rfl
@[simp] lemma bp1234_1 (p : Fin 13 → Bool) : facet1234blockPopcounts p 1 = facet1234bit p 1+facet1234bit p 2+facet1234bit p 3 := rfl
@[simp] lemma bp1234_2 (p : Fin 13 → Bool) : facet1234blockPopcounts p 2 = facet1234bit p 4 := rfl
@[simp] lemma bp1234_3 (p : Fin 13 → Bool) : facet1234blockPopcounts p 3 = facet1234bit p 5 := rfl
@[simp] lemma bp1234_4 (p : Fin 13 → Bool) : facet1234blockPopcounts p 4 = facet1234bit p 6 := rfl
@[simp] lemma bp1234_5 (p : Fin 13 → Bool) : facet1234blockPopcounts p 5 = facet1234bit p 7 := rfl
@[simp] lemma bp1234_6 (p : Fin 13 → Bool) : facet1234blockPopcounts p 6 = facet1234bit p 8 := rfl
@[simp] lemma bp1234_7 (p : Fin 13 → Bool) : facet1234blockPopcounts p 7 = facet1234bit p 9 := rfl
@[simp] lemma bp1234_8 (p : Fin 13 → Bool) : facet1234blockPopcounts p 8 = facet1234bit p 10 := rfl
@[simp] lemma bp1234_9 (p : Fin 13 → Bool) : facet1234blockPopcounts p 9 = facet1234bit p 11 := rfl
@[simp] lemma bp1234_10 (p : Fin 13 → Bool) : facet1234blockPopcounts p 10 = facet1234bit p 12 := rfl

lemma facet1234f_eq (p : Fin 13 → Bool) :
    facet1234f p = facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) := rfl

lemma facet1234bit_le_one (p : Fin 13 → Bool) (i : Fin 13) : facet1234bit p i ≤ 1 := by
  unfold facet1234bit; split_ifs <;> omega
lemma facet1234bit_eq_zero_of_false (p : Fin 13 → Bool) (i : Fin 13) (hp : p i = false) :
    facet1234bit p i = 0 := by
  unfold facet1234bit; rw [hp]; simp

macro "bpLoose1234" x:term : tactic =>
  `(tactic|
    (simp only [bp1234_0, bp1234_1, bp1234_2, bp1234_3, bp1234_4, bp1234_5, bp1234_6, bp1234_7, bp1234_8, bp1234_9, bp1234_10]
     have _hb0 := facet1234bit_le_one $x 0
     have _hb1 := facet1234bit_le_one $x 1
     have _hb2 := facet1234bit_le_one $x 2
     have _hb3 := facet1234bit_le_one $x 3
     have _hb4 := facet1234bit_le_one $x 4
     have _hb5 := facet1234bit_le_one $x 5
     have _hb6 := facet1234bit_le_one $x 6
     have _hb7 := facet1234bit_le_one $x 7
     have _hb8 := facet1234bit_le_one $x 8
     have _hb9 := facet1234bit_le_one $x 9
     have _hb10 := facet1234bit_le_one $x 10
     have _hb11 := facet1234bit_le_one $x 11
     have _hb12 := facet1234bit_le_one $x 12
     omega))
macro "bpStrict1234" x:term "," h:ident : tactic =>
  `(tactic|
    (simp only [bp1234_0, bp1234_1, bp1234_2, bp1234_3, bp1234_4, bp1234_5, bp1234_6, bp1234_7, bp1234_8, bp1234_9, bp1234_10,
       facet1234bit_eq_zero_of_false $x _ $h]
     have _hb0 := facet1234bit_le_one $x 0
     have _hb1 := facet1234bit_le_one $x 1
     have _hb2 := facet1234bit_le_one $x 2
     have _hb3 := facet1234bit_le_one $x 3
     have _hb4 := facet1234bit_le_one $x 4
     have _hb5 := facet1234bit_le_one $x 5
     have _hb6 := facet1234bit_le_one $x 6
     have _hb7 := facet1234bit_le_one $x 7
     have _hb8 := facet1234bit_le_one $x 8
     have _hb9 := facet1234bit_le_one $x 9
     have _hb10 := facet1234bit_le_one $x 10
     have _hb11 := facet1234bit_le_one $x 11
     have _hb12 := facet1234bit_le_one $x 12
     omega))

set_option maxHeartbeats 4000000 in
/-- **Single-flip (edge) nonexpansiveness of `facet1234f`.** -/
theorem facet1234f_singleFlip :
    ∀ (p : Fin 13 → Bool) (i : Fin 13),
      (∑ j, bdiff (facet1234f p j) (facet1234f (Function.update p i (!(p i))) j)) ≤ 1 := by
  intro p i
  fin_cases i
  · -- flip input bit 0 (block 0)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 0 (!(p 0))) j)) ≤ 1
    set q := Function.update p 0 (!(p 0)) with hq
    have hother : ∀ x : Fin 13, x ≠ 0 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 0 with
    | false =>
      have hqi : q 0 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp1234_0, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_0, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_0 (facet1234blockPopcounts p 0) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 0 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet1234blockPopcounts q 0 + 1 = facet1234blockPopcounts p 0 := by
        first
        | (simp only [bp1234_0, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_0, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts q 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts q 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet1234G_lip_0 (facet1234blockPopcounts q 0) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 1 (block 1)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 1 (!(p 1))) j)) ≤ 1
    set q := Function.update p 1 (!(p 1)) with hq
    have hother : ∀ x : Fin 13, x ≠ 1 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 1 with
    | false =>
      have hqi : q 1 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1234_1, facet1234bit, hother 2 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_1, facet1234bit, hother 2 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_1 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 1 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1234blockPopcounts q 1 + 1 = facet1234blockPopcounts p 1 := by
        first
        | (simp only [bp1234_1, facet1234bit, hother 2 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_1, facet1234bit, hother 2 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts q 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts q 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet1234G_lip_1 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts q 1) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 2 (block 1)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 2 (!(p 2))) j)) ≤ 1
    set q := Function.update p 2 (!(p 2)) with hq
    have hother : ∀ x : Fin 13, x ≠ 2 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 2 with
    | false =>
      have hqi : q 2 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_1 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 2 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1234blockPopcounts q 1 + 1 = facet1234blockPopcounts p 1 := by
        first
        | (simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 3 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts q 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts q 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet1234G_lip_1 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts q 1) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 3 (block 1)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 3 (!(p 3))) j)) ≤ 1
    set q := Function.update p 3 (!(p 3)) with hq
    have hother : ∀ x : Fin 13, x ≠ 3 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 3 with
    | false =>
      have hqi : q 3 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_1 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 3 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet1234blockPopcounts q 1 + 1 = facet1234blockPopcounts p 1 := by
        first
        | (simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts q 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts q 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet1234G_lip_1 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts q 1) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 4 (block 2)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 4 (!(p 4))) j)) ≤ 1
    set q := Function.update p 4 (!(p 4)) with hq
    have hother : ∀ x : Fin 13, x ≠ 4 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 4 with
    | false =>
      have hqi : q 4 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 + 1 := by
        first
        | (simp only [bp1234_2, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_2, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_2 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 4 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet1234blockPopcounts q 2 + 1 = facet1234blockPopcounts p 2 := by
        first
        | (simp only [bp1234_2, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_2, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e3, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts q 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts q 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e2]
      exact facet1234G_lip_2 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts q 2) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 5 (block 3)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 5 (!(p 5))) j)) ≤ 1
    set q := Function.update p 5 (!(p 5)) with hq
    have hother : ∀ x : Fin 13, x ≠ 5 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 5 with
    | false =>
      have hqi : q 5 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 + 1 := by
        first
        | (simp only [bp1234_3, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_3, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_3 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 5 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet1234blockPopcounts q 3 + 1 = facet1234blockPopcounts p 3 := by
        first
        | (simp only [bp1234_3, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_3, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts q 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts q 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e3]
      exact facet1234G_lip_3 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts q 3) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 6 (block 4)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 6 (!(p 6))) j)) ≤ 1
    set q := Function.update p 6 (!(p 6)) with hq
    have hother : ∀ x : Fin 13, x ≠ 6 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 6 with
    | false =>
      have hqi : q 6 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp1234_4, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_4, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_4 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 6 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet1234blockPopcounts q 4 + 1 = facet1234blockPopcounts p 4 := by
        first
        | (simp only [bp1234_4, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_4, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts q 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts q 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet1234G_lip_4 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts q 4) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 7 (block 5)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 7 (!(p 7))) j)) ≤ 1
    set q := Function.update p 7 (!(p 7)) with hq
    have hother : ∀ x : Fin 13, x ≠ 7 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 7 with
    | false =>
      have hqi : q 7 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp1234_5, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_5, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_5 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 7 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet1234blockPopcounts q 5 + 1 = facet1234blockPopcounts p 5 := by
        first
        | (simp only [bp1234_5, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_5, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts q 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts q 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet1234G_lip_5 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts q 5) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 8 (block 6)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 8 (!(p 8))) j)) ≤ 1
    set q := Function.update p 8 (!(p 8)) with hq
    have hother : ∀ x : Fin 13, x ≠ 8 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 8 with
    | false =>
      have hqi : q 8 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp1234_6, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_6, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_6 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 8 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet1234blockPopcounts q 6 + 1 = facet1234blockPopcounts p 6 := by
        first
        | (simp only [bp1234_6, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_6, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts q 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts q 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet1234G_lip_6 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts q 6) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 9 (block 7)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 9 (!(p 9))) j)) ≤ 1
    set q := Function.update p 9 (!(p 9)) with hq
    have hother : ∀ x : Fin 13, x ≠ 9 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 9 with
    | false =>
      have hqi : q 9 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 + 1 := by
        first
        | (simp only [bp1234_7, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_7, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_7 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 9 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet1234blockPopcounts q 7 + 1 = facet1234blockPopcounts p 7 := by
        first
        | (simp only [bp1234_7, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_7, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e8, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts q 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts q 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e7]
      exact facet1234G_lip_7 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts q 7) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 10 (block 8)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 10 (!(p 10))) j)) ≤ 1
    set q := Function.update p 10 (!(p 10)) with hq
    have hother : ∀ x : Fin 13, x ≠ 10 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 10 with
    | false =>
      have hqi : q 10 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp1234_8, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_8, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_8 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 10 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet1234blockPopcounts q 8 + 1 = facet1234blockPopcounts p 8 := by
        first
        | (simp only [bp1234_8, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_8, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e9, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts q 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts q 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet1234G_lip_8 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts q 8) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 11 (block 9)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 11 (!(p 11))) j)) ≤ 1
    set q := Function.update p 11 (!(p 11)) with hq
    have hother : ∀ x : Fin 13, x ≠ 11 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 := by
      simp only [bp1234_10, facet1234bit, hother 12 (by decide)]
    cases hpi : p 11 with
    | false =>
      have hqi : q 11 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 + 1 := by
        first
        | (simp only [bp1234_9, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_9, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_9 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpStrict1234 p, hpi) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
    | true =>
      have hqi : q 11 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : facet1234blockPopcounts q 9 + 1 = facet1234blockPopcounts p 9 := by
        first
        | (simp only [bp1234_9, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_9, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e10]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts q 9) (facet1234blockPopcounts p 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts q 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e9]
      exact facet1234G_lip_9 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts q 9) (by bpStrict1234 q, hqi) (facet1234blockPopcounts p 10) (by bpLoose1234 p)
  · -- flip input bit 12 (block 10)
    show (∑ j, bdiff (facet1234f p j)
          (facet1234f (Function.update p 12 (!(p 12))) j)) ≤ 1
    set q := Function.update p 12 (!(p 12)) with hq
    have hother : ∀ x : Fin 13, x ≠ 12 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet1234blockPopcounts q 0 = facet1234blockPopcounts p 0 := by
      simp only [bp1234_0, facet1234bit, hother 0 (by decide)]
    have e1 : facet1234blockPopcounts q 1 = facet1234blockPopcounts p 1 := by
      simp only [bp1234_1, facet1234bit, hother 1 (by decide), hother 2 (by decide), hother 3 (by decide)]
    have e2 : facet1234blockPopcounts q 2 = facet1234blockPopcounts p 2 := by
      simp only [bp1234_2, facet1234bit, hother 4 (by decide)]
    have e3 : facet1234blockPopcounts q 3 = facet1234blockPopcounts p 3 := by
      simp only [bp1234_3, facet1234bit, hother 5 (by decide)]
    have e4 : facet1234blockPopcounts q 4 = facet1234blockPopcounts p 4 := by
      simp only [bp1234_4, facet1234bit, hother 6 (by decide)]
    have e5 : facet1234blockPopcounts q 5 = facet1234blockPopcounts p 5 := by
      simp only [bp1234_5, facet1234bit, hother 7 (by decide)]
    have e6 : facet1234blockPopcounts q 6 = facet1234blockPopcounts p 6 := by
      simp only [bp1234_6, facet1234bit, hother 8 (by decide)]
    have e7 : facet1234blockPopcounts q 7 = facet1234blockPopcounts p 7 := by
      simp only [bp1234_7, facet1234bit, hother 9 (by decide)]
    have e8 : facet1234blockPopcounts q 8 = facet1234blockPopcounts p 8 := by
      simp only [bp1234_8, facet1234bit, hother 10 (by decide)]
    have e9 : facet1234blockPopcounts q 9 = facet1234blockPopcounts p 9 := by
      simp only [bp1234_9, facet1234bit, hother 11 (by decide)]
    cases hpi : p 12 with
    | false =>
      have hqi : q 12 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e10 : facet1234blockPopcounts q 10 = facet1234blockPopcounts p 10 + 1 := by
        first
        | (simp only [bp1234_10, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_10, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      exact facet1234G_lip_10 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts p 10) (by bpStrict1234 p, hpi)
    | true =>
      have hqi : q 12 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e10 : facet1234blockPopcounts q 10 + 1 = facet1234blockPopcounts p 10 := by
        first
        | (simp only [bp1234_10, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp1234_10, facet1234bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet1234f_eq p, facet1234f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      rw [show (∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts q 10) j))
          = ∑ j, bdiff (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts q 10) j) (facet1234G (facet1234blockPopcounts p 0) (facet1234blockPopcounts p 1) (facet1234blockPopcounts p 2) (facet1234blockPopcounts p 3) (facet1234blockPopcounts p 4) (facet1234blockPopcounts p 5) (facet1234blockPopcounts p 6) (facet1234blockPopcounts p 7) (facet1234blockPopcounts p 8) (facet1234blockPopcounts p 9) (facet1234blockPopcounts p 10) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e10]
      exact facet1234G_lip_10 (facet1234blockPopcounts p 0) (by bpLoose1234 p) (facet1234blockPopcounts p 1) (by bpLoose1234 p) (facet1234blockPopcounts p 2) (by bpLoose1234 p) (facet1234blockPopcounts p 3) (by bpLoose1234 p) (facet1234blockPopcounts p 4) (by bpLoose1234 p) (facet1234blockPopcounts p 5) (by bpLoose1234 p) (facet1234blockPopcounts p 6) (by bpLoose1234 p) (facet1234blockPopcounts p 7) (by bpLoose1234 p) (facet1234blockPopcounts p 8) (by bpLoose1234 p) (facet1234blockPopcounts p 9) (by bpLoose1234 p) (facet1234blockPopcounts q 10) (by bpStrict1234 q, hqi)


variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region. -/
def facet1234L (A : Fin 6 → Finset V) (i : Fin 13) : Finset V := (facet1234L_reg i).biUnion A

/-- The `j`-th bounded-side region. -/
def facet1234R (A : Fin 6 → Finset V) (j : Fin 17) : Finset V := (facet1234R_reg j).biUnion A

/-- **Global nonexpansiveness of `facet1234f`, derived from the single-flip reduction.** -/
theorem facet1234f_nonexpansive_via_singleFlip (p q : Fin 13 → Bool) :
    (∑ j, bdiff (facet1234f p j) (facet1234f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet1234f facet1234f_singleFlip p q

/-- The boundary input patterns map through `facet1234f` exactly to the bounded-region pattern. -/
lemma facet1234f_boundary (c : Fin 6) :
    facet1234f (fun i => decide (c ∈ facet1234L_reg i)) = fun j => decide (c ∈ facet1234R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern maps to all `false`. -/
lemma facet1234f_zero : facet1234f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet1234L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 13) :
    v ∈ facet1234L A i ↔ c ∈ facet1234L_reg i := by
  unfold facet1234L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet1234R A j ⊆ bd`. -/
lemma facet1234R_sub (hR : Regions6 bd A) (j : Fin 17) : facet1234R A j ⊆ bd := by
  unfold facet1234R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet1234L A i ⊆ bd`. -/
lemma facet1234L_sub (hR : Regions6 bd A) (i : Fin 13) : facet1234L A i ⊆ bd := by
  unfold facet1234L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet1234R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 17) :
    v ∈ facet1234R A j ↔ c ∈ facet1234R_reg j := by
  unfold facet1234R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_1234 (hR : Regions6 bd A)
    (X : Fin 13 → Finset V) (hX : ∀ i, IsRTCut bd (facet1234L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet1234L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet1234L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet1234L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet1234L A i := fun h => hc ((mem_facet1234L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_1234
    (X : Fin 13 → Finset V) (hX : ∀ i, IsRTCut bd (facet1234L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet1234L A i := by
    unfold facet1234L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet1234_hvalid (hR : Regions6 bd A)
    (X : Fin 13 → Finset V) (hX : ∀ i, IsRTCut bd (facet1234L A i) (X i)) (j : Fin 17) :
    IsRTCut bd (facet1234R A j) (contractionCut X facet1234f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet1234f j) v = mem (facet1234R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_1234 hR X hX hvc, facet1234f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet1234R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_1234 X hX hvbd hcolor, facet1234f_zero]
      have : v ∉ facet1234R A j := by
        unfold facet1234R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet1234R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 1234).**
For six pairwise-disjoint boundary regions in any finite undirected nonnegative-real-weighted
graph, the 13 larger-side regions dominate the 17 bounded-side regions. Source: the
six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone database. The
contraction map is handled by a count-lattice factorisation
(`facet1234f = facet1234G ∘ facet1234blockPopcounts`); its Hamming-nonexpansiveness comes from
the single-flip reduction over the block-popcount lattice (one block has multiplicity three). -/
theorem rtEntropyR_newFacet_n6_1234 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet1234R A j) (facet1234R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet1234L A i) (facet1234L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet1234L A i) S
      ∧ rtEntropyR G bd (facet1234L A i) (facet1234L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet1234L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet1234L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet1234L A i) (facet1234L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet1234R A j) (contractionCut X facet1234f j) :=
    fun j => facet1234_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet1234L A) (facet1234R A)
    (facet1234L_sub hR) (facet1234R_sub hR) X hXok facet1234f hvalid
    facet1234f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet1234R star6A j ⊆ star6Bd`. -/
lemma star6_facet1234R_sub (j : Fin 17) : facet1234R star6A j ⊆ star6Bd :=
  facet1234R_sub star6A_regions j
/-- `facet1234L star6A i ⊆ star6Bd`. -/
lemma star6_facet1234L_sub (i : Fin 13) : facet1234L star6A i ⊆ star6Bd :=
  facet1234L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet1234R (j : Fin 17) :
    rtEntropy star6Graph star6Bd (facet1234R star6A j) (star6_facet1234R_sub j)
      = ((![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 2, 2, 2] : Fin 17 → ℕ) j) := by
  fin_cases j <;> · unfold facet1234R facet1234R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet1234L (i : Fin 13) :
    rtEntropy star6Graph star6Bd (facet1234L star6A i) (star6_facet1234L_sub i)
      = ((![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 13 → ℕ) i) := by
  fin_cases i <;> · unfold facet1234L facet1234L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to 32 and the larger side to 39 (slack 7). -/
theorem rtEntropyR_newFacet_n6_1234_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet1234R star6A j)
        (facet1234R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet1234L star6A i)
        (facet1234L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet1234R star6A j)
      (facet1234R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 2, 2, 2] : Fin 17 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet1234R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet1234L star6A i)
      (facet1234L_sub (A := star6A) star6A_regions i) = ((![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 13 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet1234L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_1234_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet1234R star6A j)
        (facet1234R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet1234L star6A i)
        (facet1234L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet1234R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet1234L i]; fin_cases i <;> norm_num

end Facet6n1234



namespace Facet6n14

open Physlib.UndirectedMMICertificate.Facet6n174

def facet14L_reg : Fin 13 → Finset (Fin 6) := ![{0, 1}, {0, 1}, {0, 3}, {0, 1, 4}, {0, 2, 4}, {0, 4, 5}, {1, 2, 4}, {1, 3, 5}, {2, 3, 4}, {3, 4, 5}, {0, 1, 2, 5}, {0, 2, 3, 5}, {1, 2, 4, 5}]
def facet14R_reg : Fin 17 → Finset (Fin 6) := ![{0}, {0}, {0}, {1}, {1}, {2}, {3}, {1, 4}, {2, 4}, {3, 5}, {4, 5}, {0, 1, 5}, {0, 3, 4}, {0, 1, 2, 4}, {2, 3, 4, 5}, {0, 1, 2, 3, 5}, {0, 1, 2, 4, 5}]

/-! Block-popcount accessors (definitional). -/
@[simp] lemma bp14_0 (p : Fin 13 → Bool) : facet14blockPopcounts p 0 = facet14bit p 0+facet14bit p 1 := rfl
@[simp] lemma bp14_1 (p : Fin 13 → Bool) : facet14blockPopcounts p 1 = facet14bit p 2 := rfl
@[simp] lemma bp14_2 (p : Fin 13 → Bool) : facet14blockPopcounts p 2 = facet14bit p 3 := rfl
@[simp] lemma bp14_3 (p : Fin 13 → Bool) : facet14blockPopcounts p 3 = facet14bit p 4 := rfl
@[simp] lemma bp14_4 (p : Fin 13 → Bool) : facet14blockPopcounts p 4 = facet14bit p 5 := rfl
@[simp] lemma bp14_5 (p : Fin 13 → Bool) : facet14blockPopcounts p 5 = facet14bit p 6 := rfl
@[simp] lemma bp14_6 (p : Fin 13 → Bool) : facet14blockPopcounts p 6 = facet14bit p 7 := rfl
@[simp] lemma bp14_7 (p : Fin 13 → Bool) : facet14blockPopcounts p 7 = facet14bit p 8 := rfl
@[simp] lemma bp14_8 (p : Fin 13 → Bool) : facet14blockPopcounts p 8 = facet14bit p 9 := rfl
@[simp] lemma bp14_9 (p : Fin 13 → Bool) : facet14blockPopcounts p 9 = facet14bit p 10 := rfl
@[simp] lemma bp14_10 (p : Fin 13 → Bool) : facet14blockPopcounts p 10 = facet14bit p 11 := rfl
@[simp] lemma bp14_11 (p : Fin 13 → Bool) : facet14blockPopcounts p 11 = facet14bit p 12 := rfl

lemma facet14f_eq (p : Fin 13 → Bool) :
    facet14f p = facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) := rfl

lemma facet14bit_le_one (p : Fin 13 → Bool) (i : Fin 13) : facet14bit p i ≤ 1 := by
  unfold facet14bit; split_ifs <;> omega
lemma facet14bit_eq_zero_of_false (p : Fin 13 → Bool) (i : Fin 13) (hp : p i = false) :
    facet14bit p i = 0 := by
  unfold facet14bit; rw [hp]; simp

macro "bpLoose14" x:term : tactic =>
  `(tactic|
    (simp only [bp14_0, bp14_1, bp14_2, bp14_3, bp14_4, bp14_5, bp14_6, bp14_7, bp14_8, bp14_9, bp14_10, bp14_11]
     have _hb0 := facet14bit_le_one $x 0
     have _hb1 := facet14bit_le_one $x 1
     have _hb2 := facet14bit_le_one $x 2
     have _hb3 := facet14bit_le_one $x 3
     have _hb4 := facet14bit_le_one $x 4
     have _hb5 := facet14bit_le_one $x 5
     have _hb6 := facet14bit_le_one $x 6
     have _hb7 := facet14bit_le_one $x 7
     have _hb8 := facet14bit_le_one $x 8
     have _hb9 := facet14bit_le_one $x 9
     have _hb10 := facet14bit_le_one $x 10
     have _hb11 := facet14bit_le_one $x 11
     have _hb12 := facet14bit_le_one $x 12
     omega))
macro "bpStrict14" x:term "," h:ident : tactic =>
  `(tactic|
    (simp only [bp14_0, bp14_1, bp14_2, bp14_3, bp14_4, bp14_5, bp14_6, bp14_7, bp14_8, bp14_9, bp14_10, bp14_11,
       facet14bit_eq_zero_of_false $x _ $h]
     have _hb0 := facet14bit_le_one $x 0
     have _hb1 := facet14bit_le_one $x 1
     have _hb2 := facet14bit_le_one $x 2
     have _hb3 := facet14bit_le_one $x 3
     have _hb4 := facet14bit_le_one $x 4
     have _hb5 := facet14bit_le_one $x 5
     have _hb6 := facet14bit_le_one $x 6
     have _hb7 := facet14bit_le_one $x 7
     have _hb8 := facet14bit_le_one $x 8
     have _hb9 := facet14bit_le_one $x 9
     have _hb10 := facet14bit_le_one $x 10
     have _hb11 := facet14bit_le_one $x 11
     have _hb12 := facet14bit_le_one $x 12
     omega))

set_option maxHeartbeats 4000000 in
/-- **Single-flip (edge) nonexpansiveness of `facet14f`.** -/
theorem facet14f_singleFlip :
    ∀ (p : Fin 13 → Bool) (i : Fin 13),
      (∑ j, bdiff (facet14f p j) (facet14f (Function.update p i (!(p i))) j)) ≤ 1 := by
  intro p i
  fin_cases i
  · -- flip input bit 0 (block 0)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 0 (!(p 0))) j)) ≤ 1
    set q := Function.update p 0 (!(p 0)) with hq
    have hother : ∀ x : Fin 13, x ≠ 0 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 0 with
    | false =>
      have hqi : q 0 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp14_0, facet14bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_0, facet14bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_0 (facet14blockPopcounts p 0) (by bpStrict14 p, hpi) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 0 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet14blockPopcounts q 0 + 1 = facet14blockPopcounts p 0 := by
        first
        | (simp only [bp14_0, facet14bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_0, facet14bit, hother 1 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts q 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts q 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet14G_lip_0 (facet14blockPopcounts q 0) (by bpStrict14 q, hqi) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 1 (block 0)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 1 (!(p 1))) j)) ≤ 1
    set q := Function.update p 1 (!(p 1)) with hq
    have hother : ∀ x : Fin 13, x ≠ 1 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 1 with
    | false =>
      have hqi : q 1 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 + 1 := by
        first
        | (simp only [bp14_0, facet14bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_0, facet14bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_0 (facet14blockPopcounts p 0) (by bpStrict14 p, hpi) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 1 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e0 : facet14blockPopcounts q 0 + 1 = facet14blockPopcounts p 0 := by
        first
        | (simp only [bp14_0, facet14bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_0, facet14bit, hother 0 (by decide), hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts q 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts q 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e0]
      exact facet14G_lip_0 (facet14blockPopcounts q 0) (by bpStrict14 q, hqi) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 2 (block 1)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 2 (!(p 2))) j)) ≤ 1
    set q := Function.update p 2 (!(p 2)) with hq
    have hother : ∀ x : Fin 13, x ≠ 2 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 2 with
    | false =>
      have hqi : q 2 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 + 1 := by
        first
        | (simp only [bp14_1, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_1, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_1 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpStrict14 p, hpi) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 2 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e1 : facet14blockPopcounts q 1 + 1 = facet14blockPopcounts p 1 := by
        first
        | (simp only [bp14_1, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_1, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts q 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts q 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e1]
      exact facet14G_lip_1 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts q 1) (by bpStrict14 q, hqi) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 3 (block 2)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 3 (!(p 3))) j)) ≤ 1
    set q := Function.update p 3 (!(p 3)) with hq
    have hother : ∀ x : Fin 13, x ≠ 3 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 3 with
    | false =>
      have hqi : q 3 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 + 1 := by
        first
        | (simp only [bp14_2, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_2, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_2 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpStrict14 p, hpi) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 3 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e2 : facet14blockPopcounts q 2 + 1 = facet14blockPopcounts p 2 := by
        first
        | (simp only [bp14_2, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_2, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts q 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts q 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e2]
      exact facet14G_lip_2 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts q 2) (by bpStrict14 q, hqi) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 4 (block 3)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 4 (!(p 4))) j)) ≤ 1
    set q := Function.update p 4 (!(p 4)) with hq
    have hother : ∀ x : Fin 13, x ≠ 4 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 4 with
    | false =>
      have hqi : q 4 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 + 1 := by
        first
        | (simp only [bp14_3, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_3, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_3 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpStrict14 p, hpi) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 4 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e3 : facet14blockPopcounts q 3 + 1 = facet14blockPopcounts p 3 := by
        first
        | (simp only [bp14_3, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_3, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e4, e5, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts q 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts q 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e3]
      exact facet14G_lip_3 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts q 3) (by bpStrict14 q, hqi) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 5 (block 4)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 5 (!(p 5))) j)) ≤ 1
    set q := Function.update p 5 (!(p 5)) with hq
    have hother : ∀ x : Fin 13, x ≠ 5 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 5 with
    | false =>
      have hqi : q 5 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 + 1 := by
        first
        | (simp only [bp14_4, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_4, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_4 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpStrict14 p, hpi) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 5 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e4 : facet14blockPopcounts q 4 + 1 = facet14blockPopcounts p 4 := by
        first
        | (simp only [bp14_4, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_4, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e5, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts q 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts q 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e4]
      exact facet14G_lip_4 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts q 4) (by bpStrict14 q, hqi) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 6 (block 5)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 6 (!(p 6))) j)) ≤ 1
    set q := Function.update p 6 (!(p 6)) with hq
    have hother : ∀ x : Fin 13, x ≠ 6 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 6 with
    | false =>
      have hqi : q 6 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 + 1 := by
        first
        | (simp only [bp14_5, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_5, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_5 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpStrict14 p, hpi) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 6 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e5 : facet14blockPopcounts q 5 + 1 = facet14blockPopcounts p 5 := by
        first
        | (simp only [bp14_5, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_5, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e6, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts q 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts q 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e5]
      exact facet14G_lip_5 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts q 5) (by bpStrict14 q, hqi) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 7 (block 6)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 7 (!(p 7))) j)) ≤ 1
    set q := Function.update p 7 (!(p 7)) with hq
    have hother : ∀ x : Fin 13, x ≠ 7 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 7 with
    | false =>
      have hqi : q 7 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 + 1 := by
        first
        | (simp only [bp14_6, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_6, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_6 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpStrict14 p, hpi) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 7 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e6 : facet14blockPopcounts q 6 + 1 = facet14blockPopcounts p 6 := by
        first
        | (simp only [bp14_6, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_6, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e7, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts q 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts q 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e6]
      exact facet14G_lip_6 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts q 6) (by bpStrict14 q, hqi) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 8 (block 7)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 8 (!(p 8))) j)) ≤ 1
    set q := Function.update p 8 (!(p 8)) with hq
    have hother : ∀ x : Fin 13, x ≠ 8 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 8 with
    | false =>
      have hqi : q 8 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 + 1 := by
        first
        | (simp only [bp14_7, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_7, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_7 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpStrict14 p, hpi) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 8 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e7 : facet14blockPopcounts q 7 + 1 = facet14blockPopcounts p 7 := by
        first
        | (simp only [bp14_7, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_7, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e8, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts q 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts q 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e7]
      exact facet14G_lip_7 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts q 7) (by bpStrict14 q, hqi) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 9 (block 8)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 9 (!(p 9))) j)) ≤ 1
    set q := Function.update p 9 (!(p 9)) with hq
    have hother : ∀ x : Fin 13, x ≠ 9 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 9 with
    | false =>
      have hqi : q 9 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 + 1 := by
        first
        | (simp only [bp14_8, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_8, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_8 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpStrict14 p, hpi) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 9 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e8 : facet14blockPopcounts q 8 + 1 = facet14blockPopcounts p 8 := by
        first
        | (simp only [bp14_8, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_8, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e9, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts q 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts q 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e8]
      exact facet14G_lip_8 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts q 8) (by bpStrict14 q, hqi) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 10 (block 9)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 10 (!(p 10))) j)) ≤ 1
    set q := Function.update p 10 (!(p 10)) with hq
    have hother : ∀ x : Fin 13, x ≠ 10 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 10 with
    | false =>
      have hqi : q 10 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 + 1 := by
        first
        | (simp only [bp14_9, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_9, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_9 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpStrict14 p, hpi) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 10 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e9 : facet14blockPopcounts q 9 + 1 = facet14blockPopcounts p 9 := by
        first
        | (simp only [bp14_9, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_9, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e10, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts q 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts q 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e9]
      exact facet14G_lip_9 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts q 9) (by bpStrict14 q, hqi) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 11 (block 10)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 11 (!(p 11))) j)) ≤ 1
    set q := Function.update p 11 (!(p 11)) with hq
    have hother : ∀ x : Fin 13, x ≠ 11 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 := by
      simp only [bp14_11, facet14bit, hother 12 (by decide)]
    cases hpi : p 11 with
    | false =>
      have hqi : q 11 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 + 1 := by
        first
        | (simp only [bp14_10, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_10, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_10 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpStrict14 p, hpi) (facet14blockPopcounts p 11) (by bpLoose14 p)
    | true =>
      have hqi : q 11 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e10 : facet14blockPopcounts q 10 + 1 = facet14blockPopcounts p 10 := by
        first
        | (simp only [bp14_10, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_10, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e11]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts q 10) (facet14blockPopcounts p 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts q 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e10]
      exact facet14G_lip_10 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts q 10) (by bpStrict14 q, hqi) (facet14blockPopcounts p 11) (by bpLoose14 p)
  · -- flip input bit 12 (block 11)
    show (∑ j, bdiff (facet14f p j)
          (facet14f (Function.update p 12 (!(p 12))) j)) ≤ 1
    set q := Function.update p 12 (!(p 12)) with hq
    have hother : ∀ x : Fin 13, x ≠ 12 → q x = p x :=
      fun x hx => Function.update_of_ne hx _ _
    have e0 : facet14blockPopcounts q 0 = facet14blockPopcounts p 0 := by
      simp only [bp14_0, facet14bit, hother 0 (by decide), hother 1 (by decide)]
    have e1 : facet14blockPopcounts q 1 = facet14blockPopcounts p 1 := by
      simp only [bp14_1, facet14bit, hother 2 (by decide)]
    have e2 : facet14blockPopcounts q 2 = facet14blockPopcounts p 2 := by
      simp only [bp14_2, facet14bit, hother 3 (by decide)]
    have e3 : facet14blockPopcounts q 3 = facet14blockPopcounts p 3 := by
      simp only [bp14_3, facet14bit, hother 4 (by decide)]
    have e4 : facet14blockPopcounts q 4 = facet14blockPopcounts p 4 := by
      simp only [bp14_4, facet14bit, hother 5 (by decide)]
    have e5 : facet14blockPopcounts q 5 = facet14blockPopcounts p 5 := by
      simp only [bp14_5, facet14bit, hother 6 (by decide)]
    have e6 : facet14blockPopcounts q 6 = facet14blockPopcounts p 6 := by
      simp only [bp14_6, facet14bit, hother 7 (by decide)]
    have e7 : facet14blockPopcounts q 7 = facet14blockPopcounts p 7 := by
      simp only [bp14_7, facet14bit, hother 8 (by decide)]
    have e8 : facet14blockPopcounts q 8 = facet14blockPopcounts p 8 := by
      simp only [bp14_8, facet14bit, hother 9 (by decide)]
    have e9 : facet14blockPopcounts q 9 = facet14blockPopcounts p 9 := by
      simp only [bp14_9, facet14bit, hother 10 (by decide)]
    have e10 : facet14blockPopcounts q 10 = facet14blockPopcounts p 10 := by
      simp only [bp14_10, facet14bit, hother 11 (by decide)]
    cases hpi : p 12 with
    | false =>
      have hqi : q 12 = true := by rw [hq, Function.update_self, hpi]; rfl
      have e11 : facet14blockPopcounts q 11 = facet14blockPopcounts p 11 + 1 := by
        first
        | (simp only [bp14_11, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_11, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      exact facet14G_lip_11 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts p 11) (by bpStrict14 p, hpi)
    | true =>
      have hqi : q 12 = false := by rw [hq, Function.update_self, hpi]; rfl
      have e11 : facet14blockPopcounts q 11 + 1 = facet14blockPopcounts p 11 := by
        first
        | (simp only [bp14_11, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]; omega)
        | simp only [bp14_11, facet14bit, hqi, hpi, Bool.false_eq_true, if_false, if_true]
      rw [facet14f_eq p, facet14f_eq q, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      rw [show (∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts q 11) j))
          = ∑ j, bdiff (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts q 11) j) (facet14G (facet14blockPopcounts p 0) (facet14blockPopcounts p 1) (facet14blockPopcounts p 2) (facet14blockPopcounts p 3) (facet14blockPopcounts p 4) (facet14blockPopcounts p 5) (facet14blockPopcounts p 6) (facet14blockPopcounts p 7) (facet14blockPopcounts p 8) (facet14blockPopcounts p 9) (facet14blockPopcounts p 10) (facet14blockPopcounts p 11) j)
        from Finset.sum_congr rfl (fun j _ => bdiff_comm _ _)]
      rw [← e11]
      exact facet14G_lip_11 (facet14blockPopcounts p 0) (by bpLoose14 p) (facet14blockPopcounts p 1) (by bpLoose14 p) (facet14blockPopcounts p 2) (by bpLoose14 p) (facet14blockPopcounts p 3) (by bpLoose14 p) (facet14blockPopcounts p 4) (by bpLoose14 p) (facet14blockPopcounts p 5) (by bpLoose14 p) (facet14blockPopcounts p 6) (by bpLoose14 p) (facet14blockPopcounts p 7) (by bpLoose14 p) (facet14blockPopcounts p 8) (by bpLoose14 p) (facet14blockPopcounts p 9) (by bpLoose14 p) (facet14blockPopcounts p 10) (by bpLoose14 p) (facet14blockPopcounts q 11) (by bpStrict14 q, hqi)


variable {bd : Finset V}
variable {A : Fin 6 → Finset V}

/-- The `i`-th larger-side region. -/
def facet14L (A : Fin 6 → Finset V) (i : Fin 13) : Finset V := (facet14L_reg i).biUnion A

/-- The `j`-th bounded-side region. -/
def facet14R (A : Fin 6 → Finset V) (j : Fin 17) : Finset V := (facet14R_reg j).biUnion A

/-- **Global nonexpansiveness of `facet14f`, derived from the single-flip reduction.** -/
theorem facet14f_nonexpansive_via_singleFlip (p q : Fin 13 → Bool) :
    (∑ j, bdiff (facet14f p j) (facet14f q j)) ≤ ∑ i, bdiff (p i) (q i) :=
  nonexpansive_of_singleFlip facet14f facet14f_singleFlip p q

/-- The boundary input patterns map through `facet14f` exactly to the bounded-region pattern. -/
lemma facet14f_boundary (c : Fin 6) :
    facet14f (fun i => decide (c ∈ facet14L_reg i)) = fun j => decide (c ∈ facet14R_reg j) := by
  fin_cases c <;> · funext j; fin_cases j <;> rfl

/-- The purifier pattern maps to all `false`. -/
lemma facet14f_zero : facet14f (fun _ => false) = fun _ => false := by
  funext j; fin_cases j <;> rfl

/-- Membership of `v ∈ A c` in a larger-side region. -/
lemma mem_facet14L_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (i : Fin 13) :
    v ∈ facet14L A i ↔ c ∈ facet14L_reg i := by
  unfold facet14L
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- `facet14R A j ⊆ bd`. -/
lemma facet14R_sub (hR : Regions6 bd A) (j : Fin 17) : facet14R A j ⊆ bd := by
  unfold facet14R
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- `facet14L A i ⊆ bd`. -/
lemma facet14L_sub (hR : Regions6 bd A) (i : Fin 13) : facet14L A i ⊆ bd := by
  unfold facet14L
  exact Finset.biUnion_subset.2 (fun c _ => hR.sub c)

/-- Membership of `v ∈ A c` in a bounded region. -/
lemma mem_facet14R_of_color (hR : Regions6 bd A) {v : V} {c : Fin 6} (hv : v ∈ A c) (j : Fin 17) :
    v ∈ facet14R A j ↔ c ∈ facet14R_reg j := by
  unfold facet14R
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c', hc', hvc'⟩
    by_cases h : c = c'
    · rwa [h]
    · exact absurd rfl ((hR.disj c c' h).forall_ne_finset hv hvc')
  · exact fun hc => ⟨c, hc, hv⟩

/-- For a boundary vertex of color `c`, the achieving cuts realize the larger-side pattern. -/
lemma contractionPattern_of_color_14 (hR : Regions6 bd A)
    (X : Fin 13 → Finset V) (hX : ∀ i, IsRTCut bd (facet14L A i) (X i))
    {v : V} {c : Fin 6} (hv : v ∈ A c) :
    contractionPattern X v = fun i => decide (c ∈ facet14L_reg i) := by
  funext i
  simp only [contractionPattern, mem]
  by_cases hc : c ∈ facet14L_reg i
  · have : v ∈ X i := (hX i).1 ((mem_facet14L_of_color hR hv i).2 hc)
    simp [this, hc]
  · have hvL : v ∉ facet14L A i := fun h => hc ((mem_facet14L_of_color hR hv i).1 h)
    have : v ∉ X i := (hX i).2 v (hR.sub c hv) hvL
    simp [this, hc]

/-- For a purifier vertex, the achieving cuts realize the all-`false` pattern. -/
lemma contractionPattern_of_purifier_14
    (X : Fin 13 → Finset V) (hX : ∀ i, IsRTCut bd (facet14L A i) (X i))
    {v : V} (hvbd : v ∈ bd) (hvout : ∀ c, v ∉ A c) :
    contractionPattern X v = fun _ => false := by
  funext i
  simp only [contractionPattern, mem]
  have hvL : v ∉ facet14L A i := by
    unfold facet14L
    rw [Finset.mem_biUnion]
    rintro ⟨c, _, hvc⟩
    exact hvout c hvc
  have : v ∉ X i := (hX i).2 v hvbd hvL
  simp [this]

/-- **Validity of the recombined candidate cuts.** -/
lemma facet14_hvalid (hR : Regions6 bd A)
    (X : Fin 13 → Finset V) (hX : ∀ i, IsRTCut bd (facet14L A i) (X i)) (j : Fin 17) :
    IsRTCut bd (facet14R A j) (contractionCut X facet14f j) := by
  have hkey : ∀ v ∈ bd, mem (contractionCut X facet14f j) v = mem (facet14R A j) v := by
    intro v hvbd
    rw [mem_contractionCut]
    by_cases hcolor : ∃ c, v ∈ A c
    · obtain ⟨c, hvc⟩ := hcolor
      rw [contractionPattern_of_color_14 hR X hX hvc, facet14f_boundary c]
      simp only [mem]
      rw [decide_eq_decide]
      exact (mem_facet14R_of_color hR hvc j).symm
    · simp only [not_exists] at hcolor
      rw [contractionPattern_of_purifier_14 X hX hvbd hcolor, facet14f_zero]
      have : v ∉ facet14R A j := by
        unfold facet14R
        rw [Finset.mem_biUnion]
        rintro ⟨c, _, hvc⟩
        exact hcolor c hvc
      simp [mem, this]
  refine ⟨fun x hx => ?_, fun x hxbd hxout => ?_⟩
  · have hxbd : x ∈ bd := facet14R_sub hR j hx
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact this.2 hx
  · intro hxin
    have := hkey x hxbd
    simp only [mem] at this
    rw [decide_eq_decide] at this
    exact hxout (this.1 hxin)

/-- **A six-party holographic entropy cone facet (database index 14).**
For six pairwise-disjoint boundary regions in any finite undirected nonnegative-real-weighted
graph, the 13 larger-side regions dominate the 17 bounded-side regions. Source: the
six-party holographic entropy cone / Hernández-Cuenca holographic entropy cone database. The
contraction map is handled by a count-lattice factorisation
(`facet14f = facet14G ∘ facet14blockPopcounts`); its Hamming-nonexpansiveness comes from
the single-flip reduction over the block-popcount lattice (one block has multiplicity two). -/
theorem rtEntropyR_newFacet_n6_14 (G : GraphR V) {bd : Finset V} {A : Fin 6 → Finset V}
    (hR : Regions6 bd A) :
    (∑ j, rtEntropyR G bd (facet14R A j) (facet14R_sub hR j))
      ≤ ∑ i, rtEntropyR G bd (facet14L A i) (facet14L_sub hR i) := by
  have hXex : ∀ i, ∃ S, IsRTCut bd (facet14L A i) S
      ∧ rtEntropyR G bd (facet14L A i) (facet14L_sub hR i) = cutCapacityR G S :=
    fun i => rtEntropyR_eq_cap G (facet14L_sub hR i)
  choose X hXcut hXcap using hXex
  have hXok : ∀ i, IsRTCut bd (facet14L A i) (X i)
      ∧ cutCapacityR G (X i) = rtEntropyR G bd (facet14L A i) (facet14L_sub hR i) :=
    fun i => ⟨hXcut i, (hXcap i).symm⟩
  have hvalid : ∀ j, IsRTCut bd (facet14R A j) (contractionCut X facet14f j) :=
    fun j => facet14_hvalid hR X hXcut j
  exact entropyR_ineq_of_contraction G (facet14L A) (facet14R A)
    (facet14L_sub hR) (facet14R_sub hR) X hXok facet14f hvalid
    facet14f_nonexpansive_via_singleFlip

/-! ### Anti-vacuity witness: a strict six-party instance on the perfect-tensor star. -/

/-- `facet14R star6A j ⊆ star6Bd`. -/
lemma star6_facet14R_sub (j : Fin 17) : facet14R star6A j ⊆ star6Bd :=
  facet14R_sub star6A_regions j
/-- `facet14L star6A i ⊆ star6Bd`. -/
lemma star6_facet14L_sub (i : Fin 13) : facet14L star6A i ⊆ star6Bd :=
  facet14L_sub star6A_regions i

/-- Each bounded-region entropy of the star witness, as a vector of values. -/
lemma star6_facet14R (j : Fin 17) :
    rtEntropy star6Graph star6Bd (facet14R star6A j) (star6_facet14R_sub j)
      = ((![1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 2, 2] : Fin 17 → ℕ) j) := by
  fin_cases j <;> · unfold facet14R facet14R_reg star6A; decide

/-- Each larger-side region entropy of the star witness, as a vector of values. -/
lemma star6_facet14L (i : Fin 13) :
    rtEntropy star6Graph star6Bd (facet14L star6A i) (star6_facet14L_sub i)
      = ((![2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 13 → ℕ) i) := by
  fin_cases i <;> · unfold facet14L facet14L_reg star6A; decide

/-- **Strict six-party anti-vacuity witness.** On the cast star graph the facet inequality is
strict: the bounded side sums to 31 and the larger side to 36 (slack 5). -/
theorem rtEntropyR_newFacet_n6_14_strict_witness :
    (∑ j, rtEntropyR (castGraph star6Graph) star6Bd (facet14R star6A j)
        (facet14R_sub (A := star6A) star6A_regions j))
      < ∑ i, rtEntropyR (castGraph star6Graph) star6Bd (facet14L star6A i)
        (facet14L_sub (A := star6A) star6A_regions i) := by
  have hreg : ∀ j, rtEntropyR (castGraph star6Graph) star6Bd (facet14R star6A j)
      (facet14R_sub (A := star6A) star6A_regions j) = ((![1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 2, 2] : Fin 17 → ℕ) j : ℝ) := by
    intro j
    rw [rtEntropyR_castGraph, star6_facet14R j]
  have hlar : ∀ i, rtEntropyR (castGraph star6Graph) star6Bd (facet14L star6A i)
      (facet14L_sub (A := star6A) star6A_regions i) = ((![2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : Fin 13 → ℕ) i : ℝ) := by
    intro i
    rw [rtEntropyR_castGraph, star6_facet14L i]
  rw [Finset.sum_congr rfl (fun j _ => hreg j), Finset.sum_congr rfl (fun i _ => hlar i)]
  simp [Fin.sum_univ_succ]
  norm_num

/-- All min-cut entropies in the six-party strict witness are strictly positive. -/
theorem rtEntropyR_newFacet_n6_14_witness_mincuts_pos :
    (∀ j, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet14R star6A j)
        (facet14R_sub (A := star6A) star6A_regions j))
      ∧ ∀ i, 0 < rtEntropyR (castGraph star6Graph) star6Bd (facet14L star6A i)
        (facet14L_sub (A := star6A) star6A_regions i) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [rtEntropyR_castGraph, star6_facet14R j]; fin_cases j <;> norm_num
  · rw [rtEntropyR_castGraph, star6_facet14L i]; fin_cases i <;> norm_num

end Facet6n14

end Physlib.UndirectedMMICertificate
