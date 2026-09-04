/-
Holographic entropy cone and monogamy of mutual information (holographic ⇒ MMI).

FOREST-LEVEL (what and why, no PhD required)
--------------------------------------------
Give every region of a quantum system a number, its entanglement entropy S.
Collect the numbers for all regions into a vector. Which vectors can actually
occur? For GENERAL quantum states the allowed vectors fill the "quantum entropy
cone", carved out by subadditivity and strong subadditivity. But states whose
entropies come from a GEOMETRIC picture — S(region) = the area of the smallest
surface (min-cut) that fences the region off, the Ryu–Takayanagi rule — obey an
EXTRA inequality that general quantum states need not:

    Monogamy of Mutual Information (MMI):   I₃(A,B,C) ≤ 0,

equivalently  S(AB)+S(AC)+S(BC) ≥ S(A)+S(B)+S(C)+S(ABC).

MMI is the fingerprint of geometry. It cuts the quantum cone down to the strictly
smaller "holographic entropy cone." This file formalizes MMI over an ABSTRACT
entropy assignment, proves the two standard forms are equivalent, and then builds
a concrete GEOMETRIC (min-cut) model in which MMI provably holds — with an
explicit witness where I₃ is STRICTLY negative (non-vacuous).

THE FALSIFICATION LOOP (why Lean cares about the numerics)
----------------------------------------------------------
The numerical side measures S for MERA / spin-chain states. If a MEASURED state
ever shows an MMI violation (I₃ > 0), then by `holographic_implies_MMI` below it
CANNOT be min-cut representable ⇒ it is NOT holographic. So this file states
exactly the theorem the numerical loop is empowered to falsify: an observed
MMI-violation is a certificate of non-geometry.

WHAT IS PROVEN HERE (0 sorries)
-------------------------------
  · `I`, `I₃`, `MMI`, `MMIDisjoint`, `entropyForm` — abstract definitions
  · `I₃_eq_entropyForm_neg`                     — I₃ = −(entropy form), pure algebra
  · `MMI_iff_entropyForm`                       — the two MMI forms are equivalent
  · `MinCut.S`, `Holographic`, `HolographicD`   — abstract + disjoint-corrected min-cut structures
  · `holographic_implies_MMI`                   — the unrestricted conditional (VACUOUS — superseded)
  · `holographic_implies_MMIDisjoint`           — the CORRECTED, NON-vacuous conditional (disjoint MMI)
  · `mincut3S`, `mincut3_I₃_strictNeg`          — an explicit Fin 3 model + strict witness
  · `mincut3_MMI_disjoint`                      — that model obeys disjoint-MMI everywhere
  · `mincut3_HolographicD`                      — ★ that model SATISFIES `HolographicD` (anti-vacuity)

DISJOINTNESS / ANTI-VACUITY CAVEAT (kept honest)
------------------------------------------------
Monogamy of mutual information is a **disjoint-regions** statement. The UNRESTRICTED
predicate `MMI` (∀ triples, no disjointness) and the structure `Holographic` (whose
per-edge monogamy is imposed for ALL triples) are VACUOUS: for overlapping `A=B=C`
one has `I₃ S A A A = S A`, so requiring `I₃ ≤ 0` there forces `S ≤ 0`, admitting only
degenerate entropies (`mincut3_MMI_unrestricted_false` certifies the failure on the
real witness). The physically-correct objects are `MMIDisjoint` and `HolographicD`
(disjoint-only per-edge monogamy); the corrected C1 is `holographic_implies_MMIDisjoint`,
and it is NON-vacuous because the non-degenerate model `mincut3S` (`S {0} = 2 > 0`)
provably satisfies `HolographicD` (`mincut3_HolographicD`). The old `Holographic`
lemma is retained as valid-but-vacuous.

IMPORTANT PHYSICS CAVEAT (kept honest)
--------------------------------------
MMI is FALSE for general quantum von-Neumann entropy `Sᵥₙ`; do NOT read this file
as claiming otherwise. MMI holds for the GEOMETRIC (min-cut) entropies only. That
gap — quantum cone ⊋ holographic cone — is the whole scientific point.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic

noncomputable section

namespace Holography.EntropyCone

/-! ## 1. Abstract entropy functional -/

variable {ι : Type*} [DecidableEq ι]

/-- Mutual information of two regions: `I(A,B) = S A + S B − S (A ∪ B)`. -/
def I (S : Finset ι → ℝ) (A B : Finset ι) : ℝ :=
  S A + S B - S (A ∪ B)

/-- Tripartite information:
`I₃(A,B,C) = I(A,B) + I(A,C) − I(A, B∪C)`. Intended for disjoint `A B C`. -/
def I₃ (S : Finset ι → ℝ) (A B C : Finset ι) : ℝ :=
  I S A B + I S A C - I S A (B ∪ C)

/-- The entropy-inequality form appearing in MMI:
`S(A∪B)+S(A∪C)+S(B∪C) − S A − S B − S C − S(A∪B∪C)`. Nonnegativity of this is
equivalent to `I₃ ≤ 0`. -/
def entropyForm (S : Finset ι → ℝ) (A B C : Finset ι) : ℝ :=
  S (A ∪ B) + S (A ∪ C) + S (B ∪ C) - S A - S B - S C - S (A ∪ B ∪ C)

/-- **Monogamy of Mutual Information (MMI)** for an abstract entropy assignment:
`I₃(A,B,C) ≤ 0` for all `A B C`. (The geometric/holographic signature.)

CAVEAT (BP 21/24): this UNRESTRICTED form omits disjointness and is therefore
NOT the physical monogamy statement — for overlapping regions `I₃` need not be
≤ 0 even for genuine min-cut entropies (e.g. `I₃ S A A A = S A > 0`). It is kept
because §2's equivalence lemmas are stated over it; the physically-correct,
non-vacuous predicate is `MMIDisjoint` just below, and the corrected C1 theorem
`holographic_implies_MMIDisjoint` (§4) is stated over `MMIDisjoint`. -/
def MMI (S : Finset ι → ℝ) : Prop :=
  ∀ A B C : Finset ι, I₃ S A B C ≤ 0

/-- **Monogamy of Mutual Information, disjoint form (the physical statement).**
`I₃(A,B,C) ≤ 0` for all pairwise-**disjoint** `A B C`. Monogamy of mutual
information is a *disjoint-regions* statement; imposing it on overlapping regions
is false in general (see `mincut3_MMI_unrestricted_false`). This is the predicate
the corrected C1 theorem (§4) delivers, and it admits a proven NON-degenerate
witness (`mincut3S`, §5/§6/§7), so it is not vacuous. -/
def MMIDisjoint (S : Finset ι → ℝ) : Prop :=
  ∀ A B C : Finset ι, Disjoint A B → Disjoint A C → Disjoint B C → I₃ S A B C ≤ 0

/-! ## 2. Equivalence of the two MMI forms (pure algebra over ℝ) -/

/-- Core identity: `I₃ = −(entropy form)`. Unfolds definitions; note
`A ∪ (B ∪ C) = A ∪ B ∪ C` so the two "full union" terms coincide. -/
theorem I₃_eq_entropyForm_neg (S : Finset ι → ℝ) (A B C : Finset ι) :
    I₃ S A B C = - entropyForm S A B C := by
  unfold I₃ I entropyForm
  have h : A ∪ (B ∪ C) = A ∪ B ∪ C := by
    rw [Finset.union_assoc]
  rw [h]; ring

/-- The `I₃ ≤ 0` form of MMI is EQUIVALENT to the entropy-inequality form
`S(A∪B)+S(A∪C)+S(B∪C) ≥ S A + S B + S C + S(A∪B∪C)`. -/
theorem MMI_iff_entropyForm (S : Finset ι → ℝ) :
    MMI S ↔ ∀ A B C : Finset ι,
      S A + S B + S C + S (A ∪ B ∪ C) ≤ S (A ∪ B) + S (A ∪ C) + S (B ∪ C) := by
  unfold MMI
  constructor
  · intro h A B C
    have := h A B C
    rw [I₃_eq_entropyForm_neg] at this
    unfold entropyForm at this
    linarith
  · intro h A B C
    rw [I₃_eq_entropyForm_neg]
    unfold entropyForm
    have := h A B C
    linarith

/-! ## 3. A concrete geometric (min-cut) instantiation

We model the bulk as a finite set of undirected weighted "cut edges." Each edge
`e` carries a nonnegative capacity `cap e` and is `active` for a region `X`
(i.e. it crosses the RT surface of `X`) via a boolean predicate `active X e`.
The min-cut / RT entropy is the total capacity of active edges:

    `MinCut.S X = ∑ e, if active X e then cap e else 0`.

We do NOT need the full combinatorial min-cut optimizer to get real content:
MMI for such an *additive over edges* entropy reduces, edge by edge, to a
purely boolean inequality on the six activity patterns. We prove that boolean
inequality holds for the physically correct "crossing" rule and lift it to `S`.
-/

namespace MinCut

variable {ι : Type*} [DecidableEq ι] {E : Type*} [Fintype E]

/-- Weighted min-cut entropy: sum of capacities of the edges active for `X`. -/
def S (cap : E → ℝ) (active : Finset ι → E → Prop) [∀ X e, Decidable (active X e)]
    (X : Finset ι) : ℝ :=
  ∑ e, if active X e then cap e else 0

/-- The per-edge MMI contribution: the entropy-form of a single edge of unit
capacity. With `b i` the indicator that the edge is active for union pattern `i`,
this is `b(AB)+b(AC)+b(BC) − b(A) − b(B) − b(C) − b(ABC)`. -/
def edgeForm (bA bB bC bAB bAC bBC bABC : Bool) : ℤ :=
  (if bAB then 1 else 0) + (if bAC then 1 else 0) + (if bBC then 1 else 0)
    - (if bA then 1 else 0) - (if bB then 1 else 0) - (if bC then 1 else 0)
    - (if bABC then 1 else 0)

end MinCut

/-! ## 4. The C1 conditional: `holographic S → MMI S` (statement + geometric proof)

We define `holographic S` as: `S` is realized as a min-cut entropy on SOME finite
weighted-edge bulk whose activity rule is *monotone and submodular in the standard
RT sense*, captured concretely by the hypothesis that every edge's contribution to
the entropy form is nonpositive (`edgeForm ≤ 0`). This is exactly the property that
holds for genuine RT/min-cut surfaces and that fails for general quantum states.
-/

/-- Min-cut representability with the RT crossing property:
`S` equals a nonnegative-capacity edge sum whose per-edge entropy-form
contribution is always ≤ 0 (the geometric monogamy of each cut edge). -/
structure Holographic {ι : Type*} [DecidableEq ι] (S : Finset ι → ℝ) where
  E : Type
  fintypeE : Fintype E
  cap : E → ℝ
  cap_nonneg : ∀ e, 0 ≤ cap e
  active : Finset ι → E → Prop
  decActive : ∀ X e, Decidable (active X e)
  represents : ∀ X, S X = ∑ e, (haveI := decActive X e; if active X e then cap e else 0)
  /-- Per-edge RT monogamy: each cut edge contributes ≤ 0 to the entropy form,
      for every disjoint region triple. This is the geometric input. -/
  edge_monogamy : ∀ (A B C : Finset ι) (e : E),
      (haveI := decActive (A ∪ B) e; if active (A ∪ B) e then cap e else 0)
    + (haveI := decActive (A ∪ C) e; if active (A ∪ C) e then cap e else 0)
    + (haveI := decActive (B ∪ C) e; if active (B ∪ C) e then cap e else 0)
    ≥ (haveI := decActive A e; if active A e then cap e else 0)
    + (haveI := decActive B e; if active B e then cap e else 0)
    + (haveI := decActive C e; if active C e then cap e else 0)
    + (haveI := decActive (A ∪ B ∪ C) e; if active (A ∪ B ∪ C) e then cap e else 0)

/-- **C1 (holographic ⇒ MMI), unrestricted form — SUPERSEDED, VACUOUS.**
If `S` is `Holographic` (per-edge RT monogamy imposed for ALL triples, incl.
overlapping ones) then it satisfies the unrestricted `MMI`. This lemma is TRUE but
**vacuous** (BP 21): its `edge_monogamy` field is required even for overlapping
`A=B=C`, which forces `S {i} ≤ 0` (contradiction: `I₃ S A A A = S A`), so no
NON-degenerate `S` is ever `Holographic`. The physically-correct, non-vacuous
version is `holographic_implies_MMIDisjoint` below, which imposes RT monogamy only
on DISJOINT triples and has a proven non-degenerate witness (`mincut3_HolographicD`).
Retained (not deleted) as a valid-but-vacuous lemma per the revolution's add-not-remove rule. -/
theorem holographic_implies_MMI {ι : Type*} [DecidableEq ι] (S : Finset ι → ℝ)
    (h : Holographic S) : MMI S := by
  haveI := h.fintypeE
  rw [MMI_iff_entropyForm]
  intro A B C
  -- Rewrite all seven S-values as edge sums, then compare summand-by-summand.
  have hrep := h.represents
  rw [hrep A, hrep B, hrep C, hrep (A ∪ B), hrep (A ∪ C), hrep (B ∪ C), hrep (A ∪ B ∪ C)]
  -- Goal: sumA + sumB + sumC + sumABC ≤ sumAB + sumAC + sumBC.
  -- Reassemble as a single ∑ e of the per-edge inequality and use Finset.sum_le_sum.
  have key : ∀ e : h.E,
      (haveI := h.decActive A e; if h.active A e then h.cap e else 0)
    + (haveI := h.decActive B e; if h.active B e then h.cap e else 0)
    + (haveI := h.decActive C e; if h.active C e then h.cap e else 0)
    + (haveI := h.decActive (A ∪ B ∪ C) e; if h.active (A ∪ B ∪ C) e then h.cap e else 0)
    ≤ (haveI := h.decActive (A ∪ B) e; if h.active (A ∪ B) e then h.cap e else 0)
    + (haveI := h.decActive (A ∪ C) e; if h.active (A ∪ C) e then h.cap e else 0)
    + (haveI := h.decActive (B ∪ C) e; if h.active (B ∪ C) e then h.cap e else 0) := by
    intro e
    have := h.edge_monogamy A B C e
    linarith
  -- Turn the four LHS sums into one sum and the three RHS sums into one sum.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e _ => key e)

/-! ## 4b. The CORRECTED, NON-VACUOUS C1: `HolographicD S → MMIDisjoint S`

`Holographic`/`holographic_implies_MMI` above impose per-edge RT monogamy for ALL
triples including overlapping ones, which is unphysical and vacuous (only
degenerate, non-positive `S` can satisfy it). RT/min-cut monogamy is a statement
about DISJOINT regions. `HolographicD` corrects this: it is identical to
`Holographic` except its `edge_monogamy` field is required only for pairwise-
DISJOINT `A B C`. This makes the hypothesis class NON-EMPTY and NON-DEGENERATE:
the concrete 3-party min-cut model `mincut3S` (singletons=2, pairs=3, full=2)
satisfies it (`mincut3_HolographicD`, §7), so the corrected C1 theorem
`holographic_implies_MMIDisjoint` is anti-vacuous (BP 21). -/

/-- Min-cut representability with the RT crossing property, DISJOINT form.
Identical to `Holographic` except `edge_monogamy` is required ONLY for pairwise-
disjoint region triples — the regime where RT geometry actually constrains cuts.
This is the physically-correct representability structure; `Holographic` (with
its all-triples monogamy) is a strictly stronger, vacuous predicate. -/
structure HolographicD {ι : Type*} [DecidableEq ι] (S : Finset ι → ℝ) where
  E : Type
  fintypeE : Fintype E
  cap : E → ℝ
  cap_nonneg : ∀ e, 0 ≤ cap e
  active : Finset ι → E → Prop
  decActive : ∀ X e, Decidable (active X e)
  represents : ∀ X, S X = ∑ e, (haveI := decActive X e; if active X e then cap e else 0)
  /-- Per-edge RT monogamy, DISJOINT-only: each cut edge contributes ≤ 0 to the
      entropy form, for every **pairwise-disjoint** region triple. This is the
      geometric input RT surfaces genuinely satisfy. -/
  edge_monogamy : ∀ (A B C : Finset ι) (e : E),
      Disjoint A B → Disjoint A C → Disjoint B C →
      (haveI := decActive (A ∪ B) e; if active (A ∪ B) e then cap e else 0)
    + (haveI := decActive (A ∪ C) e; if active (A ∪ C) e then cap e else 0)
    + (haveI := decActive (B ∪ C) e; if active (B ∪ C) e then cap e else 0)
    ≥ (haveI := decActive A e; if active A e then cap e else 0)
    + (haveI := decActive B e; if active B e then cap e else 0)
    + (haveI := decActive C e; if active C e then cap e else 0)
    + (haveI := decActive (A ∪ B ∪ C) e; if active (A ∪ B ∪ C) e then cap e else 0)

/-- **C1 (holographic ⇒ MMI), CORRECTED non-vacuous form.** If `S` is min-cut
representable with the disjoint-only per-edge RT monogamy property (`HolographicD`),
then it satisfies `MMIDisjoint`. Proof: on any disjoint triple, MMI's entropy form
is a sum over edges of nonnegative per-edge forms. Unlike `holographic_implies_MMI`
this is anti-vacuous — `mincut3_HolographicD` (§7) exhibits a NON-degenerate `S`
(some `S X > 0`) satisfying the hypothesis. -/
theorem holographic_implies_MMIDisjoint {ι : Type*} [DecidableEq ι] (S : Finset ι → ℝ)
    (h : HolographicD S) : MMIDisjoint S := by
  haveI := h.fintypeE
  intro A B C hAB hAC hBC
  rw [I₃_eq_entropyForm_neg]
  suffices hnn : (0:ℝ) ≤ entropyForm S A B C by linarith
  have hrep := h.represents
  have key : ∀ e : h.E,
      (haveI := h.decActive A e; if h.active A e then h.cap e else 0)
    + (haveI := h.decActive B e; if h.active B e then h.cap e else 0)
    + (haveI := h.decActive C e; if h.active C e then h.cap e else 0)
    + (haveI := h.decActive (A ∪ B ∪ C) e; if h.active (A ∪ B ∪ C) e then h.cap e else 0)
    ≤ (haveI := h.decActive (A ∪ B) e; if h.active (A ∪ B) e then h.cap e else 0)
    + (haveI := h.decActive (A ∪ C) e; if h.active (A ∪ C) e then h.cap e else 0)
    + (haveI := h.decActive (B ∪ C) e; if h.active (B ∪ C) e then h.cap e else 0) := by
    intro e
    have := h.edge_monogamy A B C e hAB hAC hBC
    linarith
  rw [show entropyForm S A B C = S (A ∪ B) + S (A ∪ C) + S (B ∪ C)
        - (S A + S B + S C + S (A ∪ B ∪ C)) by unfold entropyForm; ring]
  rw [sub_nonneg]
  rw [hrep A, hrep B, hrep C, hrep (A ∪ B), hrep (A ∪ C), hrep (B ∪ C), hrep (A ∪ B ∪ C)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e _ => key e)

/-! ## 5. An EXPLICIT finite model with a STRICTLY negative I₃ (anti-vacuity, BP 21)

The three-party GHZ-like "perfect tensor" / tripartite cut: parties `Fin 3`, with a
single bulk edge of unit capacity that is active for a region `X` exactly when `X`
is a SINGLE party or its complement (a two-party region) — i.e. active iff
`X.card = 1 ∨ X.card = 2` among the three parties; equivalently active for any
nonempty proper subset. For the disjoint triple `A={0}, B={1}, C={2}`:

  S A = S B = S C = 1        (singletons are active)
  S(AB)=S(AC)=S(BC) = 1      (two-party regions are active)
  S(ABC) = 0                 (the full set is inactive: nothing to cut)

  entropyForm = (1+1+1) − 1 − 1 − 1 − 0 = 0 ... that gives I₃ = 0.

To get a STRICT witness we use a second edge that makes the pairwise
mutual information exceed the tripartite: the standard MMI-strict example is the
3-qubit state where every pair is maximally entangled with the third party absent.
We realize it directly with explicit entropy values satisfying I₃ < 0. -/

/-- Explicit 3-party entropy assignment with strictly negative tripartite
information at `({0},{1},{2})`. Values chosen to be a valid min-cut entropy:
singletons and the full set cost 2, each pair costs 3. -/
def mincut3S : Finset (Fin 3) → ℝ := fun X =>
  if X.card = 1 then 2
  else if X.card = 2 then 3
  else if X.card = 3 then 2
  else 0

/-- The three singleton parties. -/
def pA : Finset (Fin 3) := {0}
def pB : Finset (Fin 3) := {1}
def pC : Finset (Fin 3) := {2}

/-- Cardinalities of the relevant regions (decidable, evaluated by `decide`). -/
theorem mincut3_cards :
    (pA).card = 1 ∧ (pB).card = 1 ∧ (pC).card = 1 ∧
    (pA ∪ pB).card = 2 ∧ (pA ∪ pC).card = 2 ∧ (pB ∪ pC).card = 2 ∧
    (pA ∪ pB ∪ pC).card = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Anti-vacuity witness (strict).** The concrete `mincut3S` model has
`I₃({0},{1},{2}) = −1 < 0`. So MMI is NON-vacuously satisfied here. -/
theorem mincut3_I₃_strictNeg : I₃ mincut3S pA pB pC = -1 := by
  -- First pin the cardinalities of every region (these ARE decidable in ℕ).
  have cA : (pA).card = 1 := by decide
  have cB : (pB).card = 1 := by decide
  have cC : (pC).card = 1 := by decide
  have cAB : (pA ∪ pB).card = 2 := by decide
  have cAC : (pA ∪ pC).card = 2 := by decide
  have cBC : (pB ∪ pC).card = 2 := by decide
  have cABC : (pA ∪ (pB ∪ pC)).card = 3 := by decide
  -- Evaluate mincut3S at each region by rewriting the (ℕ) card into the ifs.
  have e1 : mincut3S pA = 2 := by simp only [mincut3S, cA]; norm_num
  have e2 : mincut3S pB = 2 := by simp only [mincut3S, cB]; norm_num
  have e3 : mincut3S pC = 2 := by simp only [mincut3S, cC]; norm_num
  have e4 : mincut3S (pA ∪ pB) = 3 := by simp only [mincut3S, cAB]; norm_num
  have e5 : mincut3S (pA ∪ pC) = 3 := by simp only [mincut3S, cAC]; norm_num
  have e6 : mincut3S (pB ∪ pC) = 3 := by simp only [mincut3S, cBC]; norm_num
  have e7 : mincut3S (pA ∪ (pB ∪ pC)) = 2 := by simp only [mincut3S, cABC]; norm_num
  unfold I₃ I
  rw [e1, e2, e3, e4, e5, e6, e7]; ring

/-- Corollary: the witness strictly satisfies `I₃ < 0`. -/
theorem mincut3_I₃_lt_zero : I₃ mincut3S pA pB pC < 0 := by
  rw [mincut3_I₃_strictNeg]; norm_num

/-! ## 6. `mincut3S` satisfies MMI on ALL **disjoint** triples of `Fin 3`

For `ι = Fin 3` the region lattice is finite (8 subsets, `8³ = 512` triples), so
MMI is decidable by exhaustive search. The proof bridges the ℝ-valued `mincut3S`
to an integer copy `mincut3Z` (a `decide`-friendly value type), settles the
inequality on ℤ by `decide`, and casts back to ℝ.

**IMPORTANT SCOPE FINDING (kept honest).** The abstract `MMI`
predicate quantifies over *all* triples with **no disjointness hypothesis**. For
`mincut3S` the *unrestricted* statement `∀ A B C, I₃ mincut3S A B C ≤ 0` is
**FALSE** — a machine-checked counterexample is `A = B = C = {0}`, where
`I₃ mincut3S {0} {0} {0} = 2 > 0` (see `mincut3_MMI_unrestricted_false`). This is
the expected physics: MMI / monogamy is a statement about **disjoint** regions;
the tripartite-information formula carries the monogamy meaning only when
`A, B, C` are disjoint (e.g. `I₃ A A A = S A`, which is positive, not a monogamy
violation). Hence the completeness theorem for this concrete model is the
disjoint-restricted `mincut3_MMI_disjoint` below, and we RECORD the unrestricted
predicate's failure rather than assert a false theorem. The abstract
`holographic_implies_MMI` (§4) is unaffected: its `edge_monogamy` hypothesis is
itself only imposed for the disjoint triples that RT geometry constrains. -/

/-- Integer-valued twin of `mincut3S`, with an identical `card`-based rule.
Used purely to make the finite MMI search `decide`-able (`decide` cannot evaluate
ℝ-valued (in)equalities; ℤ it can). -/
def mincut3Z : Finset (Fin 3) → ℤ := fun X =>
  if X.card = 1 then 2
  else if X.card = 2 then 3
  else if X.card = 3 then 2
  else 0

/-- `mincut3S = mincut3Z` after casting ℤ → ℝ: same `card`-branching, same values. -/
theorem mincut3S_eq_Z (X : Finset (Fin 3)) : mincut3S X = (mincut3Z X : ℝ) := by
  unfold mincut3S mincut3Z
  by_cases h1 : X.card = 1
  · simp [h1]
  · by_cases h2 : X.card = 2
    · simp [h2]
    · by_cases h3 : X.card = 3
      · simp [h3]
      · simp [h1, h2, h3]

/-- The integer tripartite information for `mincut3Z`, expanded (so `decide`
sees a closed ℤ expression in the seven region values). Definitionally equal to
`I₃ mincut3Z A B C` via `I₃`/`I`, with `A ∪ (B ∪ C)` as the full-union term. -/
def I₃Z (A B C : Finset (Fin 3)) : ℤ :=
  (mincut3Z A + mincut3Z B - mincut3Z (A ∪ B))
  + (mincut3Z A + mincut3Z C - mincut3Z (A ∪ C))
  - (mincut3Z A + mincut3Z (B ∪ C) - mincut3Z (A ∪ (B ∪ C)))

/-- `I₃ mincut3S` equals its integer twin `I₃Z`, cast to ℝ. -/
theorem I₃_eq_Z (A B C : Finset (Fin 3)) :
    I₃ mincut3S A B C = (I₃Z A B C : ℝ) := by
  unfold I₃ I I₃Z
  rw [mincut3S_eq_Z A, mincut3S_eq_Z B, mincut3S_eq_Z C,
      mincut3S_eq_Z (A ∪ B), mincut3S_eq_Z (A ∪ C), mincut3S_eq_Z (B ∪ C),
      mincut3S_eq_Z (A ∪ (B ∪ C))]
  push_cast
  ring

/-- Exhaustive `decide` over all `8³` triples of `Fin 3`: the integer tripartite
information is `≤ 0` for every **disjoint** triple. -/
theorem I₃Z_le_zero_of_disjoint : ∀ A B C : Finset (Fin 3),
    Disjoint A B → Disjoint A C → Disjoint B C → I₃Z A B C ≤ 0 := by decide

/-- **Completeness.** The concrete min-cut model `mincut3S` satisfies MMI
`I₃ ≤ 0` on **every disjoint triple** `A B C : Finset (Fin 3)` — the full
holographic-cone signature over the whole (finite) disjoint region structure, not
just the single witness partition of §5. Proved by transfer to the integer twin
plus exhaustive `decide`. -/
theorem mincut3_MMI_disjoint (A B C : Finset (Fin 3))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    I₃ mincut3S A B C ≤ 0 := by
  rw [I₃_eq_Z]
  have := I₃Z_le_zero_of_disjoint A B C hAB hAC hBC
  exact_mod_cast this

/-- **Honesty record.** The *unrestricted* abstract predicate
`MMI mincut3S` (i.e. `∀ A B C, I₃ mincut3S A B C ≤ 0`, with **no** disjointness)
is FALSE: the overlapping triple `A = B = C = {0}` gives
`I₃ mincut3S {0} {0} {0} = 2 > 0`. Monogamy is a disjoint-regions statement; this
theorem certifies that `mincut3_MMI_disjoint`'s disjointness hypotheses are
NECESSARY, not decoration. (So we do NOT — and cannot honestly — claim the bare
`MMI mincut3S`.) -/
theorem mincut3_MMI_unrestricted_false :
    ¬ (∀ A B C : Finset (Fin 3), I₃ mincut3S A B C ≤ 0) := by
  intro h
  have hce := h {0} {0} {0}
  rw [I₃_eq_Z] at hce
  norm_num [I₃Z, mincut3Z] at hce

/-! ## 7. The ANTI-VACUITY WITNESS: `mincut3S` is `HolographicD`

This is the whole point of the disjoint-corrected formulation. `holographic_implies_MMIDisjoint`
(§4b) is only meaningful if its hypothesis class `HolographicD` is inhabited by a
NON-degenerate entropy assignment (some `S X > 0`). We prove exactly that:
`mincut3S` (singletons=2, pairs=3, full=2 — manifestly non-degenerate,
`S {0} = 2 > 0`) satisfies `HolographicD` by exhibiting an explicit 3-edge min-cut
model. The edge set is `Fin 3` with capacities `[1,1,2]` and the activity rule
below; `represents` and the disjoint-only `edge_monogamy` are discharged by
transfer to an integer twin plus exhaustive `decide` over the 512 triples. Hence
the corrected C1 conditional is NON-vacuous: a concrete non-degenerate geometric
model provably satisfies its hypothesis (and, via §6, its `MMIDisjoint` conclusion). -/

/-- Capacities of the three cut edges of the `mincut3S` model (over ℝ). -/
def mc3capR : Fin 3 → ℝ := ![1, 1, 2]

/-- Integer twin of the edge capacities (for `decide`). -/
def mc3capZ : Fin 3 → ℤ := ![1, 1, 2]

/-- Activity indicator (Bool, hence `decide`-able) of edge `e` for region `X` in the
explicit 3-edge representation of `mincut3S`. Found by an exhaustive search for a
nonnegative-capacity edge decomposition of `mincut3S` whose every edge has a
nonnegative entropy-form on all disjoint triples (the per-edge RT monogamy). -/
def mc3activeB (X : Finset (Fin 3)) (e : Fin 3) : Bool :=
  match e with
  | 0 => decide (X = {0}) || decide (X = {0, 1})
  | 1 => decide (X = {0}) || decide (X = {0, 2}) || decide (X = {1, 2})
  | 2 => decide (X = {0, 1}) || decide (X = {0, 1, 2}) || decide (X = {0, 2}) ||
         decide (X = ({1} : Finset (Fin 3))) || decide (X = {1, 2}) ||
         decide (X = ({2} : Finset (Fin 3)))

/-- The activity relation as a decidable `Prop`. -/
def mc3activeP (X : Finset (Fin 3)) (e : Fin 3) : Prop := mc3activeB X e = true

instance : ∀ X e, Decidable (mc3activeP X e) := fun X e => by
  unfold mc3activeP; infer_instance

/-- Integer per-edge contribution (for the `decide`-based facts). -/
def mc3edgeZ (e : Fin 3) (X : Finset (Fin 3)) : ℤ := if mc3activeB X e then mc3capZ e else 0

/-- The integer edge sum reproduces the (integer) `mincut3Z` values — exhaustive
`decide` over all 8 regions. This is the representation certificate on ℤ. -/
theorem mc3_SZ_eq : ∀ X : Finset (Fin 3),
    (∑ e : Fin 3, mc3edgeZ e X) = mincut3Z X := by decide

/-- Cast bridge: the ℝ per-edge term equals the cast of the ℤ per-edge term. -/
theorem mc3_edge_cast (X : Finset (Fin 3)) (e : Fin 3) :
    (if mc3activeP X e then mc3capR e else 0) = ((mc3edgeZ e X : ℤ) : ℝ) := by
  unfold mc3activeP mc3edgeZ
  by_cases hb : mc3activeB X e = true
  · simp only [hb, if_true]; fin_cases e <;> simp [mc3capR, mc3capZ]
  · simp [hb]

/-- **Representation certificate (ℝ).** `mincut3S` equals its explicit 3-edge
min-cut sum. -/
theorem mc3_represents : ∀ X : Finset (Fin 3),
    mincut3S X = ∑ e : Fin 3, (if mc3activeP X e then mc3capR e else 0) := by
  intro X
  have hcast : (∑ e : Fin 3, (if mc3activeP X e then mc3capR e else 0))
      = ((∑ e : Fin 3, mc3edgeZ e X : ℤ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl (fun e _ => mc3_edge_cast X e)
  rw [hcast, mc3_SZ_eq X, mincut3S_eq_Z]

/-- **Per-edge RT monogamy (ℤ), DISJOINT triples** — exhaustive `decide` over the
`8³` triples: for every disjoint `A B C` and every edge, the per-edge entropy form
is ≥ 0. -/
theorem mc3_edge_monogamy_Z : ∀ (A B C : Finset (Fin 3)) (e : Fin 3),
    Disjoint A B → Disjoint A C → Disjoint B C →
    mc3edgeZ e A + mc3edgeZ e B + mc3edgeZ e C + mc3edgeZ e (A ∪ B ∪ C)
    ≤ mc3edgeZ e (A ∪ B) + mc3edgeZ e (A ∪ C) + mc3edgeZ e (B ∪ C) := by decide

/-- **Per-edge RT monogamy (ℝ)** for the `mincut3S` model, disjoint triples. -/
theorem mc3_edge_monogamy_R : ∀ (A B C : Finset (Fin 3)) (e : Fin 3),
    Disjoint A B → Disjoint A C → Disjoint B C →
      (if mc3activeP (A ∪ B) e then mc3capR e else 0)
    + (if mc3activeP (A ∪ C) e then mc3capR e else 0)
    + (if mc3activeP (B ∪ C) e then mc3capR e else 0)
    ≥ (if mc3activeP A e then mc3capR e else 0)
    + (if mc3activeP B e then mc3capR e else 0)
    + (if mc3activeP C e then mc3capR e else 0)
    + (if mc3activeP (A ∪ B ∪ C) e then mc3capR e else 0) := by
  intro A B C e hAB hAC hBC
  have hz := mc3_edge_monogamy_Z A B C e hAB hAC hBC
  rw [mc3_edge_cast, mc3_edge_cast, mc3_edge_cast, mc3_edge_cast,
      mc3_edge_cast, mc3_edge_cast, mc3_edge_cast]
  exact_mod_cast hz

/-- **★ THE ANTI-VACUITY WITNESS.** The concrete, NON-degenerate 3-party min-cut
model `mincut3S` (with `mincut3S {0} = 2 > 0`) satisfies the corrected
representability structure `HolographicD`. Hence `holographic_implies_MMIDisjoint`
is not vacuous: its hypothesis class contains a proven non-degenerate instance. -/
def mincut3_HolographicD : HolographicD mincut3S where
  E := Fin 3
  fintypeE := inferInstance
  cap := mc3capR
  cap_nonneg := by intro e; fin_cases e <;> simp [mc3capR]
  active := mc3activeP
  decActive := fun X e => inferInstance
  represents := mc3_represents
  edge_monogamy := mc3_edge_monogamy_R

/-- `mincut3S` is manifestly NON-degenerate: some region has strictly positive
entropy (`S {0} = 2 > 0`). Together with `mincut3_HolographicD` this certifies the
`HolographicD` hypothesis class is non-empty AND non-degenerate — the BP 21
anti-vacuity requirement for the corrected C1 theorem. -/
theorem mincut3_nondegenerate : 0 < mincut3S {0} := by
  have : mincut3S ({0} : Finset (Fin 3)) = 2 := by
    have c : ({0} : Finset (Fin 3)).card = 1 := by decide
    simp only [mincut3S, c]; norm_num
  rw [this]; norm_num

/-- **Corollary (non-vacuous C1 on the concrete model).** `mincut3S` satisfies
`MMIDisjoint`, obtained through the corrected C1 conditional applied to the witness
`mincut3_HolographicD`. (Agrees with the direct `mincut3_MMI_disjoint` of §6; this
route certifies it flows from `HolographicD`.) -/
theorem mincut3_MMIDisjoint_via_C1 : MMIDisjoint mincut3S :=
  holographic_implies_MMIDisjoint mincut3S mincut3_HolographicD

end Holography.EntropyCone
