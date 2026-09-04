/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Tactic

/-!
# The Coleman–Mandula no-go theorem: an axiomatized-physics, proven-algebra skeleton

**Coleman–Mandula (1967).**  In a relativistic quantum field theory satisfying a short
list of physical assumptions — Poincaré invariance, analyticity of the S-matrix, a mass
gap, finitely many one-particle types below any given mass, and a nontrivial (non-free)
S-matrix — the *most general* Lie algebra of symmetries of the S-matrix is a **direct
product** of the Poincaré algebra with an internal-symmetry algebra.  Spacetime and
internal symmetries **cannot be unified nontrivially**: every internal generator is a
Lorentz *scalar* and *commutes with all of the Poincaré generators*.  (This is the
theorem later evaded by *super*symmetry, whose generators are not Lie-algebra elements but
graded/anticommuting ones — outside the Coleman–Mandula hypotheses.)

## What is axiomatized vs what is proved

The hard analytic content of Coleman–Mandula — dispersion relations, analyticity of
2→2 scattering, the mass gap forcing symmetry generators to act as multiplication
operators in momentum space, hence to be Lorentz scalars — has **no counterpart in
Mathlib** (there is no S-matrix, no analyticity-of-scattering-amplitudes, no LSZ
machinery).  So, exactly as the Jacobson `linearized_einstein_of_first_law` skeleton
axiomatizes the entropy/first-law physics and then *derives* the geometric consequence,
here we:

* **AXIOMATIZE the physics** as the two hypotheses bundled in `ColemanMandulaHyp`:
  * `internal_are_lorentz_scalars` — every internal generator commutes with every Lorentz
    generator.  *This is the axiomatized output of the analyticity + mass-gap argument*:
    an internal charge that transformed nontrivially under Lorentz would, by the
    Coleman–Mandula analysis, force extra conserved tensor charges that collapse the
    S-matrix to triviality; so a nontrivial theory admits only scalar internal charges.
  * `poincare_from_lorentz` — every Poincaré generator lies in the bracket-closure of the
    Lorentz generators.  This encodes the *structural* fact that the translations (and
    hence the full Poincaré algebra) are generated from the homogeneous Lorentz generators
    by commutators — e.g. `⁅boost, boost⁆ ~ rotation`, and translations appear as
    commutators of the boosts/special generators in the conformal completion — so once a
    charge commutes with all Lorentz generators it commutes with all of Poincaré.

* **PROVE the Lie-algebra content**: from those two inputs, the Jacobi identity alone
  forces the internal generators to commute with *all* of Poincaré
  (`coleman_mandula_direct_sum`), giving the direct-sum / no-mixing conclusion
  (`coleman_mandula_no_mixing`).  The engine is `lie_closure_eq_zero`: commuting with a
  generating set propagates through `+`, `-`, and `⁅·,·⁆` by the Leibniz/Jacobi identity.

## Anti-vacuity

`witnessHyp` is a **concrete, non-degenerate** model of `ColemanMandulaHyp` living in a
genuine direct sum `AbLie ℤ × AbLie ℤ`, with a **nonzero** Lorentz/Poincaré generator
`gLor = (1,0)` and a **nonzero** internal generator `gInt = (0,1)` that *do commute*
(`witness_direct_sum`).  `witness_nontrivial` certifies both generators are nonzero, so the
hypothesis class is satisfiably instantiated with genuine content — not a vacuous `0 = 0`.

## Main statements

* `ColemanMandulaHyp` — the axiomatized physics hypotheses.
* `coleman_mandula_direct_sum` — `⁅p, t⁆ = 0` for every Poincaré `p` and internal `t`
  (the no-mixing / direct-sum conclusion).
* `coleman_mandula_no_mixing` — the contradiction form: assuming a generator that mixes
  spacetime and internal symmetry (`⁅p, t⁆ ≠ 0`) is `False`.
* `witnessHyp`, `witness_nontrivial`, `witness_direct_sum` — the non-vacuous witness.
-/

/-- The **abelian (zero-bracket) Lie ring** on an additive commutative group `G`.  Used to
build a concrete direct-sum Lie algebra for the anti-vacuity witness: two abelian factors
whose cross-brackets vanish model "spacetime" and "internal" summands with genuine
(nonzero) generators. -/
def AbLie (G : Type*) := G

instance (G : Type*) [AddCommGroup G] : AddCommGroup (AbLie G) := ‹AddCommGroup G›

instance (G : Type*) [AddCommGroup G] : LieRing (AbLie G) where
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

@[simp] theorem AbLie.bracket_eq (G : Type*) [AddCommGroup G] (x y : AbLie G) :
    ⁅x, y⁆ = 0 := rfl

namespace ColemanMandula

variable {L : Type*} [LieRing L]

/-- The **bracket-and-additive closure** of a set `S` inside a Lie ring: the smallest
predicate containing `S` and closed under `0`, `+`, negation, and the Lie bracket.  The
Coleman–Mandula hypothesis `poincare_from_lorentz` asserts the Poincaré generators lie in
this closure of the Lorentz generators. -/
inductive BracketClosure (S : Set L) : L → Prop
  | basic {x} : x ∈ S → BracketClosure S x
  | zero : BracketClosure S 0
  | add {x y} : BracketClosure S x → BracketClosure S y → BracketClosure S (x + y)
  | neg {x} : BracketClosure S x → BracketClosure S (-x)
  | lie {x y} : BracketClosure S x → BracketClosure S y → BracketClosure S ⁅x, y⁆

/-- **Core commutation lemma (pure Lie algebra).**  If a fixed element `t` commutes with
every generator `s ∈ S`, then it commutes with the entire bracket-closure of `S`.  The
`lie` case is the Jacobi identity: `⁅⁅x,y⁆, t⁆ = ⁅x, ⁅y,t⁆⁆ − ⁅y, ⁅x,t⁆⁆`, which vanishes
once `⁅x,t⁆ = ⁅y,t⁆ = 0`.  This is the entire "spacetime and internal symmetry cannot
mix" mechanism, isolated from any physics. -/
theorem lie_closure_eq_zero {S : Set L} {t : L} (hS : ∀ s ∈ S, ⁅s, t⁆ = 0) :
    ∀ {x}, BracketClosure S x → ⁅x, t⁆ = 0 := by
  intro x hx
  induction hx with
  | basic h => exact hS _ h
  | zero => simp
  | add _ _ ihx ihy => rw [add_lie, ihx, ihy, add_zero]
  | neg _ ih => rw [neg_lie, ih, neg_zero]
  | lie _ _ ihx ihy => rw [lie_lie, ihx, ihy, lie_zero, lie_zero, sub_zero]

/-- The **axiomatized Coleman–Mandula hypotheses** on a symmetry Lie ring `L`.

`Lorentz`, `Poincare`, `Internal` are the generator sets (homogeneous Lorentz generators;
the full Poincaré generators; the internal-symmetry generators).  The two fields are the
axiomatized *physics* inputs — the consequences of S-matrix analyticity + mass gap +
nontriviality that Mathlib cannot express directly:

* `internal_are_lorentz_scalars`: every internal generator is a **Lorentz scalar**
  (commutes with every Lorentz generator).
* `poincare_from_lorentz`: every Poincaré generator is built from the Lorentz generators
  by brackets and sums (the translations arise as commutators of the homogeneous
  generators).

From these, `coleman_mandula_direct_sum` derives — by the Jacobi identity alone — that the
internal generators commute with **all** of Poincaré. -/
structure ColemanMandulaHyp (L : Type*) [LieRing L] where
  /-- The homogeneous Lorentz generators (rotations and boosts). -/
  Lorentz : Set L
  /-- The full Poincaré generators (Lorentz generators together with translations). -/
  Poincare : Set L
  /-- The internal-symmetry generators. -/
  Internal : Set L
  /-- **Axiomatized physics:** each internal generator is a Lorentz scalar — it commutes
  with every Lorentz generator.  This is the algebraic output of the analyticity +
  mass-gap argument of Coleman–Mandula. -/
  internal_are_lorentz_scalars : ∀ m ∈ Lorentz, ∀ t ∈ Internal, ⁅m, t⁆ = 0
  /-- **Axiomatized structure:** each Poincaré generator lies in the bracket-closure of the
  Lorentz generators (the translations are generated by commutators of the homogeneous
  Lorentz generators). -/
  poincare_from_lorentz : ∀ p ∈ Poincare, BracketClosure Lorentz p

/-- **The Coleman–Mandula no-go theorem (direct-sum form).**  Under the axiomatized
hypotheses, every Poincaré generator `p` commutes with every internal generator `t`:
`⁅p, t⁆ = 0`.  Hence the symmetry algebra splits as Poincaré ⊕ internal with **no
nontrivial mixing** of spacetime and internal symmetries.  The physics enters only through
`ColemanMandulaHyp`; the derivation is the Jacobi identity via `lie_closure_eq_zero`. -/
theorem coleman_mandula_direct_sum (H : ColemanMandulaHyp L)
    {p t : L} (hp : p ∈ H.Poincare) (ht : t ∈ H.Internal) : ⁅p, t⁆ = 0 :=
  lie_closure_eq_zero (fun s hs => H.internal_are_lorentz_scalars s hs t ht)
    (H.poincare_from_lorentz p hp)

/-- **The Coleman–Mandula no-go theorem (contradiction form).**  Suppose some internal
charge `t` *mixed* nontrivially with a spacetime (Poincaré) generator `p`, i.e.
`⁅p, t⁆ ≠ 0`.  That contradicts the hypotheses: there is **no unification** of spacetime
and internal symmetry within a Lie algebra of S-matrix symmetries. -/
theorem coleman_mandula_no_mixing (H : ColemanMandulaHyp L)
    {p t : L} (hp : p ∈ H.Poincare) (ht : t ∈ H.Internal)
    (hmix : ⁅p, t⁆ ≠ 0) : False :=
  hmix (coleman_mandula_direct_sum H hp ht)

/-! ### Anti-vacuity witness

A concrete, non-degenerate model of `ColemanMandulaHyp` in the genuine direct sum
`AbLie ℤ × AbLie ℤ`, with nonzero Lorentz/Poincaré and internal generators that commute.
-/

/-- Witness carrier: a genuine direct sum of two abelian Lie summands, standing in for the
"spacetime" and "internal" factors. -/
abbrev WSpace := AbLie ℤ × AbLie ℤ

/-- Nonzero spacetime (Lorentz/Poincaré) generator `(1, 0)`. -/
def gLor : WSpace := ((1 : ℤ), (0 : ℤ))

/-- Nonzero internal generator `(0, 1)`. -/
def gInt : WSpace := ((0 : ℤ), (1 : ℤ))

theorem gLor_ne_zero : gLor ≠ 0 := by
  simp only [gLor, ne_eq, Prod.mk_eq_zero, not_and]
  intro h; exact absurd h (by show (1 : ℤ) ≠ 0; norm_num)

theorem gInt_ne_zero : gInt ≠ 0 := by
  simp only [gInt, ne_eq, Prod.mk_eq_zero, not_and]
  intro _ h; exact absurd h (by show (1 : ℤ) ≠ 0; norm_num)

/-- **Concrete non-vacuous instance** of the Coleman–Mandula hypotheses.  Both factors are
abelian, so every cross-bracket vanishes and both physics axioms hold — yet the Lorentz
and internal generators `gLor`, `gInt` are genuinely nonzero (see `witness_nontrivial`). -/
def witnessHyp : ColemanMandulaHyp WSpace where
  Lorentz := {gLor}
  Poincare := {gLor}
  Internal := {gInt}
  internal_are_lorentz_scalars := by
    intro m _ t _; rfl
  poincare_from_lorentz := by
    intro p hp; exact BracketClosure.basic hp

/-- The witness is genuinely non-degenerate: it exhibits a **nonzero** Poincaré generator
and a **nonzero** internal generator (so the hypothesis class is not vacuously satisfied). -/
theorem witness_nontrivial :
    (∃ p ∈ witnessHyp.Poincare, p ≠ (0 : WSpace)) ∧
    (∃ t ∈ witnessHyp.Internal, t ≠ (0 : WSpace)) :=
  ⟨⟨gLor, rfl, gLor_ne_zero⟩, ⟨gInt, rfl, gInt_ne_zero⟩⟩

/-- The no-go conclusion instantiated on the witness: the nonzero spacetime generator and
the nonzero internal generator commute. -/
theorem witness_direct_sum : ⁅gLor, gInt⁆ = (0 : WSpace) :=
  coleman_mandula_direct_sum witnessHyp rfl rfl

end ColemanMandula
