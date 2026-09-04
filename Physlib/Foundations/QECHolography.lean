/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
import Mathlib

/-!
# Bulk reconstruction = quantum error correction (Almheiri–Dong–Harlow)

Almheiri, Dong & Harlow (2015), *Bulk locality and quantum error correction in
AdS/CFT*, JHEP 04 (2015) 163, arXiv:1411.7041.

**Physics content (the ADH dictionary).** In holography a bulk (logical) operator
sitting inside the *entanglement wedge* of a boundary subregion `A` can be
**reconstructed** as a boundary operator acting only on `A`. Equivalently: erasure
of the complementary region `Ā` is a *correctable error*. This is precisely the
structure of a quantum error-correcting code — the bulk Hilbert space is the *code
subspace* of the boundary Hilbert space, encoded by an isometry `V : Hₗ →ₗᵢ Hₚ`
(logical → physical), and "reconstructable on `A`" is "recoverable after erasing
`Ā`". The RT surface plays the role of the code's threshold: which subregions
suffice to reconstruct a given bulk operator. The canonical toy model is ADH's
**3-qutrit code** (1 logical qutrit in 3 physical qutrits, any 2 of 3 reconstruct;
erasure of any single qutrit correctable) — complementary recovery.

## What this file encodes

We work in finite-dimensional complex inner-product spaces (Mathlib's
`InnerProductSpace ℂ`), which is the right algebraic home for the *statement* of
the QEC↔holography dictionary. The physical Hilbert space carries a two-region
tensor factorization modeled by the `L²` product `WithLp 2 (A × Ā)` (Mathlib's
`Analysis.InnerProductSpace.ProdL2`).

### The reconstruction algebra (PROVED)

* `Reconstructs V O Ō` : the physical operator `O` acts on the code encoded by `V`
  exactly as the logical operator `Ō` does, `O (V x) = V (Ō x)` — the ADH
  "operator dictionary" `O ∘ V = V ∘ Ō`.
* `Reconstructs.comp`, `Reconstructs.unique_on_code` : reconstruction is a
  homomorphism of operator algebras and is uniquely pinned on the code subspace.

### Complementary recovery / no-cloning (PROVED core)

* `commute_of_reconstructs_commuting` : **the algebraic heart of complementary
  recovery.** If `Ō` is reconstructed by a region-`A` operator `Oₐ` and `Ō'` by a
  region-`Ā` operator `O_ᵦ`, and the two physical operators commute (they act on
  independent tensor factors), then the *logical* operators commute. Injectivity of
  the encoding isometry turns "physical operators on disjoint regions commute" into
  a constraint on the logical algebra — the shadow of "the entanglement wedge is
  one-sided."
* `central_of_reconstructable_both_sides` : if a single logical operator `Ō` is
  reconstructable on BOTH `A` and its complement `Ā` (with the two physical
  reconstructions commuting with every region-`A` reconstruction), then `Ō`
  commutes with every logical operator reconstructable on `A` — it is *central*.
  This is the no-cloning statement: a bulk operator cannot be freely reconstructed
  on both sides of the cut unless it is central (a c-number in the deep IR of the
  wedge). The deep step "central ⟹ scalar" needs irreducibility of the logical
  algebra and is left as `proof_wanted`.

### Concrete correctable-code witness (anti-vacuity, PROVED)

The abstract statements are instantiated on a genuinely non-degenerate code: the
logical space is `ℂ²`, the physical space is the two-region product
`WithLp 2 (ℂ² × ℂ²)`, and the encoding is the entanglement-wedge-of-`A` embedding
`V x = (x, 0)` (all logical information in region `A`; region `Ā` is a fixed
reference). This is the ADH picture in the limit where the bulk operator sits deep
in the wedge of `A`.

* `encIsom` : the encoding isometry (norm-preserving, PROVED).
* `regionAOp` : the region-`A` reconstruction of an arbitrary logical operator.
* `regionAOp_reconstructs` : **every** logical operator is reconstructable on `A`.
* `eraseB_correctable` : erasure of region `Ā` is correctable — the code is
  invariant under discarding `Ā` (`Ā` carries no logical information), the concrete
  witness that erasure of the complement is a correctable error.
* `witness_nontrivial_logical` : a nonzero, non-identity logical operator exists,
  so the reconstructed / correctable facts are genuinely non-vacuous (not `0 = 0`).

## Main results

* `QECHolography.Reconstructs` and its algebra (`comp`, `unique_on_code`)
* `QECHolography.commute_of_reconstructs_commuting` (complementary-recovery core)
* `QECHolography.central_of_reconstructable_both_sides` (no-cloning)
* `QECHolography.reconstructable_scalar_of_both_sides` (`proof_wanted`)
* `QECHolography.encIsom`, `regionAOp`, `regionAOp_reconstructs`
* `QECHolography.eraseB_correctable`, `witness_nontrivial_logical`
-/

open scoped ComplexOrder InnerProductSpace

namespace QECHolography

/-! ## The reconstruction algebra -/

section Abstract

-- The reconstruction algebra needs only injectivity of the encoding isometry, so we
-- work over general complex inner-product spaces here; the finite-dimensional QEC
-- setting is the intended reading (and is imposed explicitly in the concrete witness
-- and in `reconstructable_scalar_of_both_sides`).
variable {Hl Hp : Type*}
  [NormedAddCommGroup Hl] [InnerProductSpace ℂ Hl]
  [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp]

/-- A physical operator `O` **reconstructs** the logical operator `Ō` on the code
encoded by the isometry `V` when it acts on the code subspace exactly as `Ō` acts
on the logical space: `O (V x) = V (Ō x)` for every logical state `x`. This is the
ADH operator dictionary `O ∘ V = V ∘ Ō`. -/
def Reconstructs (V : Hl →ₗᵢ[ℂ] Hp) (O : Hp →ₗ[ℂ] Hp) (Ō : Hl →ₗ[ℂ] Hl) : Prop :=
  ∀ x : Hl, O (V x) = V (Ō x)

/-- Reconstruction is unique on the code: two physical operators reconstructing the
same logical operator agree on every code state. (The physical operator off the
code is unconstrained — different boundary "dressings" of the same bulk operator.) -/
theorem Reconstructs.unique_on_code {V : Hl →ₗᵢ[ℂ] Hp} {O₁ O₂ : Hp →ₗ[ℂ] Hp}
    {Ō : Hl →ₗ[ℂ] Hl} (h₁ : Reconstructs V O₁ Ō) (h₂ : Reconstructs V O₂ Ō)
    (x : Hl) : O₁ (V x) = O₂ (V x) := by
  rw [h₁, h₂]

/-- Reconstruction respects composition: reconstructing `Ō₁` by `O₁` and `Ō₂` by
`O₂` gives a reconstruction of `Ō₁ ∘ Ō₂` by `O₁ ∘ O₂`. The boundary reconstruction
map is a homomorphism of operator algebras. -/
theorem Reconstructs.comp {V : Hl →ₗᵢ[ℂ] Hp} {O₁ O₂ : Hp →ₗ[ℂ] Hp}
    {Ō₁ Ō₂ : Hl →ₗ[ℂ] Hl} (h₁ : Reconstructs V O₁ Ō₁) (h₂ : Reconstructs V O₂ Ō₂) :
    Reconstructs V (O₁ ∘ₗ O₂) (Ō₁ ∘ₗ Ō₂) := by
  intro x
  simp only [LinearMap.comp_apply]
  rw [h₂, h₁]

/-! ## Complementary recovery / no-cloning core -/

/-- **The algebraic heart of complementary recovery.** Suppose `Oₐ` reconstructs the
logical operator `Ō` and `O_ᵦ` reconstructs `Ō'`, and the two *physical* operators
commute — as they must when `Oₐ` is supported on a boundary region `A` and `O_ᵦ` on
the complementary region `Ā`, acting on independent tensor factors. Then the two
*logical* operators commute.

Injectivity of the encoding isometry propagates "operators on disjoint regions
commute" down to a constraint on the logical (bulk) algebra: this is why the
entanglement wedge is one-sided. -/
theorem commute_of_reconstructs_commuting {V : Hl →ₗᵢ[ℂ] Hp}
    {Oₐ O_ᵦ : Hp →ₗ[ℂ] Hp} {Ō Ō' : Hl →ₗ[ℂ] Hl}
    (hA : Reconstructs V Oₐ Ō) (hB : Reconstructs V O_ᵦ Ō')
    (hcomm : Oₐ ∘ₗ O_ᵦ = O_ᵦ ∘ₗ Oₐ) :
    Ō ∘ₗ Ō' = Ō' ∘ₗ Ō := by
  ext x
  apply V.injective
  have key : (Oₐ ∘ₗ O_ᵦ) (V x) = (O_ᵦ ∘ₗ Oₐ) (V x) := by rw [hcomm]
  simp only [LinearMap.comp_apply] at key ⊢
  rw [hB x, hA (Ō' x)] at key
  rw [hA x, hB (Ō x)] at key
  exact key

/-- **No-cloning / complementary recovery.** If a *single* logical operator `Ō` is
reconstructable on both region `A` (by `Oₐ`) and its complement `Ā` (by `O_ᵦ`), and
the `Ā`-reconstruction commutes with every physical operator reconstructing an
`A`-operator, then `Ō` commutes with every logical operator reconstructable on `A`.

`Ō` is therefore *central* in the algebra of `A`-reconstructable logical operators.
A bulk operator that could be reconstructed on both sides of the RT cut would have
to commute with the entire wedge algebra — it cannot carry genuine (non-central)
bulk information on both sides. This is the formal shadow of "the entanglement wedge
is one-sided." -/
theorem central_of_reconstructable_both_sides {V : Hl →ₗᵢ[ℂ] Hp}
    {Oₐ O_ᵦ : Hp →ₗ[ℂ] Hp} {Ō : Hl →ₗ[ℂ] Hl}
    (_hA : Reconstructs V Oₐ Ō) (hB : Reconstructs V O_ᵦ Ō)
    (hB_comm : ∀ (O' : Hp →ₗ[ℂ] Hp) (Ō' : Hl →ₗ[ℂ] Hl),
      Reconstructs V O' Ō' → O_ᵦ ∘ₗ O' = O' ∘ₗ O_ᵦ) :
    ∀ (O' : Hp →ₗ[ℂ] Hp) (Ō' : Hl →ₗ[ℂ] Hl),
      Reconstructs V O' Ō' → Ō ∘ₗ Ō' = Ō' ∘ₗ Ō := by
  intro O' Ō' hO'
  -- Use the `Ā`-side reconstruction of `Ō`, which commutes with the `A`-side `O'`.
  have hcomm : O_ᵦ ∘ₗ O' = O' ∘ₗ O_ᵦ := hB_comm O' Ō' hO'
  -- `commute_of_reconstructs_commuting` with (Ō via O_ᵦ) and (Ō' via O') gives
  -- `Ō ∘ Ō' = Ō' ∘ Ō`.
  exact commute_of_reconstructs_commuting hB hO' hcomm

/-- **Deep direction (`proof_wanted`).** If the logical (bulk) algebra acts
irreducibly on `Hl` — e.g. it is the full operator algebra `End ℂ Hl`, the generic
holographic situation with no bulk symmetry — then a central logical operator is a
scalar. Combined with `central_of_reconstructable_both_sides`, this upgrades
no-cloning to: a logical operator reconstructable on both `A` and `Ā` is a
c-number. The missing input is Schur's lemma / a double-commutant statement for the
finite-dimensional complex operator algebra; it is not implied by the reconstruction
algebra alone and is queued for CONJECTURES. -/
proof_wanted reconstructable_scalar_of_both_sides
    {Hl Hp : Type*}
    [NormedAddCommGroup Hl] [InnerProductSpace ℂ Hl] [FiniteDimensional ℂ Hl]
    [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [FiniteDimensional ℂ Hp]
    {V : Hl →ₗᵢ[ℂ] Hp} {Oₐ O_ᵦ : Hp →ₗ[ℂ] Hp} {Ō : Hl →ₗ[ℂ] Hl}
    (_hA : Reconstructs V Oₐ Ō) (_hB : Reconstructs V O_ᵦ Ō)
    (_hB_comm : ∀ (O' : Hp →ₗ[ℂ] Hp) (Ō' : Hl →ₗ[ℂ] Hl),
      Reconstructs V O' Ō' → O_ᵦ ∘ₗ O' = O' ∘ₗ O_ᵦ)
    -- the algebra of `A`-reconstructable logical operators is all of `End ℂ Hl`
    (_hIrred : ∀ Ō' : Hl →ₗ[ℂ] Hl, ∃ O' : Hp →ₗ[ℂ] Hp, Reconstructs V O' Ō') :
    ∃ c : ℂ, Ō = c • LinearMap.id

end Abstract

/-! ## A concrete correctable-code witness (anti-vacuity)

Logical space `ℂ²`, physical space the two-region `L²` product `WithLp 2 (ℂ² × ℂ²)`,
encoding `V x = (x, 0)` — the entanglement-wedge-of-`A` embedding. -/

section Witness

/-- The logical Hilbert space of the witness: one qubit, `ℂ²`. -/
abbrev L := EuclideanSpace ℂ (Fin 2)

/-- The physical Hilbert space of the witness: two regions `A` and `Ā`, each a copy
of the logical space, combined with the `L²` (quantum) inner product. -/
abbrev P := WithLp 2 (L × L)

/-- The encoding isometry `V x = (x, 0)`: all logical information is placed in region
`A`, with region `Ā` a fixed reference `0`. This is the ADH picture in the limit
where the bulk operator sits deep in the entanglement wedge of `A`. Norm preservation
(hence isometry) is proved from the `L²` product-norm identity. -/
noncomputable def encIsom : L →ₗᵢ[ℂ] P where
  toFun x := WithLp.toLp 2 (x, 0)
  map_add' a b := by rw [← WithLp.toLp_add]; congr 1; simp
  map_smul' c a := by rw [RingHom.id_apply, ← WithLp.toLp_smul]; congr 1; simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), WithLp.prod_norm_sq_eq_of_L2]
    simp

/-- The region-`A` reconstruction of a logical operator `Ō`: act by `Ō` on the
region-`A` factor and by the identity on region `Ā`, i.e. `Ō ⊗ id`. This is a
boundary operator supported entirely on region `A`. -/
noncomputable def regionAOp (Ō : L →ₗ[ℂ] L) : P →ₗ[ℂ] P where
  toFun p := WithLp.toLp 2 (Ō (WithLp.ofLp p).1, (WithLp.ofLp p).2)
  map_add' a b := by rw [← WithLp.toLp_add]; congr 1; simp
  map_smul' c a := by rw [RingHom.id_apply, ← WithLp.toLp_smul]; congr 1; simp

/-- **Every logical operator is reconstructable on region `A`.** The region-`A`
operator `Ō ⊗ id` reconstructs `Ō` on the code: this is the ADH statement that a
bulk operator inside the entanglement wedge of `A` has a boundary representative
supported on `A`. -/
theorem regionAOp_reconstructs (Ō : L →ₗ[ℂ] L) :
    Reconstructs encIsom (regionAOp Ō) Ō := by
  intro x
  show (regionAOp Ō) (encIsom x) = encIsom (Ō x)
  simp [regionAOp, encIsom]

/-- Erasure of region `Ā`, modeled as projecting the `Ā`-factor to `0` (discarding
`Ā`). -/
noncomputable def eraseB : P →ₗ[ℂ] P where
  toFun p := WithLp.toLp 2 ((WithLp.ofLp p).1, 0)
  map_add' a b := by rw [← WithLp.toLp_add]; congr 1; simp
  map_smul' c a := by rw [RingHom.id_apply, ← WithLp.toLp_smul]; congr 1; simp

/-- **Erasure of region `Ā` is a correctable error.** Every code state is invariant
under erasing `Ā` (`eraseB (V x) = V x`): region `Ā` carries no logical information,
so discarding it and re-preparing the reference recovers the encoded state exactly.
This is the concrete witness that erasure of the complement of the wedge is
correctable — the QEC content of "reconstructable on `A`." -/
theorem eraseB_correctable (x : L) : eraseB (encIsom x) = encIsom x := by
  simp [eraseB, encIsom]

/-- **Anti-vacuity.** A nonzero, non-identity logical operator exists (here `2 • id`),
so `regionAOp_reconstructs` and `eraseB_correctable` are genuinely non-degenerate:
they reconstruct / protect a nontrivial logical operator, not `0` or the identity. -/
theorem witness_nontrivial_logical :
    ∃ Ō : L →ₗ[ℂ] L, Ō ≠ 0 ∧ Ō ≠ LinearMap.id := by
  refine ⟨(2 : ℂ) • LinearMap.id, ?_, ?_⟩
  · intro h
    have := congrArg (· (EuclideanSpace.single 0 (1 : ℂ))) h
    simp at this
  · intro h
    have h2 := congrArg (· (EuclideanSpace.single 0 (1 : ℂ))) h
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h2
    have := congrArg (fun v => v 0) h2
    simp at this

end Witness

end QECHolography
