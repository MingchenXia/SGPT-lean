import SGPT.Support.Alterations.Algebra.AffinePrimeDimension
import SGPT.Foundations.Envelope.AlgGeom.SchemeFunctionFieldDimension
import SGPT.NAPotential.BJChargeGauss
import SGPT.Support.Principalization.Algebra.RegularSmooth.Stalk
import SGPT.Support.Principalization.Algebra.RegularSmooth.SmoothAt
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Divisorial centres of real valuations

Source: [BJ22] (`references/bj22-trivval`), Lemma `lem:tcdiv` (every divisorial valuation is
`v_E` for a component `E` of the central fibre of an integrally closed test configuration), whose
proof goes through [BHJ17, Theorem 4.6] and Zariski's lemma [KM, Lemma 2.45]: a valuation of
transcendence degree `dim - 1` becomes a divisor on a model where its centre is large enough.
Towards `thm:BJappseq` of `chapter_NApotential.tex` (step R8 of `claude-bj-model3:plan`).
Blueprint: `claude-bj-charge.tex`.

This file proves the dimension-theoretic core of that argument, for any normal integral scheme of
finite type over `ℂ` (e.g. the normalized test configurations `normModel` of lane BJ-MODEL3):

* `height_add_card_le_ringKrullDim`: for a prime `P` of a finitely generated domain `A` over a
  field, `ht P + m ≤ dim A` if `κ(P)` contains `m` algebraically independent elements (the
  dimension formula of SGPT.Support.Alterations and `dim A/P = trdeg κ(P)` of SGPT.Foundations.Envelope);
* `coheight_le_one_of_algebraicIndependent`: on an integral scheme of finite type over `ℂ` of
  dimension `≤ n + 1`, a point whose residue field contains `n` algebraically independent
  elements has codimension `≤ 1`;
* `algebraicIndependent_residue_of_residuallyIndependent`: residues of elements of a local ring
  dominated by a valuation `w`, residually independent for `w` (`BJChargeGauss`), are
  algebraically independent;
* `isDiscreteValuationRing_stalk`, `exists_eq_smul_ord`: a normal point of codimension one has a
  DVR as stalk, and a real valuation dominating it is `β · ord`;
* `divisorialCenter`: **a real valuation of `ℂ(𝒳)` centred at a non-generic point `c` of a normal
  `𝒳` of dimension `≤ n + 1`, with `n` residually independent elements in `𝒪_{𝒳,c}`, is
  `β · ord_c` with `c` of codimension one.**

Together with `BJChargeGauss` (the Gauss extension `σ(v)` of a divisorial `v` has
`dim X` residually independent elements `u_1, …, u_{n-1}, t^λ/f`) this reduces [BJ22,
`lem:tcdiv`] to exhibiting these elements in the local ring of the centre of `σ(v)` on a
normalized flag model (see the blueprint remark `claude-bj-charge:plan`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order

section ring

variable {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- **The dimension inequality for a prime of a finitely generated domain**: if the residue field
of `P` contains `m` elements algebraically independent over `k`, then `ht P + m ≤ dim A`
(dimension formula `ht P + dim A/P = dim A` and `dim A/P = trdeg κ(P)`). -/
theorem height_add_card_le_ringKrullDim (P : Ideal A) [P.IsPrime] {ι : Type} [Finite ι]
    {x : ι → P.ResidueField} (hx : AlgebraicIndependent k x) :
    (P.height : WithBot ℕ∞) + (Nat.card ι : WithBot ℕ∞) ≤ ringKrullDim A := by
  rw [← SGPT.Support.Alterations.Algebra.AffinePrimeDimension.height_add_quotient_dimension k A P]
  let : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  have hfin : Algebra.trdeg k (A ⧸ P) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  let : FaithfulSMul (A ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  let : FaithfulSMul k (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (A ⧸ P)).injective
  let : Algebra.IsAlgebraic (A ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic P.ResidueField (nonZeroDivisors (A ⧸ P))
  have heq : Algebra.trdeg k (A ⧸ P) = Algebra.trdeg k P.ResidueField := by
    have h := trdeg_add_eq k (A ⧸ P) (A := P.ResidueField)
    rwa [trdeg_eq_zero (R := A ⧸ P), add_zero] at h
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (heq ▸ hfin)
  rw [SGPT.Foundations.Envelope.SchemeFunctionFieldDimension.affine_dimension_eq k (A ⧸ P)
    P.ResidueField d hd]
  have hcard : (Nat.card ι : Cardinal) ≤ d := by
    rw [Nat.cast_card, ← hd]
    exact hx.cardinalMk_le_trdeg
  have : Nat.card ι ≤ d := by exact_mod_cast hcard
  gcongr

end ring

section scheme

variable {𝒳 : Scheme.{0}} [IsIntegral 𝒳] (q : 𝒳 ⟶ Spec (.of ℂ)) [LocallyOfFiniteType q]

/-- **Codimension of a point with a large residue field**: on an integral scheme of finite type
over `ℂ` of dimension `≤ n + 1`, a point whose residue field contains `n` elements algebraically
independent over `ℂ` has codimension `≤ 1`. -/
theorem coheight_le_one_of_algebraicIndependent {n : ℕ}
    (hdim : topologicalKrullDim 𝒳 ≤ n + 1) (c : 𝒳)
    (x : Fin n → IsLocalRing.ResidueField (𝒳.presheaf.stalk c))
    (hx : letI := q.stalkAlgebra c; AlgebraicIndependent ℂ x) : coheight c ≤ 1 := by
  let := q.stalkAlgebra c
  obtain ⟨_, ⟨U, hU, rfl⟩, hc, -⟩ := 𝒳.isBasis_affineOpens.exists_subset_of_mem_open
    (show c ∈ (⊤ : 𝒳.Opens) from trivial) (⊤ : 𝒳.Opens).isOpen
  let := q.sectionsAlgebra U
  let := 𝒳.presheaf.algebra_section_stalk (⟨c, hc⟩ : U)
  have : IsScalarTower ℂ Γ(𝒳, U) (𝒳.presheaf.stalk c) := q.isScalarTower_sectionsAlgebra_stalk U hc
  have : Algebra.FiniteType ℂ Γ(𝒳, U) := q.finiteType_sectionsAlgebra hU
  have : Nonempty U := ⟨⟨c, hc⟩⟩
  set P := (hU.primeIdealOf ⟨c, hc⟩).asIdeal
  have : IsLocalization.AtPrime (𝒳.presheaf.stalk c) P := hU.isLocalization_stalk ⟨c, hc⟩
  -- the residue field of the stalk is that of `P`, as `ℂ`-algebras
  let e : 𝒳.presheaf.stalk c ≃ₐ[ℂ] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl (𝒳.presheaf.stalk c)
      (Localization.AtPrime P)).restrictScalars ℂ
  have : IsLocalHom e.toRingEquiv.toRingHom :=
    ⟨fun a ha => by simpa using ha.map e.symm.toRingEquiv.toRingHom⟩
  let r : IsLocalRing.ResidueField (𝒳.presheaf.stalk c) →ₐ[ℂ] P.ResidueField :=
    { IsLocalRing.ResidueField.map e.toRingEquiv.toRingHom with
      commutes' := fun a => by
        change IsLocalRing.ResidueField.map e.toRingEquiv.toRingHom
          (IsLocalRing.residue _ (algebraMap ℂ _ a)) = _
        rw [IsLocalRing.ResidueField.map_residue]
        change IsLocalRing.residue _ (e (algebraMap ℂ _ a)) = _
        rw [e.commutes]
        rfl }
  have hr : Function.Injective r := r.toRingHom.injective
  have hP := height_add_card_le_ringKrullDim (k := ℂ) P (hx.map' hr)
  -- dimensions
  have hstalk : coheight c = P.height := by
    have h1 := ringKrullDim_stalk_eq_coheight c
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (𝒳.presheaf.stalk c)] at h1
    exact (WithBot.coe_injective h1).symm
  have hA : ringKrullDim Γ(𝒳, U) ≤ topologicalKrullDim 𝒳 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have := hU.isOpenImmersion_fromSpec
    exact hU.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  rw [hstalk]
  have h2 : (P.height : WithBot ℕ∞) + (n : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) + 1 := by
    have := hP.trans (hA.trans hdim)
    simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using this
  have h3 : P.height + (n : ℕ∞) ≤ 1 + (n : ℕ∞) := by
    rw [add_comm (1 : ℕ∞)]
    exact_mod_cast h2
  exact (WithTop.add_le_add_iff_right (ENat.natCast_ne_top n)).mp h3

end scheme

section residue

open IsLocalRing SGPT.NAPotential.BJCharge

/-- **Residual independence gives independent residues in a dominated local ring**: if `w`
dominates the local ring `R` (`w > 0` on the maximal ideal) along `φ : R → L`, then the residues
of a family of `R` whose image is residually independent for `w` are algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_residue_of_residuallyIndependent {R L : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℂ R] [Field L] [Algebra ℂ L] (φ : R →ₐ[ℂ] L)
    (w : SourceRealValuation L) (hpos : ∀ s ∈ maximalIdeal R, 0 < w (φ s)) {ι : Type*}
    (e : ι → R) (he : ResiduallyIndependent w (φ ∘ e)) :
    AlgebraicIndependent ℂ (residue R ∘ e) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  have h1 : MvPolynomial.aeval (residue R ∘ e) P =
      (IsScalarTower.toAlgHom ℂ R (ResidueField R)) (MvPolynomial.aeval e P) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [h1] at hP
  have hmem : MvPolynomial.aeval e P ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    exact hP
  have h2 := hpos _ hmem
  rw [MvPolynomial.comp_aeval_apply] at h2
  change 0 < w (MvPolynomial.aeval (φ ∘ e) P) at h2
  rw [he P hP0] at h2
  exact lt_irrefl _ h2

end residue

section ord

variable {𝒳 : Scheme.{0}} [IsIntegral 𝒳] [IsLocallyNoetherian 𝒳]

/-- **A normal point of codimension one has a discrete valuation ring as stalk.** -/
theorem isDiscreteValuationRing_stalk {c : 𝒳} (hc : coheight c = 1)
    (hnorm : IsIntegrallyClosed (𝒳.presheaf.stalk c)) :
    IsDiscreteValuationRing (𝒳.presheaf.stalk c) := by
  have hdim : ringKrullDim (𝒳.presheaf.stalk c) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hc]
    rfl
  have hnf : ¬IsField (𝒳.presheaf.stalk c) := by
    intro hF
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by decide)
  have : Ring.KrullDimLE 1 (𝒳.presheaf.stalk c) := krullDimLE_of_coheight_le hc.le
  have hm : IsLocalRing.maximalIdeal (𝒳.presheaf.stalk c) ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf
  have key := (IsDiscreteValuationRing.TFAE (𝒳.presheaf.stalk c) hnf).out 0 3
  refine key.mpr ⟨inferInstance, IsLocalRing.maximalIdeal _, ⟨hm, inferInstance⟩, fun P hP => ?_⟩
  exact IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)

/-- **A real valuation dominating a discrete valuation ring of codimension one is a multiple of
`ord`**: if `w ≥ 0` on the stalk `𝒪_{𝒳,c}` (a DVR) and `w > 0` on its maximal ideal, then
`w = β · ord_c` on `ℂ(𝒳)^×` for some `β > 0`. -/
theorem exists_eq_smul_ord {c : 𝒳} (hc : coheight c = 1)
    [IsDiscreteValuationRing (𝒳.presheaf.stalk c)]
    (w : AddValuation 𝒳.functionField (WithTop ℝ))
    (h0 : ∀ s : 𝒳.presheaf.stalk c, 0 ≤ w (algebraMap _ 𝒳.functionField s))
    (hpos : ∀ s ∈ IsLocalRing.maximalIdeal (𝒳.presheaf.stalk c),
      0 < w (algebraMap _ 𝒳.functionField s)) :
    ∃ β : ℝ, 0 < β ∧ ∀ F : 𝒳.functionField, F ≠ 0 →
      w F = ((β * (Scheme.ord F c : ℝ) : ℝ) : WithTop ℝ) := by
  set R := 𝒳.presheaf.stalk c
  have : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hc.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (algebraMap R 𝒳.functionField) := IsFractionRing.injective _ _
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := hϖ.not_isUnit
  have hϖ0 : algebraMap R 𝒳.functionField ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hfin : w (algebraMap R 𝒳.functionField ϖ) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact hϖ0
  set β := (w (algebraMap R 𝒳.functionField ϖ)).untop hfin
  have hβ : w (algebraMap R 𝒳.functionField ϖ) = (β : WithTop ℝ) := (WithTop.coe_untop _ hfin).symm
  have hβpos : 0 < β := by
    have := hpos ϖ hϖm
    rw [hβ] at this
    exact_mod_cast this
  refine ⟨β, hβpos, fun F hF => ?_⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hF
  have hu : w (algebraMap R 𝒳.functionField (u : R)) = 0 := by
    have h1 : 0 ≤ w (algebraMap R 𝒳.functionField (u : R)) := h0 u
    have h2 : 0 ≤ w (algebraMap R 𝒳.functionField ↑u⁻¹) := h0 ↑u⁻¹
    have h3 : w (algebraMap R 𝒳.functionField (u : R)) + w (algebraMap R 𝒳.functionField ↑u⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    have hne : w (algebraMap R 𝒳.functionField (u : R)) ≠ ⊤ := by
      intro ht
      rw [ht, WithTop.top_add] at h3
      exact WithTop.top_ne_zero h3
    have hne' : w (algebraMap R 𝒳.functionField ↑u⁻¹) ≠ ⊤ := by
      intro ht
      rw [ht, WithTop.add_top] at h3
      exact WithTop.top_ne_zero h3
    lift w (algebraMap R 𝒳.functionField (u : R)) to ℝ using hne with a ha
    lift w (algebraMap R 𝒳.functionField ↑u⁻¹) to ℝ using hne' with b hb
    have h1' : (0 : ℝ) ≤ a := by exact_mod_cast h1
    have h2' : (0 : ℝ) ≤ b := by exact_mod_cast h2
    have h3' : a + b = 0 := by exact_mod_cast h3
    have : a = 0 := by linarith
    rw [this]
    rfl
  have hord : Scheme.ord (u • algebraMap R 𝒳.functionField ϖ ^ n) c = n := by
    rw [Scheme.ord_eq_iff hc hF, Units.smul_def]
    change Ring.ordFrac R ((u : R) • algebraMap R 𝒳.functionField ϖ ^ n) = _
    rw [Algebra.smul_def, map_mul, map_zpow₀,
      Ring.ordFrac_eq_ord R (Units.ne_zero u), Ring.ordFrac_eq_ord R hϖ.ne_zero,
      Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero (Units.ne_zero u))
        (n := 0) (by rw [Ring.ord_of_isUnit u.isUnit]; rfl),
      Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
        (n := 1) (by rw [Ring.ord_of_irreducible hϖ]; rfl)]
    simp only [Nat.cast_zero, ofAdd_zero, WithZero.coe_one, one_mul, Nat.cast_one]
    rw [← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  rw [hord, Units.smul_def, Algebra.smul_def, AddValuation.map_mul, hu, zero_add]
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, AddValuation.map_pow, hβ, ← WithTop.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  · rw [zpow_negSucc, AddValuation.map_inv, AddValuation.map_pow, hβ, ← WithTop.coe_nsmul,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    congr 1
    rw [nsmul_eq_mul, Int.cast_negSucc]
    push_cast
    ring

end ord

section center

open SGPT.NAPotential.BJCharge

variable {𝒳 : Scheme.{0}} [IsIntegral 𝒳] (q : 𝒳 ⟶ Spec (.of ℂ))

/-- The `ℂ`-algebra structures of the stalks and of the function field induced by the structure
morphism are compatible with the specialization map `𝒪_{𝒳,c} → ℂ(𝒳)`. -/
theorem algebraMap_stalk_functionField_complex (c : 𝒳) (a : ℂ) :
    letI := q.stalkAlgebra c
    letI := q.stalkAlgebra (genericPoint 𝒳)
    algebraMap (𝒳.presheaf.stalk c) 𝒳.functionField (algebraMap ℂ _ a) =
      algebraMap ℂ 𝒳.functionField a := by
  let := q.stalkAlgebra c
  let := q.stalkAlgebra (genericPoint 𝒳)
  rw [Scheme.Hom.algebraMap_stalkAlgebra, Scheme.Hom.algebraMap_stalkAlgebra,
    RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply]
  congr 2
  rw [Category.assoc, Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]

/-- The specialization map `𝒪_{𝒳,c} → ℂ(𝒳)` as a `ℂ`-algebra map. -/
def stalkToFunctionField (c : 𝒳) :
    letI := q.stalkAlgebra c
    letI := q.stalkAlgebra (genericPoint 𝒳)
    𝒳.presheaf.stalk c →ₐ[ℂ] 𝒳.functionField :=
  letI := q.stalkAlgebra c
  letI := q.stalkAlgebra (genericPoint 𝒳)
  { algebraMap (𝒳.presheaf.stalk c) 𝒳.functionField with
    commutes' := algebraMap_stalk_functionField_complex q c }

variable [IsLocallyNoetherian 𝒳] [LocallyOfFiniteType q]

/-- **Divisorial centres** (the dimension argument of [BHJ17, Theorem 4.6] / Zariski's lemma, in the
form used for [BJ22, `lem:tcdiv`]): let `𝒳` be a normal integral scheme of finite type over `ℂ` of
dimension `≤ n + 1`, `w` a real valuation of `ℂ(𝒳)` (trivial on `ℂ`) centred at a non-generic
point `c` (`w ≥ 0` on `𝒪_{𝒳,c}`, `w > 0` on its maximal ideal), and suppose `𝒪_{𝒳,c}` contains `n`
elements whose images are residually independent for `w`. Then `c` has codimension one, `𝒪_{𝒳,c}`
is a discrete valuation ring and `w = β ord_c` for some `β > 0`. -/
theorem divisorialCenter (hnorm : ∀ x : 𝒳, IsIntegrallyClosed (𝒳.presheaf.stalk x)) {n : ℕ}
    (hdim : topologicalKrullDim 𝒳 ≤ n + 1) {c : 𝒳} (hc : c ≠ genericPoint 𝒳)
    (w : letI := q.stalkAlgebra (genericPoint 𝒳); SourceRealValuation 𝒳.functionField)
    (h0 : ∀ s : 𝒳.presheaf.stalk c, 0 ≤ w (algebraMap _ 𝒳.functionField s))
    (hpos : ∀ s ∈ IsLocalRing.maximalIdeal (𝒳.presheaf.stalk c),
      0 < w (algebraMap _ 𝒳.functionField s))
    (e : Fin n → 𝒳.presheaf.stalk c)
    (he : letI := q.stalkAlgebra (genericPoint 𝒳);
      ResiduallyIndependent w (algebraMap _ 𝒳.functionField ∘ e)) :
    coheight c = 1 ∧ IsDiscreteValuationRing (𝒳.presheaf.stalk c) ∧
      ∃ β : ℝ, 0 < β ∧ ∀ F : 𝒳.functionField, F ≠ 0 →
        w F = ((β * (Scheme.ord F c : ℝ) : ℝ) : WithTop ℝ) := by
  let := q.stalkAlgebra c
  let := q.stalkAlgebra (genericPoint 𝒳)
  have hres := algebraicIndependent_residue_of_residuallyIndependent (stalkToFunctionField q c) w
    hpos e he
  have hle := coheight_le_one_of_algebraicIndependent q hdim c _ hres
  have hne : coheight c ≠ 0 := by
    rw [Ne, Order.coheight_eq_zero]
    intro hmax
    apply hc
    have h1 : c ≤ genericPoint 𝒳 := by
      rw [Scheme.le_iff_specializes]
      exact genericPoint_specializes c
    exact (inseparable_iff_specializes_and.mpr
      ⟨Scheme.le_iff_specializes.mp (hmax h1), genericPoint_specializes c⟩).eq
  have hc1 : coheight c = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  have := isDiscreteValuationRing_stalk hc1 (hnorm c)
  exact ⟨hc1, this, exists_eq_smul_ord hc1 w.toAddValuation h0 hpos⟩

end center

end SGPT.NAPotential.BJ
