import SGPT.Unibranch.UnibAlgBridge
import SGPT.Unibranch.UnibAlgPrimitive
import SGPT.Unibranch.UnibAlgZariski
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Reduced fibres of `ℂ[w] → ℂ⟦w⟧`

For a domain `R₁` which is a finite algebra over `P₀ = ℂ[w]` (not necessarily injective), the
ring `Y = ℂ⟦w⟧ ⊗_{P₀} R₁` is reduced (`isReduced_tensor_of_finite`). At every maximal ideal
`M` of `Y` (residue field `ℂ`, `exists_residue`) we present `R₁ = ℂ[z]/I`, take the point `c`
given by `M`, and compare `Y` with the formal completion `B` of `R₁` at `c` twice through the
bridge (`UnibAlgBridge`): once for `P₀ → R₁` and once for a Noether normalization
`P₂ → R₁`. The second comparison shows that `B` is reduced (`isReduced_tensor`), the first
that nilpotents of `Y` vanish near `M`.

This is the fibre hypothesis of `dvd_of_sq_eq_mul` (`UnibAlgZariski`): the formal fibres of
`ℂ[w]` at height-one primes are reduced. Lane UNIB-ALG; blueprint `claude-unib-alg.tex`.
-/

set_option autoImplicit false

open MvPowerSeries TensorProduct

namespace SGPT.Unibranch.UnibAlg

noncomputable section

variable {d : ℕ}

local notation "P₀" => MvPolynomial (Fin d) ℂ
local notation "T₀" => MvPowerSeries (Fin d) ℂ

section Fibre

variable {R₁ : Type*} [CommRing R₁] [Algebra ℂ R₁] [Algebra (MvPolynomial (Fin d) ℂ) R₁]
  [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) R₁] [Module.Finite (MvPolynomial (Fin d) ℂ) R₁]

omit [Algebra ℂ R₁] [IsScalarTower ℂ P₀ R₁] [Module.Finite P₀ R₁] in
theorem algebraMap_tensor_eq (z : ℂ) :
    algebraMap ℂ (T₀ ⊗[P₀] R₁) z = (C z : T₀) ⊗ₜ[P₀] (1 : R₁) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

omit [Algebra ℂ R₁] [IsScalarTower ℂ P₀ R₁] [Module.Finite P₀ R₁] in
theorem one_tmul_algebraMap (p : P₀) :
    (1 : T₀) ⊗ₜ[P₀] algebraMap P₀ R₁ p = (p : T₀) ⊗ₜ[P₀] (1 : R₁) :=
  (Algebra.TensorProduct.tmul_one_eq_one_tmul p).symm

theorem constantCoeff_coe_eq_eval (p : P₀) :
    constantCoeff (p : T₀) = MvPolynomial.eval 0 p := by
  rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, MvPolynomial.eval_zero,
    MvPolynomial.constantCoeff_eq]

omit [Algebra ℂ R₁] [IsScalarTower ℂ P₀ R₁] in
/-- **Residue fields.** Every maximal ideal of `ℂ⟦w⟧ ⊗ R₁` is the kernel of a `ℂ`-point which
restricts to the constant coefficient on `ℂ⟦w⟧`. -/
theorem exists_residue (M : Ideal (T₀ ⊗[P₀] R₁)) [M.IsMaximal] :
    ∃ χ : T₀ ⊗[P₀] R₁ →+* ℂ, RingHom.ker χ = M ∧ (∀ z : ℂ, χ (algebraMap ℂ _ z) = z) ∧
      ∀ t : T₀, χ (t ⊗ₜ 1) = constantCoeff t := by
  set Y := T₀ ⊗[P₀] R₁
  have : Module.Finite T₀ Y := Module.Finite.base_change P₀ T₀ R₁
  have : Algebra.IsIntegral T₀ Y := Algebra.IsIntegral.of_finite T₀ Y
  have hM₀ : (M.comap (algebraMap T₀ Y)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hM₀eq : M.comap (algebraMap T₀ Y) = spanX (Fin d) ℂ := by
    rw [← maximalIdeal_eq_spanX]
    exact IsLocalRing.eq_maximalIdeal hM₀
  let : Field (Y ⧸ M) := Ideal.Quotient.field M
  -- `ℂ⟦w⟧ → Y / M` factors through the constant coefficient
  have hfac : (Ideal.Quotient.mk M).comp (algebraMap T₀ Y) =
      (algebraMap ℂ (Y ⧸ M)).comp (constantCoeff (σ := Fin d) (R := ℂ)) := by
    ext1 t
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply ℂ Y (Y ⧸ M), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq, algebraMap_tensor_eq]
    change (t ⊗ₜ[P₀] (1 : R₁)) - (C (constantCoeff t) : T₀) ⊗ₜ[P₀] (1 : R₁) ∈ M
    rw [← sub_tmul]
    have : t - C (constantCoeff t) ∈ M.comap (algebraMap T₀ Y) := by
      rw [hM₀eq, mem_spanX_iff]
      simp
    exact this
  have : Algebra.IsIntegral ℂ (Y ⧸ M) := by
    constructor
    intro k
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨p, hpm, hp⟩ := (Algebra.IsIntegral.isIntegral (R := T₀) y)
    refine ⟨p.map constantCoeff, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hfac, ← Polynomial.hom_eval₂, hp, map_zero]
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := Y ⧸ M)
  set e := RingEquiv.ofBijective (algebraMap ℂ (Y ⧸ M)) hbij
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk M), ?_, ?_, ?_⟩
  · ext y
    simp only [RingHom.mem_ker, RingHom.comp_apply]
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.symm.injective,
      Ideal.Quotient.eq_zero_iff_mem]
  · intro z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply z
  · intro t
    have h := congrArg (fun f => f t) hfac
    simp only [RingHom.comp_apply] at h
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [show t ⊗ₜ[P₀] (1 : R₁) = algebraMap T₀ Y t from rfl, h]
    exact e.symm_apply_apply _

/-- The formal completion `B` of a presented ring at a point is reduced, provided some finite
injective `ℂ[u]`-structure with the generators vanishing at the point exists. -/
theorem isReduced_B_of_noether {s n : ℕ} {R₂ : Type*} [CommRing R₂] [IsDomain R₂] [Algebra ℂ R₂]
    [Algebra (MvPolynomial (Fin s) ℂ) R₂] [IsScalarTower ℂ (MvPolynomial (Fin s) ℂ) R₂]
    [Module.Finite (MvPolynomial (Fin s) ℂ) R₂] [FaithfulSMul (MvPolynomial (Fin s) ℂ) R₂]
    (D₂ : BridgeData n s R₂) : IsReduced D₂.B := by
  have := isReduced_tensor (d := s) R₂
  refine ⟨fun b ⟨m, hm⟩ => ?_⟩
  obtain ⟨z, rfl⟩ := D₂.bridgeMap_surjective b
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [pow_zero] at hm
    have : Subsingleton D₂.B := subsingleton_of_zero_eq_one hm.symm
    exact Subsingleton.elim _ _
  rw [← map_pow] at hm
  obtain ⟨u, hu, huz⟩ := D₂.bridgeMap_eq_zero hm
  have hnil : IsNilpotent (u * z) := ⟨m, by
    rw [mul_pow, show u ^ m = u ^ (m - 1) * u by rw [← pow_succ, Nat.sub_add_cancel hpos],
      mul_assoc, huz, mul_zero]⟩
  have h0 : u * z = 0 := hnil.eq_zero
  have := congrArg D₂.bridgeMap h0
  rw [map_mul, map_zero] at this
  exact (D₂.isUnit_bridgeMap hu).mul_right_eq_zero.mp this

/-- **Reduced fibres.** If `R₁` is a domain, finite over `ℂ[w]`, then `ℂ⟦w⟧ ⊗_{ℂ[w]} R₁` is
reduced. -/
theorem isReduced_tensor_of_finite [IsDomain R₁] : IsReduced (T₀ ⊗[P₀] R₁) := by
  classical
  set Y := T₀ ⊗[P₀] R₁
  have hft : Algebra.FiniteType ℂ R₁ := Algebra.FiniteType.trans (S := P₀) inferInstance
    inferInstance
  obtain ⟨k, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  -- it suffices to kill a nilpotent near every maximal ideal
  suffices hloc : ∀ y : Y, IsNilpotent y → ∀ (M : Ideal Y), M.IsMaximal →
      ∃ u ∉ M, u * y = 0 by
    refine ⟨fun y hy => ?_⟩
    by_contra hy0
    set ann : Ideal Y := Submodule.annihilator (Submodule.span Y {y})
    have hann : ann ≠ ⊤ := by
      intro h
      have : (1 : Y) ∈ ann := h ▸ Submodule.mem_top
      rw [Submodule.mem_annihilator_span_singleton, one_smul] at this
      exact hy0 this
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal ann hann
    obtain ⟨u, hu, huy⟩ := hloc y hy M hM
    exact hu (hle ((Submodule.mem_annihilator_span_singleton _ _).mpr (by rwa [smul_eq_mul])))
  intro y hy M hM
  obtain ⟨χM, hker, hχC, hχT⟩ := exists_residue M
  set χR : R₁ →+* ℂ := χM.comp (Algebra.TensorProduct.includeRight : R₁ →ₐ[P₀] Y).toRingHom
  have hχR_alg : ∀ p : P₀, χR (algebraMap P₀ R₁ p) = MvPolynomial.eval 0 p := by
    intro p
    change χM ((1 : T₀) ⊗ₜ[P₀] algebraMap P₀ R₁ p) = _
    rw [one_tmul_algebraMap, hχT, constantCoeff_coe_eq_eval]
  have hχR_C : ∀ z : ℂ, χR (algebraMap ℂ R₁ z) = z := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℂ P₀ R₁, hχR_alg, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval_C]
  -- the point `c`
  set c : Fin k → ℂ := fun i => χR (φ (MvPolynomial.X i))
  have hχRφ : ∀ p, χR (φ p) = MvPolynomial.eval c p := by
    have : χR.comp φ.toRingHom = MvPolynomial.eval c := by
      apply MvPolynomial.ringHom_ext
      · intro z
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.eval_C]
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, hχR_C]
      · intro i
        rw [MvPolynomial.eval_X]
        rfl
    intro p
    exact congrArg (fun f : MvPolynomial (Fin k) ℂ →+* ℂ => f p) this
  have hc : ∀ p, φ p = 0 → MvPolynomial.eval c p = 0 := fun p hp => by
    rw [← hχRφ, hp, map_zero]
  choose y₁ hy₁ using fun i => hφ (algebraMap P₀ R₁ (MvPolynomial.X i))
  have hy₁0 : ∀ i, MvPolynomial.eval c (y₁ i) = 0 := by
    intro i
    rw [← hχRφ, hy₁, hχR_alg, MvPolynomial.eval_X]
    rfl
  let D₁ : BridgeData k d R₁ := ⟨φ, hφ, c, hc, y₁, hy₁, hy₁0⟩
  have hχ : ∀ x, D₁.χ x = χM x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t r =>
      rw [D₁.χ_tmul]
      have : t ⊗ₜ[P₀] r = (t ⊗ₜ[P₀] (1 : R₁)) * ((1 : T₀) ⊗ₜ[P₀] r) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, hχT]
      congr 1
      obtain ⟨p, rfl⟩ := hφ r
      rw [D₁.evR_φ]
      exact (hχRφ p).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  -- a Noether normalization adapted to `c`
  have : Algebra.FiniteType ℂ R₁ := hft
  obtain ⟨s, g₂, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ R₁
  set c₂ : Fin s → ℂ := fun i => χR (g₂ (MvPolynomial.X i))
  set g₂' : MvPolynomial (Fin s) ℂ →ₐ[ℂ] R₁ := g₂.comp (transl (-c₂))
  have hg₂'X : ∀ i, g₂' (MvPolynomial.X i) = g₂ (MvPolynomial.X i) - algebraMap ℂ R₁ (c₂ i) := by
    intro i
    simp only [g₂', AlgHom.comp_apply, transl_X, map_add, Pi.neg_apply,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, map_neg, sub_eq_add_neg]
  have hinj' : Function.Injective g₂' :=
    hinj.comp (Function.LeftInverse.injective (g := transl c₂) (transl_transl_neg c₂))
  have hfin' : g₂'.toRingHom.Finite :=
    RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ fun q =>
      ⟨transl c₂ q, transl_neg_transl c₂ q⟩)
  let : Algebra (MvPolynomial (Fin s) ℂ) R₁ := g₂'.toRingHom.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Fin s) ℂ) R₁ :=
    IsScalarTower.of_algebraMap_eq fun z => (g₂'.commutes z).symm
  have : Module.Finite (MvPolynomial (Fin s) ℂ) R₁ := hfin'
  have : FaithfulSMul (MvPolynomial (Fin s) ℂ) R₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  choose y₂ hy₂ using fun i => hφ (algebraMap (MvPolynomial (Fin s) ℂ) R₁ (MvPolynomial.X i))
  have hy₂0 : ∀ i, MvPolynomial.eval c (y₂ i) = 0 := by
    intro i
    rw [← hχRφ, hy₂]
    change χR (g₂' (MvPolynomial.X i)) = 0
    rw [hg₂'X, map_sub, hχR_C, sub_self]
  let D₂ : BridgeData k s R₁ := ⟨φ, hφ, c, hc, y₂, hy₂, hy₂0⟩
  have hB : IsReduced D₂.B := isReduced_B_of_noether D₂
  have hB₁ : IsReduced D₁.B := hB
  have h0 : D₁.bridgeMap y = 0 := (hy.map D₁.bridgeMap).eq_zero
  obtain ⟨u, hu, huy⟩ := D₁.bridgeMap_eq_zero h0
  refine ⟨u, ?_, huy⟩
  rw [← hker, RingHom.mem_ker, ← hχ]
  exact hu

end Fibre

end

end SGPT.Unibranch.UnibAlg
