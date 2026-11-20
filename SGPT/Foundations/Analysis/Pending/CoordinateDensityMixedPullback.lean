import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamily

set_option autoImplicit false

/-!
# Pullback of the MIXED top density under a real-linear map

`FirstPass.CoordinateWedgePullback` proves the two pullback laws of the exterior POWER
of one real two-form: the power commutes with pullback along a real-linear map, and the
standard-frame density of an endomorphism pullback is the real determinant times the
original density.  Those are what make the parameter density of a form patch-independent.

The mixed exterior product of `k` DIFFERENT real two-forms
(`Pending.CoordinateWedgeFamily.coordinateWedgeFamily`) obeys the same two laws, by the
same recursion, and this module proves them.  They are what makes the mixed density a
genuine density on the regular locus rather than a chart-dependent expression, and hence
what lets the mixed densities produced by
`Pending.CoordinateDensityTelescope.actualTopPowerDensity_add_sub` be integrated over an
exhaustion of `V_reg` patch by patch.

Both proofs are the pure-power proofs of `FirstPass.CoordinateWedgePullback` with the
constant family replaced by an arbitrary one: for the first, the recursion on `k` with
`coordinateWedge_compContinuousLinearMap` at each step; for the second, that the top
exterior product is a multiple of the basis determinant of the standard real frame,
so precomposing with an endomorphism multiplies it by that endomorphism's determinant.

Dimension `0` is included: the empty product is the constant `1`, whose pullback is
itself, and the determinant of an endomorphism of the zero space is `1`.
-/

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

noncomputable section

variable {m n : ℕ}

/-- **Pullback along a real-linear map commutes with the mixed exterior product.** -/
theorem coordinateWedgeFamily_compContinuousLinearMap
    (L : ComplexModel m →L[ℝ] ComplexModel n) :
    ∀ (k : ℕ) (A : Fin k → CoordinateRealTwoForm n),
      coordinateWedgeFamily k (fun i => (A i).compContinuousLinearMap L) =
        (coordinateWedgeFamily k A).compContinuousLinearMap L := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => intro A; ext v; rfl
    | 1, _ => intro A; rfl
    | k + 2, ih =>
      intro A
      ext v
      rw [coordinateWedgeFamily_add_two_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply,
        coordinateWedgeFamily_add_two_apply,
        ih (k + 1) (by omega) (fun i => A i.castSucc),
        ← coordinateWedge_compContinuousLinearMap]
      rfl

/-- **Pullback of the mixed top density under a real-linear endomorphism multiplies it
by the real determinant.**  The mixed analogue of
`FirstPass.MongeAmpere.actualTopPowerDensity_compContinuousLinearMap`. -/
theorem actualMixedTopDensity_compContinuousLinearMap (A : Fin n → CoordinateRealTwoForm n)
    (L : ComplexModel n →L[ℝ] ComplexModel n) :
    actualMixedTopDensity (fun i => (A i).compContinuousLinearMap L) =
      LinearMap.det (L : ComplexModel n →ₗ[ℝ] ComplexModel n) * actualMixedTopDensity A := by
  set b := coordinateRealBasis n
  have hΦ := (coordinateWedgeFamily n A).toAlternatingMap.eq_smul_basis_det b
  unfold actualMixedTopDensity
  rw [coordinateWedgeFamily_compContinuousLinearMap L n A,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ← coe_coordinateRealBasis]
  change (coordinateWedgeFamily n A).toAlternatingMap (L ∘ b) =
    _ * (coordinateWedgeFamily n A).toAlternatingMap b
  rw [hΦ]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_self, mul_one]
  rw [show (⇑L ∘ ⇑b) = ⇑(L : ComplexModel n →ₗ[ℝ] ComplexModel n) ∘ ⇑b from rfl,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  ring

end

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
