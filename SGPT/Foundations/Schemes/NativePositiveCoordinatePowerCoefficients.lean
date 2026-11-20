import SGPT.Foundations.Schemes.NativePositiveProjectiveCoordinateSections
/-!
# NativePositiveCoordinatePowerCoefficients

In every original line frame the actual extension unit frame coefficient is exactly the dth power of the true global positive coordinate coefficient. Genuine transitions and actual iterated-power normalization supply the equality.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n) (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The actual extension unit frame has original coefficient precisely the dth power of the genuine degree-q coordinate section coefficient. -/
theorem nativePositiveProjectivePowerFrame_unit_originalCoefficients
    (d : ℕ) (i : Fin (n + 1)) (j : L.atlas.I) {W : X.Opens}
    (h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) (k : W ⟶ L.atlas.opens j) :
    ((L.atlas.frame j).tensorPower (q * d)).coefficients k
      (((nativePositiveProjectivePowerFrame K n f L q e d i).coefficients h).symm 1) =
    (((L.atlas.frame j).tensorPower q).coefficients k
      ((bundleTensorPower L.sheaf q).val.map (homOfLE le_top).op
        (nativePositiveProjectiveCoordinateSection K n f L q e i))) ^ d := by
  let P := nativePositiveProjectivePowerFrame K n f L q e d i
  let C := nativePositiveProjectiveCoordinateFrame K n f L q e i
  let A := nativeLineTensorPowerMulIso L.atlas q d
  let t := (P.coefficients h).symm 1
  have hN := nativePositiveProjectivePowerFrame_coefficients K n f L q e d i h t
  have hC : (C.tensorPower d).coefficients h (A.hom.val.app (.op W) t) = 1 :=
    hN.symm.trans ((P.coefficients h).apply_symm_apply 1)
  have ht := localBundleFrameTransition_coefficients C ((L.atlas.frame j).tensorPower q) h k
    ((bundleTensorPower L.sheaf q).val.map (homOfLE le_top).op
      (nativePositiveProjectiveCoordinateSection K n f L q e i))
  have hOne := nativePositiveProjectiveCoordinateSection_coefficients K n f L q e i h
  change C.coefficients h _ = 1 at hOne
  rw [hOne, mul_one] at ht
  have hp := localBundleFrameTransition_coefficients (C.tensorPower d)
    (((L.atlas.frame j).tensorPower q).tensorPower d) h k (A.hom.val.app (.op W) t)
  rw [localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val, hC, mul_one] at hp
  have hM := nativeLineTensorPowerMulIso_anyFrame L.atlas q d (L.atlas.frame j) k t
  exact hM.symm.trans (hp.trans (congrArg (fun r ↦ r ^ d) ht.symm))

end
end SGPT.Foundations.Schemes
