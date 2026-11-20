import SGPT.Foundations.Schemes.PolynomialProjectiveCoordinatePullback
import SGPT.Foundations.Schemes.PolynomialProjectiveTwistingTransition
import SGPT.Foundations.Schemes.NativePolynomialPullbackPower
/-!
# NativeProjectiveCoordinateUnitLocus

True projective ratio unit loci are the actual intersections of coordinate opens, by the genuine affine chart isomorphism and literal homogeneous-localization coordinate maps.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine projective ratio's unit locus is the other coordinate open inside the actual chart. -/
theorem polynomialProjCoordinateRegularRatio_basicOpen (j i : Fin (n + 1)) :
    (polynomialProjCoordinateOpen K n j).toScheme.basicOpen
      ((polynomialProjCoordinateOpen K n j).topIso.inv
        (polynomialProjCoordinateRegularRatio K n j i)) =
      (polynomialProjCoordinateOpen K n j).ι ⁻¹ᵁ polynomialProjCoordinateOpen K n i := by
  let e := polynomialProjCoordinateSchemeIso K n j
  have hc : e.hom ≫ polynomialProjCoordinateImmersion K n j =
      (polynomialProjCoordinateOpen K n j).ι := by
    change e.hom ≫ (e.inv ≫ (polynomialProjCoordinateOpen K n j).ι) = _
    simp
  have hg := congrArg (fun V ↦ e.hom ⁻¹ᵁ V)
    (polynomialProjCoordinateImmersion_preimage_coordinateOpen K n j i)
  rw [← Scheme.Hom.comp_preimage, hc] at hg
  calc
    _ = e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j i) := by
      rw [← polynomialProjCoordinateSchemeIso_top_ratio,
        ← Scheme.Hom.preimage_basicOpen_top, basicOpen_eq_of_affine]
    _ = _ := hg.symm

/-- The actual ratio viewed on the entire projective scheme has precisely the intersection unit locus. -/
theorem polynomialProjCoordinateRegularRatio_globalBasicOpen (j i : Fin (n + 1)) :
    (polynomialProj K n).basicOpen (polynomialProjCoordinateRegularRatio K n j i) =
      polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n i := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv,
    polynomialProjCoordinateRegularRatio_basicOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  simp

end
end SGPT.Foundations.Schemes
