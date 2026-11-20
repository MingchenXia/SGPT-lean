import SGPT.Foundations.Schemes.NativeAffineLinePower
import SGPT.Foundations.Schemes.PolynomialFiberPowerFiniteness
import SGPT.Foundations.Schemes.NativeAffineLineNormality
/-!
# NativeAffineLinePowerFiniteness

The actual native one-variable polynomial identification retains projected constants and the actual fiber coordinate. The literal native power regular map is conjugate to the true polynomial power map. Positive powers are finite over actual affine bases.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The actual single-variable polynomial identification retains base regular functions. -/
theorem nativeAffineLineSinglePolynomialEquiv_C (U : Scheme.{u}) [IsAffine U] (r : Γ(U, ⊤)) :
    nativeAffineLineSinglePolynomialEquiv U (Polynomial.C r) =
      (nativeAffineLineProjection U).appTop r := by
  change nativeAffineLinePolynomialEquiv U
    ((MvPolynomial.uniqueAlgEquiv Γ(U, ⊤) PUnit.{u + 1}).symm (Polynomial.C r)) = _
  have h : (MvPolynomial.uniqueAlgEquiv Γ(U, ⊤) PUnit.{u + 1}).symm (Polynomial.C r) =
      MvPolynomial.C r := by simp [MvPolynomial.uniqueAlgEquiv]
  rw [h, nativeAffineLinePolynomialEquiv_C]

/-- The actual single-variable polynomial identification retains the genuine fiber coordinate. -/
theorem nativeAffineLineSinglePolynomialEquiv_X (U : Scheme.{u}) [IsAffine U] :
    nativeAffineLineSinglePolynomialEquiv U Polynomial.X = nativeAffineLineCoordinate U := by
  change nativeAffineLinePolynomialEquiv U
    ((MvPolynomial.uniqueAlgEquiv Γ(U, ⊤) PUnit.{u + 1}).symm Polynomial.X) = _
  have h : (MvPolynomial.uniqueAlgEquiv Γ(U, ⊤) PUnit.{u + 1}).symm Polynomial.X =
      MvPolynomial.X PUnit.unit := by simp [MvPolynomial.uniqueAlgEquiv]
  rw [h, nativeAffineLinePolynomialEquiv_X]

/-- The literal coefficient homomorphism of the native power map is the actual polynomial power map. -/
theorem nativeAffineLinePower_regular_triangle (U : Scheme.{u}) [IsAffine U] (q : ℕ) :
    (nativeAffineLinePower U q).appTop.hom.comp (nativeAffineLineSinglePolynomialEquiv U).toRingHom =
      (nativeAffineLineSinglePolynomialEquiv U).toRingHom.comp (polynomialFiberPowerHom Γ(U, ⊤) q) := by
  apply Polynomial.ringHom_ext
  · intro r
    change (nativeAffineLinePower U q).appTop
      (nativeAffineLineSinglePolynomialEquiv U (Polynomial.C r)) =
      nativeAffineLineSinglePolynomialEquiv U (polynomialFiberPowerHom Γ(U, ⊤) q (Polynomial.C r))
    rw [polynomialFiberPowerHom_C, nativeAffineLineSinglePolynomialEquiv_C]
    exact congrArg (fun f ↦ f.appTop r) (nativeAffineLinePower_projection U q)
  · change (nativeAffineLinePower U q).appTop
      (nativeAffineLineSinglePolynomialEquiv U Polynomial.X) =
      nativeAffineLineSinglePolynomialEquiv U (polynomialFiberPowerHom Γ(U, ⊤) q Polynomial.X)
    rw [polynomialFiberPowerHom_X, map_pow, nativeAffineLineSinglePolynomialEquiv_X,
      nativeAffineLinePower_coordinate]

private theorem finite_of_equiv_triangle {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (f : R →+* R) (g : S →+* S)
    (ht : g.comp e.toRingHom = e.toRingHom.comp f) (hf : f.Finite) : g.Finite := by
  have hg : g = e.toRingHom.comp (f.comp e.symm.toRingHom) := by
    apply RingHom.ext
    intro r
    change g r = e (f (e.symm r))
    have h := DFunLike.congr_fun ht (e.symm r)
    change g (e (e.symm r)) = e (f (e.symm r)) at h
    simpa only [e.apply_symm_apply] using h
  rw [hg]
  exact (RingHom.Finite.of_surjective _ e.surjective).comp
    (hf.comp (RingHom.Finite.of_surjective _ e.symm.surjective))

/-- The actual global regular-section homomorphism of a positive native fiber power is finite. -/
theorem nativeAffineLinePower_appTop_finite (U : Scheme.{u}) [IsAffine U]
    (q : ℕ) (hq : 0 < q) : (nativeAffineLinePower U q).appTop.hom.Finite :=
  finite_of_equiv_triangle (nativeAffineLineSinglePolynomialEquiv U)
    (polynomialFiberPowerHom Γ(U, ⊤) q) (nativeAffineLinePower U q).appTop.hom
    (nativeAffineLinePower_regular_triangle U q) (polynomialFiberPowerHom_finite Γ(U, ⊤) q hq)

/-- Every positive actual fiber power over an affine base is a genuine finite scheme morphism. -/
theorem nativeAffineLinePower_isFinite_affine (U : Scheme.{u}) [IsAffine U]
    (q : ℕ) (hq : 0 < q) : IsFinite (nativeAffineLinePower U q) := by
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  exact ⟨inferInstance, nativeAffineLinePower_appTop_finite U q hq⟩

end
end SGPT.Foundations.Schemes
