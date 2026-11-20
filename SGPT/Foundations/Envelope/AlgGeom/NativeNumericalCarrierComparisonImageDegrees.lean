import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalCarrierComparisonImage

/-! # Original whole-line degree tests through actual original curve images

The actual point-image and finite closed-curve-image producers in Image are
used here to compare the two ORIGINAL integer kernels. The accepted Image
producer is kept unchanged. No kernel equality is supplied as a premise.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonImageDegrees

open NativeNumericalCarrierComparison NativeNumericalCarrierComparisonCurves
open NativeNumericalCarrierComparisonImage NativeClosedCurveDegrees
open scoped TensorProduct
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))


/-- The original native Picard quotient homomorphism, with its canonical additive structure. -/
def additiveClassMap : Additive X.Pic →ₗ[ℤ]
    Additive (NativeCurveNumericalClasses.NumericalClass p) :=
  (NativeCurveNumericalClasses.classMap p).toAdditive.toIntLinearMap

/-- Every original additive native numerical class has an original Picard representative. -/
theorem additiveClassMap_surjective : Function.Surjective (additiveClassMap p) := by
  intro a
  obtain ⟨b, hb⟩ := NativeCurveNumericalClasses.classMap_surjective p a.toMul
  exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩


section Projective
variable [IsProjective p]

section CurveMaps
variable (C : IntegralCurveMap p)
private local instance curve_integral : IsIntegral C.carrier := C.integral


private theorem degree_pullback_eq_zero_of_closed
    (L : X.Modules) (hL : IsInvertible L)
    (hclosed : ∀ D : ClosedIntegralCurve X,
      Multiplicative.toAdd (D.picardDegree p (CurvePicardDegrees.lineClass L hL)) = 0) :
    letI : IsProper C.structureMorphism := C.projective.isProper
    letI : CompactSpace C.carrier :=
      QuasiCompact.compactSpace_of_compactSpace C.structureMorphism
    CurveLineDegrees.degree C.structureMorphism ((Scheme.Modules.pullback C.morphism).obj L) = 0 := by
  classical
  let : IsProper C.structureMorphism := C.projective.isProper
  let : CompactSpace C.carrier :=
    QuasiCompact.compactSpace_of_compactSpace C.structureMorphism
  let : IsProper C.morphism := morphism_isProper p C
  let : IsIntegral C.morphism.image := image_isIntegral p C
  by_cases hnon : Nontrivial C.morphism.image
  · let : Nontrivial C.morphism.image := hnon
    let D := closedImage p C
    let qD := D.structureMorphism p
    let : IsProper qD := (D.projectiveFactorization p).isProper
    let : CompactSpace D.carrier := QuasiCompact.compactSpace_of_compactSpace qD
    let : IsFinite C.morphism.toImage := toImage_isFinite p C
    let : IsDominant C.morphism.toImage := inferInstance
    have hD : CurveLineDegrees.degree qD ((Scheme.Modules.pullback D.inclusion).obj L) = 0 := by
      have h := hclosed D
      rw [D.picardDegree_lineClass p L hL] at h
      exact h
    have hd := CurveFiniteDominantLineDegrees.degree_pullback C.morphism.toImage
      qD (D.projectiveFactorization p) D.dimension.le C.dimension.le
      ((Scheme.Modules.pullback D.inclusion).obj L) (hL.pullback D.inclusion)
    have hmap : C.morphism.toImage ≫ D.inclusion = C.morphism :=
      Scheme.Hom.toImage_imageι C.morphism
    let e := (Scheme.Modules.pullbackComp C.morphism.toImage D.inclusion).app L ≪≫
      (Scheme.Modules.pullbackCongr hmap).app L
    have hs : C.morphism.toImage ≫ qD = C.structureMorphism := image_structure_triangle p C
    have hd0 : CurveLineDegrees.degree (C.morphism.toImage ≫ qD)
        ((Scheme.Modules.pullback C.morphism.toImage).obj
          ((Scheme.Modules.pullback D.inclusion).obj L)) = 0 := by
      exact hd.trans (mul_eq_zero.mpr (Or.inr hD))
    have hchange := congrArg (fun q : C.carrier ⟶ Spec (.of k) =>
      CurveLineDegrees.degree q ((Scheme.Modules.pullback C.morphism.toImage).obj
        ((Scheme.Modules.pullback D.inclusion).obj L))) hs
    exact (CurveLineDegrees.degree_eq_of_iso C.structureMorphism e).symm.trans
      (hchange.symm.trans hd0)
  · let : Subsingleton C.morphism.image := not_nontrivial_iff_subsingleton.mp hnon
    obtain ⟨e⟩ := invertible_nonempty_iso_unit_of_subsingleton (hL.pullback C.morphism.imageι)
    let epull : (Scheme.Modules.pullback C.morphism).obj L ≅ unitObj C.carrier :=
      (Scheme.Modules.pullbackCongr (Scheme.Hom.toImage_imageι C.morphism)).symm.app L ≪≫
      (Scheme.Modules.pullbackComp C.morphism.toImage C.morphism.imageι).symm.app L ≪≫
      (Scheme.Modules.pullback C.morphism.toImage).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso C.morphism.toImage
    rw [CurveLineDegrees.degree_eq_of_iso C.structureMorphism epull, CurveLineDegrees.degree_unit]

/-- All closed original integer degree tests imply each actual original
projective curve-map degree test. Its image geometry is proved internally. -/
theorem curveDegree_eq_one_of_closed (a : X.Pic)
    (hclosed : ∀ D : ClosedIntegralCurve X, D.picardDegree p a = 1) :
    CurvePicardDegrees.curveDegreeHom C.structureMorphism C.projective
      C.dimension.le C.morphism a = 1 := by
  let : IsProper C.structureMorphism := C.projective.isProper
  let : CompactSpace C.carrier :=
    QuasiCompact.compactSpace_of_compactSpace C.structureMorphism
  obtain ⟨L, hL, rfl⟩ := ProjectiveGeneratedLineClasses.exists_line_representative a
  apply Multiplicative.ext
  rw [toAdd_one, CurvePicardDegrees.curveDegreeHom_lineClass]
  apply degree_pullback_eq_zero_of_closed p C L hL
  intro D
  have h := congrArg Multiplicative.toAdd (hclosed D)
  simpa only [toAdd_one] using h


end CurveMaps

/-- The two original INTEGER kernels agree, by actual point/curve image
factorization and actual original degree scaling, with no matching hypothesis. -/
theorem mem_curveNumericalKernel_iff_closed (a : X.Pic) :
    a ∈ NativeCurveNumericalClasses.curveNumericalKernel p ↔
      ∀ D : ClosedIntegralCurve X, D.picardDegree p a = 1 := by
  constructor
  · intro h D
    let : IsIntegral D.carrier := D.integral
    exact (NativeCurveNumericalClasses.mem_curveNumericalKernel p a).mp h
      (D.structureMorphism p) (D.projectiveFactorization p) D.dimension D.inclusion rfl
  · intro h
    apply (NativeCurveNumericalClasses.mem_curveNumericalKernel p a).mpr
    intro T hT q hq hdim i hi
    exact curveDegree_eq_one_of_closed p ⟨T, hT, q, hq, hdim, i, hi⟩ a h

/-- The genuine original quotient map has exactly the CLOSED-CURVE integer kernel,
by the internally proved geometric comparison, with no matching premise. -/
theorem additiveClassMap_ker :
    (additiveClassMap p).ker = integerKernel (closedIntegerFunctional p) := by
  ext a
  change NativeCurveNumericalClasses.classMap p a.toMul = 1 ↔
    (fun D : ClosedIntegralCurve X => D.additiveDegree p a) = 0
  rw [funext_iff]
  change (a.toMul : NativeCurveNumericalClasses.NumericalClass p) = 1 ↔
    ∀ D : ClosedIntegralCurve X, D.additiveDegree p a = 0
  rw [QuotientGroup.eq_one_iff, mem_curveNumericalKernel_iff_closed]
  constructor
  · intro h D
    change Multiplicative.toAdd (D.picardDegree p a.toMul) = 0
    have he := congrArg Multiplicative.toAdd (h D)
    simpa only [toAdd_one] using he
  · intro h D
    apply Multiplicative.ext
    rw [toAdd_one]
    exact h D

/-- The actual closed integer-kernel quotient IS the original all-curve-map
native numerical quotient; the equality of kernels was proved geometrically. -/
def integerCarrierComparison : ClosedIntegerQuotient p ≃ₗ[ℤ]
    Additive (NativeCurveNumericalClasses.NumericalClass p) :=
  (Submodule.quotEquivOfEq _ _ (additiveClassMap_ker p).symm) ≪≫ₗ
    (additiveClassMap p).quotKerEquivOfSurjective (additiveClassMap_surjective p)

/-- The integer carrier comparison preserves EVERY original native Picard class. -/
theorem integerCarrierComparison_mk (a : Additive X.Pic) :
    integerCarrierComparison p ((integerKernel (closedIntegerFunctional p)).mkQ a) =
      Additive.ofMul (NativeCurveNumericalClasses.classMap p a.toMul) := by
  change integerCarrierComparison p (Submodule.Quotient.mk a) = _
  simp only [integerCarrierComparison, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The two EXISTING original real numerical carriers are canonically equivalent.
The actual geometric integer kernel theorem and actual same-family tensor theorem
supply the bridge; neither is an incoming matching certificate. -/
def realCarrierComparison : NativeRealNumericalClasses.Space p ≃ₗ[ℝ]
    NativeCurveNumericalClasses.RealNumericalClass p :=
  closedQuotientComparison p ≪≫ₗ (integerCarrierComparison p).baseChange ℤ ℝ

/-- Every original tensor class is retained by the comparison of the two original carriers. -/
theorem realCarrierComparison_projection_tmul (r : ℝ) (a : Additive X.Pic) :
    realCarrierComparison p (NativeRealNumericalClasses.projection p (r ⊗ₜ[ℤ] a)) =
      r ⊗ₜ[ℤ] Additive.ofMul (NativeCurveNumericalClasses.classMap p a.toMul) := by
  simp only [realCarrierComparison, LinearEquiv.trans_apply,
    closedQuotientComparison_projection_tmul, LinearEquiv.baseChange_tmul,
    integerCarrierComparison_mk]

/-- The comparison sends the SAME original actual invertible line to its
SAME original all-map native real class. -/
theorem realCarrierComparison_lineClass (L : X.Modules) (hL : IsInvertible L) :
    realCarrierComparison p (NativeRealNumericalClasses.lineClass p L hL) =
      NativeCurveNumericalClasses.nativeRealClass p
        (NativeCurveNumericalClasses.classMap p (CurvePicardDegrees.lineClass L hL)) :=
  realCarrierComparison_projection_tmul p 1
    (Additive.ofMul (CurvePicardDegrees.lineClass L hL))

/-- EVERY actual original closed-curve real degree is retained by the
comparison of the two existing original real numerical carriers. -/
theorem curveDegree_realCarrierComparison (D : ClosedIntegralCurve X)
    (θ : NativeRealNumericalClasses.Space p) :
    letI : IsIntegral D.carrier := D.integral
    NativeCurveNumericalClasses.realCurveDegree p
      (D.structureMorphism p) (D.projectiveFactorization p) D.dimension D.inclusion rfl
      (realCarrierComparison p θ) = NativeRealNumericalClasses.curveDegree p D θ := by
  let : IsIntegral D.carrier := D.integral
  obtain ⟨z, rfl⟩ := NativeRealNumericalClasses.projection_surjective p θ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
      rw [realCarrierComparison_projection_tmul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Projective

end SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonImageDegrees
