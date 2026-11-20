import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalCarrierComparisonImageDegrees
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalNefCone

/-! # Exact original nef inequalities under the two existing real numerical carriers

The target is closed-curve nef membership iff nonnegativity of every existing
original all-projective-curve-map real degree after realCarrierComparison.
No new replacement cone, finite-dimensionality, or Kleiman assertion is defined.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
open scoped TensorProduct
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonNef

open NativeNumericalCarrierComparisonCurves NativeClosedCurveDegrees
open NativeNumericalCarrierComparisonImage NativeNumericalCarrierComparisonImageDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]

section CurveMaps
variable (C : IntegralCurveMap p)
private local instance curve_integral : IsIntegral C.carrier := C.integral

/-- A point-image original curve map has zero original integer degree on
EVERY original Picard class, with its line representative produced internally. -/
theorem curveMapIntegerDegree_eq_zero_of_subsingleton_image
    [Subsingleton C.morphism.image] (a : X.Pic) :
    Multiplicative.toAdd (CurvePicardDegrees.curveDegreeHom C.structureMorphism
      C.projective C.dimension.le C.morphism a) = 0 := by
  let : IsProper C.structureMorphism := C.projective.isProper
  let : CompactSpace C.carrier :=
    QuasiCompact.compactSpace_of_compactSpace C.structureMorphism
  let : IsProper C.morphism := morphism_isProper p C
  let : IsIntegral C.morphism.image := image_isIntegral p C
  obtain ⟨L, hL, rfl⟩ := ProjectiveGeneratedLineClasses.exists_line_representative a
  rw [CurvePicardDegrees.curveDegreeHom_lineClass]
  obtain ⟨e⟩ := invertible_nonempty_iso_unit_of_subsingleton (hL.pullback C.morphism.imageι)
  let epull : (Scheme.Modules.pullback C.morphism).obj L ≅ unitObj C.carrier :=
    (Scheme.Modules.pullbackCongr (Scheme.Hom.toImage_imageι C.morphism)).symm.app L ≪≫
    (Scheme.Modules.pullbackComp C.morphism.toImage C.morphism.imageι).symm.app L ≪≫
    (Scheme.Modules.pullback C.morphism.toImage).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso C.morphism.toImage
  exact (CurveLineDegrees.degree_eq_of_iso C.structureMorphism epull).trans
    (CurveLineDegrees.degree_unit C.structureMorphism)

/-- The SAME actual finite image factor produces ONE natural-number degree
coefficient, uniformly for ALL original Picard classes. -/
theorem curveMapIntegerDegree_image_factor [Nontrivial C.morphism.image] :
    ∃ n : ℕ, ∀ a : X.Pic,
      Multiplicative.toAdd (CurvePicardDegrees.curveDegreeHom C.structureMorphism
        C.projective C.dimension.le C.morphism a) =
        (n : ℤ) * Multiplicative.toAdd ((closedImage p C).picardDegree p a) := by
  let : IsProper C.structureMorphism := C.projective.isProper
  let : CompactSpace C.carrier :=
    QuasiCompact.compactSpace_of_compactSpace C.structureMorphism
  let : IsProper C.morphism := morphism_isProper p C
  let : IsIntegral C.morphism.image := image_isIntegral p C
  let : IsFinite C.morphism.toImage := toImage_isFinite p C
  let : IsDominant C.morphism.toImage := inferInstance
  let := (DominantFunctionFieldMaps.functionFieldMap C.morphism.toImage).hom.toAlgebra
  let n := Module.finrank (C.morphism.image).functionField C.carrier.functionField
  refine ⟨n, ?_⟩
  intro a
  obtain ⟨L, hL, rfl⟩ := ProjectiveGeneratedLineClasses.exists_line_representative a
  let D := closedImage p C
  let qD := D.structureMorphism p
  let : IsProper qD := (D.projectiveFactorization p).isProper
  let : CompactSpace D.carrier := QuasiCompact.compactSpace_of_compactSpace qD
  rw [CurvePicardDegrees.curveDegreeHom_lineClass, D.picardDegree_lineClass p L hL]
  have hd := CurveFiniteDominantLineDegrees.degree_pullback C.morphism.toImage
    qD (D.projectiveFactorization p) D.dimension.le C.dimension.le
    ((Scheme.Modules.pullback D.inclusion).obj L) (hL.pullback D.inclusion)
  have hmap : C.morphism.toImage ≫ D.inclusion = C.morphism :=
    Scheme.Hom.toImage_imageι C.morphism
  let e := (Scheme.Modules.pullbackComp C.morphism.toImage D.inclusion).app L ≪≫
    (Scheme.Modules.pullbackCongr hmap).app L
  have hs : C.morphism.toImage ≫ qD = C.structureMorphism := image_structure_triangle p C
  have hchange := congrArg (fun q : C.carrier ⟶ Spec (.of k) =>
    CurveLineDegrees.degree q ((Scheme.Modules.pullback C.morphism.toImage).obj
      ((Scheme.Modules.pullback D.inclusion).obj L))) hs
  exact (hchange.trans (CurveLineDegrees.degree_eq_of_iso C.structureMorphism e)).symm.trans hd

/-- The original real degree of a point-image map vanishes on the WHOLE
original closed-curve numerical carrier after the actual carrier comparison. -/
theorem curveMapRealDegree_eq_zero_of_subsingleton_image
    [Subsingleton C.morphism.image] (θ : NativeRealNumericalClasses.Space p) :
    NativeCurveNumericalClasses.realCurveDegree p C.structureMorphism C.projective
      C.dimension C.morphism C.triangle (realCarrierComparison p θ) = 0 := by
  obtain ⟨z, rfl⟩ := NativeRealNumericalClasses.projection_surjective p θ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
      rw [realCarrierComparison_projection_tmul,
        NativeCurveNumericalClasses.realCurveDegree_tmul,
        NativeCurveNumericalClasses.curveDegree_classMap,
        curveMapIntegerDegree_eq_zero_of_subsingleton_image p C a.toMul]
      simp only [Int.cast_zero, mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- ONE nonnegative integer coefficient uniformly compares the existing
original real degrees on the ENTIRE actual original numerical carrier. -/
theorem exists_curveMapRealDegree_image_factor [Nontrivial C.morphism.image] :
    ∃ n : ℕ, ∀ θ : NativeRealNumericalClasses.Space p,
      NativeCurveNumericalClasses.realCurveDegree p C.structureMorphism C.projective
        C.dimension C.morphism C.triangle (realCarrierComparison p θ) =
        (n : ℝ) * NativeRealNumericalClasses.curveDegree p (closedImage p C) θ := by
  obtain ⟨n, hn⟩ := curveMapIntegerDegree_image_factor p C
  refine ⟨n, ?_⟩
  intro θ
  obtain ⟨z, rfl⟩ := NativeRealNumericalClasses.projection_surjective p θ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
      rw [realCarrierComparison_projection_tmul,
        NativeCurveNumericalClasses.realCurveDegree_tmul,
        NativeCurveNumericalClasses.curveDegree_classMap,
        NativeRealNumericalClasses.curveDegree_projection,
        ClosedIntegralCurve.realDegree_tmul]
      have hcast :
          ((Multiplicative.toAdd (CurvePicardDegrees.curveDegreeHom C.structureMorphism
            C.projective C.dimension.le C.morphism a.toMul) : ℤ) : ℝ) =
          (n : ℝ) * ((closedImage p C).additiveDegree p a : ℝ) := by
        change ((Multiplicative.toAdd (CurvePicardDegrees.curveDegreeHom C.structureMorphism
          C.projective C.dimension.le C.morphism a.toMul) : ℤ) : ℝ) =
          (n : ℝ) * ((Multiplicative.toAdd ((closedImage p C).picardDegree p a.toMul) : ℤ) : ℝ)
        exact_mod_cast hn a.toMul
      rw [hcast]
      exact mul_left_comm _ _ _
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

end CurveMaps

/-- The actual closed-curve nef cone equals nonnegativity of ALL original
projective integral curve-map real degrees after the proved original carrier
comparison. No replacement cone, Kleiman, or dimension assumption is introduced. -/
theorem mem_nefCone_iff_all_curveMaps (θ : NativeRealNumericalClasses.Space p) :
    θ ∈ NativeRealNumericalClasses.nefCone p ↔
      ∀ {T : Scheme.{u}} [IsIntegral T]
        (q : T ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
        (hdim : topologicalKrullDim T = 1) (i : T ⟶ X) (hi : i ≫ p = q),
        0 ≤ NativeCurveNumericalClasses.realCurveDegree p q hq hdim i hi
          (realCarrierComparison p θ) := by
  rw [NativeRealNumericalClasses.mem_nefCone]
  constructor
  · intro hclosed T hT q hq hdim i hi
    let C : IntegralCurveMap p := ⟨T, hT, q, hq, hdim, i, hi⟩
    change 0 ≤ NativeCurveNumericalClasses.realCurveDegree p C.structureMorphism C.projective
      C.dimension C.morphism C.triangle (realCarrierComparison p θ)
    by_cases hnon : Nontrivial C.morphism.image
    · let : Nontrivial C.morphism.image := hnon
      obtain ⟨n, hn⟩ := exists_curveMapRealDegree_image_factor p C
      rw [hn θ]
      exact mul_nonneg (Nat.cast_nonneg n) (hclosed (closedImage p C))
    · let : Subsingleton C.morphism.image := not_nontrivial_iff_subsingleton.mp hnon
      rw [curveMapRealDegree_eq_zero_of_subsingleton_image p C]
  · intro h D
    let : IsIntegral D.carrier := D.integral
    have hd := h (D.structureMorphism p) (D.projectiveFactorization p) D.dimension D.inclusion rfl
    rw [curveDegree_realCarrierComparison] at hd
    exact hd

end SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonNef
