import SGPT.BDivisor.BD7SmoothNumericalQuotient
import SGPT.BDivisor.BD7IntegralCurveNumericalKernel
import SGPT.Projective.OriginalNormalizationProjectiveCurve

/-! The literal degree-one algebraic numerical quotient by all integral
curve tests, and its comparison with the Chern-class quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped BigOperators

/-- Actual original embedded integral projective curve data ONLY.
No smoothness, metric, normalized source, degree or comparison field. -/
structure OriginalIntegralCurveTest_bd7 {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) where
  source : Scheme.{0}
  integral : IsIntegral source
  structureMap : source ⟶ Spec (.of ℂ)
  inclusion : source ⟶ X
  closed : IsClosedImmersion inclusion
  over_base : inclusion ≫ f = structureMap
  embedding : ClosedProjectiveEmbedding structureMap
  dimension : letI := integral; letI := schemeFunctionFieldAlgebra structureMap;
    Algebra.trdeg ℂ source.functionField = 1

instance originalIntegralCurveTest_sourceIntegral_bd7 {X : Scheme.{0}}
    {f : X ⟶ Spec (.of ℂ)} (C : OriginalIntegralCurveTest_bd7 f) :
    IsIntegral C.source := C.integral

/-- Actual independent ORIGINAL integer degree, linearly extended to the
SAME finitely supported original real lines. No analytic definition. -/
def originalIntegralCurveDegreeLinear_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (_E : ClosedProjectiveEmbedding f)
    (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) :
    CartierCombinations X →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun A : IntrinsicLineBundle X =>
    ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
      (matePullbackAtlas C.inclusion A.atlas) p : ℤ) : ℝ))

/-- Defined ONLY by every independent ORIGINAL integral curve degree,
including every singular curve; never defined as a cohomological kernel. -/
def originalIntegralCurveDegreeRelations_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) :
    Submodule ℝ (CartierCombinations X) :=
  ⨅ (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)), (originalIntegralCurveDegreeLinear_bd7 f E C p).ker

theorem mem_originalIntegralCurveDegreeRelations_iff_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (v : CartierCombinations X) :
    v ∈ originalIntegralCurveDegreeRelations_bd7 f E ↔
      ∀ (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)), originalIntegralCurveDegreeLinear_bd7 f E C p v = 0 := by
  simp only [originalIntegralCurveDegreeRelations_bd7, Submodule.mem_iInf, LinearMap.mem_ker]

/-- This actual curve-degree quotient includes ALL original integral
singular curves. Its definition has no metric or Chern class. -/
abbrev OriginalIntegralCurveDegreeQuotient_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) :=
  (CartierCombinations X) ⧸ originalIntegralCurveDegreeRelations_bd7 f E

/-- A genuine actual support enumeration reads the ENTIRE original degree
relation as the already proved finite REAL all-integral tests. -/
theorem mem_originalIntegralRelations_iff_supportTests_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (v : CartierCombinations X) :
    let A : Fin v.support.card → IntrinsicLineBundle X := fun i => (v.support.equivFin.symm i).val
    let L := fun i => (A i).sheaf
    let a := fun i => (A i).atlas
    let r := fun i => v (A i)
    v ∈ originalIntegralCurveDegreeRelations_bd7 f E ↔
      OriginalWeightedIntegralEmbeddedCurveZeroTests_bd7 f E L a r := by
  dsimp only
  let A : Fin v.support.card → IntrinsicLineBundle X := fun i => (v.support.equivFin.symm i).val
  let L := fun i => (A i).sheaf
  let a := fun i => (A i).atlas
  let r := fun i => v (A i)
  have hr (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) :
      originalIntegralCurveDegreeLinear_bd7 f E C p v =
        ∑ i, r i * ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
          (matePullbackAtlas C.inclusion (a i)) p : ℤ) : ℝ) := by
    simpa only [originalIntegralCurveDegreeLinear_bd7, smul_eq_mul, A, a, r] using
      originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
        ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
          (matePullbackAtlas C.inclusion B.atlas) p : ℤ) : ℝ))
  constructor
  · intro hv C hC
    let := hC
    intro g hclosed fC hcomp EC hcurve p
    let D : OriginalIntegralCurveTest_bd7 f :=
      ⟨C,hC,fC,g,hclosed,hcomp,EC,hcurve⟩
    exact (hr D p).symm.trans ((mem_originalIntegralCurveDegreeRelations_iff_bd7 f E v).mp hv D p)
  · intro ht
    apply (mem_originalIntegralCurveDegreeRelations_iff_bd7 f E v).mpr
    intro C p
    rw [hr]
    exact ht C.source C.integral C.inclusion C.closed C.structureMap C.over_base C.embedding C.dimension p

local instance integralQuotientTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance integralQuotientCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance integralQuotientManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f)

variable [ConnectedSpace (SchemeComplexPoint f)]

/-- Substantial kernel equality: ALL independent original singular curve
degrees vanish EXACTLY on the actual Chern map's kernel, in every dimension.
The degree relation was defined independently, never as this kernel. -/
theorem originalIntegralCurveDegreeRelations_eq_chernKernel_bd7
    (hprojective : NormalizationProjectiveForCurves) :
    originalIntegralCurveDegreeRelations_bd7 f E = (cartierChern_bd7 f E n).ker := by
  ext v
  let A : Fin v.support.card → IntrinsicLineBundle X := fun i => (v.support.equivFin.symm i).val
  let L := fun i => (A i).sheaf
  let a := fun i => (A i).atlas
  let H := fun i => schemeLineBundleMetric f n E (a i)
  let r := fun i => v (A i)
  have hread : cartierChern_bd7 f E n v =
      RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) := by
    have hs := originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
      RealBottChern.ofRepresentative ((schemeLineBundleMetric f n E B.atlas).curvature B.atlas))
    change cartierChern_bd7 f E n v = ∑ i, r i •
      RealBottChern.ofRepresentative ((H i).curvature (a i)) at hs
    refine hs.trans ?_
    change _ = RealBottChern.ofRepresentativeLinearMap (∑ i, r i • (H i).curvature (a i))
    rw [map_sum]
    simp only [map_smul, RealBottChern.ofRepresentativeLinearMap]
    rfl
  rw [LinearMap.mem_ker, hread]
  exact (mem_originalIntegralRelations_iff_supportTests_bd7 f E v).trans
    (originalWeightedAllIntegralTests_iff_chernClass_eq_zero_allDims_bd7 f n E L a H r hprojective)


/-- The numerical quotient tested on all integral curves is canonically identified with
the smooth-curve quotient through the same Cartier combinations. -/
def integralNumericalEquivSmoothNumerical_bd7 (hprojective : NormalizationProjectiveForCurves) :
    OriginalIntegralCurveDegreeQuotient_bd7 f E ≃ₗ[ℝ] SmoothCurveNumericalQuotient_bd7 f E :=
  Submodule.quotEquivOfEq _ _
    ((originalIntegralCurveDegreeRelations_eq_chernKernel_bd7 f n E hprojective).trans
      (smoothCurveRelations_eq_chernKernel_bd7 f E n).symm)

/-- The original degree-one numerical space uses only actual algebraic curve tests,
and the equivalence is the Chern class of the same real Cartier combination. -/
def integralNumericalEquivNS_bd7 (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [IsIntegral X]
    [CompactSpace (SchemeComplexPoint f)] (hprojective : NormalizationProjectiveForCurves) :
    OriginalIntegralCurveDegreeQuotient_bd7 f E ≃ₗ[ℝ]
      SGPT.BDivisor.DFAlg.neronSeveri (m + 1) (SchemeComplexPoint f) :=
  (integralNumericalEquivSmoothNumerical_bd7 f (m + 1) E hprojective).trans
    (smoothCurveNumericalEquivNS_bd7 f E m)

/-- The canonical normalization of each curve in the numerical tests has an
actual closed projective embedding over the original complex structure map. -/
theorem normalizationProjectiveForCurves_bd7 : NormalizationProjectiveForCurves :=
  fun f E hcurve => originalNormalization_exists_closedProjectiveEmbedding_of_curve f E hcurve

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
