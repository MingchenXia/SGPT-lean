import SGPT.BDivisor.BD7IntegralNumericalQuotient
import SGPT.Projective.NativeNefCurveDegree

/-! Independent degree inequalities on every integral curve descend to the
actual all-integral numerical quotient. Native nefness implies every one of them
through the normalization of that same singular curve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped BigOperators Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- The independently defined signed degree descends to the quotient by all such degrees. -/
def originalIntegralCurveDegreeOnQuotient_bd7
    (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) :
    OriginalIntegralCurveDegreeQuotient_bd7 f E →ₗ[ℝ] ℝ :=
  (originalIntegralCurveDegreeRelations_bd7 f E).liftQ
    (originalIntegralCurveDegreeLinear_bd7 f E C p)
    (fun v hv => (mem_originalIntegralCurveDegreeRelations_iff_bd7 f E v).mp hv C p)

@[simp] theorem originalIntegralCurveDegreeOnQuotient_mkQ_bd7
    (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) (v : CartierCombinations X) :
    originalIntegralCurveDegreeOnQuotient_bd7 f E C p
        ((originalIntegralCurveDegreeRelations_bd7 f E).mkQ v) =
      originalIntegralCurveDegreeLinear_bd7 f E C p v := rfl

/-- The sign of each actual integral curve degree defines the algebraic nef cone. -/
def originalIntegralDegreeNefCone_bd7 :
    ConvexCone ℝ (OriginalIntegralCurveDegreeQuotient_bd7 f E) where
  carrier := {α | ∀ (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)),
    0 ≤ originalIntegralCurveDegreeOnQuotient_bd7 f E C p α}
  smul_mem' _ hr _ h C p := by
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg hr.le (h C p)
  add_mem' _ hα _ hβ C p := by
    rw [map_add]
    exact add_nonneg (hα C p) (hβ C p)

theorem mem_originalIntegralDegreeNefCone_bd7 (α : OriginalIntegralCurveDegreeQuotient_bd7 f E) :
    α ∈ originalIntegralDegreeNefCone_bd7 f E ↔
      ∀ (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)),
        0 ≤ originalIntegralCurveDegreeOnQuotient_bd7 f E C p α := Iff.rfl

local instance integralNefTopology {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance integralNefCharts {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g d
local instance integralNefManifold {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

/-- For the same real combination of original lines, nefness of its Chern class
makes every independent original integral curve degree nonnegative. -/
theorem originalIntegralCurveDegreeLinear_nonneg_of_nativeNef_bd7
    (hprojective : NormalizationProjectiveForCurves)
    (omega : KahlerBackground n (SchemeComplexPoint f)) (v : CartierCombinations X)
    (hv : ClassNefWithRespectTo omega (cartierChern_bd7 f E n v))
    (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) :
    0 ≤ originalIntegralCurveDegreeLinear_bd7 f E C p v := by
  let A : Fin v.support.card → IntrinsicLineBundle X := fun i => (v.support.equivFin.symm i).val
  let L := fun i => (A i).sheaf
  let a := fun i => (A i).atlas
  let H := fun i => schemeLineBundleMetric f n E (a i)
  let r := fun i => v (A i)
  let β : ClosedRealOneOneForm n (SchemeComplexPoint f) := ∑ i, r i • (H i).curvature (a i)
  have hread : cartierChern_bd7 f E n v = RealBottChern.ofRepresentative β := by
    have hs := originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
      RealBottChern.ofRepresentative ((schemeLineBundleMetric f n E B.atlas).curvature B.atlas))
    change cartierChern_bd7 f E n v =
      ∑ i, r i • RealBottChern.ofRepresentative ((H i).curvature (a i)) at hs
    refine hs.trans ?_
    change _ = RealBottChern.ofRepresentativeLinearMap (∑ i, r i • (H i).curvature (a i))
    rw [map_sum]
    simp only [map_smul, RealBottChern.ofRepresentativeLinearMap]
    rfl
  have hβ : NefWithRespectTo omega β := by rwa [hread] at hv
  let ν := originalNormalizationMap C.source
  let fN := ν ≫ C.structureMap
  let EN := Classical.choice (hprojective C.structureMap C.embedding C.dimension)
  let := originalNormalizationCurve_smoothOfRelativeDimension C.structureMap C.embedding C.dimension
  let := EN.isSeparated
  let := EN.quasiCompact
  let : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
  let Apos := originalHyperplanePositiveLine fN 1 EN
  let κ : KahlerBackground 1 (SchemeComplexPoint fN) := ⟨Apos.curvature, Apos.positive⟩
  have hr : originalIntegralCurveDegreeLinear_bd7 f E C p v =
      ∑ i, r i * ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
        (matePullbackAtlas C.inclusion (a i)) p : ℤ) : ℝ) := by
    simpa only [originalIntegralCurveDegreeLinear_bd7, smul_eq_mul, A, a, r] using
      originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
        ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
          (matePullbackAtlas C.inclusion B.atlas) p : ℤ) : ℝ))
  rw [hr, originalWeightedIntegralCurveDegrees_eq_normalizedDegreeAlong_bd7
    f n E C.inclusion C.structureMap C.over_base C.embedding C.dimension EN L a H r p κ]
  exact degreeAlong_nonneg_of_nativeNef omega κ
    (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ C.inclusion)
      (by rw [Category.assoc, C.over_base]) 1 n ∞) β hβ

variable [ConnectedSpace (SchemeComplexPoint f)]

/-- The Chern linear map on the independent all-integral quotient. -/
def originalIntegralQuotientChern_bd7 (hprojective : NormalizationProjectiveForCurves) :
    OriginalIntegralCurveDegreeQuotient_bd7 f E →ₗ[ℝ] RealBottChern n (SchemeComplexPoint f) :=
  (originalIntegralCurveDegreeRelations_bd7 f E).liftQ (cartierChern_bd7 f E n) (by
    rw [originalIntegralCurveDegreeRelations_eq_chernKernel_bd7 f n E hprojective])

@[simp] theorem originalIntegralQuotientChern_mkQ_bd7
    (hprojective : NormalizationProjectiveForCurves) (v : CartierCombinations X) :
    originalIntegralQuotientChern_bd7 f E n hprojective
        ((originalIntegralCurveDegreeRelations_bd7 f E).mkQ v) = cartierChern_bd7 f E n v := rfl

theorem originalIntegralDegreeNefCone_of_nativeClassNef_bd7
    (hprojective : NormalizationProjectiveForCurves)
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (α : OriginalIntegralCurveDegreeQuotient_bd7 f E)
    (hα : ClassNefWithRespectTo omega (originalIntegralQuotientChern_bd7 f E n hprojective α)) :
    α ∈ originalIntegralDegreeNefCone_bd7 f E := by
  obtain ⟨v, rfl⟩ := (originalIntegralCurveDegreeRelations_bd7 f E).mkQ_surjective α
  apply (mem_originalIntegralDegreeNefCone_bd7 f E _).mpr
  intro C p
  rw [originalIntegralCurveDegreeOnQuotient_mkQ_bd7]
  exact originalIntegralCurveDegreeLinear_nonneg_of_nativeNef_bd7 f E n hprojective omega v hα C p

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
