import SGPT.BDivisor.BD7SmoothNumericalKernel
import SGPT.BDivisor.BD7CurveComponentDegree
import SGPT.BDivisor.BD7IntegralCurveNormalizedDegree

/-! Real numerical equivalence tested against every integral algebraic curve. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff

local instance singularTestTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance singularTestCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance singularTestManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

section IntegralCurve
variable {X C : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) [IsIntegral C] (g : C ⟶ X)
    (fC : C ⟶ Spec (.of ℂ)) (hcomp : g ≫ f = fC)
    (EC : ClosedProjectiveEmbedding fC)
    (hcurve : letI := schemeFunctionFieldAlgebra fC; Algebra.trdeg ℂ C.functionField = 1)
    (EN : ClosedProjectiveEmbedding (originalNormalizationMap C ≫ fC))
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

omit [IsSeparated f] [QuasiCompact f] in
/-- The independent degree on an original integral singular
projective curve equals degreeAlong its SAME true normalization/composite
native map. No source smoothness, flatness, frame/period equality is supplied. -/
theorem originalIntegralCurveDegree_eq_normalizedActualMapDegreeAlong_bd7
    (p : Spec (.of ℂ)) :
    let ν := originalNormalizationMap C
    let fN := ν ≫ fC
    letI := originalNormalizationCurve_smoothOfRelativeDimension fC EC hcurve
    letI := EN.isSeparated
    letI := EN.quasiCompact
    ∀ (κ : KahlerBackground 1 (SchemeComplexPoint fN)),
    letI : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
    ((originalIntegralCurveLineDegree_bd7 fC EC hcurve (matePullbackAtlas g a) p : ℤ) : ℝ) =
      degreeAlong κ (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ g)
        (by rw [Category.assoc, hcomp]) 1 n ∞) (H.curvature a) := by
  dsimp only
  let ν := originalNormalizationMap C
  let fN := ν ≫ fC
  let := originalNormalizationCurve_smoothOfRelativeDimension fC EC hcurve
  let := EN.isSeparated
  let := EN.quasiCompact
  intro κ
  let : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
  have hd := originalIntegralCurveLineDegree_eq_normalizedCurveLineDegree_bd7 fC EC hcurve EN
    (matePullbackAtlas g a) p
  have he : originalCurveLineDegree_bd3 fN EN (matePullbackAtlas ν (matePullbackAtlas g a)) p =
      originalCurveLineDegree_bd3 fN EN (matePullbackAtlas (ν ≫ g) a) p := by
    rw [originalCurveLineDegree_eq_eulerDifference_bd3, originalCurveLineDegree_eq_eulerDifference_bd3]
    exact congrArg (fun d : ℤ => d - originalProjectiveLineCechEuler fN EN
      (SheafOfModules.unit (originalNormalizationScheme C).ringCatSheaf))
      (originalProjectiveLineCechEuler_eq_of_iso fN EN ((Scheme.Modules.pullbackComp ν g).app L))
  exact (congrArg (fun d : ℤ => (d : ℝ)) (hd.trans he)).trans
    (originalAlgebraicCurveLineDegree_eq_degreeAlong_bd3 f n E (ν ≫ g) fN
      (by rw [Category.assoc, hcomp]) EN a H p κ)

end IntegralCurve
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped BigOperators Manifold ContDiff

local instance singularFiniteTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance singularFiniteCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance singularFiniteManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-- Actual REAL linear tests of INDEPENDENT ORIGINAL integer degrees,
including EVERY original integral singular embedded curve. No metric. -/
def OriginalWeightedIntegralEmbeddedCurveZeroTests_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (_E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i)) (r : Fin N → ℝ) : Prop :=
  ∀ (C : Scheme.{0}) (hC : IsIntegral C), letI := hC;
    ∀ (g : C ⟶ X) (_hclosed : IsClosedImmersion g)
      (fC : C ⟶ Spec (.of ℂ)) (_hcomp : g ≫ f = fC)
      (EC : ClosedProjectiveEmbedding fC)
      (hcurve : letI := schemeFunctionFieldAlgebra fC; Algebra.trdeg ℂ C.functionField = 1)
      (p : Spec (.of ℂ)),
      ∑ i, r i * ((originalIntegralCurveLineDegree_bd7 fC EC hcurve (matePullbackAtlas g (a i)) p : ℤ) : ℝ) = 0

/-- SAME actual normalized native map reads EVERY original weighted degree
using real-linearity, never an invented line of irrational tensor power. -/
theorem originalWeightedIntegralCurveDegrees_eq_normalizedDegreeAlong_bd7
    {X C : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) [IsIntegral C] (g : C ⟶ X)
    (fC : C ⟶ Spec (.of ℂ)) (hcomp : g ≫ f = fC)
    (EC : ClosedProjectiveEmbedding fC)
    (hcurve : letI := schemeFunctionFieldAlgebra fC; Algebra.trdeg ℂ C.functionField = 1)
    (EN : ClosedProjectiveEmbedding (originalNormalizationMap C ≫ fC))
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f n E (L i)) (r : Fin N → ℝ) (p : Spec (.of ℂ)) :
    let ν := originalNormalizationMap C
    let fN := ν ≫ fC
    letI := originalNormalizationCurve_smoothOfRelativeDimension fC EC hcurve
    letI := EN.isSeparated
    letI := EN.quasiCompact
    ∀ (κ : KahlerBackground 1 (SchemeComplexPoint fN)),
    letI : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
    (∑ i, r i * ((originalIntegralCurveLineDegree_bd7 fC EC hcurve (matePullbackAtlas g (a i)) p : ℤ) : ℝ)) =
      degreeAlong κ (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ g)
        (by rw [Category.assoc, hcomp]) 1 n ∞) (∑ i, r i • (H i).curvature (a i)) := by
  dsimp only
  let ν := originalNormalizationMap C
  let fN := ν ≫ fC
  let := originalNormalizationCurve_smoothOfRelativeDimension fC EC hcurve
  let := EN.isSeparated
  let := EN.quasiCompact
  intro κ
  let : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
  calc
    _ = ∑ i, r i * degreeAlong κ
        (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ g)
          (by rw [Category.assoc, hcomp]) 1 n ∞) ((H i).curvature (a i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [originalIntegralCurveDegree_eq_normalizedActualMapDegreeAlong_bd7 f n E g fC hcomp EC
        hcurve EN (a i) (H i) p κ]
    _ = _ := (degreeAlong_finite_sum_actual κ
      (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ g)
        (by rw [Category.assoc, hcomp]) 1 n ∞) r (fun i => (H i).curvature (a i))).symm

/-- Weighted ALL integral singular curve tests manufacture weighted whole
smooth tests through ALL actual components, with exact original sheaf maps. -/
theorem originalWeightedSmoothTests_of_allIntegralTests_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {N : ℕ} (L : Fin N → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i)) (r : Fin N → ℝ)
    (hnum : OriginalWeightedIntegralEmbeddedCurveZeroTests_bd7 f E L a r) :
    OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r := by
  intro C p
  let EC := C.embedding E
  let := smoothProjective_componentIndex_finite C.structureMap EC
  let : Fintype ↥(_root_.irreducibleComponents C.source) := Fintype.ofFinite _
  let d (j : Fin N) (i : ↥(_root_.irreducibleComponents C.source)) : ℤ :=
    letI := smoothProjective_component_smoothDimension C.structureMap 1 EC i.val i.property
    letI := (smoothProjective_componentEmbedding C.structureMap 1 EC i.val i.property).isSeparated
    letI := (smoothProjective_componentEmbedding C.structureMap 1 EC i.val i.property).quasiCompact
    originalCurveLineDegree_bd3
      ((smoothProjectiveComponentOpen C.structureMap 1 EC i.val i.property).ι ≫ C.structureMap)
      (smoothProjective_componentEmbedding C.structureMap 1 EC i.val i.property)
      (matePullbackAtlas (smoothProjectiveComponentOpen C.structureMap 1 EC i.val i.property).ι
        (matePullbackAtlas C.inclusion (a j))) p
  have hsum (j : Fin N) : originalCurveLineDegree_bd3 C.structureMap EC
      (matePullbackAtlas C.inclusion (a j)) p = ∑ i, d j i :=
    SGPT.Okounkov.OriginalBook.CurveComponents.originalCurveLineDegree_eq_sum_components_bd7
      C.structureMap EC (matePullbackAtlas C.inclusion (a j)) p
  calc
    _ = ∑ j, ∑ i, r j * (d j i : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hsum j, Int.cast_sum, Finset.mul_sum]
    _ = ∑ i, ∑ j, r j * (d j i : ℝ) := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      let U := smoothProjectiveComponentOpen C.structureMap 1 EC i.val i.property
      let fU := U.ι ≫ C.structureMap
      let EU := smoothProjective_componentEmbedding C.structureMap 1 EC i.val i.property
      let := smoothProjective_component_isIntegral C.structureMap 1 EC i.val i.property
      let := smoothProjective_component_closedImmersion C.structureMap 1 EC i.val i.property
      let := smoothProjective_component_smoothDimension C.structureMap 1 EC i.val i.property
      let := EU.isSeparated
      let := EU.quasiCompact
      have hd : letI := schemeFunctionFieldAlgebra fU; Algebra.trdeg ℂ (U : Scheme).functionField = 1 :=
        nativeSmoothFunctionField_trdeg fU 1
      have ht := hnum U inferInstance (U.ι ≫ C.inclusion) inferInstance fU
        (by rw [Category.assoc, C.over_base]) EU hd p
      have he (j : Fin N) : d j i =
          originalIntegralCurveLineDegree_bd7 fU EU hd (matePullbackAtlas (U.ι ≫ C.inclusion) (a j)) p := by
        change originalCurveLineDegree_bd3 fU EU (matePullbackAtlas U.ι (matePullbackAtlas C.inclusion (a j))) p = _
        rw [originalCurveLineDegree_eq_eulerDifference_bd3, originalIntegralCurveLineDegree_eq_eulerDifference_bd7]
        exact congrArg (fun z : ℤ => z - originalProjectiveLineCechEuler fU EU
          (SheafOfModules.unit (U : Scheme).ringCatSheaf))
          (originalProjectiveLineCechEuler_eq_of_iso fU EU
            ((Scheme.Modules.pullbackComp U.ι C.inclusion).app (L j)))
      calc
        _ = ∑ j, r j * ((originalIntegralCurveLineDegree_bd7 fU EU hd
            (matePullbackAtlas (U.ι ≫ C.inclusion) (a j)) p : ℤ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [he j]
        _ = 0 := ht

/-- A geometric embedding of the canonical normalization of each projective integral curve. -/
def NormalizationProjectiveForCurves : Prop :=
  ∀ {C : Scheme.{0}} [IsIntegral C] (g : C ⟶ Spec (.of ℂ))
    (_ : ClosedProjectiveEmbedding g)
    (_ : letI := schemeFunctionFieldAlgebra g
      Algebra.trdeg ℂ C.functionField = 1),
    Nonempty (ClosedProjectiveEmbedding (originalNormalizationMap C ≫ g))

/-- Actual zero Chern REAL combination annihilates ALL independent original
singular integral curve tests, without individual class-zero assumptions. -/
theorem originalWeightedAllIntegralTests_of_chernClass_eq_zero_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {N : ℕ} (L : Fin N → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i)) (H : ∀ i, SchemeLineBundleMetric f n E (L i)) (r : Fin N → ℝ)
    (hprojective : NormalizationProjectiveForCurves)
    (hz : RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0) :
    OriginalWeightedIntegralEmbeddedCurveZeroTests_bd7 f E L a r := by
  intro C hC
  let := hC
  intro g _hclosed fC hcomp EC hcurve p
  let ν := originalNormalizationMap C
  let fN := ν ≫ fC
  let EN := Classical.choice (hprojective fC EC hcurve)
  let := originalNormalizationCurve_smoothOfRelativeDimension fC EC hcurve
  let := EN.isSeparated
  let := EN.quasiCompact
  let : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
  let A := originalHyperplanePositiveLine fN 1 EN
  let κ : KahlerBackground 1 (SchemeComplexPoint fN) := ⟨A.curvature,A.positive⟩
  have hd := originalWeightedIntegralCurveDegrees_eq_normalizedDegreeAlong_bd7 f n E g fC hcomp EC
    hcurve EN L a H r p κ
  exact hd.trans (degreeAlong_eq_zero_of_isNumericallyTrivial_compactCurve _
    (isNumericallyTrivial_of_ofRepresentative_eq_zero hz) κ
    (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ g)
      (by rw [Category.assoc, hcomp]) 1 n ∞))

/-- Exact finite REAL original numerical kernel, ALL singular integral
original curves and EVERY original dimension, including zero. -/
theorem originalWeightedAllIntegralTests_iff_chernClass_eq_zero_allDims_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f n E (L i)) (r : Fin N → ℝ)
    (hprojective : NormalizationProjectiveForCurves) :
    OriginalWeightedIntegralEmbeddedCurveZeroTests_bd7 f E L a r ↔
      RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0 :=
  ⟨fun h => originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_allDims_bd7 f n E L a H r
      (originalWeightedSmoothTests_of_allIntegralTests_bd7 f E L a r h),
    originalWeightedAllIntegralTests_of_chernClass_eq_zero_bd7 f n E L a H r hprojective⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
