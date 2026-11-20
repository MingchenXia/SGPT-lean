import SGPT.BDivisor.BD3AlgebraicCurveLineTests
import SGPT.Projective.ActualCurveDegreeLinearity
import SGPT.Projective.NativeCITowerPeriodBase
import SGPT.Projective.NumEqCurveComponents
import SGPT.Projective.OriginalPositiveTensorTwist

/-!
# Numerical kernel of real algebraic Cartier combinations

The algebraic degrees use the EP-free signed zero-cycle construction of BD3.
Smooth embedded complete-intersection curves detect the whole Chern kernel.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped BigOperators

theorem slotIntegral_update_finite_sum_actual_bd7
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (κ : KahlerBackground n M) (v : Fin n → ClosedRealOneOneForm n M) (j : Fin n)
    {N : ℕ} (r : Fin N → ℝ) (theta : Fin N → ClosedRealOneOneForm n M) :
    slotIntegral κ (Function.update v j (∑ i, r i • theta i)) =
      ∑ i, r i * slotIntegral κ (Function.update v j (theta i)) := by
  let F : ClosedRealOneOneForm n M →ₗ[ℝ] ℝ :=
    { toFun := fun eta => slotIntegral κ (Function.update v j eta)
      map_add' := slotIntegral_update_add κ v j
      map_smul' := fun c eta => slotIntegral_update_smul κ v j c eta }
  change F (∑ i, r i • theta i) = ∑ i, r i * F (theta i)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem slotIntegral_first_cons_finite_sum_actual_bd7
    {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (k + 1)) M]
    [IsComplexManifold (k + 1) M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (κ : KahlerBackground (k + 1) M) (beta : Fin k → ClosedRealOneOneForm (k + 1) M)
    {N : ℕ} (r : Fin N → ℝ) (theta : Fin N → ClosedRealOneOneForm (k + 1) M) :
    slotIntegral κ (Fin.cons (∑ i, r i • theta i) beta) =
      ∑ i, r i * slotIntegral κ (Fin.cons (theta i) beta) := by
  have hu (eta : ClosedRealOneOneForm (k + 1) M) :
      Function.update (Fin.cons κ.form beta : Fin (k + 1) → ClosedRealOneOneForm (k + 1) M) 0 eta = Fin.cons eta beta := by
    funext i
    refine Fin.cases (by simp) (fun j => by simp) i
  simpa only [hu] using slotIntegral_update_finite_sum_actual_bd7 κ (Fin.cons κ.form beta : Fin (k + 1) → ClosedRealOneOneForm (k + 1) M) 0 r theta

local instance finitePeriodTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance finitePeriodCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance finitePeriodManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

namespace WholeOriginalCITower

theorem terminal_weighted_originalLineDegrees_eq_power_product_bd7 (k : ℕ) {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (P : Fin k → OriginalPositiveLine f (k + 1) E)
    (T : WholeOriginalCITower k f E P) {N : ℕ} (L : Fin N → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i)) (H : ∀ i, SchemeLineBundleMetric f (k + 1) E (L i))
    (r : Fin N → ℝ) (p : Spec (.of ℂ)) (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    (∑ i, r i * ((originalCurveLineDegree_bd3 (terminal k f T).structureMap ((terminal k f T).embedding E)
      (matePullbackAtlas (terminal k f T).inclusion (a i)) p : ℤ) : ℝ)) =
      (∏ i, (powers k T i : ℝ)) *
        slotIntegral κ (Fin.cons (∑ i, r i • (H i).curvature (a i)) (fun i => (P i).curvature)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  calc
    _ = ∑ i, r i * ((∏ j, (powers k T j : ℝ)) *
        slotIntegral κ (Fin.cons ((H i).curvature (a i)) (fun j => (P j).curvature))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [terminal_originalLineDegree_eq_power_product_bd3 k f E P T (a i) (H i) p κ]
    _ = (∏ j, (powers k T j : ℝ)) *
        ∑ i, r i * slotIntegral κ (Fin.cons ((H i).curvature (a i)) (fun j => (P j).curvature)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [slotIntegral_first_cons_finite_sum_actual_bd7]

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped BigOperators Manifold ContDiff

local instance weightedCurveTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance weightedCurveCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance weightedCurveManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f) (g : Y ⟶ X)
  (fY : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 fY] [IsSeparated fY] [QuasiCompact fY]
  (hcomp : g ≫ f = fY) (EY : ClosedProjectiveEmbedding fY)
  {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
  (H : ∀ i, SchemeLineBundleMetric f n E (L i)) (r : Fin N → ℝ)

omit [IsSeparated f] [QuasiCompact f] in
theorem originalWeightedCurveLineDegrees_eq_degreeAlong_bd7
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint fY)) :
    let : CompactSpace (SchemeComplexPoint fY) := EY.analyticCompact
    (∑ i, r i * ((originalCurveLineDegree_bd3 fY EY (matePullbackAtlas g (a i)) p : ℤ) : ℝ)) =
      degreeAlong κ (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fY f g hcomp 1 n ∞)
        (∑ i, r i • (H i).curvature (a i)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint fY) := EY.analyticCompact
  calc
    _ = ∑ i, r i * degreeAlong κ
        (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fY f g hcomp 1 n ∞)
        ((H i).curvature (a i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [originalAlgebraicCurveLineDegree_eq_degreeAlong_bd3 f n E g fY hcomp EY (a i) (H i) p κ]
    _ = _ := (degreeAlong_finite_sum_actual κ
      (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fY f g hcomp 1 n ∞)
      r (fun i => (H i).curvature (a i))).symm

namespace OriginalCurveOver
variable {f n E}

theorem weightedLineDegrees_eq_degreeAlong_bd7 (C : OriginalCurveOver f)
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint C.structureMap)) :
    let : CompactSpace (SchemeComplexPoint C.structureMap) := C.native_compact E
    (∑ i, r i * ((originalCurveLineDegree_bd3 C.structureMap (C.embedding E)
      (matePullbackAtlas C.inclusion (a i)) p : ℤ) : ℝ)) =
      degreeAlong κ (C.nativeMap n).contMDiff (∑ i, r i • (H i).curvature (a i)) :=
  originalWeightedCurveLineDegrees_eq_degreeAlong_bd7 f n E C.inclusion C.structureMap C.over_base
    (C.embedding E) L a H r p κ

end OriginalCurveOver
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped BigOperators

local instance weightedNumericalTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance weightedNumericalCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance weightedNumericalManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-- PURE original weighted smooth embedded curve tests, from independent ORIGINAL integer line degrees. -/
def OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i)) (r : Fin N → ℝ) : Prop :=
  ∀ (C : OriginalCurveOver f) (p : Spec (.of ℂ)),
    ∑ i, r i * ((originalCurveLineDegree_bd3 C.structureMap (C.embedding E)
      (matePullbackAtlas C.inclusion (a i)) p : ℤ) : ℝ) = 0

theorem slotIntegral_weighted_originalPositive_tuple_eq_zero_of_curveTests_bd7
    (k : ℕ) {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {N : ℕ} (L : Fin N → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i)) (H : ∀ i, SchemeLineBundleMetric f (k + 1) E (L i))
    (r : Fin N → ℝ) (hnum : OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r)
    (P : Fin k → OriginalPositiveLine f (k + 1) E) (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    slotIntegral κ (Fin.cons (∑ i, r i • (H i).curvature (a i)) (fun i => (P i).curvature)) = 0 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  obtain ⟨T⟩ := exists_wholeOriginalCITower k f E P
  let p : Spec (.of ℂ) := genericPoint _
  have h := WholeOriginalCITower.terminal_weighted_originalLineDegrees_eq_power_product_bd7 k f E P T L a H r p κ
  rw [hnum (WholeOriginalCITower.terminal k f T) p] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (WholeOriginalCITower.powers_real_prod_pos k T).ne'

theorem originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_bd7
    {m : ℕ} {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (m + 2) f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f (m + 2) E (L i)) (r : Fin N → ℝ)
    (hnum : OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r) :
    RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let A := originalHyperplanePositiveLine f (m + 2) E
  let κ : KahlerBackground (m + 2) (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  let theta (i : Fin N) := (H i).curvature (a i)
  let alpha := ∑ i, r i • theta i
  have hfirst := slotIntegral_weighted_originalPositive_tuple_eq_zero_of_curveTests_bd7 (m + 1) f E L a H r hnum
    (fun _ => A) κ
  have h1 : slotIntegral κ (oneSlot κ alpha) = 0 := by
    rw [oneSlot_eq_cons]
    exact hfirst
  have heach (i : Fin N) : slotIntegral κ (Function.update (oneSlot κ alpha) 1 (theta i)) = 0 := by
    obtain ⟨M, _hM, hpos⟩ := exists_positive_originalTensorTwist f (m + 2) E (a i) (H i) A
    let Q : OriginalPositiveLine f (m + 2) E :=
      { sheaf := bundleTensor (L i) (bundleTensorPower A.sheaf M)
        atlas := pairwiseTensorAtlas (a i) (A.atlas.tensorPower M)
        metric := (H i).tensorProduct (A.metric.tensorPower A.atlas M) (a i) (A.atlas.tensorPower M)
        positive := hpos }
    have htwist := slotIntegral_weighted_originalPositive_tuple_eq_zero_of_curveTests_bd7 (m + 1) f E L a H r hnum
      (Fin.cons Q (fun _ : Fin m => A)) κ
    have hperiod : slotIntegral κ
        (Fin.cons alpha (Fin.cons (theta i + (M : ℝ) • κ.form) (fun _ : Fin m => κ.form))) = 0 := by
      have heq := slotIntegral_eq_of_bottChernRel κ
        (Fin.cons alpha (fun j => ((Fin.cons Q (fun _ : Fin m => A) :
          Fin (m + 1) → OriginalPositiveLine f (m + 2) E) j).curvature))
        (Fin.cons alpha (Fin.cons (theta i + (M : ℝ) • κ.form) (fun _ : Fin m => κ.form)))
        (fun j => by
          refine Fin.cases (ClosedRealOneOneForm.BottChernRel.refl alpha) (fun l => ?_) j
          refine Fin.cases ?_ (fun _ => ClosedRealOneOneForm.BottChernRel.refl κ.form) l
          exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
            (originalTensorTwist_curvature f (m + 2) E (a i) (H i) A M))
      exact heq.symm.trans htwist
    rw [← update_oneSlot_eq_cons κ alpha (theta i + (M : ℝ) • κ.form),
      slotIntegral_update_add κ (oneSlot κ alpha) 1,
      slotIntegral_update_smul κ (oneSlot κ alpha) 1] at hperiod
    have hrestore : Function.update (oneSlot κ alpha) 1 κ.form = oneSlot κ alpha := by
      apply Function.update_eq_self_iff.mpr
      simp [oneSlot]
    rw [hrestore, h1, smul_zero, add_zero] at hperiod
    exact hperiod
  have h2 : slotIntegral κ (twoSlot κ alpha) = 0 := by
    change slotIntegral κ (Function.update (oneSlot κ alpha) 1 (∑ i, r i • theta i)) = 0
    rw [slotIntegral_update_finite_sum_actual_bd7 κ (oneSlot κ alpha) 1 r theta]
    simp only [heach, mul_zero, Finset.sum_const_zero]
  exact ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero κ alpha h1 h2

theorem originalWeightedCurveZeroTests_of_chernClass_eq_zero_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {N : ℕ} (L : Fin N → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i)) (H : ∀ i, SchemeLineBundleMetric f n E (L i))
    (r : Fin N → ℝ)
    (hzero : RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0) :
    OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r := by
  let A := originalHyperplanePositiveLine f n E
  let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  have hn := isNumericallyTrivial_of_ofRepresentative_eq_zero hzero
  intro C p
  let : CompactSpace (SchemeComplexPoint C.structureMap) := C.native_compact E
  let κC := C.nativeBackground n κ
  have hcurve := C.weightedLineDegrees_eq_degreeAlong_bd7 L a H r p κC
  have hz := degreeAlong_eq_zero_of_isNumericallyTrivial_compactCurve
    (∑ i, r i • (H i).curvature (a i)) hn κC (C.nativeMap n).contMDiff
  exact hcurve.trans hz

theorem originalWeightedSmoothEmbeddedCurveZeroTests_iff_chernClass_eq_zero_bd7
    {m : ℕ} {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (m + 2) f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f (m + 2) E (L i)) (r : Fin N → ℝ) :
    OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r ↔
      RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0 :=
  ⟨originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_bd7 f E L a H r,
    originalWeightedCurveZeroTests_of_chernClass_eq_zero_bd7 f (m + 2) E L a H r⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass
open scoped BigOperators

local instance finiteDimensionTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance finiteDimensionCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance finiteDimensionManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

theorem originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_dim_one_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f 1 E (L i)) (r : Fin N → ℝ)
    (hnum : OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r) :
    RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let A := originalHyperplanePositiveLine f 1 E
  let κ : KahlerBackground 1 (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  let P : Fin 0 → OriginalPositiveLine f 1 E := Fin.elim0
  have hz := slotIntegral_weighted_originalPositive_tuple_eq_zero_of_curveTests_bd7 0 f E L a H r hnum P κ
  have htuple : (Fin.cons (∑ i, r i • (H i).curvature (a i)) (fun i : Fin 0 => (P i).curvature) :
      Fin 1 → ClosedRealOneOneForm 1 (SchemeComplexPoint f)) = fun _ => ∑ i, r i • (H i).curvature (a i) := by
    funext i
    fin_cases i
    rfl
  rw [htuple] at hz
  exact ofRepresentative_eq_zero_of_slotIntegral_eq_zero_dim_one κ (∑ i, r i • (H i).curvature (a i)) hz

theorem originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_allDims_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f n E (L i)) (r : Fin N → ℝ)
    (hnum : OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r) :
    RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0 := by
  cases n with
  | zero =>
    have hz : (∑ i, r i • (H i).curvature (a i)) = 0 := by
      apply ClosedRealOneOneForm.ext
      intro e z
      apply ContinuousAlternatingMap.ext
      intro v
      change ((∑ i, r i • (H i).curvature (a i)).val.coeff e z) v = 0
      exact ((∑ i, r i • (H i).curvature (a i)).val.coeff e z).map_coord_zero
        (0 : Fin 2) (Subsingleton.elim (v 0) 0)
    rw [hz, RealBottChern.ofRepresentative_zero]
  | succ n =>
    cases n with
    | zero => exact originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_dim_one_bd7 f E L a H r hnum
    | succ m => exact originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_bd7 f E L a H r hnum

theorem originalWeightedSmoothEmbeddedCurveZeroTests_iff_chernClass_eq_zero_allDims_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {N : ℕ} (L : Fin N → X.Modules) (a : ∀ i, LineBundleAtlas (L i))
    (H : ∀ i, SchemeLineBundleMetric f n E (L i)) (r : Fin N → ℝ) :
    OriginalWeightedSmoothEmbeddedCurveZeroTests_bd7 f E L a r ↔
      RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) = 0 :=
  ⟨originalFinite_chernClass_eq_zero_of_smoothEmbeddedCurveTests_allDims_bd7 f n E L a H r,
    originalWeightedCurveZeroTests_of_chernClass_eq_zero_bd7 f n E L a H r⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
