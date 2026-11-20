import SGPT.Projective.AlgebraicNativeCutCharts
import SGPT.Foundations.Schemes.NativeProjectiveCutGeometry
import SGPT.Projective.ActualDiffeomorphSlotIntegral
import SGPT.Projective.NativeCICutIntrinsicPeriod

/-! The SAME original algebraic zero scheme and SAME full native cut have
the actual original mixed period. Blueprint: original-algebraic-cut-period.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass MixedMassClassInvariance
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension (m + 2) f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 2) E L)

local instance cutPeriodPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance cutPeriodPointCharts : ChartedSpace (ComplexModel (m + 2)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 2)
local instance cutPeriodPointManifold : IsComplexManifold (m + 2) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 2)

variable (hK : (H.curvature a).val.IsKahler)
  (D : NativeRegularCut (schemeNativePositiveLine f (m + 2) E a H hK))
  (σ : bundlePowerGlobalSections L D.power)
  [SmoothOfRelativeDimension (m + 1) (sectionZeroι (a.tensorPower D.power) σ ≫ f)]
  (hread : ∀ (j : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens j →
    sectionCoefficient
      (positivePower (schemeHermitianLineBundle f (m + 2) E a H) (D.power - 1)).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f (m + 2) E a H (a.frame j)) (D.power - 1)).val
        D.cuttingSection p =
      schemeOpenRegularFunction f (m + 2) E (a.opens j) (algCoef (a.frame j) D.power σ) p)

local instance cutPeriodSourceTopology : TopologicalSpace
    (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := schemeAnalyticPointTopology _
local instance cutPeriodSourceCharts : ChartedSpace (ComplexModel (m + 1))
    (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := schemeAnalyticTNChartedSpace _ _
local instance cutPeriodSourceManifold : IsComplexManifold (m + 1)
    (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := schemeAnalyticTN_isComplexManifold _ _

include hread in
/-- Actual entire original algebraic zero-scheme mixed period, no period certificate input. -/
theorem originalAlgebraicCut_slotIntegral
    (κ : KahlerBackground (m + 2) (SchemeComplexPoint f))
    (κZ : KahlerBackground (m + 1)
      (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)))
    (beta : Fin (m + 1) → ClosedRealOneOneForm (m + 2) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : CompactSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
      (E.sectionZero (a.tensorPower D.power) σ).analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    let : MeasurableSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := borel _
    let : BorelSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := ⟨rfl⟩
    slotIntegral κZ (fun i => ClosedRealOneOneForm.pullback
      (schemeComplexPointMap_contMDiff f (sectionZeroι (a.tensorPower D.power) σ) (m + 1) (m + 2) ∞)
        (beta i)) = (D.power : ℝ) * slotIntegral κ (Fin.snoc beta (H.curvature a)) := by
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := borel _
  let : BorelSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := ⟨rfl⟩
  let : CompactSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
    (E.sectionZero (a.tensorPower D.power) σ).analyticCompact
  let : ChartedSpace (ComplexModel (m + 1)) D.carrier := D.carrierCharts
  let : IsComplexManifold (m + 1) D.carrier := D.carrierComplex
  let : MeasurableSpace D.carrier := borel _
  let : BorelSpace D.carrier := ⟨rfl⟩
  have hdim : m + 2 - 1 = m + 1 := by omega
  let : SmoothOfRelativeDimension (m + 2 - 1) (sectionZeroι (a.tensorPower D.power) σ ≫ f) := by
    simpa only [hdim] using inferInstanceAs
      (SmoothOfRelativeDimension (m + 1) (sectionZeroι (a.tensorPower D.power) σ ≫ f))
  let : ChartedSpace (ComplexModel (m + 2 - 1))
      (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := schemeAnalyticTNChartedSpace _ _
  let : IsComplexManifold (m + 2 - 1)
      (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) := schemeAnalyticTN_isComplexManifold _ _
  let e := regularCutNativeDiffeomorph f (m + 2) E a H hK D σ hread
  let κD := D.restrictKahler κ
  have hperiod := D.slotIntegral_restrict_eq_power κ beta κD
  have hintegral := slotIntegral_pullback_actualDiffeomorph e κD κZ
    (fun i => ClosedRealOneOneForm.pullback D.inclusion.contMDiff (beta i))
  refine (slotIntegral_eq_of_bottChernRel κZ _ _ (fun i => ?_)).trans (hintegral.trans hperiod)
  apply ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
  have hcomp : (D.inclusion : D.carrier → SchemeComplexPoint f) ∘ e =
      schemeComplexPointMap (sectionZeroι (a.tensorPower D.power) σ ≫ f) f
        (sectionZeroι (a.tensorPower D.power) σ) rfl := by funext q; rfl
  have hgeo := FormPullbackCompMixed.pullback_comp_geometricallyEq D.inclusion.contMDiff e.contMDiff (beta i).val
  exact hgeo

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
