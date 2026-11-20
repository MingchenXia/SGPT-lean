import SGPT.Projective.OkounkovOriginalBigOfIVolume
import SGPT.Projective.OkounkovOriginalRightScalarAllDimensions
import SGPT.Okounkov.OkoNSAlgebraic

/-! Actual original rational positive perturbation metric, SAME physical Chern/current and true original bigness.
Blueprint: okounkov-original-perturb-geometry.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open scoped Topology
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance perturbGeometryTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbGeometryCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance perturbGeometryManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- LITERAL original physical power/tensor metric in EVERY actual original dimension. -/
def originalPerturbMetric {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas A) (K : SchemeLineBundleMetric f n E A) (q p : ℕ) :
    SchemeLineBundleMetric f n E (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) :=
  (H.tensorPower a q).tensorProduct (K.tensorPower b p) (a.tensorPower q) (b.tensorPower p)

/-- Genuine SAME physical Chern tensor-power reader, with all original chart domains. -/
theorem originalPerturbMetric_curvature {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas A) (K : SchemeLineBundleMetric f n E A) (q p : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ((originalPerturbMetric f n E a H b K q p).curvature (OkoNS.perturbAtlas a b q p)).val.GeometricallyEq
      ((q:ℝ)•H.curvature a+(p:ℝ)•K.curvature b).val := by
  let := E.isSeparated
  let := E.quasiCompact
  have h1 := (H.tensorPower a q).curvature_tensorProduct (K.tensorPower b p) (a.tensorPower q)
    (b.tensorPower p) (OkoNS.perturbAtlas a b q p)
  have h2 := H.curvature_tensorPower a q
  have h3 := K.curvature_tensorPower b p
  intro c z hz
  have e1 := h1 c hz
  have e2 := h2 c hz
  have e3 := h3 c hz
  refine e1.trans ?_
  rw [ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_add,e2,e3]

/-- ACTUAL original positive rational perturbations manufacture true Kähler currents and EXISTING ordinary h0-growth bigness. -/
theorem original_positivePerturbation_kahler_and_big [IsIntegral X] [Nonempty (SchemeComplexPoint f)]
    {L A : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas A) (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature b).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (q p : ℕ) (hq : 0<q) (hp : 0<p) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsKahlerCurrentPotential
      ((originalPerturbMetric f n E a H b K q p).curvature (OkoNS.perturbAtlas a b q p))
      (fun x => (q:EReal)*φ x) ∧
    SGPT.LineBundle.IsBig f (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) n := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨K.curvature b,hK⟩
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  let κp := kahlerSmul κ hpR
  let M := bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)
  let aM := OkoNS.perturbAtlas a b q p
  let HM := originalPerturbMetric f n E a H b K q p
  have hgeo := originalPerturbMetric_curvature f n E a H b K q p
  have hgeoSub : (HM.curvature aM-κp.form).val.GeometricallyEq ((q:ℝ)•H.curvature a).val := by
    intro c z hz
    rw [sub_eq_add_neg,ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_neg,hgeo c hz,ClosedRealOneOneForm.coeff_add]
    change (((q:ℝ)•H.curvature a).val.coeff c z+((p:ℝ)•K.curvature b).val.coeff c z)+ -
      ((p:ℝ)•K.curvature b).val.coeff c z=((q:ℝ)•H.curvature a).val.coeff c z
    exact add_neg_cancel_right _ _
  have hcurrent : IsKahlerCurrentPotential (HM.curvature aM) (fun x => (q:EReal)*φ x) := by
    refine ⟨κp,(hgeoSub.thetaPshPotential_iff _).mpr ?_⟩
    exact isThetaPshPotential_nonneg_smul hφ (by exact_mod_cast hq.le)
  have hpos := original_iVolume_pos_of_kahler_allDimensions f n E aM HM hcurrent
  exact ⟨hcurrent,original_isBig_of_positive_iVolume_allDimensions f n E aM HM
    (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hcurrent) hpos⟩
end SGPT.Okounkov.OriginalBook
