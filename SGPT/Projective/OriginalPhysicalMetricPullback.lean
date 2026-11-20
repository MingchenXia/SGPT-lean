import SGPT.Projective.OriginalAnalyticFramePullback
import SGPT.Projective.OriginalAtlasWeightedMetric
import SGPT.Okounkov.SchemeLineBundleMetricGeometry
import SGPT.Okounkov.SchemeAnalyticMorphism
import SGPT.Foundations.Analysis.Pending.MeteredDivisorRestriction

/-! SAME actual original pulled sheaf, original frames, physical metric
and original Chern pullback. Blueprint: original-physical-metric-pullback.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  (EX : ClosedProjectiveEmbedding (h ≫ f)) (EY : ClosedProjectiveEmbedding f)

local instance physicalSourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance physicalTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance physicalSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance physicalTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m

local instance physicalSourceManifold [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] :
    IsComplexManifold n (SchemeComplexPoint (h ≫ f)) := schemeAnalyticTN_isComplexManifold (h ≫ f) n
local instance physicalTargetManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold m (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f m

variable {L : Y.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f m EY L)

include EX in
private theorem originalPhysicalWeight_smooth (i : a.I)
    (e : ComplexChart n (SchemeComplexPoint (h ≫ f))) :
    ContDiffOn ℝ ∞ (fun z => H.frameNormSq (a.frame i)
      (schemeComplexPointMap (h ≫ f) f h rfl (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹'
        (schemeComplexPointImage (h ≫ f) ⁻¹' (h ⁻¹ᵁ a.opens i))) := by
  let := EX.isSeparated
  let := EX.quasiCompact
  let := EY.isSeparated
  let := EY.quasiCompact
  let := schemeAnalyticTN_isComplexManifold (h ≫ f) n
  let := schemeAnalyticTN_isComplexManifold f m
  exact MeteredDivisorRestriction.contDiffOn_comp_chart_symm
    (schemeComplexPointMap_contMDiff f h n m ∞)
    ((a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f))
    (H.smooth (a.frame i)) e

/-- Genuine metric on the SAME actual sheaf pullback, with actual inherited weights. -/
def originalPhysicalPullbackMetric :
    SchemeLineBundleMetric (h ≫ f) n EX ((Scheme.Modules.pullback h).obj L) :=
  atlasWeightedMetric (h ≫ f) n EX (matePullbackAtlas h a)
    (fun i p => H.frameNormSq (a.frame i) (schemeComplexPointMap (h ≫ f) f h rfl p))
    (originalPhysicalWeight_smooth f h n m EX EY a H)
    (fun i p hp => H.positive (a.frame i) (schemeComplexPointMap (h ≫ f) f h rfl p) hp)

/-- The inherited physical weight is EXACT in EVERY original atlas frame. -/
theorem originalPhysicalPullbackMetric_atlas (i : a.I) (p : SchemeComplexPoint (h ≫ f))
    (hp : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ a.opens i) :
    (originalPhysicalPullbackMetric f h n m EX EY a H).frameNormSq
      (matePullbackFrame h (a.frame i)) p =
        H.frameNormSq (a.frame i) (schemeComplexPointMap (h ≫ f) f h rfl p) := by
  apply atlasWeightedMetric_frame
  · intro i j q hi hj
    change H.frameNormSq (a.frame i) (schemeComplexPointMap (h ≫ f) f h rfl q) =
      Complex.normSq (schemeFrameTransition (h ≫ f) n EX
        (matePullbackFrame h (a.frame i)) (matePullbackFrame h (a.frame j)) q) *
          H.frameNormSq (a.frame j) (schemeComplexPointMap (h ≫ f) f h rfl q)
    rw [matePullbackFrame_analytic_transition f h n m EX EY (a.frame i) (a.frame j) q hi hj]
    exact H.transition (a.frame i) (a.frame j) (schemeComplexPointMap (h ≫ f) f h rfl q) hi hj
  · exact hp

/-- The SAME physical metric is inherited in ANY original local frame. -/
theorem originalPhysicalPullbackMetric_frame {U : Y.Opens} (α : LocalBundleFrame L U)
    (p : SchemeComplexPoint (h ≫ f))
    (hp : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ U) :
    (originalPhysicalPullbackMetric f h n m EX EY a H).frameNormSq (matePullbackFrame h α) p =
      H.frameNormSq α (schemeComplexPointMap (h ≫ f) f h rfl p) := by
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p))
  have hi' : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ a.opens i := hi
  rw [(originalPhysicalPullbackMetric f h n m EX EY a H).transition
    (matePullbackFrame h α) (matePullbackFrame h (a.frame i)) p hp hi',
      originalPhysicalPullbackMetric_atlas f h n m EX EY a H i p hi',
      matePullbackFrame_analytic_transition f h n m EX EY α (a.frame i) p hp hi']
  exact (H.transition α (a.frame i) (schemeComplexPointMap (h ≫ f) f h rfl p) hp hi).symm

/-- The SAME inherited original physical metric has the true original Chern pullback. -/
theorem originalPhysicalPullbackMetric_curvature :
    letI := EX.isSeparated
    letI := EX.quasiCompact
    letI := EY.isSeparated
    letI := EY.quasiCompact
    ((originalPhysicalPullbackMetric f h n m EX EY a H).curvature (matePullbackAtlas h a)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (schemeComplexPointMap_contMDiff f h n m ∞) (H.curvature a)).val := by
  let := EX.isSeparated
  let := EX.quasiCompact
  let := EY.isSeparated
  let := EY.quasiCompact
  let := schemeAnalyticTN_isComplexManifold (h ≫ f) n
  let := schemeAnalyticTN_isComplexManifold f m
  intro e u hu
  let F := schemeComplexPointMap (h ≫ f) f h rfl
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (F (e.val.symm u)))
  have hi' : schemeComplexPointImage (h ≫ f) (e.val.symm u) ∈ h ⁻¹ᵁ a.opens i := hi
  refine ((originalPhysicalPullbackMetric f h n m EX EY a H).curvature_coeff_frame
    (matePullbackAtlas h a) (matePullbackFrame h (a.frame i)) e hu hi').trans ?_
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' a.opens i) :=
    (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  have hlog : ∀ d : ComplexChart m (SchemeComplexPoint f),
      ContDiffOn ℝ ∞ (fun z => Real.log (H.frameNormSq (a.frame i) (d.val.symm z)))
        (d.val.target ∩ d.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' a.opens i)) :=
    fun d => (H.smooth (a.frame i) d).log (fun _ hz => (H.positive (a.frame i) _ hz.2).ne')
  have hlocal := MeteredDivisorRestriction.coeff_pullback_eq_neg_smoothDDC
    (schemeComplexPointMap_contMDiff f h n m ∞) (θ := H.curvature a)
    (h := fun q => Real.log (H.frameNormSq (a.frame i) q)) hO
    hlog (fun d z hz hU =>
      (H.curvature_coeff_frame a (a.frame i) d hz hU).trans
        (smoothDDC_neg (d.val.isOpen_inter_preimage_symm hO) (hlog d) ⟨hz, hU⟩))
    e hu hi
  have heq : (fun z => -Real.log
      ((originalPhysicalPullbackMetric f h n m EX EY a H).frameNormSq
        (matePullbackFrame h (a.frame i)) (e.val.symm z))) =ᶠ[𝓝 u]
      (fun z => -Real.log (H.frameNormSq (a.frame i) (F (e.val.symm z)))) := by
    filter_upwards [(e.val.isOpen_inter_preimage_symm
      ((h ⁻¹ᵁ a.opens i).isOpen.preimage (schemeComplexPointImage_continuous (h ≫ f)))).mem_nhds
        ⟨hu, hi'⟩] with z hz
    rw [originalPhysicalPullbackMetric_atlas f h n m EX EY a H i _ hz.2]
  exact (smoothDDC_congr heq).trans
    ((smoothDDC_neg
      (e.val.isOpen_inter_preimage_symm (hO.preimage
        (schemeComplexPointMap_contMDiff f h n m ∞).continuous))
      (MeteredDivisorRestriction.contDiffOn_comp_chart_symm
        (schemeComplexPointMap_contMDiff f h n m ∞)
        (h := fun q => Real.log (H.frameNormSq (a.frame i) q)) hO hlog e)
      ⟨hu, hi⟩).trans hlocal.symm)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
