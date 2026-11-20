import SGPT.LineBundle.SchemeMetricIsoTransport
import SGPT.LineBundle.RiemannRochAmple
import SGPT.NAPotential.FSPosAlgebraic
import SGPT.Foundations.Analysis.Pending.PositiveClasses
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Actual original ample polarizations manufacture actual positive smooth
physical metrics by the genuine sheaf isomorphism and positive tensor roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.FSPos

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f]

local instance rootMetricTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance rootMetricCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance rootMetricManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The actual positive q-th root metric on the original L, defined on
EVERY original local frame and obeying the exact original transition law. -/
def rootMetric {L : X.Modules} {q : ℕ} (hq : 0 < q)
    (H : SchemeLineBundleMetric f n E (bundleTensorPower L q)) : SchemeLineBundleMetric f n E L where
  frameNormSq α p := H.frameNormSq (α.tensorPower q) p ^ ((q : ℝ)⁻¹)
  smooth α c := (H.smooth (α.tensorPower q) c).rpow_const_of_ne
    (fun z hz => (H.positive (α.tensorPower q) _ hz.2).ne')
  positive α p hp := Real.rpow_pos_of_pos (H.positive (α.tensorPower q) p hp) _
  transition α β p hp hq' := by
    rw [H.transition (α.tensorPower q) (β.tensorPower q) p hp hq',
      schemeFrameTransition_tensorPower f n E α β q p hp hq', map_pow,
      Real.mul_rpow (pow_nonneg (Complex.normSq_nonneg _) _) (H.positive (β.tensorPower q) p hq').le,
      Real.pow_rpow_inv_natCast (Complex.normSq_nonneg _) hq.ne']

/-- Taking the actual physical root divides the actual Chern coefficient
by q, read in every original frame and on every original chart target. -/
theorem rootMetric_curvature {L : X.Modules} {q : ℕ} (hq : 0 < q)
    (H : SchemeLineBundleMetric f n E (bundleTensorPower L q))
    (a : LineBundleAtlas L) (b : LineBundleAtlas (bundleTensorPower L q)) :
    let := E.isSeparated
    let := E.quasiCompact
    ((rootMetric f n E hq H).curvature a).val.GeometricallyEq
      (((q : ℝ)⁻¹) • H.curvature b).val := by
  let := E.isSeparated
  let := E.quasiCompact
  dsimp only
  intro c z hz
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (c.val.symm z))
  let α := a.frame i
  let U := c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' a.opens i)
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm
    ((a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f))
  have hzU : z ∈ U := ⟨hz, hi⟩
  have hlog : ContDiffOn ℝ ∞ (fun w => -Real.log (H.frameNormSq (α.tensorPower q) (c.val.symm w))) U :=
    ((H.smooth (α.tensorPower q) c).log (fun w hw =>
      (H.positive (α.tensorPower q) _ hw.2).ne')).neg
  have heq : (fun w => -Real.log ((rootMetric f n E hq H).frameNormSq α (c.val.symm w))) =ᶠ[𝓝 z]
      fun w => ((q : ℝ)⁻¹) • (-Real.log (H.frameNormSq (α.tensorPower q) (c.val.symm w))) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    change -Real.log (H.frameNormSq (α.tensorPower q) (c.val.symm w) ^ ((q : ℝ)⁻¹)) = _
    rw [Real.log_rpow (H.positive (α.tensorPower q) _ hw.2)]
    simp only [smul_eq_mul]
    ring
  rw [(rootMetric f n E hq H).curvature_coeff_frame a α c hz hi,
    ClosedRealOneOneForm.coeff_smul, H.curvature_coeff_frame b (α.tensorPower q) c hz hi,
    smoothDDC_congr heq, smoothDDC_smul hU hlog ((q : ℝ)⁻¹) hzU]

/-- The actual positive power metric gives an actual positive original
root metric; strict positivity is proved from its actual own curvature. -/
theorem rootMetric_isKahler {L : X.Modules} {q : ℕ} (hq : 0 < q)
    (H : SchemeLineBundleMetric f n E (bundleTensorPower L q))
    (a : LineBundleAtlas L) (b : LineBundleAtlas (bundleTensorPower L q))
    (hH : let := E.isSeparated; let := E.quasiCompact; (H.curvature b).val.IsKahler) :
    let := E.isSeparated
    let := E.quasiCompact
    ((rootMetric f n E hq H).curvature a).val.IsKahler := by
  let := E.isSeparated
  let := E.quasiCompact
  apply (rootMetric_curvature f n E hq H a b).isKahler_iff.mpr
  refine ⟨fun c z hz => ⟨(((q : ℝ)⁻¹) • H.curvature b).property.2 c z hz, fun v hv => ?_⟩,
    (((q : ℝ)⁻¹) • H.curvature b).property.1⟩
  simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (by exact_mod_cast hq)) ((hH.1 c z hz).2 v hv)

/-- The original algebraic ample polarization itself manufactures a
positive smooth physical metric on the original L. No positive metric,
Chern representative, or intersection conclusion is supplied by the caller. -/
theorem exists_positive_metric_of_amplePolarization {L : X.Modules}
    (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∃ H : SchemeLineBundleMetric f n E L,
      let := E.isSeparated
      let := E.quasiCompact
      (H.curvature a).val.IsKahler := by
  let := E.isSeparated
  let := E.quasiCompact
  let E' := P.toClosedProjectiveEmbedding
  let HFS := fubiniStudyMetric f E' n
  let Hq := transportMetric f n E' HFS P.iso
  have hFS : (HFS.curvature (hyperplaneAtlas E')).val.IsKahler := fubiniStudy_isKahler f E' n
  have hqK : (Hq.curvature (a.tensorPower P.power)).val.IsKahler :=
    (transportMetric_curvature f n E' HFS P.iso (a.tensorPower P.power) (hyperplaneAtlas E')).isKahler_iff.mpr hFS
  let Hroot := rootMetric f n E' P.power_pos Hq
  have hroot : (Hroot.curvature a).val.IsKahler :=
    rootMetric_isKahler f n E' P.power_pos Hq a (a.tensorPower P.power) hqK
  refine ⟨reembedMetric f n E' Hroot E, ?_⟩
  exact (reembedMetric_curvature f n E' Hroot E a a).isKahler_iff.mpr hroot

end SGPT.LineBundle.AmpleChern
