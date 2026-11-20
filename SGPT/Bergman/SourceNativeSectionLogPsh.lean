import SGPT.Bergman.SourceNativeFirstChernForm
import SGPT.Foundations.Analysis.Pending.BergmanSupWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.PSH SGPT.PSH.LineBundleMetric
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The SAME physical section logarithm, with the genuine extended log0=-inf. -/
def sourceSectionLogNormSq (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : HolomorphicSections (n := n) L.Fiber) : X → EReal :=
  fun x => logNormSq (s x)

/-- Exact same-frame section logarithm, including coefficient zero. The
smooth real frame potential cancels in EReal without a log0 fallback. -/
theorem sourceSectionLogNormSq_add_framePotential
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (s : HolomorphicSections (n := n) L.Fiber)
    (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    sourceSectionLogNormSq L s x + (-Real.log (‖e.val.symm x 1‖ ^ 2) : ℝ) =
      logNormSq (sectionCoefficient L.Fiber e.val s x) := by
  let := e.property
  have hp : 0 < ‖e.val.symm x 1‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L e hx))
  dsimp only [sourceSectionLogNormSq, logNormSq]
  rw [norm_eq_coefficient_mul_frameNorm L.Fiber e.val s hx, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add]
  dsimp only [frameNorm]
  rw [ENNReal.log_ofReal_of_pos (x := ‖e.val.symm x 1‖ ^ 2) hp,
    add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- Same actual section coefficient is genuinely holomorphic in EVERY
original source chart, not only in a chosen preferred chart. -/
theorem sourceSectionCoefficient_chart_holomorphic
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (s : HolomorphicSections (n := n) L.Fiber)
    (c : ComplexChart n X) (e : AtlasFrame L) :
    DifferentiableOn ℂ (fun z => sectionCoefficient L.Fiber e.val s (c.val.symm z))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let := e.property
  intro z hz
  have hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (sectionCoefficient L.Fiber e.val s) (c.val.symm z) :=
    ((e.val.contMDiffAt_section_iff hz.2).mp (s.contMDiff (c.val.symm z))).mdifferentiableAt
      (by simp)
  exact (differentiableAt_comp_chart_symm c hz.1 hg).differentiableWithinAt

/-- The actual smooth Chern potential plus the actual log coefficient
internally produce theta-plurisubharmonicity of the physical section log.
IsOwn is only the natural original theta=c1(L,h) reader, not a PSH outcome. -/
theorem sourceSectionLogNormSq_thetaPlurisubharmonic_of_isOwn
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm n X) (hθ : SGPT.PSH.GlobalL2.IsOwnFirstChernForm L θ)
    (s : HolomorphicSections (n := n) L.Fiber) :
    ThetaPlurisubharmonic θ.val (sourceSectionLogNormSq L s) := by
  intro c z hz
  let p := c.val.symm z
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩
  let W := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
  let ρ : ComplexModel n → ℝ := fun w => -Real.log (‖e.val.symm (c.val.symm w) 1‖ ^ 2)
  have hW : IsOpen W := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hzW : z ∈ W := ⟨hz, mem_baseSet_trivializationAt ℂ L.Fiber p⟩
  have hρ : ContDiffOn ℝ ∞ ρ W :=
    ((hL c e).log (fun w hw =>
      (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L e hw.2))).ne')).neg
  refine ⟨W, ρ, hzW, ⟨hW, fun _ hw => hw.1, hρ, fun w hw => ?_⟩, ?_⟩
  · exact (hθ c e w hw.1 hw.2).symm
  · have hp := SGPT.Foundations.Analysis.Pending.BergmanSupWeight.plurisubharmonicOn_logNormSq_comp
      hW (sourceSectionCoefficient_chart_holomorphic L s c e)
    intro w hw
    apply (hp w hw).congr
    filter_upwards [hW.mem_nhds hw] with y hy
    exact (sourceSectionLogNormSq_add_framePotential L s e hy.2).symm

/-- A nonzero original global section's true analytic zero set has empty
interior. Hence the actual physical logarithm has no open set of poles,
including n=0, without a nondegeneracy certificate from the caller. -/
theorem sourceSectionLogNormSq_locallyNondegenerate [ConnectedSpace X]
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (s : HolomorphicSections (n := n) L.Fiber)
    (hs : s ≠ 0) : LocallyNondegenerate (sourceSectionLogNormSq L s) := by
  have hi := SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    (sectionZeroSet_isComplexAnalytic L.Fiber s) (sectionZeroSet_ne_univ L.Fiber s hs)
  intro x U hU hx
  by_contra hn
  push Not at hn
  have hsub : U ⊆ sectionZeroSet L.Fiber s := by
    intro y hy
    exact (logNormSq_eq_bot_iff (s y)).mp (hn y hy)
  have hxI : x ∈ interior (sectionZeroSet L.Fiber s) :=
    mem_interior.mpr ⟨U, hsub, hU, hx⟩
  rw [hi] at hxI
  exact hxI

/-- A genuine nonzero entire original section produces the full native
theta-PSH condition in the actual internally manufactured Chern background. -/
theorem sourceSectionLogNormSq_isThetaPsh [ConnectedSpace X]
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (s : HolomorphicSections (n := n) L.Fiber) (hs : s ≠ 0) :
    IsThetaPshPotential (sourceNativeFirstChernForm L hL).val (sourceSectionLogNormSq L s) :=
  ⟨sourceSectionLogNormSq_thetaPlurisubharmonic_of_isOwn L hL _
    (sourceNativeFirstChernForm_isOwn L hL) s,
    sourceSectionLogNormSq_locallyNondegenerate L s hs⟩

end SGPT.Bergman.NativeHermitianMetric
