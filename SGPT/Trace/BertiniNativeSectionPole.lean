import SGPT.Bergman.SourceNativeSectionLogPsh
import SGPT.Trace.OTExt2NormalPole

/-! Literal fixed-native-metric normalized section-square weights, without connectedness. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniNativeSectionPole
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (P : HermitianHolomorphicLineBundle.{0,0} n X) (s : HolomorphicSections (n := n) P.Fiber)

def poleScale : ℝ := Real.exp (-4) / (2 * (‖s‖ ^ 2 + 1))

def poleSection : HolomorphicSections (n := n) P.Fiber :=
  (((Real.sqrt (poleScale P s) : ℝ) : ℂ)) • s

def poleWeight (x : X) : ℝ := ‖poleSection P s x‖ ^ 2

theorem poleScale_pos : 0 < poleScale P s := by
  unfold poleScale
  positivity

theorem poleWeight_eq (x : X) : poleWeight P s x = poleScale P s * ‖s x‖ ^ 2 := by
  change ‖(((Real.sqrt (poleScale P s) : ℝ) : ℂ)) • s x‖ ^ 2 = _
  rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (poleScale_pos P s).le]

theorem poleWeight_nonneg (x : X) : 0 ≤ poleWeight P s x := sq_nonneg _

theorem poleWeight_lt_exp (x : X) : poleWeight P s x < Real.exp (-4) := by
  have hnorm : ‖s x‖ ≤ ‖s‖ := norm_apply_le_sectionSize _ s x
  have hsq : ‖s x‖ ^ 2 ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [poleWeight_eq]
  have hmul : poleScale P s * ‖s x‖ ^ 2 ≤ poleScale P s * ‖s‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (poleScale_pos P s).le
  refine hmul.trans_lt ?_
  unfold poleScale
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (show 0 < 2 * (‖s‖ ^ 2 + 1) by positivity)).mpr
  have hp : 0 < Real.exp (-4) := Real.exp_pos _
  nlinarith [sq_nonneg ‖s‖]

theorem poleWeight_zero_iff (x : X) : poleWeight P s x = 0 ↔ s x = 0 := by
  rw [poleWeight_eq,mul_eq_zero]
  simp only [(poleScale_pos P s).ne',false_or,pow_eq_zero_iff (by decide : 2 ≠ 0),norm_eq_zero]

theorem poleWeight_chartSmooth (hP : IsSourceSmoothHermitianMetric P) :
    ChartSmooth (n := n) (poleWeight P s) := by
  have hs : IsHolomorphicSectionOn P.Fiber (poleSection P s) univ :=
    (poleSection P s).mdifferentiable.mdifferentiableOn
  have h := (sourceNativeHermitianMetric P hP).smooth (poleSection P s) univ isOpen_univ hs
  intro c
  simpa only [poleWeight,sourceNativeHermitianMetric_normSq,Set.preimage_univ,Set.inter_univ] using h c

theorem poleWeight_log_thetaPlurisubharmonic (hP : IsSourceSmoothHermitianMetric P) :
    ThetaPlurisubharmonic (sourceNativeFirstChernForm P hP).val (SGPT.Trace.OTExt2.logPole (poleWeight P s)) := by
  exact sourceSectionLogNormSq_thetaPlurisubharmonic_of_isOwn P hP _
    (sourceNativeFirstChernForm_isOwn P hP) (poleSection P s)

end SGPT.Trace.BertiniNativeSectionPole
