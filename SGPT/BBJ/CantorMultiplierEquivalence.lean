import SGPT.BBJ.CantorZeroLelong
import SGPT.PSH.SourceIEnvelope
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
import SGPT.Foundations.Analysis.Pending.LocalPotentials

/-! Full positive-level multiplier ideals of the same literal Cantor average. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open scoped Topology ENNReal ContDiff Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

private theorem projectiveZero_native_psh :
    IsThetaPshPotential projectiveNativeFSBackground.form.val (fun _ : P1 => 0) :=
  (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff
    projectiveNativeFSBackground.form).mpr projectiveNativeFSBackground.isSemipositive

private theorem projectiveZero_native_lelong (p : P1) :
    NonKahlerLocus.lelongNumber (n := 1) (fun _ : P1 => 0) p = 0 := by
  apply le_antisymm _ zero_le
  by_contra h
  exact EReal.coe_ne_bot (0 : ℝ)
    (NonKahlerLocus.eq_bot_of_lelongNumber_pos (by norm_num)
      projectiveZero_native_psh.1 (lt_of_not_ge h))

/-- Actual Skoda unit membership at every positive real level, including every Cantor pole. -/
theorem one_mem_multiplierIdeal_cantorLogPotential {c : ℝ} (hc : 0 < c) (p : P1) :
    (multiplierIdeal (n := 1) c cantorLogPotential).mem p (fun _ => 1) := by
  apply SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt
    isThetaPshPotential_cantorLogPotential.1 hc
  rw [lelongNumber_cantorLogPotential]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- The actual full multiplier stalk consists of every holomorphic germ. -/
theorem mem_multiplierIdeal_cantorLogPotential_iff {c : ℝ} (hc : 0 < c)
    (p : P1) (g : P1 → ℂ) :
    (multiplierIdeal (n := 1) c cantorLogPotential).mem p g ↔ HolomorphicAt 1 g p := by
  refine ⟨fun h => h.1, fun hg => ?_⟩
  simpa only [mul_one] using
    MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul hg
      (one_mem_multiplierIdeal_cantorLogPotential hc p)

private theorem mem_multiplierIdeal_projectiveZero_iff {c : ℝ} (hc : 0 < c)
    (p : P1) (g : P1 → ℂ) :
    (multiplierIdeal (n := 1) c (fun _ : P1 => 0)).mem p g ↔ HolomorphicAt 1 g p := by
  refine ⟨fun h => h.1, fun hg => ?_⟩
  have hunit : (multiplierIdeal (n := 1) c (fun _ : P1 => 0)).mem p (fun _ => 1) := by
    apply SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt
      projectiveZero_native_psh.1 hc
    rw [projectiveZero_native_lelong]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  simpa only [mul_one] using
    MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul hg hunit

/-- Literal equality of the full actual germ ideals at every positive real exponent. -/
theorem multiplierIdeal_cantorLogPotential_eq_zero {c : ℝ} (hc : 0 < c) :
    multiplierIdeal (n := 1) c cantorLogPotential =
      multiplierIdeal (n := 1) c (fun _ : P1 => 0) := by
  apply GermIdeal.ext
  funext p g
  exact propext ((mem_multiplierIdeal_cantorLogPotential_iff hc p g).trans
    (mem_multiplierIdeal_projectiveZero_iff hc p g).symm)

/-- Genuine preferred-to-all-chart transport gives native multiplier equivalence. -/
theorem iEquivalentOnManifold_cantorLogPotential_zero :
    IEnvelope.IEquivalentOnManifold (n := 1) cantorLogPotential (fun _ : P1 => 0) := by
  constructor
  · intro c hc
    apply GenuineMultiplierIdealChartInclusion.multiplierIdealIncluded_of_multiplierIdeal_le
      isThetaPshPotential_cantorLogPotential.1 projectiveZero_native_psh.1 hc hc
    rw [multiplierIdeal_cantorLogPotential_eq_zero hc]
    exact fun _ _ h => h
  · intro c hc
    apply GenuineMultiplierIdealChartInclusion.multiplierIdealIncluded_of_multiplierIdeal_le
      projectiveZero_native_psh.1 isThetaPshPotential_cantorLogPotential.1 hc hc
    rw [multiplierIdeal_cantorLogPotential_eq_zero hc]
    exact fun _ _ h => h

/-- Actual FS Levi positivity and universal local tests manufacture original zero FS-PSH. -/
theorem isThetaPSH_projectiveZero :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (fun _ : P1 => 0) := by
  refine isThetaPSH_global_from_relative (fun _ => projectiveFSPotential)
    (fun _ => contDiff_projectiveFSPotential.contDiffOn) (fun _ _ _ => rfl)
    ?_ (fun _ => EReal.coe_ne_top (0 : ℝ)) ?_
  · intro i
    change PlurisubharmonicOn
      (fun z => (0 : EReal)+(projectiveFSPotential z : EReal)) (projectiveModelChart i).target
    simp only [zero_add]
    apply plurisubharmonicOn_of_levi_nonneg
      (contDiff_projectiveFSPotential.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (projectiveModelChart i).open_target
    intro z hz v
    have hnonneg := projectiveNativeFSBackground.isSemipositive (projectiveNativeChart i) z hz v
    change 0 ≤ smoothDDC projectiveFSPotential z ![v, Complex.I • v] at hnonneg
    rw [smoothDDC_complexDiagonal_eq_leviForm
      ((contDiff_projectiveFSPotential.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) v] at hnonneg
    have h := mul_nonneg hnonneg Real.pi_pos.le
    simpa only [div_mul_cancel₀ _ Real.pi_ne_zero] using h
  · intro x _ O _ hxO
    exact ⟨x, ⟨mem_univ x, hxO⟩, EReal.coe_ne_bot (0 : ℝ)⟩

/-- The same original Bool-chart germ tests and genuine QPSH domain give source I-equivalence. -/
theorem sourceIEquivalent_cantorLogPotential_zero :
    sourceIEquivalent projectiveLineAtlas cantorLogPotential (fun _ : P1 => 0) := by
  have hv : projectiveLineAtlas.IsQPSH cantorLogPotential :=
    ⟨projectiveFSForm, isThetaPSH_cantorLogPotential⟩
  have hzero : projectiveLineAtlas.IsQPSH (fun _ : P1 => 0) :=
    ⟨projectiveFSForm, isThetaPSH_projectiveZero⟩
  refine ⟨⟨hv, hzero, ?_⟩, ⟨hzero, hv, ?_⟩⟩
  · intro c hc i
    exact (iEquivalentOnManifold_cantorLogPotential_zero.1 c hc) (projectiveNativeChart i)
  · intro c hc i
    exact (iEquivalentOnManifold_cantorLogPotential_zero.2 c hc) (projectiveNativeChart i)

end SGPT.BBJ
