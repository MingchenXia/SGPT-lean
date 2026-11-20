import SGPT.BBJ.CantorPrefixes
import SGPT.BBJ.MovingProjectiveSection
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory
open SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology NNReal ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
/-- The actual extremely fast coefficient has its literal finite logarithm. -/
theorem cantorCoefficient_log (n : ℕ) :
    Real.log (cantorCoefficient n) = -(16 : ℝ)^(n+1)*Real.log 2 := by
  rw [cantorCoefficient,Real.log_pow,Real.log_div (by norm_num) (by norm_num)]
  simp only [Real.log_one,zero_sub,Nat.cast_pow,Nat.cast_ofNat]
  ring

/-- The matching prefix term has the actual quantitative logarithmic decay,
including bottom when the original code equals its finite prefix. -/
theorem movingProjectiveSectionPotential_matching_prefix (b : ℕ → Bool) (n : ℕ) :
    movingProjectiveSectionPotential (cantorPrefixReal (fun i : Fin n => b i))
      (projectiveCantorCode b) ≤ ((-(16 : ℝ)^(n+1)*Real.log 2 : ℝ) : EReal) := by
  let c := cantorPrefixReal (fun i : Fin n => b i)
  have htail : |cantorCode b-c| < 2*cantorCoefficient n := cantorPrefixReal_restrict_abs_lt b n
  change movingProjectiveSectionPotential c
    (projectiveLineHomeomorph ((cantorCode b : ℂ) : OnePoint ℂ)) ≤ _
  rw [movingProjectiveSectionPotential_finite]
  by_cases he : cantorCode b=c
  · simp [he]
  · have hz : (cantorCode b : ℂ)-(c : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr he)
    have hn : ‖(cantorCode b : ℂ)-(c : ℂ)‖ < 2*cantorCoefficient n := by
      simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using htail
    have hlog := Real.log_le_log (sq_pos_of_pos (norm_pos_iff.mpr hz))
      (pow_le_pow_left₀ (norm_nonneg _) hn.le 2)
    simp only [Real.log_pow,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (cantorCoefficient_pos n).ne',cantorCoefficient_log] at hlog
    have hF : 0 ≤ Real.log (1+Complex.normSq (cantorCode b : ℂ)) :=
      Real.log_nonneg (by have := Complex.normSq_nonneg (cantorCode b : ℂ); linarith)
    have hC : 0 ≤ Real.log (1+c^2) := Real.log_nonneg (by nlinarith [sq_nonneg c])
    have hm : (2 : ℝ) ≤ (16 : ℝ)^(n+1) := by
      have h := (Nat.le_pow (Nat.succ_pos n) : 16 ≤ 16^(n+1))
      exact le_trans (by norm_num : (2 : ℝ) ≤ 16) (by exact_mod_cast h)
    have hnum := mul_nonneg (sub_nonneg.mpr hm) (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
    rw [logNormSq_of_ne_zero hz,Real.log_pow,← EReal.coe_sub,← EReal.coe_sub,EReal.coe_le_coe_iff]
    norm_num at hlog hF hC ⊢
    nlinarith

private theorem finite_off_cantor_prefix_lower (z : ℂ)
    (hz : projectiveLineHomeomorph (z : OnePoint ℂ) ∉ projectiveCantorSet) :
    ∃ L : ℝ, L ≤ 0 ∧ ∀ (n : ℕ) (s : Fin n → Bool),
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorPrefixReal s)
        (projectiveLineHomeomorph (z : OnePoint ℂ)) := by
  let C : Set ℂ := range (fun b : ℕ → Bool => (cantorCode b : ℂ))
  have hcompact : IsCompact C := isCompact_range
    (Complex.continuous_ofReal.comp continuous_cantorCode)
  have hnonempty : C.Nonempty := ⟨(cantorCode (fun _ => false) : ℂ),fun _ => false,rfl⟩
  have hzC : z ∉ C := by
    rintro ⟨b,rfl⟩
    exact hz ⟨b,rfl⟩
  let d := Metric.infDist z C
  have hd : 0 < d := (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hzC
  let B := Real.log (d^2)-Real.log (1+Complex.normSq z)-Real.log 2
  refine ⟨min 0 B,min_le_left _ _,fun n s => ?_⟩
  let c := cantorPrefixReal s
  have hcC : (c : ℂ) ∈ C := ⟨cantorPrefixBits s,rfl⟩
  have hgap : d ≤ dist z (c : ℂ) := Metric.infDist_le_dist_of_mem hcC
  rw [dist_eq_norm] at hgap
  have hzc : z-(c : ℂ) ≠ 0 := norm_pos_iff.mp (hd.trans_le hgap)
  have hlog := Real.log_le_log (sq_pos_of_pos hd)
    (pow_le_pow_left₀ hd.le hgap 2)
  have hc0 : 0 ≤ c := cantorPrefixReal_nonneg s
  have hc1 : c < 1/2 := cantorPrefixReal_lt_half s
  have hCLog : Real.log (1+c^2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by nlinarith)
  apply le_trans (EReal.coe_le_coe_iff.mpr (min_le_right 0 B))
  rw [movingProjectiveSectionPotential_finite,logNormSq_of_ne_zero hzc,
    ← EReal.coe_sub,← EReal.coe_sub,EReal.coe_le_coe_iff]
  dsimp only [B]
  linarith

/-- Every actual point outside the concrete projective Cantor set has one
internally produced finite nonpositive lower bound for EVERY prefix center. -/
theorem movingProjectiveSectionPotential_prefix_uniform_lower (p : P1)
    (hp : p ∉ projectiveCantorSet) :
    ∃ L : ℝ, L ≤ 0 ∧ ∀ (n : ℕ) (s : Fin n → Bool),
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorPrefixReal s) p := by
  obtain ⟨q,rfl⟩ := projectiveLineHomeomorph.surjective p
  induction q using OnePoint.rec with
  | infty =>
    refine ⟨-Real.log 2,?_,fun n s => ?_⟩
    · exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
    · exact movingProjectiveSectionPotential_infinity_lower (cantorPrefixReal s)
        (cantorPrefixReal_nonneg s) (cantorPrefixReal_lt_half s).le
  | coe z => exact finite_off_cantor_prefix_lower z hp

end SGPT.BBJ
