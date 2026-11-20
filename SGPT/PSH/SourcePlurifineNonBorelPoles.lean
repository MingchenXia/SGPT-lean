import SGPT.PSH.SourcePlurifineNonBorelSeparation

/-! Actual cylinder mass forces a pole at every other Cantor code. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceNonBorelDraft
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.BBJ SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
local notation "Bits" => ℕ → Bool

lemma deficit_other_cylinder_lower {a d : Bits} {n : ℕ}
    (hn : 2*cantorCoefficient n ≤ |cantorCode a-cantorCode d|/2) :
    ENNReal.ofReal ((weight a d/8)*(16*(8 : ℝ)^n*Real.log 2)) ≤
      ∫⁻ b, ((Real.log 2 : EReal)-kernel a b (code d)).toENNReal ∂cantorBitProbability := by
  let T := cantorCylinder (Finset.range n) d
  let D : ℝ := weight a d/8
  let A : ℝ := D*((16 : ℝ)^(n+1)*Real.log 2)
  have hA : 0 ≤ A := by
    dsimp [A, D]
    exact mul_nonneg (div_nonneg (weight_bounds a d).1 (by norm_num))
      (mul_nonneg (pow_nonneg (by norm_num) _) (Real.log_nonneg (by norm_num)))
  have hpoint (b : Bits) : T.indicator (fun _ => ENNReal.ofReal A) b ≤
      ((Real.log 2 : EReal)-kernel a b (code d)).toENNReal := by
    by_cases hb : b ∈ T
    · rw [Set.indicator_of_mem hb]
      have hk := kernel_other_cylinder_upper hn hb
      have hsub := EReal.sub_le_sub (le_refl (Real.log 2 : EReal)) hk
      rw [← EReal.coe_sub] at hsub
      have hl : (A : EReal) ≤ (Real.log 2 : EReal)-kernel a b (code d) := by
        apply le_trans (b := ((Real.log 2- -(weight a d/8)*((16 : ℝ)^(n+1)*Real.log 2) : ℝ) : EReal)) ?_ hsub
        apply EReal.coe_le_coe_iff.mpr
        dsimp [A, D]
        have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith
      simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hl
    · rw [Set.indicator_of_notMem hb]
      exact zero_le
  have hI := lintegral_mono (μ := cantorBitProbability) hpoint
  rw [lintegral_indicator_const (measurableSet_cantorCylinder _ _),
    cantorBitProbability_cylinder, Finset.card_range] at hI
  have he : A*(1/2 : ℝ)^n = D*(16*(8 : ℝ)^n*Real.log 2) := by
    dsimp [A]
    rw [pow_succ]
    calc
      _ = D*(16*((16 : ℝ)^n*(1/2 : ℝ)^n)*Real.log 2) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  have hc : ENNReal.ofReal A*(1/2 : ℝ≥0∞)^n =
      ENNReal.ofReal (D*(16*(8 : ℝ)^n*Real.log 2)) := by
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) by
      symm
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<2)]
      norm_num,
      ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2), ← ENNReal.ofReal_mul hA, he]
  rw [hc] at hI
  exact hI

lemma separator_eq_bot_at_other_code {a d : Bits} (hne : a ≠ d) :
    separator a (code d) = ⊥ := by
  let I : ℝ≥0∞ := ∫⁻ b, ((Real.log 2 : EReal)-kernel a b (code d)).toENNReal
    ∂cantorBitProbability
  have htop : I = ⊤ := by
    by_contra hfin
    have hgap : 0 < |cantorCode a-cantorCode d|/2 := by
      exact div_pos (abs_pos.mpr (sub_ne_zero.mpr (fun h => hne (cantorCode_injective h))))
        (by norm_num)
    have ht : Tendsto (fun n => 2*cantorCoefficient n) atTop (𝓝 0) := by
      simpa only [mul_zero] using summable_cantorCoefficient.tendsto_atTop_zero.const_mul 2
    have hev : ∀ᶠ n : ℕ in atTop,
        2*cantorCoefficient n ≤ |cantorCode a-cantorCode d|/2 :=
      (ht.eventually (gt_mem_nhds hgap)).mono (fun _ hn => hn.le)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    let D : ℝ := weight a d/8
    have hD : 0 < D := div_pos (weight_pos hne) (by norm_num)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (I.toReal/(D*16*Real.log 2))
      (by norm_num : (1 : ℝ) < 8)
    let n := max N k
    have hkn : (8 : ℝ)^k ≤ (8 : ℝ)^n :=
      pow_le_pow_right₀ (by norm_num) (le_max_right N k)
    have hreal : I.toReal < D*(16*(8 : ℝ)^n*Real.log 2) := by
      have h := (div_lt_iff₀ (by positivity : 0 < D*16*Real.log 2)).mp hk
      calc
        _ < (8 : ℝ)^k*(D*16*Real.log 2) := h
        _ ≤ (8 : ℝ)^n*(D*16*Real.log 2) :=
          mul_le_mul_of_nonneg_right hkn (by positivity)
        _ = _ := by ring
    have hle := deficit_other_cylinder_lower (a := a) (d := d) (hN n (le_max_left N k))
    change ENNReal.ofReal (D*(16*(8 : ℝ)^n*Real.log 2)) ≤ I at hle
    rw [← ENNReal.ofReal_toReal hfin] at hle
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hle)) hreal
  change (Real.log 2 : EReal)-(I : EReal) = ⊥
  simp [htop, sub_eq_add_neg]

end SGPT.PSH.SourceNonBorelDraft
