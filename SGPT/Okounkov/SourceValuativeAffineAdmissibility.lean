import SGPT.Envelopes.SourcePositiveAffineEnvelopes

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.SourceValuativeClosure
open Set Filter
open scoped Topology ENNReal
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.Pending

/-- The actual printed REAL-root interval eventually contains each fixed
coefficient when genuine finite masses converge down to a positive mass.
This is a numeric helper; the source consumer supplies actual QEA masses. -/
theorem eventually_sourceAffineCoefficient_of_tendsto {n : ℕ}
    {p : ℝ≥0∞} {q : ℕ → ℝ≥0∞} (hp : 0 < p) (hpfin : p ≠ ⊤)
    (hpq : ∀ j, p ≤ q j) (hqfin : ∀ j, q j ≠ ⊤)
    (hlim : Tendsto q atTop (𝓝 p)) {a : ℝ} (ha : 1 < a) :
    ∀ᶠ j in atTop, SourceAffineCoefficient n p (q j) a := by
  have ht : Tendsto (fun j => (q j).toReal) atTop (𝓝 p.toReal) :=
    (ENNReal.tendsto_toReal_iff hqfin hpfin).mpr hlim
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hpfin
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hd : Tendsto (fun j => (q j).toReal - a ^ n * ((q j).toReal - p.toReal))
      atTop (𝓝 p.toReal) := by
    have hc : Tendsto (fun _ : ℕ => a ^ n) atTop (𝓝 (a ^ n)) := tendsto_const_nhds
    have hpconst : Tendsto (fun _ : ℕ => p.toReal) atTop (𝓝 p.toReal) := tendsto_const_nhds
    simpa only [sub_self, mul_zero, sub_zero] using
      ht.sub (hc.mul (ht.sub hpconst))
  filter_upwards [hd.eventually (eventually_gt_nhds hpR)] with j hj
  apply (sourceAffineCoefficient_iff hp (hpq j) (hqfin j)).mpr
  refine ⟨ha, ?_⟩
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (hqfin j) tsub_le_self)) (hqfin j)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ha0.le n),
    ENNReal.toReal_sub_of_le (hpq j) (hqfin j)]
  linarith

end SGPT.Okounkov.SourceValuativeClosure
