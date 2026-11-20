import SGPT.Bergman.SourceSmoothWeightedBergmanBound

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.MultiplierSectionSingularity

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.GeneralBMTransport SGPT.Bergman.BernsteinMarkov
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

/-- Genuine extended logarithm of a physical weighted point bound. Even
pointwise zeros have log=-infinity and satisfy this exact obstacle bound. -/
theorem normalizedLogNormSq_add_shift_le_of_weighted_bound
    {E : Type*} [NormedAddCommGroup E] (a : E) (v P : ℝ) (hP : 0 < P)
    (k : ℕ) (hk : 0 < k)
    (hb : ENNReal.ofReal (‖a‖ ^ 2 * Real.exp (-((k : ℝ) * v))) ≤ ENNReal.ofReal P) :
    (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq a +
      ((-((k : ℝ)⁻¹ * Real.log P) : ℝ) : EReal) ≤ (v : EReal) := by
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  by_cases ha : a = 0
  · simp only [ha, logNormSq, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      ENNReal.ofReal_zero, ENNReal.log_zero,
      EReal.coe_mul_bot_of_pos (inv_pos.mpr hkp), EReal.bot_add]
    exact bot_le
  have hn : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have hb' := (ENNReal.ofReal_le_ofReal_iff hP.le).mp hb
  have hlog := Real.log_le_log (mul_pos hn (Real.exp_pos _)) hb'
  rw [Real.log_mul hn.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [logNormSq, ENNReal.log_ofReal_of_pos hn, ← EReal.coe_mul,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  calc
    (k : ℝ)⁻¹ * Real.log (‖a‖ ^ 2) + -((k : ℝ)⁻¹ * Real.log P)
        = (k : ℝ)⁻¹ * (Real.log (‖a‖ ^ 2) - Real.log P) := by ring
    _ ≤ (k : ℝ)⁻¹ * ((k : ℝ) * v) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hkp.le)
    _ = v := by rw [← mul_assoc, inv_mul_cancel₀ hkp.ne', one_mul]

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

/-- Actual source896-903 obstacle constant from the SAME raw original
smooth positive volume and SAME actual full H0 unit ball. One C works
for every positive degree and every original section, zero included. -/
theorem exists_source_smooth_weighted_section_obstacle
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k,
      weightedL2Norm (twistedPower L T k).Fiber k
        (wholeWeightedSubset (n := n) v).erealWeight
        (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) s ≤ 1 →
      ∀ x : X, (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq (s x) +
        ((-((k : ℝ)⁻¹ * Real.log (C * (k : ℝ) ^ n)) : ℝ) : EReal) ≤ (v x : EReal) := by
  obtain ⟨C, hC, hb⟩ := exists_global_weighted_polynomial_section_bound L T hL hT v hv μ hμ
  refine ⟨C, hC, fun k hk s hs x => ?_⟩
  have hI := integral_realWeightedSectionDensity_le_one_of_admissible L T v μ k s hs
  have hpoint := (hb k hk s x).trans
    (by simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (C * (k : ℝ) ^ n))) hI)
  exact normalizedLogNormSq_add_shift_le_of_weighted_bound (s x) (v x) (C * (k : ℝ) ^ n)
    (mul_pos hC (pow_pos (Nat.cast_pos.mpr hk) n)) k hk hpoint

end SGPT.Bergman.MultiplierSectionSingularity
