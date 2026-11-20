import SGPT.Foundations.Analysis.Pending.HolomorphicNormalOrderDiscrepancy
import SGPT.Foundations.Analysis.Pending.PrincipalGeneratorLogNormNormalForm
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization

set_option autoImplicit false

/-! # Actual common prime multiplicity of the original finite family

The normal exponent and transverse residual are produced before every
logarithmic coefficient and bounded real remainder. This local coordinate
producer does not assume a greatest divisor or a generic Lelong value.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.ActualFiniteFamilyPrimeMultiplicity

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

/-- The whole original finite family supplies its own common coordinate
power and a genuine residual nonzero frequently on the hyperplane. -/
theorem exists_common_prime_multiplicity {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) z)
    (hne : ∃ i, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0) :
    ∃ (a : ℕ) (H : Fin N → ComplexModel (m + 1) → ℂ),
      (∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (H i) z) ∧
      (∀ i, f i =ᶠ[𝓝 0] fun z => z (Fin.last m) ^ a * H i z) ∧
      ∃ i, ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z (Fin.last m) = 0 ∧ H i z ≠ 0 := by
  classical
  let P : ℕ → Prop := fun a => ∃ (i : Fin N) (H : ComplexModel (m + 1) → ℂ),
    (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z) ∧
    (f i =ᶠ[𝓝 0] fun z => z (Fin.last m) ^ a * H z) ∧
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z (Fin.last m) = 0 ∧ H z ≠ 0
  have hex : ∃ a, P a := by
    obtain ⟨i, hi⟩ := hne
    obtain ⟨a, H, hH, hfact, hfreq⟩ :=
      HolomorphicNormalOrderDiscrepancy.exists_finite_normal_order_of_nonzero_germ
        (hf i) (Filter.not_eventually.mp hi)
    exact ⟨a, i, H, hH, hfact, hfreq⟩
  let a := Nat.find hex
  obtain ⟨i, Hi, hHi, hfi, hfreq⟩ := Nat.find_spec hex
  have hquot : ∀ j : Fin N, ∃ H : ComplexModel (m + 1) → ℂ,
      (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z) ∧
      (f j =ᶠ[𝓝 0] fun z => z (Fin.last m) ^ a * H z) ∧ (j = i → H = Hi) := by
    intro j
    by_cases hji : j = i
    · subst j
      exact ⟨Hi, hHi, hfi, fun _ => rfl⟩
    · by_cases hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f j z = 0
      · refine ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _, ?_, ?_⟩
        · filter_upwards [hzero] with z hz
          simp only [hz, mul_zero]
        · intro h
          exact False.elim (hji h)
      · obtain ⟨k, Q, hQ, hfact, hQfreq⟩ :=
          HolomorphicNormalOrderDiscrepancy.exists_finite_normal_order_of_nonzero_germ
            (hf j) (Filter.not_eventually.mp hzero)
        have hak : a ≤ k := Nat.find_min' hex ⟨j, Q, hQ, hfact, hQfreq⟩
        refine ⟨fun z => z (Fin.last m) ^ (k - a) * Q z, ?_, ?_, ?_⟩
        · filter_upwards [hQ] with z hz
          exact (((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiableAt).pow
            (k - a)).mul hz
        · filter_upwards [hfact] with z hz
          rw [hz, ← mul_assoc, ← pow_add, show a + (k - a) = k by omega]
        · intro h
          exact False.elim (hji h)
  choose H hH hfact hEq using hquot
  refine ⟨a, H, hH, hfact, i, ?_⟩
  rw [hEq i rfl]
  exact hfreq

private theorem lelongNumber_zero_on_hyperplane {n : ℕ} (j : Fin n)
    {x : ComplexModel n} (hx : x j = 0) :
    lelongNumber (n := n) (fun _ : ComplexModel n => (0 : EReal)) x = 0 := by
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add (b := 0)
  intro ε hε _
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hnormc : ContinuousAt (fun z : ComplexModel n => ‖z j‖) x :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.continuousAt.norm
  have hnorm : ∀ᶠ z in 𝓝 x, ‖z j‖ < 1 :=
    hnormc.eventually (gt_mem_nhds (by
      change ‖x j‖ < 1
      rw [hx, norm_zero]
      exact zero_lt_one))
  have hle : ∀ᶠ z in 𝓝[≠] x,
      ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖) ≤ 0 := by
    filter_upwards [hnorm.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog : ENNReal.log (ENNReal.ofReal ‖z j‖) ≤ 0 := by
      simpa only [ENNReal.log_one] using
        ENNReal.log_monotone (ENNReal.ofReal_le_one.mpr hz.le)
    calc
      _ ≤ ((ε : ℝ) : EReal) * 0 := by gcongr
      _ = 0 := mul_zero _
  have h := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := n) hle
  rw [ActualLelongPositiveScaling.lelongNumber_smul_eq hεr,
    LocalHolomorphicLelongReaderCovariance.lelongNumber_coordinate_log_eq_one_of_eq_zero j hx,
    mul_one, ENNReal.ofReal_coe_nnreal] at h
  simpa only [zero_add] using h

private theorem lelongNumber_scaled_coordinate_eq {n : ℕ} (j : Fin n)
    {x : ComplexModel n} (hx : x j = 0) {a : ℝ} (ha : 0 ≤ a) :
    lelongNumber (n := n)
      (fun z : ComplexModel n => (a : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) x =
      ENNReal.ofReal a := by
  by_cases hzero : a = 0
  · subst a
    simpa only [EReal.coe_zero, zero_mul, ENNReal.ofReal_zero] using
      lelongNumber_zero_on_hyperplane j hx
  · rw [ActualLelongPositiveScaling.lelongNumber_smul_eq (lt_of_le_of_ne ha (Ne.symm hzero)),
      LocalHolomorphicLelongReaderCovariance.lelongNumber_coordinate_log_eq_one_of_eq_zero j hx,
      mul_one]

private theorem generatorLog_coordinate_factor {m N a : ℕ}
    (H : Fin N → ComplexModel (m + 1) → ℂ) (z : ComplexModel (m + 1)) :
    generatorLog (fun i w => w (Fin.last m) ^ a * H i w) z =
      ((2 * (a : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z (Fin.last m)‖) +
        generatorLog H z := by
  have hsum : (∑ i : Fin N, ‖z (Fin.last m) ^ a * H i z‖ ^ 2) =
      ‖z (Fin.last m)‖ ^ (a * 2) * generatorNormSq H z := by
    simp only [norm_mul, mul_pow, norm_pow, ← pow_mul, generatorNormSq, Finset.mul_sum]
  rw [generatorLog_eq_log_sum, hsum, ENNReal.ofReal_mul (by positivity),
    ENNReal.log_mul_add, ENNReal.ofReal_pow (norm_nonneg _) (a * 2), ENNReal.log_pow,
    generatorLog_eq_log_sum]
  have hcoef : ((a * 2 : ℕ) : EReal) = ((2 * (a : ℝ) : ℝ) : EReal) := by
    rw [← EReal.coe_natCast]
    congr 1
    push_cast
    ring
  rw [hcoef]
  rfl

private theorem generatorLog_factor_germ {m N a : ℕ}
    (f H : Fin N → ComplexModel (m + 1) → ℂ) {p : ComplexModel (m + 1)}
    (hfact : ∀ i, f i =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H i z) :
    generatorLog f =ᶠ[𝓝 p] fun z =>
      ((2 * (a : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z (Fin.last m)‖) +
        generatorLog H z := by
  filter_upwards [eventually_all.mpr hfact] with z hz
  have hfamily : generatorLog f z =
      generatorLog (fun i w => w (Fin.last m) ^ a * H i w) z := by
    simp only [generatorLog_eq_log_sum]
    apply congrArg (fun t : ℝ => ENNReal.log (ENNReal.ofReal t))
    exact Finset.sum_congr rfl fun i _ => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hz i)
  rw [hfamily, generatorLog_coordinate_factor]

private theorem norm_sum_continuousAt {m N : ℕ}
    (H : Fin N → ComplexModel (m + 1) → ℂ) {p : ComplexModel (m + 1)}
    (hH : ∀ i, DifferentiableAt ℂ (H i) p) : ContinuousAt (generatorNormSq H) p := by
  have hcont : ∀ i, ContinuousAt (H i) p := fun i => (hH i).continuousAt
  change ContinuousAt (fun z => ∑ i, ‖H i z‖ ^ 2) p
  fun_prop

private theorem raw_reader_lower {m N a : ℕ}
    (f H : Fin N → ComplexModel (m + 1) → ℂ) {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) (hH : ∀ i, DifferentiableAt ℂ (H i) p)
    (hfact : ∀ i, f i =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H i z) :
    ENNReal.ofReal (2 * (a : ℝ)) ≤ lelongNumber (n := m + 1) (generatorLog f) p := by
  let B := generatorNormSq H p + 1
  have hB : 0 < B := by dsimp only [B]; linarith [generatorNormSq_nonneg H p]
  have hnorm : ∀ᶠ z in 𝓝 p, generatorNormSq H z ≤ B :=
    ((norm_sum_continuousAt H hH).eventually
      (gt_mem_nhds (by dsimp only [B]; exact lt_add_one _))).mono fun _ hz => hz.le
  have hupper : ∀ᶠ z in 𝓝[≠] p, generatorLog f z ≤
      ((2 * (a : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z (Fin.last m)‖) +
        (Real.log B : EReal) := by
    filter_upwards [(generatorLog_factor_germ f H hfact).filter_mono nhdsWithin_le_nhds,
      hnorm.filter_mono nhdsWithin_le_nhds] with z hz hbound
    rw [hz]
    have hlog : generatorLog H z ≤ (Real.log B : EReal) := by
      rw [generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal (generatorNormSq H z)) ≤ _
      exact (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hbound)).trans_eq
        (ENNReal.log_ofReal_of_pos hB)
    exact add_le_add le_rfl hlog
  have h := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := m + 1) hupper
  rw [LelongChartReaderInvariance.lelongNumber_add_continuous_eq continuousAt_const,
    lelongNumber_scaled_coordinate_eq (Fin.last m) hp (by positivity)] at h
  exact h

private theorem raw_reader_eq_of_positive_residual {m N a : ℕ}
    (f H : Fin N → ComplexModel (m + 1) → ℂ) {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) (hH : ∀ i, DifferentiableAt ℂ (H i) p)
    (hfact : ∀ i, f i =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H i z)
    (hpos : 0 < generatorNormSq H p) :
    lelongNumber (n := m + 1) (generatorLog f) p = ENNReal.ofReal (2 * (a : ℝ)) := by
  have hc := norm_sum_continuousAt H hH
  have hpositive : ∀ᶠ z in 𝓝 p, 0 < generatorNormSq H z :=
    hc.eventually (lt_mem_nhds hpos)
  have heq : generatorLog f =ᶠ[𝓝 p] fun z =>
      ((2 * (a : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z (Fin.last m)‖) +
        (Real.log (generatorNormSq H z) : EReal) := by
    filter_upwards [generatorLog_factor_germ f H hfact, hpositive] with z hz hzpos
    rw [hz, generatorLog_eq_log_sum]
    change _ + ENNReal.log (ENNReal.ofReal (generatorNormSq H z)) = _
    rw [ENNReal.log_ofReal_of_pos hzpos]
  rw [LelongNumberComparison.lelongNumber_congr heq,
    CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
      (boundedRealGermAt_of_continuousAt (hc.log hpos.ne')),
    lelongNumber_scaled_coordinate_eq (Fin.last m) hp (by positivity)]

/-- The common exponent is chosen before every coefficient and bounded
remainder; genuine open unit pieces and the entire local infimum follow. -/
theorem exists_generic_prime_reader {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) z)
    (hne : ∃ i, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0) :
    ∃ (a : ℕ) (H : Fin N → ComplexModel (m + 1) → ℂ),
      (∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (H i) z) ∧
      (∀ i, f i =ᶠ[𝓝 0] fun z => z (Fin.last m) ^ a * H i z) ∧
      (∃ i, ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z (Fin.last m) = 0 ∧ H i z ≠ 0) ∧
      ∀ (c : ℝ), 0 < c → ∀ (b : ComplexModel (m + 1) → ℝ), BoundedRealGermAt b 0 →
      let w := fun z => (c : EReal) * generatorLog f z + (b z : EReal)
      ∃ (R : ℝ) (O : Set (ComplexModel (m + 1))),
        0 < R ∧ IsOpen O ∧ O ⊆ ball 0 R ∧
        (O ∩ {x | x (Fin.last m) = 0}).Nonempty ∧
        (∀ x ∈ ball 0 R, x (Fin.last m) = 0 →
          ENNReal.ofReal (2 * c * (a : ℝ)) ≤ lelongNumber (n := m + 1) w x) ∧
        (∀ x ∈ O, x (Fin.last m) = 0 →
          lelongNumber (n := m + 1) w x = ENNReal.ofReal (2 * c * (a : ℝ))) ∧
        (∀ (r : ℝ), 0 < r → r ≤ R →
          (⨅ x ∈ ball 0 r ∩ {x | x (Fin.last m) = 0},
            lelongNumber (n := m + 1) w x) = ENNReal.ofReal (2 * c * (a : ℝ))) ∧
        (⨅ x ∈ ball 0 R ∩ {x | x (Fin.last m) = 0},
          lelongNumber (n := m + 1) w x).toReal / 2 = c * (a : ℝ) := by
  classical
  obtain ⟨a, H, hH, hfact, i, hfreq⟩ := exists_common_prime_multiplicity f hf hne
  refine ⟨a, H, hH, hfact, ⟨i, hfreq⟩, ?_⟩
  intro c hc b hb
  dsimp only
  obtain ⟨B, hB, hbound⟩ := hb
  obtain ⟨R, hR, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_all.mpr hH).and ((eventually_all.mpr hfact).and hbound))
  have hHat (p : ComplexModel (m + 1)) (hp : p ∈ ball 0 R) :
      ∀ j, DifferentiableAt ℂ (H j) p := (hsmall p hp).1
  have hfactAt (p : ComplexModel (m + 1)) (hp : p ∈ ball 0 R) :
      ∀ j, f j =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H j z := by
    intro j
    filter_upwards [isOpen_ball.mem_nhds hp] with z hz
    exact (hsmall z hz).2.1 j
  have hbAt (p : ComplexModel (m + 1)) (hp : p ∈ ball 0 R) :
      BoundedRealGermAt b p :=
    ⟨B, hB, (show ∀ᶠ z in 𝓝 p, z ∈ ball 0 R from isOpen_ball.mem_nhds hp).mono
      fun z hz => (hsmall z hz).2.2⟩
  have hcoef : ENNReal.ofReal c * ENNReal.ofReal (2 * (a : ℝ)) =
      ENNReal.ofReal (2 * c * (a : ℝ)) := by
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    ring
  have hlower (p : ComplexModel (m + 1)) (hp : p ∈ ball 0 R)
      (hplane : p (Fin.last m) = 0) :
      ENNReal.ofReal (2 * c * (a : ℝ)) ≤ lelongNumber (n := m + 1)
        (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) p := by
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq (hbAt p hp),
      ActualLelongPositiveScaling.lelongNumber_smul_eq hc, ← hcoef]
    gcongr
    exact raw_reader_lower f H hplane (hHat p hp) (hfactAt p hp)
  have hpositive (p : ComplexModel (m + 1)) (hp : H i p ≠ 0) :
      0 < generatorNormSq H p := by
    have hterm : 0 < ‖H i p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
    exact hterm.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg ‖H j p‖)
      (Finset.mem_univ i))
  have hexact (p : ComplexModel (m + 1)) (hp : p ∈ ball 0 R)
      (hplane : p (Fin.last m) = 0) (hpos : 0 < generatorNormSq H p) :
      lelongNumber (n := m + 1)
        (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) p =
          ENNReal.ofReal (2 * c * (a : ℝ)) := by
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq (hbAt p hp),
      ActualLelongPositiveScaling.lelongNumber_smul_eq hc,
      raw_reader_eq_of_positive_residual f H hplane (hHat p hp) (hfactAt p hp) hpos,
      hcoef]
  obtain ⟨y, ⟨hyplane, hyne⟩, hyball⟩ :=
    (hfreq.and_eventually (ball_mem_nhds (0 : ComplexModel (m + 1)) hR)).exists
  have hypos := hpositive y hyne
  obtain ⟨O, hOprops, hO, hyO⟩ := _root_.eventually_nhds_iff.mp
    (((norm_sum_continuousAt H (hHat y hyball)).eventually (lt_mem_nhds hypos)).and
      (isOpen_ball.mem_nhds hyball))
  have hOR : O ⊆ ball 0 R := fun x hx => (hOprops x hx).2
  have hOexact : ∀ x ∈ O, x (Fin.last m) = 0 → lelongNumber (n := m + 1)
      (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) x =
        ENNReal.ofReal (2 * c * (a : ℝ)) :=
    fun x hx hxplane => hexact x (hOR hx) hxplane (hOprops x hx).1
  have hinf (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
      (⨅ x ∈ ball 0 r ∩ {x | x (Fin.last m) = 0},
        lelongNumber (n := m + 1)
          (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) x) =
          ENNReal.ofReal (2 * c * (a : ℝ)) := by
    apply le_antisymm
    · obtain ⟨x, ⟨hxplane, hxne⟩, hxball⟩ :=
        (hfreq.and_eventually (ball_mem_nhds (0 : ComplexModel (m + 1)) hr)).exists
      exact (iInf₂_le x ⟨hxball, hxplane⟩).trans_eq
        (hexact x (ball_subset_ball hrR hxball) hxplane (hpositive x hxne))
    · exact le_iInf fun x => le_iInf fun hx =>
        hlower x (ball_subset_ball hrR hx.1) hx.2
  refine ⟨R, O, hR, hO, hOR, ⟨y, hyO, hyplane⟩, hlower, hOexact, hinf, ?_⟩
  rw [hinf R hR le_rfl, ENNReal.toReal_ofReal (by positivity)]
  ring


end

end SGPT.Foundations.Analysis.Pending.ActualFiniteFamilyPrimeMultiplicity
