import SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
import SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.CoordinateDensityFrame

set_option autoImplicit false

/-! Actual directional C0 errors control ORIGINAL signed coefficient and full
current tests. Full BP statement and ENTIRE proof precede this source.
No given coefficient bound, test-integrability or current-limit certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.SmoothC0OriginalCurrentConvergence
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere XiaoFormC0Topology
  LelongPoincareDivisor _root_.SGPT.Foundations.Analysis.LocalCurrents

private theorem polarization {n : ℕ} (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (v w : ComplexModel n) :
    2 * A ![v,w] = A ![v,Complex.I • v] + A ![w,Complex.I • w] -
      A ![v + Complex.I • w,Complex.I • (v + Complex.I • w)] := by
  simp only [smul_add,smul_smul,Complex.I_mul_I,neg_one_smul,
    coordinateFrame_twoForm_add_left,coordinateFrame_twoForm_add_right,
    coordinateFrame_twoForm_neg_right,hA w v,coordinateFrame_twoForm_swap A v w,
    coordinateFrame_twoForm_I_smul_left_of_isOneOne hA w w]
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem integrable_scalar
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (σ : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (v : Fin 2 → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    Integrable (fun z => φ z * σ.val.coeff e z v) b.addHaar := by
  have hL : LocallyIntegrableOn (fun z => σ.val.coeff e z v) (chartTarget e) b.addHaar :=
    ((formEvaluationCLM v).contDiff.comp_contDiffOn (σ.val.smooth e)).continuousOn
      |>.locallyIntegrableOn e.val.open_target.measurableSet
  exact φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hL

private theorem scalar_integral
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (σ : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (v : Fin 2 → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    smoothFormDistribution b σ.val e v φ = ∫ z, φ z * σ.val.coeff e z v ∂b.addHaar := by
  rw [smoothFormDistribution_apply]
  have hi : Integrable (fun z => φ z • σ.val.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b σ.val e)
  change (formEvaluationCLM v) (∫ z, φ z • σ.val.coeff e z ∂b.addHaar) = _
  rw [← (formEvaluationCLM v).integral_comp_comm hi]
  simp only [map_smul,formEvaluationCLM_apply,smul_eq_mul]

variable [CompactSpace M]

private theorem line_bound (ω : KahlerBackground n M) (σ : ClosedRealOneOneForm n M)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (v : ComplexModel n) : |σ.val.coeff e z ![v,Complex.I • v]| ≤
      formC0Seminorm ω σ * |ω.form.val.coeff e z ![v,Complex.I • v]| := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · let p : LineProbe n M := ⟨e,z,hz,v,hv⟩
    have hd := probe_denominator_pos ω p
    have ha := abs_normalizedProbe_le ω σ p
    change |σ.val.coeff e z ![v,Complex.I • v] /
      ω.form.val.coeff e z ![v,Complex.I • v]| ≤ formC0Seminorm ω σ at ha
    rw [abs_div,abs_of_pos hd] at ha
    rw [abs_of_pos hd]
    exact (div_le_iff₀ hd).mp ha

/-- ONE actual finite scalar-test bound BEFORE ALL signed smooth forms,
with actual integrability and original coefficient reader produced internally. -/
theorem exists_scalar_test_bound (ω : KahlerBackground n M)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (e : ComplexChart n M) (v w : ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ : ClosedRealOneOneForm n M,
      |smoothFormDistribution b σ.val e ![v,w] φ| ≤ B * formC0Seminorm ω σ := by
  let f (t : ComplexModel n) (z : ComplexModel n) :=
    φ z * ω.form.val.coeff e z ![t,Complex.I • t]
  let H (z : ComplexModel n) := (|f v z| + |f w z| + |f (v + Complex.I • w) z|) / 2
  have hf (t : ComplexModel n) : Integrable (f t) b.addHaar :=
    integrable_scalar b ω.form e _ φ
  have hH : Integrable H b.addHaar := ((hf v).abs.add (hf w).abs |>.add
    (hf (v + Complex.I • w)).abs).div_const 2
  have hHn (z : ComplexModel n) : 0 ≤ H z := by dsimp [H]; positivity
  refine ⟨∫ z, H z ∂b.addHaar,integral_nonneg hHn,fun σ => ?_⟩
  let p := formC0Seminorm ω σ
  have hp : 0 ≤ p := norm_nonneg (probeLinearMap ω σ)
  have hpoint (z : ComplexModel n) : |φ z * σ.val.coeff e z ![v,w]| ≤ p * H z := by
    by_cases hz : z ∈ e.val.target
    · have hpol := polarization (σ.val.coeff e z) (σ.property.2 e z hz) v w
      have h1 := line_bound ω σ e hz v
      have h2 := line_bound ω σ e hz w
      have h3 := line_bound ω σ e hz (v + Complex.I • w)
      have ha : |σ.val.coeff e z ![v,w]| ≤ p *
          (|ω.form.val.coeff e z ![v,Complex.I • v]| +
           |ω.form.val.coeff e z ![w,Complex.I • w]| +
           |ω.form.val.coeff e z ![v + Complex.I • w,Complex.I • (v + Complex.I • w)]|) / 2 := by
        have ht := abs_sub (σ.val.coeff e z ![v,Complex.I • v] +
          σ.val.coeff e z ![w,Complex.I • w])
          (σ.val.coeff e z ![v + Complex.I • w,Complex.I • (v + Complex.I • w)])
        rw [← hpol,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
        have hs := abs_add_le (σ.val.coeff e z ![v,Complex.I • v])
          (σ.val.coeff e z ![w,Complex.I • w])
        change _ ≤ p * _ at h1 h2 h3
        nlinarith
      rw [abs_mul]
      have hm := mul_le_mul_of_nonneg_left ha (abs_nonneg (φ z))
      dsimp [H,f]
      simp only [abs_mul]
      nlinarith only [hm]
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (φ.tsupport_subset ht))
      simp [H,f,hφ]
  rw [scalar_integral]
  calc |∫ z, φ z * σ.val.coeff e z ![v,w] ∂b.addHaar|
      ≤ ∫ z, |φ z * σ.val.coeff e z ![v,w]| ∂b.addHaar :=
        by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
          (fun z => φ z * σ.val.coeff e z ![v,w]) (μ := b.addHaar))
    _ ≤ ∫ z, p * H z ∂b.addHaar :=
      integral_mono (integrable_scalar b σ e _ φ).abs (hH.const_mul p) hpoint
    _ = (∫ z, H z ∂b.addHaar) * formC0Seminorm ω σ := by
      rw [integral_const_mul,mul_comm]

private theorem tendsto_scalar {ι : Type*} {F : Filter ι}
    (ω : KahlerBackground n M)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (σ : ι → ClosedRealOneOneForm n M) (θ : ClosedRealOneOneForm n M)
    (hlim : Tendsto (fun i => formC0Seminorm ω (σ i - θ)) F (𝓝 0))
    (e : ComplexChart n M) (v : Fin 2 → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    Tendsto (fun i => smoothFormDistribution b (σ i).val e v φ) F
      (𝓝 (smoothFormDistribution b θ.val e v φ)) := by
  have hv : v = ![v 0,v 1] := by ext j; fin_cases j <;> rfl
  rw [hv]
  obtain ⟨B,hB,hbound⟩ := exists_scalar_test_bound ω b e (v 0) (v 1) φ
  have hdiff (i : ι) : smoothFormDistribution b (σ i - θ).val e ![v 0,v 1] φ =
      smoothFormDistribution b (σ i).val e ![v 0,v 1] φ -
        smoothFormDistribution b θ.val e ![v 0,v 1] φ := by
    simp only [scalar_integral]
    have heq (z : ComplexModel n) : φ z * (σ i - θ).val.coeff e z ![v 0,v 1] =
        φ z * (σ i).val.coeff e z ![v 0,v 1] - φ z * θ.val.coeff e z ![v 0,v 1] := by
      rw [sub_eq_add_neg,ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_neg,
        ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.neg_apply]
      ring
    simp_rw [heq]
    exact integral_sub (integrable_scalar b (σ i) e _ φ) (integrable_scalar b θ e _ φ)
  have hab : ∀ i, |smoothFormDistribution b (σ i).val e ![v 0,v 1] φ -
      smoothFormDistribution b θ.val e ![v 0,v 1] φ| ≤ B * formC0Seminorm ω (σ i - θ) := by
    intro i
    rw [← hdiff]
    exact hbound _
  have ht := squeeze_zero' (Eventually.of_forall fun i => abs_nonneg
      (smoothFormDistribution b (σ i).val e ![v 0,v 1] φ -
        smoothFormDistribution b θ.val e ![v 0,v 1] φ))
    (Eventually.of_forall hab) (by simpa using hlim.const_mul B)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

/-- Directional C0 convergence yields weak convergence on EVERY ORIGINAL
full chart test, retaining the SAME arbitrary filter and signed smooth forms. -/
theorem tendsto_smoothGlobalCurrent_of_C0 {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] {ι : Type*} {F : Filter ι} (ω : KahlerBackground (m + 1) X)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ (ComplexModel (m + 1)))
    (σ : ι → ClosedRealOneOneForm (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    (hlim : Tendsto (fun i => formC0Seminorm ω (σ i - θ)) F (𝓝 0))
    (e : ComplexChart (m + 1) X)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    Tendsto (fun i => (GlobalCurrents.smoothGlobalCurrent b
      (k := degreeTwo (Nat.succ_pos m)) (σ i).val).inChart e η) F
      (𝓝 ((GlobalCurrents.smoothGlobalCurrent b
        (k := degreeTwo (Nat.succ_pos m)) θ.val).inChart e η)) := by
  simp only [GlobalCurrents.smoothGlobalCurrent_inChart,smoothCurrentFamily,
    toLocalCurrent,wedgePairing_apply]
  exact tendsto_finsetSum _ fun s _ => (tendsto_scalar ω b σ θ hlim e _ _).const_smul
    (Equiv.Perm.sign s.out)

end SGPT.Foundations.Analysis.Pending.SmoothC0OriginalCurrentConvergence
