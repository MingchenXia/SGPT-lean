import SGPT.Trace.OTExt2LocalCutoff
import SGPT.Trace.TwistedL2MGauge
import SGPT.Trace.TwistedL2XFlat

/-!
# Pointwise and integral estimates for the local critical-gain extension

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:local-calc`.  Xia, *Foundations of
pluripotential theory*, proof of `lem:local-critical-gain-extension`, paragraph *The correction*.

For the cut-off extension `G_ε = f(z') χ(R/ε)` (`R = |w|²`, `χ = chenCutoff`, `χ = 1` on
`(-∞, 1/2]`, `0` on `[1, ∞)`) of a holomorphic `f(z')`:

* `norm_dbarPairing_holo_mul_ofReal_sq`: `|⟨∂̄(h g), v⟩|² = |h|² |∂g(v)|²` for `h` holomorphic and
  `g` real;
* `norm_dbarPairing_cutoff_le`: on the shell `ε/2 ≤ R ≤ ε` the data density is `4 M² |f|²`, where
  `M` bounds `|χ'|` and `|∂ψ_ε(v)|² ≤ (R/ε) H(v)` (`ψ_ε = log(ε + R)`); off the shell `∂̄G_ε = 0`;
* `norm_dbarPairing_cutoff_le_sigma`: the bound `M² ε⁻¹ |f|² |v|²` for the Kähler norm;
* `log_sq_le_two_inv`: `(log t)² ≤ 2/t` for `0 < t ≤ 1`.

Integrals over products `ℂ^m × ℂ^d`:

* `lintegral_image_prod`: `∫_{A × B} g(z') h(w) = (∫_A g)(∫_B h)`;
* `lintegral_shell_rpow_le`: `∫_{ε/2 ≤ |w|² ≤ ε} |w|^{-2d} ≤ 2^d vol(B(0,1))`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Metric Complex
open scoped Topology ENNReal ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
  SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTMargin (normalWeight normalWeight_nonneg)

variable {n : ℕ}

/-! ### The data pairing of a cut-off holomorphic function -/

theorem norm_dbarDir_ofReal_sq {g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hg : DifferentiableAt ℝ g z) (v : ComplexModel n) :
    ‖dbarDir v (fun y => (g y : ℂ)) z‖ ^ 2 = holDerivSq g z v := by
  have h : HasFDerivAt (fun y => (g y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hg.hasFDerivAt
  unfold dbarDir holDerivSq
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `|⟨∂̄(h g), v⟩|² = |h|² |∂g(v)|²` for `h` holomorphic and `g` real. -/
theorem norm_dbarPairing_holo_mul_ofReal_sq {h : ComplexModel n → ℂ} {g : ComplexModel n → ℝ}
    {z : ComplexModel n} (hh : DifferentiableAt ℂ h z) (hg : DifferentiableAt ℝ g z)
    (v : ComplexModel n) :
    ‖dbarPairing (fun y => h y * (g y : ℂ)) z v‖ ^ 2 = ‖h z‖ ^ 2 * holDerivSq g z v := by
  have hg' : DifferentiableAt ℝ (fun y => (g y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hg
  rw [dbarPairing_eq_dbarDir, dbarDir_holo_mul hh hg', norm_mul, mul_pow,
    norm_dbarDir_ofReal_sq hg]

theorem deriv_chenCutoff_of_lt_half {x : ℝ} (hx : x < 1 / 2) : deriv chenCutoff x = 0 := by
  have : chenCutoff =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds hx] with y hy using chenCutoff_of_le hy.le
  rw [this.deriv_eq, deriv_const]

theorem deriv_chenCutoff_of_gt_one {x : ℝ} (hx : 1 < x) : deriv chenCutoff x = 0 :=
  deriv_chenCutoff_of_lt hx

/-- `|∂(χ(R/ε))(v)|² = (χ'(R/ε)/ε)² |∂R(v)|²`. -/
theorem holDerivSq_chen_comp {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : DifferentiableAt ℝ R z) (ε : ℝ) (v : ComplexModel n) :
    holDerivSq (fun y => chenCutoff (R y / ε)) z v =
      (deriv chenCutoff (R z / ε) / ε) ^ 2 * holDerivSq R z v := by
  set θ : ℝ → ℝ := fun t => chenCutoff (t / ε)
  have hθ : HasDerivAt θ (deriv chenCutoff (R z / ε) * (1 / ε)) (R z) := by
    have h1 : HasDerivAt (fun t : ℝ => t / ε) (1 / ε) (R z) := (hasDerivAt_id _).div_const ε
    exact ((contDiff_chenCutoff (k := ⊤)).differentiable (by simp) _).hasDerivAt.comp _ h1
  change holDerivSq (fun y => θ (R y)) z v = _
  rw [holDerivSq_comp hθ.differentiableAt hR, hθ.deriv]
  ring

/-- `|∂R(v)|² = (ε + R)² |∂ log(ε + R)(v)|²`. -/
theorem holDerivSq_eq_sq_mul_holDerivSq_log {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : DifferentiableAt ℝ R z) {ε : ℝ} (hεR : 0 < ε + R z) (v : ComplexModel n) :
    holDerivSq R z v = (ε + R z) ^ 2 * holDerivSq (fun y => Real.log (ε + R y)) z v := by
  set θ : ℝ → ℝ := fun t => Real.log (ε + t)
  have hθ : HasDerivAt θ (1 / (ε + R z)) (R z) := by
    have h := ((hasDerivAt_id (R z)).const_add ε).log hεR.ne'
    simpa [θ] using h
  change holDerivSq R z v = (ε + R z) ^ 2 * holDerivSq (fun y => θ (R y)) z v
  rw [holDerivSq_comp hθ.differentiableAt hR, hθ.deriv]
  field_simp

/-- The data density of the cut-off extension (FPT: `g_ε = ρ'(R/ε)(1 + R/ε) ∂̄ψ_ε G`). -/
theorem norm_dbarPairing_cutoff_le {h : ComplexModel n → ℂ} {R : ComplexModel n → ℝ}
    {z : ComplexModel n} (hh : DifferentiableAt ℂ h z) (hR : DifferentiableAt ℝ R z)
    (hRz : 0 < R z) {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : ∀ x, |deriv chenCutoff x| ≤ M)
    (v : ComplexModel n) {H : ℝ}
    (hH : holDerivSq (fun y => Real.log (ε + R y)) z v ≤ R z / ε * H) :
    ‖dbarPairing (fun y => h y * (chenCutoff (R y / ε) : ℂ)) z v‖ ^ 2 ≤
      (4 * M ^ 2 * ‖h z‖ ^ 2 * (if ε / 2 ≤ R z ∧ R z ≤ ε then 1 else 0)) * H := by
  have hdiv : DifferentiableAt ℝ (fun y => R y / ε) z := by
    simpa only [div_eq_mul_inv] using hR.mul_const ε⁻¹
  have hcd : DifferentiableAt ℝ (fun y => chenCutoff (R y / ε)) z :=
    ((contDiff_chenCutoff (k := ⊤)).differentiable (by simp) _).comp z hdiv
  rw [norm_dbarPairing_holo_mul_ofReal_sq hh hcd, holDerivSq_chen_comp hR ε v,
    holDerivSq_eq_sq_mul_holDerivSq_log hR (by linarith : 0 < ε + R z) v]
  set d := deriv chenCutoff (R z / ε)
  have hD0 : 0 ≤ holDerivSq (fun y => Real.log (ε + R y)) z v := holDerivSq_nonneg _ _ _
  split_ifs with hs
  · have hd : d ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp (hM _)).1 (abs_le.mp (hM _)).2
    have hH0 : 0 ≤ H := by
      have : 0 ≤ R z / ε * H := hD0.trans hH
      exact (mul_nonneg_iff_of_pos_left (div_pos hRz hε)).mp this
    have h1 : (ε + R z) ^ 2 * (R z / ε) ≤ 4 * ε ^ 2 := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ hε]
      have : ε + R z ≤ 2 * ε := by linarith [hs.2]
      have h2 : (ε + R z) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
      nlinarith [hs.2]
    have hh0 : 0 ≤ ‖h z‖ ^ 2 := by positivity
    calc ‖h z‖ ^ 2 * ((d / ε) ^ 2 *
          ((ε + R z) ^ 2 * holDerivSq (fun y => Real.log (ε + R y)) z v))
        ≤ ‖h z‖ ^ 2 * ((d / ε) ^ 2 * ((ε + R z) ^ 2 * (R z / ε * H))) := by
          gcongr
      _ = ‖h z‖ ^ 2 * d ^ 2 * ((ε + R z) ^ 2 * (R z / ε)) / ε ^ 2 * H := by
          field_simp
      _ ≤ ‖h z‖ ^ 2 * M ^ 2 * (4 * ε ^ 2) / ε ^ 2 * H := by
          gcongr
      _ = 4 * M ^ 2 * ‖h z‖ ^ 2 * 1 * H := by
          field_simp
  · have hd : d = 0 := by
      simp only [not_and_or, not_le] at hs
      rcases hs with hs | hs
      · exact deriv_chenCutoff_of_lt_half (by rw [div_lt_iff₀ hε]; linarith)
      · exact deriv_chenCutoff_of_gt_one (by rw [lt_div_iff₀ hε]; linarith)
    rw [hd]
    simp

/-- The Kähler-norm bound of the data: `|⟨∂̄G_ε, v⟩|² ≤ M² ε⁻¹ |f|² |v|²` on the shell. -/
theorem norm_dbarPairing_cutoff_le_sigma {h : ComplexModel n → ℂ} {m : ℕ} {z : ComplexModel n}
    (hh : DifferentiableAt ℂ h z) {ε : ℝ} (hε : 0 < ε) {M : ℝ}
    (hM : ∀ x, |deriv chenCutoff x| ≤ M) (v : ComplexModel n) :
    ‖dbarPairing (fun y => h y * (chenCutoff (normalWeight n m y / ε) : ℂ)) z v‖ ^ 2 ≤
      (M ^ 2 / ε * ‖h z‖ ^ 2 * (if ε / 2 ≤ normalWeight n m z ∧ normalWeight n m z ≤ ε then 1
        else 0)) * ‖v‖ ^ 2 := by
  have hR : DifferentiableAt ℝ (normalWeight n m) z :=
    (contDiff_normalWeight m).differentiable (by simp) z
  have hdiv : DifferentiableAt ℝ (fun y => normalWeight n m y / ε) z := by
    simpa only [div_eq_mul_inv] using hR.mul_const ε⁻¹
  have hcd : DifferentiableAt ℝ (fun y => chenCutoff (normalWeight n m y / ε)) z :=
    ((contDiff_chenCutoff (k := ⊤)).differentiable (by simp) _).comp z hdiv
  rw [norm_dbarPairing_holo_mul_ofReal_sq hh hcd, holDerivSq_chen_comp hR ε v]
  set d := deriv chenCutoff (normalWeight n m z / ε)
  have hhd := holDerivSq_normalWeight_le m z v
  have hv := normalWeight_le_norm_sq' m v
  have hR0 := normalWeight_nonneg n m z
  have hv0 := normalWeight_nonneg n m v
  split_ifs with hs
  · have hd : d ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp (hM _)).1 (abs_le.mp (hM _)).2
    have h1 : holDerivSq (normalWeight n m) z v ≤ ε * ‖v‖ ^ 2 := by
      calc holDerivSq (normalWeight n m) z v ≤ normalWeight n m z * normalWeight n m v := hhd
        _ ≤ ε * ‖v‖ ^ 2 := mul_le_mul hs.2 hv hv0 hε.le
    have hh0 : 0 ≤ ‖h z‖ ^ 2 := by positivity
    calc ‖h z‖ ^ 2 * ((d / ε) ^ 2 * holDerivSq (normalWeight n m) z v)
        ≤ ‖h z‖ ^ 2 * ((d / ε) ^ 2 * (ε * ‖v‖ ^ 2)) := by gcongr
      _ = ‖h z‖ ^ 2 * d ^ 2 / ε * ‖v‖ ^ 2 := by field_simp
      _ ≤ ‖h z‖ ^ 2 * M ^ 2 / ε * ‖v‖ ^ 2 := by gcongr
      _ = M ^ 2 / ε * ‖h z‖ ^ 2 * 1 * ‖v‖ ^ 2 := by ring
  · have hd : d = 0 := by
      simp only [not_and_or, not_le] at hs
      rcases hs with hs | hs
      · exact deriv_chenCutoff_of_lt_half (by rw [div_lt_iff₀ hε]; linarith)
      · exact deriv_chenCutoff_of_gt_one (by rw [lt_div_iff₀ hε]; linarith)
    rw [hd]
    simp

/-! ### A scalar inequality -/

/-- `(log t)² ≤ 2/t` for `0 < t ≤ 1`. -/
theorem log_sq_le_two_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : Real.log t ^ 2 ≤ 2 * t⁻¹ := by
  set s := -Real.log t with hs
  have hs0 : 0 ≤ s := by rw [hs, neg_nonneg]; exact Real.log_nonpos ht.le ht1
  have he : Real.exp s = t⁻¹ := by rw [hs, Real.exp_neg, Real.exp_log ht]
  have hq := Real.quadratic_le_exp_of_nonneg hs0
  have : Real.log t ^ 2 = s ^ 2 := by rw [hs]; ring
  rw [this, ← he]
  nlinarith

/-! ### Integrals over products `ℂ^m × ℂ^d` -/

/-- `∫_{e(A × B)} g(z') h(w) = (∫_A g)(∫_B h)` for `e = prodModelEquiv m d`. -/
theorem lintegral_image_prod (m d : ℕ) {A : Set (ComplexModel m)} {B : Set (ComplexModel d)}
    (g : ComplexModel m → ℝ≥0∞) (h : ComplexModel d → ℝ≥0∞) (hg : AEMeasurable g)
    (hh : AEMeasurable h) :
    ∫⁻ z in prodModelEquiv m d '' (A ×ˢ B),
        g ((prodModelEquiv m d).symm z).1 * h ((prodModelEquiv m d).symm z).2 =
      (∫⁻ x in A, g x) * ∫⁻ w in B, h w := by
  have hmp := measurePreserving_prodModelEquiv m d
  have hemb : MeasurableEmbedding (prodModelEquiv m d) :=
    (prodModelEquiv m d).toHomeomorph.measurableEmbedding
  rw [← hmp.setLIntegral_comp_emb hemb]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [← Measure.prod_restrict]
  exact lintegral_prod_mul hg.restrict hh.restrict

theorem measure_image_prod (m d : ℕ) (A : Set (ComplexModel m)) (B : Set (ComplexModel d)) :
    volume (prodModelEquiv m d '' (A ×ˢ B)) = volume A * volume B := by
  have hmp := measurePreserving_prodModelEquiv m d
  have hemb : MeasurableEmbedding (prodModelEquiv m d) :=
    (prodModelEquiv m d).toHomeomorph.measurableEmbedding
  rw [← hmp.measure_preimage_emb hemb, Set.preimage_image_eq _ (prodModelEquiv m d).injective,
    Measure.prod_prod]

theorem measurableSet_shell (d : ℕ) (ε : ℝ) :
    MeasurableSet {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε} :=
  ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
    (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet

/-- `∫_{ε/2 ≤ |w|² ≤ ε} |w|^{-2d} ≤ 2^d vol(B(0,1))`. -/
theorem lintegral_shell_le (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ w in {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε},
        ENNReal.ofReal ((‖w‖ ^ 2)⁻¹ ^ d) ≤
      2 ^ d * volume (ball (0 : ComplexModel d) 1) := by
  have hsub : {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε} ⊆
      closedBall 0 (Real.sqrt ε) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    exact Real.le_sqrt_of_sq_le hw.2
  calc ∫⁻ w in {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε},
          ENNReal.ofReal ((‖w‖ ^ 2)⁻¹ ^ d)
      ≤ ∫⁻ _ in {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε},
          ENNReal.ofReal ((2 / ε) ^ d) := by
        refine setLIntegral_mono' (measurableSet_shell d ε) fun w hw => ?_
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
        have h1 : 0 < ε / 2 := by positivity
        calc (‖w‖ ^ 2)⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ h1 hw.1
          _ = 2 / ε := by rw [inv_div]
    _ = ENNReal.ofReal ((2 / ε) ^ d) *
          volume {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε} := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((2 / ε) ^ d) * volume (closedBall (0 : ComplexModel d) (Real.sqrt ε)) :=
        by gcongr
    _ = 2 ^ d * volume (ball (0 : ComplexModel d) 1) := by
        rw [Measure.addHaar_closedBall _ _ (Real.sqrt_nonneg ε), SGPT.Trace.OTMargin.finrank_real_complexModel',
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), pow_mul, Real.sq_sqrt hε.le,
          ← mul_pow, div_mul_cancel₀ _ hε.ne', ENNReal.ofReal_pow (by norm_num)]
        simp

end SGPT.Trace.OTExt2
