import SGPT.Analysis.CZHessianLimit
import SGPT.Envelopes.LapClass3Approx

/-!
# The complex Hessian of a function with bounded `ω`-Laplacian is an `L²_loc` function

Lane CZ-LP (`claude-cz-lp`, node `czlp:density`).  Let `X` be a compact complex manifold of
dimension `n = m + 1` with a Kähler form `ω` and `f ∈ C^{1,1̄}(X)` (continuous with bounded
`ω`-Laplacian, `LapClass.HasBoundedMetricLaplacian`).

* `exists_setIntegral_hessian_sq_le`: on a compact subset `K` of a chart,
  `∫_K ∑ |∂_p∂̄_q u|² ≤ C_K ∫_X (Δ_ω u)² ωⁿ` for every chart-smooth `u` (the `L²` identity of
  `LapClass3Energy` and `sum_norm_sq_le_re_trace_mul`).
* `LapApprox`: the strong approximations of `LapClass3Approx`.
* `LapApprox.exists_density`: in every chart `e`, `f ∘ e⁻¹` has a locally integrable Hessian density
  `h` (`CZLp.IsHessianDensityOn`), the almost everywhere limit of the complex Hessians of the
  approximations; moreover `|Re tr(N⁻¹ h)| ≤ K` almost everywhere (the Laplacian bound) and
  `h ∈ L²_loc` (`LapApprox.lintegral_density_sq_lt_top`).

This is the regularity statement `C^{1,1̄}(X) ⊆ W^{2,2}_loc` (complex Hessian part) used to give a
meaning to `θ_fⁿ` (`LapClass3Measure`); its `L^p` analogue for `p > 2` (Calderón–Zygmund) is not
needed for the existence of `θ_fⁿ` and is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix ComplexOrder ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent SGPT.Foundations.Analysis.Pending.ClosedTopCurrents
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11

theorem complexHessian_sub' {n : ℕ} {w v : ComplexModel n → ℝ} {z : ComplexModel n}
    (hw : ContDiffAt ℝ 2 w z) (hv : ContDiffAt ℝ 2 v z) :
    complexHessian (fun y => w y - v y) z = complexHessian w z - complexHessian v z := by
  have e : (fun y => w y - v y) = fun y => w y + (-1) * v y := by funext y; ring
  rw [e, AubinYauLocalStep.complexHessian_fun_add hw (contDiffAt_const.mul hv),
    AubinYauLocalStep.complexHessian_const_mul hv]
  simp [sub_eq_add_neg]

theorem le_two_pow_mul_sq_add (k : ℕ) (x : ℝ) : x ≤ 2 ^ k * x ^ 2 + (1 / 2 : ℝ) ^ k := by
  have ht : (0 : ℝ) < 2 ^ k := by positivity
  have hs : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
  have key : 0 ≤ (2 : ℝ) ^ k * (2 ^ k * x ^ 2 + (1 / 2) ^ k - x) := by
    nlinarith [sq_nonneg ((2 : ℝ) ^ k * x - 1 / 2)]
  have := (mul_nonneg_iff_of_pos_left ht).mp key
  linarith

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- The intrinsic energy density is nonnegative. -/
theorem hessEnergy_nonneg (w : KahlerBackground (m + 1) M) {u : M → ℝ}
    (hu : ChartSmooth (n := m + 1) u) (x : M) : 0 ≤ hessEnergy w u hu x := by
  set e := complexChartAt (n := m + 1) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  set N := normalizedHermitianMatrix (w.form.val.coeff e (e.val x))
  have hN := posDef_coeff w.isKahler.1 hz
  have hu2 : ContDiffAt ℝ 2 (fun y => u (e.val.symm y)) (e.val x) :=
    ((hu e _ hz).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hA := complexHessian_isHermitian hu2
  have hb := sum_norm_sq_le_re_trace_mul hN hA
  have htr : 0 < N.trace.re := (Complex.pos_iff.mp hN.trace_pos).1
  have hE : hessEnergy w u hu x = (N⁻¹ * complexHessian (fun y => u (e.val.symm y)) (e.val x) *
      N⁻¹ * complexHessian (fun y => u (e.val.symm y)) (e.val x)).trace.re := by
    rw [hessEnergy_eq_chart w hu hx, ← Matrix.mul_assoc]
  rw [hE]
  by_contra hneg
  push Not at hneg
  have h0 : 0 ≤ ∑ p, ∑ q, ‖complexHessian (fun y => u (e.val.symm y)) (e.val x) p q‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : (N.trace.re) ^ 2 * (N⁻¹ * complexHessian (fun y => u (e.val.symm y)) (e.val x) *
      N⁻¹ * complexHessian (fun y => u (e.val.symm y)) (e.val x)).trace.re < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Local `L²` bound for complex Hessians** of chart-smooth functions. -/
theorem exists_setIntegral_hessian_sq_le (w : KahlerBackground (m + 1) M)
    (e : ComplexChart (m + 1) M) {K : Set (ComplexModel (m + 1))} (hK : IsCompact K)
    (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : M → ℝ, ChartSmooth (n := m + 1) u →
      ∫ z in K, ∑ p, ∑ q, ‖complexHessian (fun y => u (e.val.symm y)) z p q‖ ^ 2 ≤
        C * ∫ x, laplacian w.form.val u x ^ 2 ∂(kahlerVolume w) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, le_rfl, fun u _ => by simp [hKe]⟩
  -- bounds for the trace of `N` and the volume density on `K`
  have hNc : ContinuousOn (fun z => (normalizedHermitianMatrix (w.form.val.coeff e z)).trace.re)
      e.val.target := by
    have hcoeff : ContinuousOn (fun z => w.form.val.coeff e z) e.val.target :=
      (w.form.val.smooth e).continuousOn
    have hlin : Continuous fun A : CoordinateRealTwoForm (m + 1) =>
        (normalizedHermitianMatrix A).trace.re := by
      simp only [normalizedHermitianMatrix, Matrix.trace, Matrix.diag]
      fun_prop
    exact hlin.comp_continuousOn hcoeff
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn (hNc.mono hKt)
  obtain ⟨z₁, hz₁, hmin⟩ := hK.exists_isMinOn hKne ((continuousOn_volDensity w e).mono hKt)
  set c := volDensity w e z₁ with hc
  have hc0 : 0 < c := volDensity_pos w e (hKt hz₁)
  refine ⟨T ^ 2 / c, by positivity, fun u hu => ?_⟩
  have hEc := continuous_hessEnergy w u hu
  have hE0 := hessEnergy_nonneg w hu
  have hu2 : ∀ z ∈ e.val.target, ContDiffAt ℝ 2 (fun y => u (e.val.symm y)) z := fun z hz =>
    ((hu e z hz).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hpt : ∀ z ∈ K, ∑ p, ∑ q, ‖complexHessian (fun y => u (e.val.symm y)) z p q‖ ^ 2 ≤
      T ^ 2 / c * (volDensity w e z * hessEnergy w u hu (e.val.symm z)) := by
    intro z hz
    have hzt := hKt hz
    have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
    have hez : e.val (e.val.symm z) = z := e.val.right_inv hzt
    have hN := posDef_coeff w.isKahler.1 hzt
    have hb := sum_norm_sq_le_re_trace_mul hN (complexHessian_isHermitian (hu2 z hzt))
    have hE := hessEnergy_eq_chart w hu hx
    rw [hez, ← Matrix.mul_assoc] at hE
    rw [← hE] at hb
    have hTz : (normalizedHermitianMatrix (w.form.val.coeff e z)).trace.re ^ 2 ≤ T ^ 2 := by
      have := hT z hz
      rw [Real.norm_eq_abs] at this
      exact sq_le_sq' (by linarith [neg_abs_le ((normalizedHermitianMatrix
        (w.form.val.coeff e z)).trace.re)]) ((le_abs_self _).trans this)
    have hEz := hE0 (e.val.symm z)
    have hvz : c ≤ volDensity w e z := hmin hz
    calc ∑ p, ∑ q, ‖complexHessian (fun y => u (e.val.symm y)) z p q‖ ^ 2
        ≤ (normalizedHermitianMatrix (w.form.val.coeff e z)).trace.re ^ 2 *
            hessEnergy w u hu (e.val.symm z) := hb
      _ ≤ T ^ 2 * hessEnergy w u hu (e.val.symm z) := mul_le_mul_of_nonneg_right hTz hEz
      _ = T ^ 2 / c * (c * hessEnergy w u hu (e.val.symm z)) := by field_simp
      _ ≤ T ^ 2 / c * (volDensity w e z * hessEnergy w u hu (e.val.symm z)) := by
          gcongr
  have hcontK : ContinuousOn (fun z => ∑ p, ∑ q,
      ‖complexHessian (fun y => u (e.val.symm y)) z p q‖ ^ 2) K := by
    refine continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun q _ => ?_
    exact ((continuousOn_complexHessian_apply e.val.open_target (hu e) p q).mono hKt).norm.pow 2
  have hcontR : ContinuousOn (fun z => volDensity w e z * hessEnergy w u hu (e.val.symm z)) K :=
    ((continuousOn_volDensity w e).mono hKt).mul
      (hEc.comp_continuousOn (e.val.continuousOn_symm.mono hKt))
  calc ∫ z in K, ∑ p, ∑ q, ‖complexHessian (fun y => u (e.val.symm y)) z p q‖ ^ 2
      ≤ ∫ z in K, T ^ 2 / c * (volDensity w e z * hessEnergy w u hu (e.val.symm z)) :=
        setIntegral_mono_on (hcontK.integrableOn_compact hK)
          ((hcontR.integrableOn_compact hK).const_mul _) hK.measurableSet hpt
    _ = T ^ 2 / c * ∫ x in e.val.symm '' K, hessEnergy w u hu x ∂(kahlerVolume w) := by
        rw [integral_const_mul, setIntegral_kahlerVolume_image w e hK.measurableSet hKt hEc]
    _ ≤ T ^ 2 / c * ∫ x, hessEnergy w u hu x ∂(kahlerVolume w) :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral (hEc.integrable_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)))
          (Eventually.of_forall hE0)) (by positivity)
    _ = T ^ 2 / c * ∫ x, laplacian w.form.val u x ^ 2 ∂(kahlerVolume w) := by
        rw [integral_hessEnergy_eq]

/-! ### Strong approximations and chart densities -/

/-- **Strong approximations** of `f ∈ C^{1,1̄}(X)` (`exists_lapCauchy_approx`). -/
structure LapApprox (w : KahlerBackground (m + 1) M) (f : M → ℝ) where
  K : ℝ
  v : ℕ → M → ℝ
  K_nonneg : 0 ≤ K
  smooth : ∀ k, ChartSmooth (n := m + 1) (v k)
  lap_le : ∀ k x, |laplacian w.form.val (v k) x| ≤ K
  close : ∀ k x, |v k x - f x| ≤ 1 / ((k : ℝ) + 1)
  cauchy : ∀ k, ∫ x, (laplacian w.form.val (v (k + 1)) x - laplacian w.form.val (v k) x) ^ 2
    ∂(kahlerVolume w) ≤ (1 / 4 : ℝ) ^ k

theorem nonempty_lapApprox (w : KahlerBackground (m + 1) M) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) : Nonempty (LapApprox w f) := by
  obtain ⟨K, hK, v, hv, hvK, hvf, hvc⟩ := exists_lapCauchy_approx w hf
  exact ⟨⟨K, v, hK, hv, hvK, hvf, hvc⟩⟩

namespace LapApprox

variable {w : KahlerBackground (m + 1) M} {f : M → ℝ}

omit [BorelSpace M] in
theorem tendstoUniformly (A : LapApprox w f) : TendstoUniformly A.v f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.mpr ⟨k₀, fun k hk x => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt (A.close k x) (lt_of_le_of_lt ?_ hk₀)
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hk)

omit [BorelSpace M] in
theorem chartHess_sub (A : LapApprox w f) (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target) (k : ℕ) :
    complexHessian (fun y => A.v (k + 1) (e.val.symm y)) z -
        complexHessian (fun y => A.v k (e.val.symm y)) z =
      complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z := by
  have h := fun j => ((A.smooth j e z hz).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact (complexHessian_sub' (h (k + 1)) (h k)).symm

/-- **Existence of the Hessian density in a chart**, as the almost everywhere limit of the complex
Hessians of the approximations. -/
theorem exists_density (A : LapApprox w f) (hfc : Continuous f) (e : ComplexChart (m + 1) M) :
    ∃ h : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      IsHessianDensityOn (fun z => f (e.val.symm z)) h e.val.target ∧
      ∀ᵐ z, z ∈ e.val.target →
        Tendsto (fun k => complexHessian (fun y => A.v k (e.val.symm y)) z) atTop (𝓝 (h z)) := by
  refine exists_isHessianDensityOn_of_summable e.val.open_target (fun k => A.smooth k e)
    (hfc.comp_continuousOn e.val.continuousOn_symm) (fun K _ _ =>
      (A.tendstoUniformly.comp _).tendstoUniformlyOn) fun K hK hKt => ?_
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_hessian_sq_le w e hK hKt
  set d : ℕ → ComplexModel (m + 1) → ℝ := fun k z => ∑ p, ∑ q,
    ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y)) z p q -
      complexHessian (fun y => A.v k (e.val.symm y)) z p q‖ with hd
  set c : ℝ := C + ((m + 1 : ℕ) : ℝ) ^ 2 * (volume K).toReal with hcdef
  have hdc : ∀ k, ContinuousOn (d k) K := fun k =>
    continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun q _ =>
      (((continuousOn_complexHessian_apply e.val.open_target (A.smooth (k + 1) e) p q).sub
        (continuousOn_complexHessian_apply e.val.open_target (A.smooth k e) p q)).mono hKt).norm
  have hbound : ∀ k, ∫⁻ z in K, ENNReal.ofReal (d k z) ≤ ENNReal.ofReal (c * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hsm : ChartSmooth (n := m + 1) (fun x => A.v (k + 1) x - A.v k x) := fun e' =>
      (A.smooth (k + 1) e').sub (A.smooth k e')
    have hL2 := hC _ hsm
    have hlap : ∀ x, laplacian w.form.val (fun x => A.v (k + 1) x - A.v k x) x =
        laplacian w.form.val (A.v (k + 1)) x - laplacian w.form.val (A.v k) x := fun x =>
      laplacian_sub w.form.val (A.smooth (k + 1)) (A.smooth k) x
    simp only [hlap] at hL2
    have hL2' : ∫ z in K, ∑ p, ∑ q,
        ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^ 2 ≤
        C * (1 / 4 : ℝ) ^ k := hL2.trans (mul_le_mul_of_nonneg_left (A.cauchy k) hC0)
    -- pointwise `‖x‖ ≤ 2ᵏ ‖x‖² + 2⁻ᵏ`
    have hpt : ∀ z ∈ K, d k z ≤ 2 ^ k * (∑ p, ∑ q,
        ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^ 2) +
          ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k := by
      intro z hz
      rw [hd]
      simp only
      rw [← A.chartHess_sub e (hKt hz) k, Finset.mul_sum]
      have hcard : ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k =
          ∑ _p : Fin (m + 1), ∑ _q : Fin (m + 1), (1 / 2 : ℝ) ^ k := by
        simp [Finset.sum_const]; ring
      rw [hcard, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q _ => ?_
      exact le_two_pow_mul_sq_add k _
    have hint : ∫ z in K, d k z ≤ c * (1 / 2 : ℝ) ^ k := by
      have hcontQ : ContinuousOn (fun z => ∑ p, ∑ q,
          ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^ 2)
          K := by
        refine continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun q _ => ?_
        exact ((continuousOn_complexHessian_apply e.val.open_target (hsm e) p q).mono
          hKt).norm.pow 2
      have hI : IntegrableOn (fun z => 2 ^ k * (∑ p, ∑ q,
          ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^
            2) + ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) K := by
        have hI1 : IntegrableOn (fun z => 2 ^ k * (∑ p, ∑ q,
            ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^
              2)) K := (hcontQ.integrableOn_compact hK).const_mul _
        have hI2 : IntegrableOn (fun _ => ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) K :=
          integrableOn_const hK.measure_lt_top.ne
        exact hI1.add hI2
      calc ∫ z in K, d k z ≤ ∫ z in K, (2 ^ k * (∑ p, ∑ q,
            ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^
              2) + ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) :=
            setIntegral_mono_on ((hdc k).integrableOn_compact hK) hI hK.measurableSet hpt
        _ = 2 ^ k * (∫ z in K, ∑ p, ∑ q,
            ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^
              2) + ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k * (volume K).toReal := by
            have hI1 : IntegrableOn (fun z => 2 ^ k * (∑ p, ∑ q,
                ‖complexHessian (fun y => A.v (k + 1) (e.val.symm y) - A.v k (e.val.symm y)) z p q‖ ^
                  2)) K := (hcontQ.integrableOn_compact hK).const_mul _
            have hI2 : IntegrableOn (fun _ => ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) K :=
              integrableOn_const hK.measure_lt_top.ne
            rw [integral_add hI1 hI2, integral_const_mul, setIntegral_const, smul_eq_mul,
              measureReal_def]
            ring
        _ ≤ 2 ^ k * (C * (1 / 4 : ℝ) ^ k) +
              ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k * (volume K).toReal := by
            gcongr
        _ = c * (1 / 2 : ℝ) ^ k := by
            rw [hcdef, show (1 / 4 : ℝ) ^ k = (1 / 2) ^ k * (1 / 2) ^ k by
              rw [← mul_pow]; norm_num]
            have : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
            linear_combination (C * (1 / 2 : ℝ) ^ k) * this
    rw [← ofReal_integral_eq_lintegral_ofReal ((hdc k).integrableOn_compact hK)
      (Eventually.of_forall fun z => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hint
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  have hc0 : 0 ≤ c := by positivity
  simp_rw [ENNReal.ofReal_mul hc0]
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
  exact ENNReal.ofReal_ne_top

end LapApprox

end SGPT.Envelopes.LapClass3
