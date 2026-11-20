import SGPT.Envelopes.LapClassBridge
import SGPT.Envelopes.LapClass2Density
import SGPT.Foundations.Analysis.Pending.ClosedTopCurrents

/-!
# The bounded-Laplacian class read in a chart

Lane LAP-CLASS2 (`claude-lap-class2`, nodes `lap-class2:chart`, `lap-class2:dim-one`).  The class
`C^{1,1̄}_ω(X)` of the book (`HasBoundedMetricLaplacian w f`, LAP-CLASS) is defined globally on
`X` by testing against chart-smooth functions on `X`.  Here it is transported to a holomorphic
chart `e`:

* `integral_mul_laplacian_chartExtend`: for a smooth `φ` with compact support in the chart target,
  extended by zero to `χ = φ ∘ e` (`ChartPartition.chartExtend`),
  `∫_X f Δ_ω χ ω^N = ∫ f(e⁻¹ z) V(z) (Δ_e φ)(z) dz`, `V` the density of `ω^N` in the chart and
  `Δ_e` the chart Laplacian;
* `integral_comp_chartExtend`: `∫_X F(χ) ω^N = ∫ V(z) F(φ(z)) dz` for continuous `F` with
  `F(0) = 0`.

In **dimension one** the density of `ω` and the inverse of its coefficient cancel:
`V Δ_e φ = π⁻¹ ∂∂̄φ` (`volDensity_mul_chartLaplacian_dim_one`).  So a bounded `ω`-Laplacian is a
bounded flat Laplacian in every chart (`HasBoundedMetricLaplacian.abs_integral_leviForm_le_dim_one`),
the flat Laplacian has an `L^∞` density (`exists_levi_density_of_abs_le`, Riesz–Markov and
Radon–Nikodym), and for `n = 1` the complex Hessian is the Laplacian.  Hence:

* `HasBoundedMetricLaplacian.hasBoundedComplexHessian_of_dim_one`: for `n = 1`, the book's
  `C^{1,1̄}(X)` is contained in the class `DNTC11.HasBoundedComplexHessian` of the earlier DNT
  clauses;
* `hasBoundedMetricLaplacian_iff_hasBoundedComplexHessian_of_dim_one`: for `n = 1` the two classes
  coincide (the converse is LAP-CLASS's `HasBoundedComplexHessian.hasBoundedMetricLaplacian`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent ChartPartition ClosedTopCurrents
  SmoothMixedMeasureDensity MixedHessian

/-! ### The chart Laplacian of an extension by zero -/

section Chart

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The chart Laplacian vanishes off the support. -/
theorem chartLaplacian_eq_zero_of_notMem_tsupport (g : SmoothRealForm N Y 2) (e : ComplexChart N Y)
    {φ : ComplexModel N → ℝ} {z : ComplexModel N} (hz : z ∉ tsupport φ) :
    chartLaplacian g e φ z = 0 := by
  rw [chartLaplacian, complexHessian_eq_zero_of_notMem_tsupport hz]
  simp

/-- The support of the extension by zero of `φ` lies in `e⁻¹(tsupport φ)`. -/
theorem tsupport_chartExtend_subset (e : ComplexChart N Y) {φ : ComplexModel N → ℝ}
    (hφc : HasCompactSupport φ) (hφt : tsupport φ ⊆ e.val.target) :
    tsupport (chartExtend e φ) ⊆ e.val.symm '' tsupport φ :=
  (support_chartExtend_subset e).trans
    (hφc.isCompact.image_of_continuousOn (e.val.continuousOn_symm.mono hφt)).isClosed.closure_eq.le

/-- The Laplacian of the extension by zero of `φ` is the chart Laplacian of `φ`. -/
theorem laplacian_chartExtend_of_mem {g : SmoothRealForm N Y 2} (hg : g.IsHermitian)
    (e : ComplexChart N Y) {φ : ComplexModel N → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφt : tsupport φ ⊆ e.val.target) {y : Y}
    (hy : y ∈ e.val.source) :
    laplacian g (chartExtend e φ) y = chartLaplacian g e φ (e.val y) := by
  have hχ := chartSmooth_chartExtend e hφ hφc.isCompact hφt
  rw [laplacian_eq hg (chartSmooth_two' hχ) hy]
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  have hev : (fun w => chartExtend e φ (e.val.symm w)) =ᶠ[𝓝 (e.val y)] φ := by
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    rw [chartExtend_of_mem (e.val.map_target hw), e.val.right_inv hw]
  simp only [chartLaplacian]
  rw [complexHessian_congr' hev]

end Chart

/-! ### Integrals over `X` read in a chart -/

section Integral

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- An integral over `X` of a continuous function vanishing off `e⁻¹(K)` is read in the chart. -/
theorem integral_kahlerVolume_eq_chart (w : KahlerBackground (m + 1) Y)
    (e : ComplexChart (m + 1) Y) {K : Set (ComplexModel (m + 1))} (hK : IsCompact K)
    (hKt : K ⊆ e.val.target) {G : Y → ℝ} (hG : Continuous G)
    (hG0 : ∀ x ∉ e.val.symm '' K, G x = 0) :
    ∫ x, G x ∂(kahlerVolume w) = ∫ z in K, volDensity w e z * G (e.val.symm z) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
  exact setIntegral_kahlerVolume_image w e hK.measurableSet hKt hG

/-- **The pairing with `Δ_ω` read in a chart.** -/
theorem integral_mul_laplacian_chartExtend (w : KahlerBackground (m + 1) Y)
    (e : ComplexChart (m + 1) Y) {φ : ComplexModel (m + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφt : tsupport φ ⊆ e.val.target) {f : Y → ℝ}
    (hf : Continuous f) :
    ∫ x, f x * laplacian w.form.val (chartExtend e φ) x ∂(kahlerVolume w) =
      ∫ z, f (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z) := by
  have hχ := chartSmooth_chartExtend e hφ hφc.isCompact hφt
  have hG : Continuous fun x => f x * laplacian w.form.val (chartExtend e φ) x :=
    hf.mul (continuous_laplacian_of_chartSmooth w.isKahler.1 hχ)
  rw [integral_kahlerVolume_eq_chart w e hφc.isCompact hφt hG (fun x hx => by
    rw [laplacian_eq_zero_of_notMem_tsupport _
      (fun h => hx (tsupport_chartExtend_subset e hφc hφt h)), mul_zero])]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport φ)
    (f := fun z => f (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z))
    fun z hz => by rw [chartLaplacian_eq_zero_of_notMem_tsupport _ _ hz, mul_zero, mul_zero]]
  refine setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun z hz => ?_
  rw [laplacian_chartExtend_of_mem w.isKahler.1 e hφ hφc hφt (e.val.map_target (hφt hz)),
    e.val.right_inv (hφt hz)]
  ring

/-- **Integrals of the extension by zero read in the chart**: `∫_X F(χ) ω^N = ∫ V F(φ)` for
continuous `F` with `F(0) = 0`. -/
theorem integral_comp_chartExtend (w : KahlerBackground (m + 1) Y)
    (e : ComplexChart (m + 1) Y) {φ : ComplexModel (m + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφt : tsupport φ ⊆ e.val.target) {F : ℝ → ℝ}
    (hF : Continuous F) (hF0 : F 0 = 0) :
    ∫ x, F (chartExtend e φ x) ∂(kahlerVolume w) = ∫ z, volDensity w e z * F (φ z) := by
  have hχ := chartSmooth_chartExtend e hφ hφc.isCompact hφt
  have hG : Continuous fun x => F (chartExtend e φ x) :=
    hF.comp (YauUniformEstimate.continuous_of_chartSmooth hχ)
  rw [integral_kahlerVolume_eq_chart w e hφc.isCompact hφt hG (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_chartExtend_subset e hφc hφt h)),
      hF0])]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport φ)
    (f := fun z => volDensity w e z * F (φ z))
    fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, hF0, mul_zero]]
  refine setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun z hz => ?_
  rw [chartExtend_of_mem (e.val.map_target (hφt hz)), e.val.right_inv (hφt hz)]

/-- **A bounded `ω`-Laplacian in a chart** (all dimensions): if `f ∈ C^{1,1̄}_ω(X)`, there is
`M ≥ 0` such that in every chart, for every smooth `φ` with compact support in the target,
`|∫ f(e⁻¹z) V(z) (Δ_e φ)(z) dz| ≤ M ∫ V |φ|`. -/
theorem HasBoundedMetricLaplacian.abs_integral_chartLaplacian_le (w : KahlerBackground (m + 1) Y)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (e : ComplexChart (m + 1) Y) (φ : ComplexModel (m + 1) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ e.val.target →
      |∫ z, f (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z)| ≤
        M * ∫ z, volDensity w e z * |φ z| := by
  obtain ⟨hfc, M, hLE, hGE⟩ := hf
  refine ⟨max M 0, le_max_right _ _, fun e φ hφ hφc hφt => ?_⟩
  have hχ := chartSmooth_chartExtend e hφ hφc.isCompact hφt
  have h := abs_integral_mul_laplacian_le w hfc hLE hGE hχ
  rw [integral_mul_laplacian_chartExtend w e hφ hφc hφt hfc,
    integral_comp_chartExtend w e hφ hφc hφt continuous_abs abs_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact integral_nonneg fun z => by
    by_cases hz : z ∈ e.val.target
    · exact mul_nonneg (volDensity_pos w e hz).le (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport fun h => hz (hφt h)]

end Integral

/-! ### Dimension one -/

section DimOne

/-- In dimension one the Hermitian form of a `1 × 1` matrix is `|v₀|² Re A₀₀`. -/
theorem hermQuad_dim_one (A : Matrix (Fin 1) (Fin 1) ℂ) (v : ComplexModel 1) :
    DNTC11.hermQuad A v = Complex.normSq (v 0) * (A 0 0).re := by
  have h : v 0 * A 0 0 * star (v 0) = A 0 0 * ((Complex.normSq (v 0) : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, Complex.star_def]
    ring
  simp only [DNTC11.hermQuad, DNTC11.sesqForm, Fin.sum_univ_one, Fin.isValue]
  rw [h, Complex.re_mul_ofReal]
  ring

/-- In dimension one the Levi form is `|v₀|²` times the Laplacian `∂∂̄u`. -/
theorem leviForm_dim_one {u : ComplexModel 1 → ℝ} {z : ComplexModel 1} (hu : ContDiffAt ℝ 2 u z)
    (v : ComplexModel 1) :
    leviForm u z v = Complex.normSq (v 0) * leviForm u z (coordinateVector 0) := by
  rw [← DNTC11.hermQuad_complexHessian hu, ← DNTC11.hermQuad_complexHessian hu, hermQuad_dim_one,
    hermQuad_dim_one]
  simp [coordinateVector]

/-- The mixed coefficient of `1 × 1` matrices. -/
theorem mixedCoefficient_cons_dim_one (K H : Matrix (Fin 1) (Fin 1) ℂ) :
    mixedCoefficient (Fin.cons K (fun _ : Fin 0 => H) : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) =
      K 0 0 := by
  have h : (Fin.cons K (fun _ : Fin 0 => H) : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) = fun _ => K := by
    funext i
    fin_cases i
    rfl
  rw [h, mixedCoefficient_diagonal]
  simp

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y]
  [IsComplexManifold 1 Y]

/-- The density of the Kähler form of a curve in a chart. -/
theorem volDensity_eq_chartDensity_toReal (w : KahlerBackground 1 Y) (e : ComplexChart 1 Y)
    {z : ComplexModel 1} (hz : z ∈ e.val.target) :
    volDensity w e z = (chartDensity (fun _ : Fin 1 => w.form) e z).toReal := by
  have hden : volDensity w e z = actualMixedTopDensity fun _ : Fin 1 => w.form.val.coeff e z := by
    rw [volDensity, ProductTestForms.formPow_coeff, TopDegreeDensity.topDensity_formPower,
      actualMixedTopDensity_const]
  rw [chartDensity, ← hden, ENNReal.toReal_ofReal (volDensity_pos w e hz).le]

/-- **In dimension one, `ω Δ_ω φ = π⁻¹ ∂∂̄φ` in every chart**: the density of `ω` times the chart
Laplacian is the flat Laplacian `∂∂̄φ = leviForm φ · e₀` divided by `π`. -/
theorem volDensity_mul_chartLaplacian_dim_one (w : KahlerBackground 1 Y) (e : ComplexChart 1 Y)
    {z : ComplexModel 1} (hz : z ∈ e.val.target) (φ : ComplexModel 1 → ℝ) :
    volDensity w e z * chartLaplacian w.form.val e φ z =
      leviForm φ z (coordinateVector 0) / Real.pi := by
  have h := chartDensity_mul_chartLaplacian (m := 0) w e hz φ
  rw [← volDensity_eq_chartDensity_toReal w e hz] at h
  rw [h]
  rw [mixedCoefficient_cons_dim_one]
  simp [complexHessian, leviForm]

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- **A bounded `ω`-Laplacian is a bounded flat Laplacian in dimension one**: if
`f ∈ C^{1,1̄}_ω(X)` and `dim X = 1`, there is `M ≥ 0` such that in every chart
`|∫ f(e⁻¹z) ∂∂̄φ(z) dz| ≤ π M ∫ V |φ|` for all smooth `φ` with compact support in the target. -/
theorem HasBoundedMetricLaplacian.abs_integral_leviForm_le_dim_one (w : KahlerBackground 1 Y)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (e : ComplexChart 1 Y) (φ : ComplexModel 1 → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ e.val.target →
      |∫ z, f (e.val.symm z) * leviForm φ z (coordinateVector 0)| ≤
        ∫ z, Real.pi * M * volDensity w e z * |φ z| := by
  obtain ⟨M, hM0, hM⟩ := hf.abs_integral_chartLaplacian_le w
  refine ⟨M, hM0, fun e φ hφ hφc hφt => ?_⟩
  have h := hM e φ hφ hφc hφt
  have heq : ∫ z, f (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z) =
      (∫ z, f (e.val.symm z) * leviForm φ z (coordinateVector 0)) / Real.pi := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ e.val.target
    · dsimp only
      rw [volDensity_mul_chartLaplacian_dim_one w e hz]
      ring
    · have hz' : z ∉ tsupport φ := fun h => hz (hφt h)
      simp [chartLaplacian_eq_zero_of_notMem_tsupport _ _ hz',
        leviForm_eq_zero_of_notMem_tsupport hz']
  rw [heq, abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos] at h
  have hint : ∫ z, Real.pi * M * volDensity w e z * |φ z| =
      Real.pi * M * ∫ z, volDensity w e z * |φ z| := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hint]
  linarith

/-- **For `n = 1` the book's `C^{1,1̄}(X)` has bounded complex Hessian**: a continuous function with
bounded `ω`-Laplacian on a compact Kähler curve has, in every chart, an `L^∞_loc` density of its
distributional complex Hessian (`DNTC11.HasBoundedComplexHessian`, the class of the earlier DNT
clauses).  Proof: the flat Laplacian is bounded in charts
(`abs_integral_leviForm_le_dim_one`), so it has a bounded density (`exists_levi_density_of_abs_le`:
Riesz–Markov and Radon–Nikodym); for `n = 1` the complex Hessian is the Laplacian. -/
theorem HasBoundedMetricLaplacian.hasBoundedComplexHessian_of_dim_one (w : KahlerBackground 1 Y)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    DNTC11.HasBoundedComplexHessian (n := 1) f := by
  obtain ⟨M, hM0, hM⟩ := hf.abs_integral_leviForm_le_dim_one w
  refine ⟨hf.1, fun e => ?_⟩
  have hg : ContinuousOn (fun z => f (e.val.symm z)) e.val.target :=
    hf.1.comp_continuousOn e.val.continuousOn_symm
  set m : ComplexModel 1 → ℝ := fun z => Real.pi * M * volDensity w e z with hmdef
  have hm : ContinuousOn m e.val.target :=
    continuousOn_const.mul (continuousOn_volDensity w e)
  have hm0 : ∀ z ∈ e.val.target, 0 ≤ m z := fun z hz => by
    have := volDensity_pos w e hz
    simp only [hmdef]
    positivity
  obtain ⟨ρ, hρm, hρb, hρ⟩ := exists_levi_density_of_abs_le e.val.open_target hg hm hm0
    (coordinateVector 0) fun φ hφ hφc hφt hφ0 => by
      refine (hM e φ hφ hφc hφt).trans (le_of_eq ?_)
      exact integral_congr_ae (Eventually.of_forall fun z => by
        simp only [hmdef, abs_of_nonneg (hφ0 z)])
  refine ⟨fun z => Matrix.of fun _ _ => (ρ z : ℂ),
    { isOpen := e.val.open_target
      continuousOn := hg
      isHermitian := fun z => ?_
      measurable := fun i j => Complex.continuous_ofReal.measurable.comp hρm
      bounded := fun K hK hKt => ?_
      levi := fun φ hφ hφc hφt v => ?_ }⟩
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hm.mono hKt)
    refine ⟨C, (ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall fun z hz i j => ?_)⟩
    have h1 := hρb z (hKt hz)
    have h2 := hC z hz
    rw [Real.norm_eq_abs] at h2
    simp only [Matrix.of_apply, Complex.norm_real, Real.norm_eq_abs]
    exact h1.trans ((le_abs_self _).trans h2)
  · have hφ2 : ∀ z, ContDiffAt ℝ 2 φ z := fun z =>
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
    have e1 : ∫ z, f (e.val.symm z) * leviForm φ z v =
        Complex.normSq (v 0) * ∫ z, f (e.val.symm z) * leviForm φ z (coordinateVector 0) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun z => by
        simp only
        rw [leviForm_dim_one (hφ2 z) v]
        ring)
    have e2 : ∫ z, DNTC11.hermQuad ((fun z => Matrix.of fun _ _ => (ρ z : ℂ)) z) v * φ z =
        Complex.normSq (v 0) * ∫ z, ρ z * φ z := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun z => by
        simp only
        rw [hermQuad_dim_one]
        simp only [Matrix.of_apply, Complex.ofReal_re]
        ring)
    rw [e1, e2, hρ φ hφ hφc hφt]

end DimOne

end SGPT.Envelopes.LapClass
