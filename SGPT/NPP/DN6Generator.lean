import SGPT.NPP.DN6Chart

/-!
# The generator of the joint smoothing on a compact Kähler manifold

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, `eq:chern-smoothing-generator`):
for every integrable `g` and every smooth `χ`,
`∫ (Ψ_g(·, t) - g)/t² χ ω^N → a ∫ g Δ_ω χ ω^N` as `t → 0⁺`.

The smoothing `Ψ` enters only through `IsChartAverage`: near every point, in a chart `e`, it is a
fibrewise average `Ψ_g(e⁻¹ z, t) = ∫ g(e⁻¹ G(z, tξ)) k(z, ξ) dξ` with `G` smooth, `G(z, 0) = z`,
an even weight `k` of mass one, and the second-order coefficient of `h ∘ G` is `a Δ_ω h`
(`IsChartAverage.laplacian`).

Proof (FPT Step 7):
* `exists_nhds_generatorPiece`: for a test function `θ` supported in a small chart patch, the chart
  pairing `exists_tendsto_pairing` (adjoint expansion) gives a continuous `Φ_θ` with
  `∫ (Ψ_g - g)/t² θ → ∫ g Φ_θ` for every measurable integrable `g`; for smooth `h` the pointwise
  expansion `tendstoUniformlyOn_fibreAverage` and `IsChartAverage.laplacian` give the limit
  `a ∫ Δ_ω h θ`, hence `∫ h Φ_θ = a ∫ Δ_ω h θ`;
* `generator_of_isChartAverage`: a partition of unity sums the pieces to `Φ = Σ Φ_θ`; Green's
  identity (`integral_mul_laplacian_comm`) and the fundamental lemma (`le_of_integral_mul_nonpos`)
  give `Φ = a Δ_ω χ`; measurable representatives (`mono`) remove the measurability assumption.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN6

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending KahlerLaplacianChart IntegrationCurrent ChartPartition
open SGPT.Envelopes.LapClass

/-! ### Flat lemmas -/

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem continuous_fibreAverage {G : E × E → E} (hG : Continuous G) {k : E × E → ℝ}
    (hk : Continuous k) {R : ℝ} (hks : ∀ z ξ, R < ‖ξ‖ → k (z, ξ) = 0) {g : E → ℝ}
    (hg : Continuous g) (t : ℝ) : Continuous fun z => fibreAverage μ G k g z t := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hset : (fun z => fibreAverage μ G k g z t) =
      fun z => ∫ ξ in closedBall (0 : E) R, g (G (z, t • ξ)) * k (z, ξ) ∂μ := by
    funext z
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
    simp only [mem_closedBall, dist_zero_right, not_le] at hξ
    rw [hks z ξ hξ, mul_zero]
  rw [hset]
  refine continuous_parametric_integral_of_continuous ?_ (isCompact_closedBall 0 R)
  exact (hg.comp (hG.comp (continuous_fst.prodMk (continuous_const.smul continuous_snd)))).mul
    (hk.comp (continuous_fst.prodMk continuous_snd))

/-- Uniform convergence on a compact set against a continuous weight vanishing off it. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn_continuous {l : Filter ℝ} {K : Set E}
    (hK : IsCompact K) {ψ : E → ℝ} (hψ : Continuous ψ) (hψK : ∀ z ∉ K, ψ z = 0)
    {D : ℝ → E → ℝ} {φ : E → ℝ} (hD : TendstoUniformlyOn D φ l K) (hDc : ∀ t, Continuous (D t))
    (hφc : Continuous φ) :
    Tendsto (fun t => ∫ z, D t z * ψ z ∂μ) l (𝓝 (∫ z, φ z * ψ z ∂μ)) := by
  have hψs : HasCompactSupport ψ := HasCompactSupport.intro hK hψK
  have hint : ∀ f : E → ℝ, Continuous f → Integrable (fun z => f z * ψ z) μ := fun f hf =>
    (hf.mul hψ).integrable_of_hasCompactSupport hψs.mul_left
  rw [Metric.tendsto_nhds]
  intro ε hε
  set I := ∫ z, |ψ z| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  have hψi : Integrable (fun z => |ψ z|) μ := (hψ.integrable_of_hasCompactSupport hψs).abs
  have hev := Metric.tendstoUniformlyOn_iff.mp hD (ε / (2 * (I + 1))) (by positivity)
  filter_upwards [hev] with t ht
  rw [Real.dist_eq, ← integral_sub (hint _ (hDc t)) (hint _ hφc)]
  have hb : ∀ z, ‖D t z * ψ z - φ z * ψ z‖ ≤ ε / (2 * (I + 1)) * |ψ z| := by
    intro z
    by_cases hz : z ∈ K
    · rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h := ht z hz
      rw [Real.dist_eq, abs_sub_comm] at h
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg _)
    · rw [hψK z hz]; simp
  calc |∫ z, D t z * ψ z - φ z * ψ z ∂μ| = ‖∫ z, D t z * ψ z - φ z * ψ z ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ε / (2 * (I + 1)) * |ψ z| ∂μ :=
        norm_integral_le_of_norm_le (hψi.const_mul _) (Eventually.of_forall hb)
    _ = ε / (2 * (I + 1)) * I := by rw [integral_const_mul]
    _ < ε := by
        have h1 : ε / (2 * (I + 1)) * I ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end Flat

/-! ### The chart representation of the smoothing -/

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **Chart representation of a smoothing `Ψ`** (FPT `lem:chern-joint-smoothing`, Step 1: "`Ψ_u`
is an average of `u ∘ F`"): in the chart `e`, for `z ∈ O` and `0 < t < t₁`,
`Ψ_g(e⁻¹ z, t) = ∫ g(e⁻¹ G(z, tξ)) k(z, ξ) dξ` with `G` smooth, `G(z, 0) = z`, a smooth weight
`k(z, ξ)` even in `ξ`, vanishing for `‖ξ‖ > R` and of mass one, and the second-order coefficient of
`h ∘ G` at `(z, 0)` is `a Δ_ω h(z)` (FPT Step 7: first moments vanish, the holomorphic quadratic
part averages out, and the second moments give the metric trace). -/
structure IsChartAverage (wY : KahlerBackground N Y) (Ψ : (Y → ℝ) → Y → ℝ → ℝ) (a : ℝ)
    (e : ComplexChart N Y) (G : ComplexModel N × ComplexModel N → ComplexModel N)
    (k : ComplexModel N × ComplexModel N → ℝ) (R : ℝ) (O : Set (ComplexModel N)) (t₁ : ℝ) :
    Prop where
  smooth : ContDiff ℝ ∞ G
  zero : ∀ z, G (z, 0) = z
  weight_smooth : ContDiff ℝ ∞ k
  radius_pos : 0 < R
  weight_supp : ∀ z ξ, R < ‖ξ‖ → k (z, ξ) = 0
  weight_even : ∀ z ξ, k (z, -ξ) = k (z, ξ)
  weight_mass : ∀ z ∈ O, ∫ ξ, k (z, ξ) = 1
  isOpen : IsOpen O
  subset : O ⊆ e.val.target
  pos : 0 < t₁
  eq : ∀ (g : Y → ℝ) (z : ComplexModel N), z ∈ O → ∀ t : ℝ, 0 < t → t < t₁ →
    Ψ g (e.val.symm z) t = ∫ ξ, g (e.val.symm (G (z, t • ξ))) * k (z, ξ)
  laplacian : ∀ h : ComplexModel N → ℝ, ContDiff ℝ ∞ h → ∀ z ∈ O,
    weightSecondCoeff volume (compWeight G k h) z = a * chartLaplacian wY.form.val e h z

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem integrable_mul_continuous (wY : KahlerBackground N Y) {g θ : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (hθ : Continuous θ) :
    Integrable (fun y => g y * θ y) (kahlerVolume wY) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hθ.continuousOn
  have h := hg.bdd_mul (c := C) hθ.aestronglyMeasurable
    (Eventually.of_forall fun y => hC y (mem_univ y))
  simpa only [mul_comm] using h

/-- **One chart piece of the generator.** -/
theorem exists_nhds_generatorPiece (wY : KahlerBackground N Y) {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    {a r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcont : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → ∀ t : ℝ, 0 < t → t < r₀ →
      Continuous fun x => Ψ g x t)
    {e : ComplexChart N Y} {G : ComplexModel N × ComplexModel N → ComplexModel N}
    {k : ComplexModel N × ComplexModel N → ℝ} {R : ℝ}
    {O : Set (ComplexModel N)} {t₁ : ℝ} (hD : IsChartAverage wY Ψ a e G k R O t₁) {x₀ : Y}
    (hx₀ : x₀ ∈ e.val.source) (hx₀O : e.val x₀ ∈ O) :
    ∃ U : Set Y, IsOpen U ∧ x₀ ∈ U ∧ ∀ θ : Y → ℝ, ChartSmooth (n := N) θ → tsupport θ ⊆ U →
      ∃ Φ : Y → ℝ, Continuous Φ ∧
        (∀ g : Y → ℝ, StronglyMeasurable g → Integrable g (kahlerVolume wY) →
          Tendsto (fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * θ y ∂kahlerVolume wY) (𝓝[>] 0)
            (𝓝 (∫ y, g y * Φ y ∂kahlerVolume wY))) ∧
        ∀ h : Y → ℝ, ChartSmooth (n := N) h →
          ∫ y, h y * Φ y ∂kahlerVolume wY =
            a * ∫ y, laplacian wY.form.val h y * θ y ∂kahlerVolume wY := by
  obtain ⟨ε, hε, hpair⟩ := exists_tendsto_pairing (μ := volume) hD.smooth hD.zero
    hD.weight_smooth hD.radius_pos hD.weight_supp hD.weight_even (e.val x₀) hD.isOpen hx₀O
    hD.weight_mass
  refine ⟨e.val.source ∩ e.val ⁻¹' (O ∩ ball (e.val x₀) ε),
    e.val.isOpen_inter_preimage (hD.isOpen.inter isOpen_ball), ⟨hx₀, hx₀O, mem_ball_self hε⟩,
    fun θ hθ hθU => ?_⟩
  have hθc : Continuous θ := YauUniformEstimate.continuous_of_chartSmooth hθ
  have hθs : tsupport θ ⊆ e.val.source := hθU.trans inter_subset_left
  set ψ := chartTransfer wY e θ with hψdef
  have hψ : ContDiff ℝ ∞ ψ := contDiff_chartTransfer wY e hθ hθs
  have hψL : tsupport ψ ⊆ e.val '' tsupport θ := tsupport_chartTransfer_subset wY e hθs
  have hLO : e.val '' tsupport θ ⊆ O ∩ ball (e.val x₀) ε := by
    rintro _ ⟨y, hy, rfl⟩; exact (hθU hy).2
  obtain ⟨t₀, C, φ, ht₀, hC, hCO, hφc, hφv, hψv, hmaps, hlim⟩ :=
    hpair ψ hψ (hψL.trans (hLO.trans inter_subset_right))
  have hCt : C ⊆ e.val.target := hCO.trans hD.subset
  have hψO : tsupport ψ ⊆ O := hψL.trans (hLO.trans inter_subset_left)
  have hψC : tsupport ψ ⊆ C := closure_minimal (fun z hz => by
    by_contra hzC; exact hz (hψv z hzC)) hC.isClosed
  set β : ComplexModel N → ℝ := fun z => φ z / chartVol wY e z with hβdef
  have hβc : ContinuousOn β e.val.target :=
    hφc.continuousOn.div (contDiffOn_chartVol wY e).continuousOn fun z hz =>
      (chartVol_pos wY e hz).ne'
  have hβv : ∀ z ∉ C, β z = 0 := fun z hz => by simp [hβdef, hφv z hz]
  have hΦc : Continuous (chartExtend e β) := continuous_chartExtend_of_vanish e hβc hC hCt hβv
  have hφt : ∀ z ∉ e.val.target, φ z = 0 := fun z hz => hφv z fun h => hz (hCt h)
  -- the representation on the support of `ψ`
  have hrepeq : ∀ (g : Y → ℝ), ∀ z ∈ tsupport ψ, ∀ t : ℝ, 0 < t → t < min (t₀ / R) t₁ →
      Ψ g (e.val.symm z) t = fibreAverage volume G k (chartRep e g) z t := by
    intro g z hz t ht0 ht
    rw [hD.eq g z (hψO hz) t ht0 (ht.trans_le (min_le_right _ _)), fibreAverage]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    by_cases hξ : ‖ξ‖ ≤ R
    · have hη : ‖t • ξ‖ < t₀ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have h1 := ht.trans_le (min_le_left _ _)
        rw [lt_div_iff₀ hD.radius_pos] at h1
        exact (mul_le_mul_of_nonneg_left hξ ht0.le).trans_lt h1
      rw [chartRep_of_mem e g (hCt (hmaps z hz _ hη))]
    · rw [hD.weight_supp z ξ (not_le.mp hξ), mul_zero, mul_zero]
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < min (min (t₀ / R) t₁) r₀ :=
    Ioo_mem_nhdsGT (lt_min (lt_min (div_pos ht₀ hD.radius_pos) hD.pos) hr₀)
  -- the transfer of `(Ψ_g - g)/t² θ` to the chart
  have htransfer : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → StronglyMeasurable g →
      ∀ t : ℝ, 0 < t → t < min (min (t₀ / R) t₁) r₀ →
        ∫ y, (Ψ g y t - g y) / t ^ 2 * θ y ∂kahlerVolume wY =
          ∫ z, (fibreAverage volume G k (chartRep e g) z t - chartRep e g z) / t ^ 2 * ψ z := by
    intro g hg hgm t ht0 ht
    have htr : t < r₀ := ht.trans_le (min_le_right _ _)
    have h1 : StronglyMeasurable fun y => Ψ g y t - g y :=
      ((hcont g hg t ht0 htr).stronglyMeasurable).sub hgm
    have hm : StronglyMeasurable fun y => (Ψ g y t - g y) / t ^ 2 := by
      have h2 : StronglyMeasurable fun y => (Ψ g y t - g y) * (t ^ 2)⁻¹ :=
        h1.mul (stronglyMeasurable_const (b := ((t ^ 2)⁻¹ : ℝ)))
      simpa only [div_eq_mul_inv] using h2
    rw [integral_mul_eq_chart wY e hm hθc hθs]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : ψ z = 0
    · simp only [show chartTransfer wY e θ z = 0 from hz, show ψ z = 0 from hz, mul_zero]
    · have hzs : z ∈ tsupport ψ := subset_tsupport ψ hz
      have hzt : z ∈ e.val.target := by
        by_contra h; exact hz (chartTransfer_of_notMem wY e θ h)
      rw [hrepeq g z hzs t ht0 (ht.trans_le (min_le_left _ _)), chartRep_of_mem e g hzt]
  -- the two halves separately
  have htransfer1 : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → ∀ t : ℝ, 0 < t →
      t < min (min (t₀ / R) t₁) r₀ →
        ∫ y, Ψ g y t * θ y ∂kahlerVolume wY =
          ∫ z, fibreAverage volume G k (chartRep e g) z t * ψ z := by
    intro g hg t ht0 ht
    have htr : t < r₀ := ht.trans_le (min_le_right _ _)
    rw [integral_mul_eq_chart wY e (hcont g hg t ht0 htr).stronglyMeasurable hθc hθs]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : ψ z = 0
    · simp only [show chartTransfer wY e θ z = 0 from hz, show ψ z = 0 from hz, mul_zero]
    · rw [hrepeq g z (subset_tsupport ψ hz) t ht0 (ht.trans_le (min_le_left _ _))]
  have htransfer2 : ∀ g : Y → ℝ, StronglyMeasurable g →
      ∫ y, g y * θ y ∂kahlerVolume wY = ∫ z, chartRep e g z * ψ z := by
    intro g hgm
    rw [integral_mul_eq_chart wY e hgm hθc hθs]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : ψ z = 0
    · simp only [show chartTransfer wY e θ z = 0 from hz, show ψ z = 0 from hz, mul_zero]
    · have hzt : z ∈ e.val.target := by
        by_contra h; exact hz (chartTransfer_of_notMem wY e θ h)
      rw [chartRep_of_mem e g hzt]
  -- every measurable integrable `g`
  have hpart1 : ∀ g : Y → ℝ, StronglyMeasurable g → Integrable g (kahlerVolume wY) →
      Tendsto (fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * θ y ∂kahlerVolume wY) (𝓝[>] 0)
        (𝓝 (∫ y, g y * chartExtend e β y ∂kahlerVolume wY)) := by
    intro g hgm hg
    have hlimg := hlim (chartRep e g) (stronglyMeasurable_chartRep e hgm)
      (integrableOn_chartRep wY e hgm hg hC hCt)
    rw [integral_mul_chartExtend wY e hgm hΦc hφt]
    refine hlimg.congr' ?_
    filter_upwards [hev] with t ⟨ht0, ht⟩
    have htr : t < r₀ := ht.trans_le (min_le_right _ _)
    have hi1 : Integrable (fun y => Ψ g y t * θ y) (kahlerVolume wY) :=
      integral_continuous ((hcont g hg t ht0 htr).mul hθc) _
    have hi2 : Integrable (fun y => g y * θ y) (kahlerVolume wY) :=
      integrable_mul_continuous wY hg hθc
    have e1 : (fun y => (Ψ g y t - g y) / t ^ 2 * θ y) =
        fun y => (Ψ g y t * θ y - g y * θ y) / t ^ 2 := by
      funext y; ring
    rw [e1, integral_div, integral_sub hi1 hi2, htransfer1 g hg t ht0 ht, htransfer2 g hgm]
  refine ⟨chartExtend e β, hΦc, hpart1, fun h hh => ?_⟩
  -- smooth `h`: the pointwise expansion
  have hhc : Continuous h := YauUniformEstimate.continuous_of_chartSmooth hh
  have hhm : StronglyMeasurable h := hhc.stronglyMeasurable
  have hhi : Integrable h (kahlerVolume wY) := integral_continuous hhc _
  obtain ⟨V, hVo, hCV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure hC hD.isOpen hCO
  obtain ⟨b, hbs, -, hbO, hb1⟩ := exists_contDiff_eq_one_of_isCompact hVc hD.isOpen hVO
  set h' : ComplexModel N → ℝ := fun z => h (e.val.symm z) * b z with hh'def
  have hh' : ContDiff ℝ ∞ h' :=
    contDiff_mul_of_tsupport_subset' e.val.open_target hbs (hbO.trans hD.subset) (hh e)
  have hh'V : ∀ z ∈ V, h' z = chartRep e h z := fun z hz => by
    have hzt : z ∈ e.val.target := hD.subset (hVO (subset_closure hz))
    simp only [hh'def, hb1 z (subset_closure hz), mul_one, chartRep_of_mem e h hzt]
  have hK : IsCompact (tsupport ψ) := hC.of_isClosed_subset (isClosed_tsupport ψ) hψC
  have hY : ∀ t : ℝ, 0 < t → t < min (min (t₀ / R) t₁) r₀ →
      ∫ y, (Ψ h y t - h y) / t ^ 2 * θ y ∂kahlerVolume wY =
        ∫ z, (fibreAverage volume G k h' z t - h' z) / t ^ 2 * ψ z := by
    intro t ht0 ht
    rw [htransfer h hhi hhm t ht0 ht]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : ψ z = 0
    · simp only [show chartTransfer wY e θ z = 0 from hz, show ψ z = 0 from hz, mul_zero]
    · have hzs : z ∈ tsupport ψ := subset_tsupport ψ hz
      have hzC := hψC hzs
      have hfa : fibreAverage volume G k (chartRep e h) z t = fibreAverage volume G k h' z t := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only
        by_cases hξ : ‖ξ‖ ≤ R
        · have hη : ‖t • ξ‖ < t₀ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
            have h1 := (ht.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
            rw [lt_div_iff₀ hD.radius_pos] at h1
            exact (mul_le_mul_of_nonneg_left hξ ht0.le).trans_lt h1
          rw [hh'V _ (hCV (hmaps z hzs _ hη))]
        · rw [hD.weight_supp z ξ (not_le.mp hξ), mul_zero, mul_zero]
      rw [hfa, hh'V z (hCV hzC)]
  have hlim2 : Tendsto (fun t => ∫ z, (fibreAverage volume G k h' z t - h' z) / t ^ 2 * ψ z)
      (𝓝[>] 0) (𝓝 (∫ z, weightSecondCoeff volume (compWeight G k h') z * ψ z)) :=
    tendsto_integral_mul_of_tendstoUniformlyOn_continuous hK hψ.continuous
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      (tendstoUniformlyOn_fibreAverage (hh'.of_le (WithTop.coe_le_coe.mpr le_top))
        (hD.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hD.zero
        (hD.weight_smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hD.radius_pos hD.weight_supp
        hD.weight_even hK fun z hz => hD.weight_mass z (hψO hz))
      (fun t => ((continuous_fibreAverage hD.smooth.continuous hD.weight_smooth.continuous
        hD.weight_supp hh'.continuous t).sub hh'.continuous).div_const _)
      (continuous_weightSecondCoeff (((hh'.comp (hD.smooth.comp contDiff_fst)).mul
        (hD.weight_smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd))).of_le
          (WithTop.coe_le_coe.mpr le_top)) (R := R)
        fun p ξ hξ => by simp [compWeight, hD.weight_supp _ _ hξ])
  have hval : ∫ z, weightSecondCoeff volume (compWeight G k h') z * ψ z =
      a * ∫ y, laplacian wY.form.val h y * θ y ∂kahlerVolume wY := by
    rw [integral_mul_eq_chart wY e
      (continuous_laplacian_of_chartSmooth wY.isKahler.1 hh).stronglyMeasurable hθc hθs,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : ψ z = 0
    · simp only [show chartTransfer wY e θ z = 0 from hz, show ψ z = 0 from hz, mul_zero]
    · have hzs : z ∈ tsupport ψ := subset_tsupport ψ hz
      have hzC := hψC hzs
      have hzt := hCt hzC
      rw [hD.laplacian h' hh' z (hψO hzs),
        laplacian_eq wY.isKahler.1 (chartSmooth_two' hh) (e.val.map_target hzt),
        e.val.right_inv hzt]
      have hgerm : h' =ᶠ[𝓝 z] fun w => h (e.val.symm w) := by
        filter_upwards [hVo.mem_nhds (hCV hzC)] with w hw
        rw [hh'V w hw, chartRep_of_mem e h (hD.subset (hVO (subset_closure hw)))]
      have hcl : chartLaplacian wY.form.val e h' z =
          chartLaplacian wY.form.val e (fun w => h (e.val.symm w)) z := by
        simp only [chartLaplacian]
        rw [complexHessian_congr' hgerm]
      rw [hcl]
      ring
  have hlimB : Tendsto (fun t => ∫ y, (Ψ h y t - h y) / t ^ 2 * θ y ∂kahlerVolume wY) (𝓝[>] 0)
      (𝓝 (a * ∫ y, laplacian wY.form.val h y * θ y ∂kahlerVolume wY)) := by
    rw [← hval]
    refine hlim2.congr' ?_
    filter_upwards [hev] with t ⟨ht0, ht⟩
    exact (hY t ht0 ht).symm
  exact tendsto_nhds_unique (hpart1 h hhm hhi) hlimB

/-- **The generator of the smoothing** (FPT `lem:chern-joint-smoothing`,
`eq:chern-smoothing-generator`): if `Ψ` is a chart average near every point
(`IsChartAverage`), `Ψ_g(·, t)` is continuous for `0 < t < r₀`, and `Ψ` is monotone for the
`ω^N`-a.e. order, then `∫ (Ψ_g(·, t) - g)/t² χ ω^N → a ∫ g Δ_ω χ ω^N` for every integrable `g`
and every smooth `χ`. -/
theorem generator_of_isChartAverage (wY : KahlerBackground N Y) {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hrep : ∀ x₀ : Y, ∃ (e : ComplexChart N Y)
      (G : ComplexModel N × ComplexModel N → ComplexModel N)
      (k : ComplexModel N × ComplexModel N → ℝ) (R : ℝ) (O : Set (ComplexModel N)) (t₁ : ℝ),
        x₀ ∈ e.val.source ∧ e.val x₀ ∈ O ∧ IsChartAverage wY Ψ a e G k R O t₁)
    (hcont : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → ∀ t : ℝ, 0 < t → t < r₀ →
      Continuous fun x => Ψ g x t)
    (hmono : ∀ g g' : Y → ℝ, Integrable g (kahlerVolume wY) → Integrable g' (kahlerVolume wY) →
      g ≤ᵐ[kahlerVolume wY] g' → ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → Ψ g x t ≤ Ψ g' x t) :
    ∃ a : ℝ, 0 < a ∧ ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) →
      ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
        Tendsto (fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * χ y ∂(kahlerVolume wY)) (𝓝[>] 0)
          (𝓝 (a * ∫ y, g y * laplacian wY.form.val χ y ∂(kahlerVolume wY))) := by
  refine ⟨a, ha, fun g hg χ hχ => ?_⟩
  have hpiece : ∀ x₀ : Y, ∃ U : Set Y, IsOpen U ∧ x₀ ∈ U ∧
      ∀ θ : Y → ℝ, ChartSmooth (n := N) θ → tsupport θ ⊆ U →
        ∃ Φ : Y → ℝ, Continuous Φ ∧
          (∀ g : Y → ℝ, StronglyMeasurable g → Integrable g (kahlerVolume wY) →
            Tendsto (fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * θ y ∂kahlerVolume wY) (𝓝[>] 0)
              (𝓝 (∫ y, g y * Φ y ∂kahlerVolume wY))) ∧
          ∀ h : Y → ℝ, ChartSmooth (n := N) h →
            ∫ y, h y * Φ y ∂kahlerVolume wY =
              a * ∫ y, laplacian wY.form.val h y * θ y ∂kahlerVolume wY := fun x₀ => by
    obtain ⟨e, G, k, R, O, t₁, hx, hxO, hD⟩ := hrep x₀
    exact exists_nhds_generatorPiece wY hr₀ hcont hD hx hxO
  choose U hUo hxU hUθ using hpiece
  obtain ⟨m, χs, idx, hχs, -, hχS, -, hsum⟩ := exists_chartSmooth_partitionOfUnity (n := N)
    (fun x : Y => (⟨U x, hUo x⟩ : TopologicalSpace.Opens Y)) (fun x => ⟨x, hxU x⟩)
  set θ : Fin m → Y → ℝ := fun i y => χs i y * χ y with hθdef
  have hθs : ∀ i, ChartSmooth (n := N) (θ i) := fun i e => (hχs i e).mul (hχ e)
  have hθU : ∀ i, tsupport (θ i) ⊆ U (idx i) := fun i =>
    (tsupport_mul_subset_left (f := χs i) (g := χ)).trans (hχS i)
  choose Φ hΦc hΦlim hΦsm using fun i => hUθ (idx i) (θ i) (hθs i) (hθU i)
  set Φs : Y → ℝ := fun y => ∑ i, Φ i y with hΦsdef
  have hΦsc : Continuous Φs := continuous_finsetSum _ fun i _ => hΦc i
  have hχc : Continuous χ := YauUniformEstimate.continuous_of_chartSmooth hχ
  have hθc : ∀ i, Continuous (θ i) := fun i =>
    YauUniformEstimate.continuous_of_chartSmooth (hθs i)
  have hθsum : ∀ y, ∑ i, θ i y = χ y := fun y => by
    simp only [hθdef]; rw [← Finset.sum_mul, hsum, one_mul]
  have hLχ : Continuous (laplacian wY.form.val χ) :=
    continuous_laplacian_of_chartSmooth wY.isKahler.1 hχ
  -- (i) measurable integrable `g`
  have hmeas : ∀ g : Y → ℝ, StronglyMeasurable g → Integrable g (kahlerVolume wY) →
      Tendsto (fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * χ y ∂kahlerVolume wY) (𝓝[>] 0)
        (𝓝 (∫ y, g y * Φs y ∂kahlerVolume wY)) := by
    intro g hgm hg
    have hsplit : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ∑ i, ∫ y, (Ψ g y t - g y) / t ^ 2 * θ i y ∂kahlerVolume wY =
          ∫ y, (Ψ g y t - g y) / t ^ 2 * χ y ∂kahlerVolume wY := by
      filter_upwards [Ioo_mem_nhdsGT hr₀] with t ⟨ht0, ht⟩
      have hint : ∀ i, Integrable (fun y => (Ψ g y t - g y) / t ^ 2 * θ i y)
          (kahlerVolume wY) := fun i => by
        have h1 : Integrable (fun y => Ψ g y t * θ i y) (kahlerVolume wY) :=
          integral_continuous ((hcont g hg t ht0 ht).mul (hθc i)) _
        have h2 : Integrable (fun y => g y * θ i y) (kahlerVolume wY) :=
          integrable_mul_continuous wY hg (hθc i)
        refine ((h1.sub h2).div_const (t ^ 2)).congr (Eventually.of_forall fun y => ?_)
        simp only [Pi.sub_apply]; ring
      rw [← integral_finsetSum _ fun i _ => hint i]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [← Finset.mul_sum, hθsum]
    have hlim := tendsto_finsetSum Finset.univ fun i _ => hΦlim i g hgm hg
    have hval : ∑ i, ∫ y, g y * Φ i y ∂kahlerVolume wY = ∫ y, g y * Φs y ∂kahlerVolume wY := by
      rw [← integral_finsetSum _ fun i _ => integrable_mul_continuous wY hg (hΦc i)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hΦsdef, Finset.mul_sum]
    rw [← hval]
    exact hlim.congr' hsplit
  -- (ii) smooth `h`: `∫ h Φs = a ∫ h Δ_ω χ`
  have hsmooth : ∀ h : Y → ℝ, ChartSmooth (n := N) h →
      ∫ y, h y * Φs y ∂kahlerVolume wY =
        ∫ y, h y * (a * laplacian wY.form.val χ y) ∂kahlerVolume wY := by
    intro h hh
    have hhc : Continuous h := YauUniformEstimate.continuous_of_chartSmooth hh
    have hLc : Continuous (laplacian wY.form.val h) :=
      continuous_laplacian_of_chartSmooth wY.isKahler.1 hh
    calc ∫ y, h y * Φs y ∂kahlerVolume wY = ∑ i, ∫ y, h y * Φ i y ∂kahlerVolume wY := by
          rw [← integral_finsetSum _ fun i _ =>
            integral_continuous (f := fun y => h y * Φ i y) (hhc.mul (hΦc i)) _]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [hΦsdef, Finset.mul_sum]
      _ = ∑ i, a * ∫ y, laplacian wY.form.val h y * θ i y ∂kahlerVolume wY :=
          Finset.sum_congr rfl fun i _ => hΦsm i h hh
      _ = a * ∫ y, laplacian wY.form.val h y * χ y ∂kahlerVolume wY := by
          rw [← Finset.mul_sum,
            ← integral_finsetSum _ fun i _ => integral_continuous
              (f := fun y => laplacian wY.form.val h y * θ i y) (hLc.mul (hθc i)) _]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          rw [← Finset.mul_sum, hθsum]
      _ = a * ∫ y, h y * laplacian wY.form.val χ y ∂kahlerVolume wY := by
          rw [integral_mul_laplacian_comm wY hh hχ]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          ring
      _ = ∫ y, h y * (a * laplacian wY.form.val χ y) ∂kahlerVolume wY := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          ring
  -- (iii) `Φs = a Δ_ω χ`
  have hident : ∀ y, Φs y = a * laplacian wY.form.val χ y := by
    have hDc : Continuous fun y => Φs y - a * laplacian wY.form.val χ y :=
      hΦsc.sub (continuous_const.mul hLχ)
    have hzero : ∀ h : Y → ℝ, ChartSmooth (n := N) h →
        ∫ y, (Φs y - a * laplacian wY.form.val χ y) * h y ∂kahlerVolume wY = 0 := by
      intro h hh
      have hhc : Continuous h := YauUniformEstimate.continuous_of_chartSmooth hh
      have e1 : (fun y => (Φs y - a * laplacian wY.form.val χ y) * h y) =
          fun y => h y * Φs y - h y * (a * laplacian wY.form.val χ y) := by
        funext y; ring
      rw [e1, integral_sub (integral_continuous (f := fun y => h y * Φs y) (hhc.mul hΦsc) _)
        (integral_continuous (f := fun y => h y * (a * laplacian wY.form.val χ y))
          (hhc.mul (continuous_const.mul hLχ)) _), hsmooth h hh, sub_self]
    intro y
    have h1 := le_of_integral_mul_nonpos wY hDc (fun h hh _ => (hzero h hh).le) y
    have h2 := le_of_integral_mul_nonpos wY hDc.neg (fun h hh _ => by
      have e2 : (fun y => -(Φs y - a * laplacian wY.form.val χ y) * h y) =
          fun y => -((Φs y - a * laplacian wY.form.val χ y) * h y) := by
        funext y; ring
      simp only [Pi.neg_apply]
      rw [e2, integral_neg, hzero h hh, neg_zero]) y
    simp only [Pi.neg_apply] at h2
    linarith
  -- (iv) measurable representatives
  set g' := hg.1.mk g with hg'def
  have hg'm : StronglyMeasurable g' := hg.1.stronglyMeasurable_mk
  have hgg' : g =ᵐ[kahlerVolume wY] g' := hg.1.ae_eq_mk
  have hg' : Integrable g' (kahlerVolume wY) := hg.congr hgg'
  have hΨ : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → Ψ g x t = Ψ g' x t := fun x t ht0 ht =>
    le_antisymm (hmono g g' hg hg' hgg'.le x t ht0 ht)
      (hmono g' g hg' hg hgg'.symm.le x t ht0 ht)
  have hval : ∫ y, g' y * Φs y ∂kahlerVolume wY =
      a * ∫ y, g y * laplacian wY.form.val χ y ∂kahlerVolume wY := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hgg'] with y hy
    rw [hident y, hy]
    ring
  rw [← hval]
  refine (hmeas g' hg'm hg').congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with t ⟨ht0, ht⟩
  refine integral_congr_ae ?_
  filter_upwards [hgg'] with y hy
  rw [hΨ y t ht0 ht, hy]

/-- Smoothness of `(z, t) ↦ Ψ(e⁻¹ z, t)` in every chart gives continuity of `Ψ(·, t)`. -/
theorem continuous_of_contDiffOn_charts {F : Y → ℝ → ℝ} {r₀ : ℝ}
    (hF : ∀ e : ComplexChart N Y,
      ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => F (e.val.symm p.1) p.2)
        (e.val.target ×ˢ Ioo 0 r₀)) {t : ℝ} (ht0 : 0 < t) (ht : t < r₀) :
    Continuous fun x => F x t := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hc : ContinuousOn (fun z => F (e.val.symm z) t) e.val.target :=
    (hF e).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      fun z hz => ⟨hz, ht0, ht⟩
  have hca : ContinuousAt (fun z => F (e.val.symm z) t) (e.val x) :=
    hc.continuousAt (e.val.open_target.mem_nhds (e.val.map_source hx))
  have hev : (fun y => F (e.val.symm (e.val y)) t) =ᶠ[𝓝 x] fun y => F y t := by
    filter_upwards [e.val.open_source.mem_nhds hx] with y hy
    rw [e.val.left_inv hy]
  exact (hca.comp (e.val.continuousAt hx)).congr hev

end SGPT.NPP.DN6
