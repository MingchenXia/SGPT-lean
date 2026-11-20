import SGPT.NPP.DN6Generator
import SGPT.NPP.DN6Laplacian
import SGPT.NPP.DN5Regularity
import SGPT.NPP.DN5Interface

/-!
# The generator of the smoothing of lane DN5

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, `eq:chern-smoothing-generator`).
The smoothing `SGPT.NPP.DN5.smoothing wY A` is a chart average in the sense of
`SGPT.NPP.DN6.IsChartAverage` near every point (`isChartAverage_smoothing`): in the preferred chart
`e` at `x₀`, `Ψ_g(e⁻¹ z, t) = ∫ g(F(e⁻¹ z, tξ)) χ(|ξ|²_ω) dξ / ∫ χ(|ξ|²_ω)` (`DN5.chartSmoothing`),
the map `Φ(z, ξ) = e(F(e⁻¹ z, ξ))` is a local fibre map (smooth, holomorphic in `ξ`, `Φ(z, 0) = z`,
`D_ξΦ(z, 0) = id`; `DN5.isLocalFibreMap_goodSet`), and we cut `Φ` and the normalized weight off
smoothly away from `(e x₀, 0)`.  The Laplacian identification is
`SGPT.NPP.DN6.weightSecondCoeff_eq_chartLaplacian`, with `a = ∫ -χ₁(‖ζ‖²) dζ > 0`.

Main result: `generatorEstimate : SGPT.NPP.DN5.GeneratorEstimate` (the `generator` field of
`SGPT.NPP.DN2.IsJointSmoothing` for `Ψ = DN5.smoothing wY A`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN6

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending KahlerLaplacianChart IntegrationCurrent

/-- `β • f` is smooth when `β` is smooth with support in an open set on which `f` is smooth. -/
theorem contDiff_smul_of_tsupport_subset {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Set P} (hD : IsOpen D) {β : P → ℝ}
    {f : P → F} (hβ : ContDiff ℝ ∞ β) (hβD : tsupport β ⊆ D) (hf : ContDiffOn ℝ ∞ f D) :
    ContDiff ℝ ∞ (fun p => β p • f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ D
  · exact hβ.contDiffAt.smul (hf.contDiffAt (hD.mem_nhds hp))
  · have hnot : p ∉ tsupport β := fun h => hp (hβD h)
    have hev : (fun p => β p • f p) =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp hnot] with q hq
      simp [hq]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The radial constant `a = ∫ -χ₁(‖ζ‖²) dζ` is positive. -/
theorem integral_neg_chiOne_pos (N : ℕ) :
    0 < ∫ ζ : ComplexModel N, -DN3.chiOne N (‖ζ‖ ^ 2) := by
  have hc : Continuous fun ζ : ComplexModel N => -DN3.chiOne N (‖ζ‖ ^ 2) :=
    ((DN3.contDiff_chiOne N).continuous.comp (continuous_norm.pow 2)).neg
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    DN3.hasCompactSupport_chiOne_normSq.neg (fun ζ => ?_) ?_
  · simpa using DN3.chiOne_nonpos N (‖ζ‖ ^ 2)
  · show -DN3.chiOne N (‖(0 : ComplexModel N)‖ ^ 2) ≠ 0
    rw [norm_zero, zero_pow two_ne_zero]
    exact (DN3.neg_chiOne_pos_of_lt N (by norm_num)).ne'

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

local notation "E" => ComplexModel N

theorem fibreWeight_neg (wY : KahlerBackground N Y) (e : ComplexChart N Y) (z ξ : E) :
    DN5.fibreWeight wY e z (-ξ) = DN5.fibreWeight wY e z ξ := by
  simp only [DN5.fibreWeight, DN5.fibreNormSq, DN2.chartNormSq]
  congr 2
  have h : (![-ξ, Complex.I • -ξ] : Fin 2 → E) = fun i => (-1 : ℝ) • (![ξ, Complex.I • ξ] i) := by
    funext i; fin_cases i <;> simp
  rw [h, ContinuousAlternatingMap.map_smul_univ]
  simp

/-- **The smoothing of lane DN5 is a chart average near every point**, with `a = ∫ -χ₁(‖ζ‖²)`. -/
theorem isChartAverage_smoothing (wY : KahlerBackground N Y) (A : DN5.FibreAtlas N Y) (x₀ : Y) :
    ∃ (e : ComplexChart N Y) (G : E × E → E) (k : E × E → ℝ) (R : ℝ) (O : Set E) (t₁ : ℝ),
      x₀ ∈ e.val.source ∧ e.val x₀ ∈ O ∧
      IsChartAverage wY (DN5.smoothing wY A) (∫ ζ : E, -DN3.chiOne N (‖ζ‖ ^ 2)) e G k R O t₁ := by
  set e := complexChartAt (n := N) x₀ with he
  have hx₀ : x₀ ∈ e.val.source := mem_complexChartAt_source x₀
  set z₀ := e.val x₀ with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hx₀
  set Φ : E → E → E := fun z ξ => e.val (DN5.fibreMap A e z ξ) with hΦdef
  have hΦ : DN5.IsLocalFibreMap Φ (DN5.goodSet A e) := DN5.isLocalFibreMap_goodSet A e
  have hU₀ : IsOpen (DN5.goodSet A e) := DN5.isOpen_goodSet A e
  have hz₀U₀ : ((z₀, 0) : E × E) ∈ DN5.goodSet A e := DN5.mem_goodSet_of_mem_target A hz₀
  obtain ⟨U₁, hU₁o, hz₀U₁, hU₁t, R₁, hR₁⟩ := DN5.exists_fibreWeight_support_bound wY e hz₀
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.mp hU₀ _ hz₀U₀
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.isOpen_iff.mp hU₁o _ hz₀U₁
  set δ := min δ₁ δ₂ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ < δ₁ := by
    have := min_le_left δ₁ δ₂; rw [hδdef]; linarith
  have hδ2 : δ < δ₂ := by
    have := min_le_right δ₁ δ₂; rw [hδdef]; linarith
  have hK₁ : closedBall ((z₀, 0) : E × E) δ ⊆ DN5.goodSet A e :=
    (closedBall_subset_ball hδ1).trans hball₁
  have hK₂ : closedBall z₀ δ ⊆ U₁ := (closedBall_subset_ball hδ2).trans hball₂
  -- the cut-off fibre map
  obtain ⟨β₁, hβ₁s, -, hβ₁U, hβ₁1⟩ := exists_contDiff_eq_one_of_isCompact
    (isCompact_closedBall ((z₀, 0) : E × E) δ) hU₀ hK₁
  set G : E × E → E := fun q => q.1 + β₁ q • (Φ q.1 q.2 - q.1) with hGdef
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_fst.add (contDiff_smul_of_tsupport_subset hU₀ hβ₁s hβ₁U
      (hΦ.contDiffOn.sub contDiffOn_fst))
  have hG0 : ∀ z, G (z, 0) = z := by
    intro z
    by_cases hb : β₁ (z, 0) = 0
    · simp [hGdef, hb]
    · have hmem : ((z, 0) : E × E) ∈ DN5.goodSet A e := hβ₁U (subset_tsupport _ hb)
      simp [hGdef, hΦ.map_zero z hmem]
  have hGΦ : ∀ q ∈ closedBall ((z₀, 0) : E × E) δ, G q = Φ q.1 q.2 := by
    intro q hq; simp [hGdef, hβ₁1 q hq]
  -- the normalized weight
  set w : E → E → ℝ := fun z ξ => DN5.fibreWeight wY e z ξ with hwdef
  obtain ⟨b, hbs, hbc, -, hb1⟩ := exists_contDiff_eq_one_of_isCompact
    (isCompact_closedBall (0 : E) R₁) isOpen_univ (subset_univ _)
  set m : E → ℝ := fun z => ∫ ξ, w z ξ with hmdef
  have hmeq : ∀ z ∈ U₁, m z = ∫ ξ, (fun _ => (1 : ℝ)) ξ * (w z ξ * b ξ) := by
    intro z hz
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [one_mul]
    by_cases hw : w z ξ = 0
    · rw [hw, zero_mul]
    · rw [hb1 ξ (by simpa using hR₁ z hz ξ hw), mul_one]
  have hmc : ContDiffOn ℝ ∞ m U₁ := by
    have hK : ContDiffOn ℝ ∞ (fun q : E × E => w q.1 q.2 * b q.2) (U₁ ×ˢ univ) :=
      ((DN5.contDiffOn_fibreWeight wY e).mono (prod_mono hU₁t subset_rfl)).mul
        (hbs.comp contDiff_snd).contDiffOn
    have h := DN5.contDiffOn_integral_mul_kernel (K := fun z y => w z y * b y) hU₁o hK hbc
      (fun p y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
      (f := fun _ => (1 : ℝ)) (integrableOn_const hbc.measure_lt_top.ne)
    exact h.congr fun z hz => hmeq z hz
  have hmpos : ∀ z ∈ U₁, 0 < m z := fun z hz => DN5.integral_fibreWeight_pos wY (hU₁t hz)
  set k₀ : E × E → ℝ := fun q => w q.1 q.2 / m q.1 with hk₀def
  have hk₀ : ContDiffOn ℝ ∞ k₀ (U₁ ×ˢ univ) :=
    ((DN5.contDiffOn_fibreWeight wY e).mono (prod_mono hU₁t subset_rfl)).div
      (hmc.comp contDiffOn_fst fun q hq => hq.1) fun q hq => (hmpos q.1 hq.1).ne'
  obtain ⟨γ, hγs, -, hγU, hγ1⟩ := exists_contDiff_eq_one_of_isCompact
    (isCompact_closedBall z₀ δ) hU₁o hK₂
  set R := max R₁ 1 with hRdef
  set k : E × E → ℝ := fun q => k₀ q * γ q.1 + (1 - γ q.1) * DN3.kernel N q.2 with hkdef
  have hγfst : tsupport (fun q : E × E => γ q.1) ⊆ U₁ ×ˢ univ :=
    (closure_minimal (fun q (hq : q ∈ Function.support (fun q : E × E => γ q.1)) =>
      (⟨subset_tsupport γ hq, mem_univ _⟩ : q ∈ tsupport γ ×ˢ (univ : Set E)))
      ((isClosed_tsupport γ).prod isClosed_univ)).trans (prod_mono hγU subset_rfl)
  have hks : ContDiff ℝ ∞ k :=
    (contDiff_mul_of_tsupport_subset' (hU₁o.prod isOpen_univ) (hγs.comp contDiff_fst) hγfst
      hk₀).add ((contDiff_const.sub (hγs.comp contDiff_fst)).mul
        ((DN3.contDiff_kernel N).comp contDiff_snd))
  have hkz : ∀ z ∈ closedBall z₀ δ, ∀ ξ, k (z, ξ) = w z ξ / m z := by
    intro z hz ξ
    simp [hkdef, hk₀def, hγ1 z hz]
  -- the domain
  set O := ball z₀ δ with hOdef
  have hOt : O ⊆ e.val.target := ball_subset_closedBall.trans (hK₂.trans hU₁t)
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set t₁ := δ / R with ht₁def
  have hsample : ∀ z ∈ O, ∀ ξ : E, ‖ξ‖ ≤ R → ∀ t : ℝ, 0 < t → t < t₁ →
      ((z, t • ξ) : E × E) ∈ ball ((z₀, 0) : E × E) δ := by
    intro z hz ξ hξ t ht0 ht
    rw [← ball_prod_same]
    refine ⟨hz, ?_⟩
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have h1 : t * R < δ := by rwa [ht₁def, lt_div_iff₀ hR] at ht
    exact (mul_le_mul_of_nonneg_left hξ ht0.le).trans_lt h1
  refine ⟨e, G, k, R, O, t₁, hx₀, mem_ball_self hδ, ?_⟩
  refine
    { smooth := hGs
      zero := hG0
      weight_smooth := hks
      radius_pos := hR
      weight_supp := ?_
      weight_even := ?_
      weight_mass := ?_
      isOpen := isOpen_ball
      subset := hOt
      pos := div_pos hδ hR
      eq := ?_
      laplacian := ?_ }
  · -- support
    intro z ξ hξ
    have hk1 : DN3.kernel N ξ = 0 :=
      DN3.kernel_eq_zero N ((le_max_right _ _).trans hξ.le)
    by_cases hz : z ∈ U₁
    · have hw : w z ξ = 0 := by
        by_contra hw
        have := hR₁ z hz ξ hw
        linarith [le_max_left R₁ 1]
      simp [hkdef, hk₀def, hw, hk1]
    · have hγ0 : γ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hγU h)
      simp [hkdef, hγ0, hk1]
  · -- evenness
    intro z ξ
    simp only [hkdef, hk₀def, hwdef, fibreWeight_neg, DN3.kernel, norm_neg]
  · -- mass one
    intro z hz
    have hzc : z ∈ closedBall z₀ δ := ball_subset_closedBall hz
    have hzU : z ∈ U₁ := hK₂ hzc
    rw [integral_congr_ae (Eventually.of_forall fun ξ => hkz z hzc ξ), integral_div]
    exact div_self (hmpos z hzU).ne'
  · -- the representation
    intro g z hz t ht0 ht
    have hzt : z ∈ e.val.target := hOt hz
    have hzc : z ∈ closedBall z₀ δ := ball_subset_closedBall hz
    rw [DN5.smoothing_eq_chartSmoothing_symm A hzt g t, DN5.chartSmoothing, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hkz z hzc ξ]
    by_cases hw : w z ξ = 0
    · simp [hwdef] at hw ⊢
      simp [hw]
    · have hξ : ‖ξ‖ ≤ R := (hR₁ z (hK₂ hzc) ξ hw).trans (le_max_left _ _)
      have hq := hsample z hz ξ hξ t ht0 ht
      have hqg := hK₁ (ball_subset_closedBall hq)
      rw [hGΦ _ (ball_subset_closedBall hq)]
      simp only [hΦdef]
      rw [e.val.left_inv (DN5.goodSet_target A hqg).2]
      simp only [hwdef]
      ring
  · -- the Laplacian
    intro h hh z hz
    have hzt : z ∈ e.val.target := hOt hz
    have hzc : z ∈ closedBall z₀ δ := ball_subset_closedBall hz
    -- near `(z, 0)`, `G = Φ`
    have hV : IsOpen {η : E | ((z, η) : E × E) ∈ ball ((z₀, 0) : E × E) δ} :=
      isOpen_ball.preimage (continuous_const.prodMk continuous_id)
    have h0V : (0 : E) ∈ {η : E | ((z, η) : E × E) ∈ ball ((z₀, 0) : E × E) δ} := by
      show ((z, 0) : E × E) ∈ ball ((z₀, 0) : E × E) δ
      rw [← ball_prod_same]
      exact ⟨hz, mem_ball_self hδ⟩
    have hloc : ∀ η ∈ {η : E | ((z, η) : E × E) ∈ ball ((z₀, 0) : E × E) δ},
        (fun η => G (z, η)) =ᶠ[𝓝 η] Φ z := by
      intro η hη
      filter_upwards [hV.mem_nhds hη] with η' hη'
      exact hGΦ _ (ball_subset_closedBall hη')
    have hGη : fderiv ℝ (fun η => G (z, η)) 0 = ContinuousLinearMap.id ℝ E := by
      rw [(hloc 0 h0V).fderiv_eq]
      exact hΦ.fderiv_zero z (hK₁ (ball_subset_closedBall h0V))
    have hhol : ∀ᶠ η in 𝓝 (0 : E), DifferentiableAt ℂ (fun η => G (z, η)) η := by
      filter_upwards [hV.mem_nhds h0V] with η hη
      exact (hΦ.holo (z, η) (hK₁ (ball_subset_closedBall hη))).congr_of_eventuallyEq (hloc η hη)
    exact weightSecondCoeff_eq_chartLaplacian wY e hzt (hGs.of_le (WithTop.coe_le_coe.mpr le_top))
      (hG0 z) hGη hhol (hks.of_le (WithTop.coe_le_coe.mpr le_top)) (hkz z hzc)
      (hh.of_le (WithTop.coe_le_coe.mpr le_top))

universe v

/-- **The generator of the joint smoothing** (FPT `eq:chern-smoothing-generator`) for the
smoothing `SGPT.NPP.DN5.smoothing` of lane DN5: the `GeneratorEstimate`, i.e. the
`generator` field of `SGPT.NPP.DN2.IsJointSmoothing`, with `a = ∫ -χ₁(‖ζ‖²) dζ`. -/
theorem generatorEstimate : DN5.GeneratorEstimate.{v} := by
  intro N Y _ _ _ _ _ _ wY A
  obtain ⟨r₀, hr⟩ := DN5.exists_isUniformRadius wY A
  have hcont : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → ∀ t : ℝ, 0 < t → t < r₀ →
      Continuous fun x => DN5.smoothing wY A g x t := fun g hg t ht0 ht =>
    continuous_of_contDiffOn_charts (fun e => DN5.smoothing_contDiffOn hr hg e) ht0 ht
  exact generator_of_isChartAverage wY (integral_neg_chiOne_pos N) hr.1
    (isChartAverage_smoothing wY A) hcont
    (fun g g' hg hg' hle x t ht0 ht => DN5.smoothing_mono hr hg hg' hle x ht0 ht)

end SGPT.NPP.DN6
