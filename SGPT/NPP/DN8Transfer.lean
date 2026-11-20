import SGPT.NPP.DN8Chart
import SGPT.NPP.DN2LogChart
import SGPT.NPP.LocalMetricLaplacianLimits

/-!
# Transfer of a bounded metric Laplacian through a holomorphic section

Lane DN8, `thm:DNT23_C11bar`: the last step of FPT `thm:big-metric-laplacian-rooftop`
(`chapters/inputs/q10-big-envelope-regularity.tex`): "we may therefore work on `Y` ... and return
through the isomorphism over `X ∖ Z` at the end".

Let `(X, ω)`, `(Y, ω_Y)` be compact Kähler manifolds of the same dimension, `u` a `θ`-psh function
on `Y`, finite on an open set `U ⊆ Y` with `u ∈ C^{1,1̄}_{ω_Y}(U)`, and `s : O → Y` a holomorphic
map on an open set `O ⊆ X` with `s(O) ⊆ U` (for a modification `π : Y → X` biholomorphic over
`O = X ∖ nK`, `s = π⁻¹`).  Then `f = u ∘ s` lies in `C^{1,1̄}_ω(O)`
(`hasBoundedMetricLaplacianOn_of_holomorphic_section`).

Bounded metric Laplacian depends on the Kähler form in general; here it transfers because `u` is
quasi-plurisubharmonic: near each point `u` is the uniform limit of smooth functions with uniformly
bounded Levi forms (`exists_chart_approximants`), Levi forms are natural under holomorphic maps
(`leviForm_comp_holomorphic`), and smooth local limits with bounded Laplacians give the
distributional bound (`hasBoundedMetricLaplacianOn_of_local_smooth_limits`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Manifold ComplexOrder

namespace SGPT.NPP.DN8

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart SGPT.Foundations.Analysis.Pending.ChartPartition
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Envelopes.LapClass

variable {m : ℕ} {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

/-- A holomorphic map on an open set is holomorphic in charts. -/
theorem contDiffAt_chart_comp_of_contMDiffOn {s : X → Y} {O : Set X} (hO : IsOpen O)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ s O)
    (e : ComplexChart (m + 1) X) (d : ComplexChart (m + 1) Y) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target) (hzO : e.val.symm z ∈ O) (hzd : s (e.val.symm z) ∈ d.val.source) :
    ContDiffAt ℂ ∞ (fun z => d.val (s (e.val.symm z))) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas e.property)
    (IsManifold.subset_maximalAtlas d.property)
    (e.val.map_target hz) hzd).mp (hs.contMDiffAt (hO.mem_nhds hzO))
  simpa [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    e.val.right_inv hz, contDiffWithinAt_univ, Function.comp_def] using h.2

/-- **The chart Laplacian of `a ∘ Φ`** for a holomorphic `Φ` and a Levi bound on `a`. -/
theorem abs_chartLaplacian_comp_le {g : SmoothRealForm (m + 1) X 2} (hg : g.IsHermitian)
    (e : ComplexChart (m + 1) X) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target)
    {Φ : ComplexModel (m + 1) → ComplexModel (m + 1)} (hΦ : ContDiffAt ℂ ∞ Φ z)
    {a : ComplexModel (m + 1) → ℝ} (ha : ContDiffAt ℝ 2 a (Φ z)) {K : ℝ} (hK : 0 ≤ K)
    (hlevi : ∀ ξ, |leviForm a (Φ z) ξ| ≤ K * ‖ξ‖ ^ 2) :
    |chartLaplacian g e (fun z => a (Φ z)) z| ≤
      K * ‖fderiv ℂ Φ z‖ ^ 2 * ((normalizedHermitianMatrix (g.coeff e z))⁻¹).trace.re := by
  have hP := (posDef_coeff hg hz).inv.posSemidef
  obtain ⟨k, wv, hwv, htr⟩ := exists_trace_eq_sum_leviForm hP
  have hΦ2 : ContDiffAt ℂ 2 Φ z := hΦ.of_le two_le_infty
  have hcomp2 : ContDiffAt ℝ 2 (fun z => a (Φ z)) z :=
    ha.comp z ((hΦ2.restrict_scalars ℝ))
  rw [chartLaplacian, hwv _ _ hcomp2, htr, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [SGPT.NPP.DN2.leviForm_comp_holomorphic hΦ2 ha]
  refine (hlevi _).trans ?_
  have h1 := (fderiv ℂ Φ z).le_opNorm (wv i)
  have h2 : ‖fderiv ℂ Φ z (wv i)‖ ^ 2 ≤ (‖fderiv ℂ Φ z‖ * ‖wv i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc K * ‖fderiv ℂ Φ z (wv i)‖ ^ 2 ≤ K * (‖fderiv ℂ Φ z‖ * ‖wv i‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 hK
    _ = K * ‖fderiv ℂ Φ z‖ ^ 2 * ‖wv i‖ ^ 2 := by ring

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- **Transfer of `C^{1,1̄}` through a holomorphic section.**  If `u` is `θ`-psh on `Y`, finite on
the open set `U`, with `u ∈ C^{1,1̄}_{ω_Y}(U)`, and `s` is holomorphic on the open set `O ⊆ X` with
`s(O) ⊆ U`, then `f = u ∘ s ∈ C^{1,1̄}_ω(O)` for every Kähler form `ω` on `X`. -/
theorem hasBoundedMetricLaplacianOn_of_holomorphic_section (w : KahlerBackground (m + 1) X)
    (wY : KahlerBackground (m + 1) Y) (θ : SmoothRealForm (m + 1) Y 2) {u : Y → EReal}
    (hu : ThetaPlurisubharmonic θ u) {U : Set Y} (hU : IsOpen U)
    (hfin : ∀ y ∈ U, u y = ((u y).toReal : EReal))
    (hY : HasBoundedMetricLaplacianOn wY U (fun y => (u y).toReal)) {O : Set X} (hO : IsOpen O)
    {s : X → Y} (hs : ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ s O)
    (hsU : ∀ x ∈ O, s x ∈ U) {f : X → ℝ} (hf : ∀ x ∈ O, f x = (u (s x)).toReal) :
    HasBoundedMetricLaplacianOn w O f := by
  refine DNTBig.hasBoundedMetricLaplacianOn_of_local_smooth_limits w hO fun x hx => ?_
  set y₀ := s x with hy₀def
  obtain ⟨r, hr, hrt, a, K, hK, ha, hconv, hlevi⟩ :=
    exists_chart_approximants wY θ hu hU hfin hY (hsU x hx)
  set eY := complexChartAt (n := m + 1) y₀ with heYdef
  set z₀ := eY.val y₀ with hz₀def
  set eX := complexChartAt (n := m + 1) x with heXdef
  set zx := eX.val x with hzxdef
  have hxX : x ∈ eX.val.source := mem_complexChartAt_source x
  have hy₀Y : y₀ ∈ eY.val.source := mem_complexChartAt_source y₀
  set Φ : ComplexModel (m + 1) → ComplexModel (m + 1) := fun z => eY.val (s (eX.val.symm z))
    with hΦdef
  set D := eX.val.target ∩ eX.val.symm ⁻¹' (O ∩ s ⁻¹' eY.val.source) with hDdef
  have hDo : IsOpen D :=
    eX.val.isOpen_inter_preimage_symm (hs.continuousOn.isOpen_inter_preimage hO eY.val.open_source)
  have hzxD : zx ∈ D := ⟨eX.val.map_source hxX, by
    simp only [mem_preimage, hzxdef, eX.val.left_inv hxX]; exact ⟨hx, hy₀Y⟩⟩
  have hΦhol : ∀ z ∈ D, ContDiffAt ℂ ∞ Φ z := fun z hz =>
    contDiffAt_chart_comp_of_contMDiffOn hO hs eX eY hz.1 hz.2.1 hz.2.2
  have hΦzx : Φ zx = z₀ := by simp only [hΦdef, hzxdef, eX.val.left_inv hxX, hz₀def, hy₀def]
  -- a small ball around `zx`
  have hnhds : D ∩ Φ ⁻¹' ball z₀ (r / 2) ∈ 𝓝 zx := by
    refine Filter.inter_mem (hDo.mem_nhds hzxD) ?_
    have hc : ContinuousAt Φ zx := (hΦhol zx hzxD).continuousAt
    exact hc.preimage_mem_nhds (by rw [hΦzx]; exact isOpen_ball.mem_nhds (mem_ball_self (by linarith)))
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp hnhds
  set ρ' := δ / 3 with hρ'def
  have hρ' : 0 < ρ' := by positivity
  have hBD : closedBall zx (2 * ρ') ⊆ D ∩ Φ ⁻¹' ball z₀ (r / 2) :=
    (closedBall_subset_ball (by linarith)).trans hδD
  have hBD' : ball zx δ ⊆ D := hδD.trans inter_subset_left
  -- the approximants on `X`
  let ζ : ContDiffBump zx := ⟨ρ', 2 * ρ', hρ', by linarith⟩
  have hζt : tsupport ζ ⊆ ball zx δ := by
    rw [ζ.tsupport_eq]
    exact closedBall_subset_ball (by show 2 * ρ' < δ; linarith)
  have hΦc : ContDiffOn ℝ ∞ Φ (ball zx δ) := fun z hz =>
    ((hΦhol z (hBD' hz)).restrict_scalars ℝ).contDiffWithinAt
  have hΦmaps : MapsTo Φ (ball zx δ) (ball z₀ r) := fun z hz =>
    ball_subset_ball (by linarith) (hδD hz).2
  set h : ℕ → ComplexModel (m + 1) → ℝ := fun j z => ζ z * a j (Φ z) with hhdef
  have hh : ∀ j, ContDiff ℝ ∞ (h j) := fun j =>
    contDiff_mul_of_tsupport_subset isOpen_ball ζ.contDiff hζt ((ha j).comp hΦc hΦmaps)
  have hhc : ∀ j, HasCompactSupport (h j) := fun j => ζ.hasCompactSupport.mul_right
  have hht : ∀ j, tsupport (h j) ⊆ eX.val.target := fun j =>
    tsupport_mul_subset_left.trans (hζt.trans (hBD'.trans inter_subset_left))
  set A : ℕ → X → ℝ := fun j => chartExtend eX (h j) with hAdef
  have hA : ∀ j, ChartSmooth (n := m + 1) (A j) := fun j =>
    chartSmooth_chartExtend eX (hh j) (hhc j).isCompact (hht j)
  set V := eX.val.source ∩ eX.val ⁻¹' ball zx ρ' with hVdef
  have hVo : IsOpen V := eX.val.isOpen_inter_preimage isOpen_ball
  have hxV : x ∈ V := ⟨hxX, mem_ball_self hρ'⟩
  have hball : ∀ x' ∈ V, eX.val x' ∈ closedBall zx (2 * ρ') := fun x' hx' =>
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hx'.2
  have hVO : V ⊆ O := fun x' hx' => by
    have h1 : eX.val.symm (eX.val x') ∈ O := (hBD (hball x' hx')).1.2.1
    rwa [eX.val.left_inv hx'.1] at h1
  have hone : ∀ z ∈ ball zx ρ', ζ z = 1 := fun z hz =>
    ζ.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hAV : ∀ j, ∀ x' ∈ V, A j x' = a j (Φ (eX.val x')) := fun j x' hx' => by
    simp only [hAdef, hhdef]
    rw [chartExtend_of_mem hx'.1, hone _ hx'.2, one_mul]
  have hfV : ∀ x' ∈ V, f x' = (u (eY.val.symm (Φ (eX.val x')))).toReal := fun x' hx' => by
    have hsrc : s (eX.val.symm (eX.val x')) ∈ eY.val.source := (hBD (hball x' hx')).1.2.2
    rw [eX.val.left_inv hx'.1] at hsrc
    simp only [hΦdef, eX.val.left_inv hx'.1, eY.val.left_inv hsrc]
    exact hf x' (hVO hx')
  -- the bounds on the compact ball
  have hBc : IsCompact (closedBall zx ρ') := isCompact_closedBall _ _
  have hBρD : closedBall zx ρ' ⊆ D := (closedBall_subset_ball (by linarith)).trans hBD'
  have hDΦ : ContinuousOn (fun z => fderiv ℂ Φ z) D := by
    have hcd : ContDiffOn ℂ ∞ Φ D := fun z hz => (hΦhol z hz).contDiffWithinAt
    exact hcd.continuousOn_fderiv_of_isOpen hDo (by simp)
  obtain ⟨Dm, hDm⟩ := hBc.exists_bound_of_continuousOn (hDΦ.mono hBρD)
  have htrc : ContinuousOn
      (fun z => ((normalizedHermitianMatrix (w.form.val.coeff eX z))⁻¹).trace.re)
      (closedBall zx ρ') :=
    Complex.continuous_re.comp_continuousOn ((continuous_id.matrix_trace).comp_continuousOn
      ((SGPT.Envelopes.LapClass3.continuousOn_inv_coeff w eX).mono
        (hBρD.trans inter_subset_left)))
  obtain ⟨Tm, hTm0, hTm⟩ := exists_le_of_continuousOn hBc htrc
  refine ⟨V, hVo, hxV, hVO, A, hA, ?_, K * Dm ^ 2 * Tm, by positivity, fun j x' hx' => ?_⟩
  · -- uniform convergence on `V`
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with j hj x' hx'
    rw [hAV j x' hx', hfV x' hx']
    exact hj _ (ball_subset_closedBall (hBD (hball x' hx')).2)
  · -- the Laplacian bound on `V`
    have hz : eX.val x' ∈ eX.val.target := eX.val.map_source hx'.1
    have hzB : eX.val x' ∈ ball zx ρ' := hx'.2
    have hzD : eX.val x' ∈ D := hBρD (ball_subset_closedBall hzB)
    rw [laplacian_eq w.isKahler.1 (chartSmooth_two' (hA j)) hx'.1]
    have hev : (fun z => A j (eX.val.symm z)) =ᶠ[𝓝 (eX.val x')] fun z => a j (Φ z) := by
      filter_upwards [(isOpen_ball.inter eX.val.open_target).mem_nhds ⟨hzB, hz⟩] with z hz'
      simp only [hAdef, hhdef]
      rw [chartExtend_of_mem (eX.val.map_target hz'.2), eX.val.right_inv hz'.2, hone z hz'.1,
        one_mul]
    have hlap : chartLaplacian w.form.val eX (fun z => A j (eX.val.symm z)) (eX.val x') =
        chartLaplacian w.form.val eX (fun z => a j (Φ z)) (eX.val x') := by
      simp only [chartLaplacian]
      rw [complexHessian_congr' hev]
    rw [hlap]
    have hΦz : Φ (eX.val x') ∈ ball z₀ r :=
      ball_subset_ball (by linarith) (hBD (hball x' hx')).2
    have ha2 : ContDiffAt ℝ 2 (a j) (Φ (eX.val x')) :=
      (((ha j) _ hΦz).contDiffAt (isOpen_ball.mem_nhds hΦz)).of_le two_le_infty
    refine (abs_chartLaplacian_comp_le w.isKahler.1 eX hz (hΦhol _ hzD) ha2 hK
      (hlevi j _ hΦz)).trans ?_
    have hD1 : ‖fderiv ℂ Φ (eX.val x')‖ ≤ Dm := hDm _ (ball_subset_closedBall hzB)
    have hD2 : ‖fderiv ℂ Φ (eX.val x')‖ ^ 2 ≤ Dm ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hD1 2
    have hT1 := (le_abs_self _).trans (hTm _ (ball_subset_closedBall hzB))
    have hT0 : 0 ≤ ((normalizedHermitianMatrix (w.form.val.coeff eX (eX.val x')))⁻¹).trace.re := by
      have := (posDef_coeff w.isKahler.1 hz).inv.posSemidef.trace_nonneg
      exact (Complex.nonneg_iff.mp this).1
    calc K * ‖fderiv ℂ Φ (eX.val x')‖ ^ 2 *
          ((normalizedHermitianMatrix (w.form.val.coeff eX (eX.val x')))⁻¹).trace.re
        ≤ K * Dm ^ 2 * ((normalizedHermitianMatrix (w.form.val.coeff eX (eX.val x')))⁻¹).trace.re :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 hK) hT0
      _ ≤ K * Dm ^ 2 * Tm := mul_le_mul_of_nonneg_left hT1 (by positivity)

end SGPT.NPP.DN8
