import SGPT.NPP.DN8Flat
import SGPT.Envelopes.LapClass2Chart
import SGPT.Envelopes.LapClassKahlerClass

/-!
# Local smooth approximants with bounded Levi forms, in a chart of the modification

Lane DN8, `thm:DNT23_C11bar` (transfer step of FPT `thm:big-metric-laplacian-rooftop`).
Let `(Y, ω)` be a compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form, `u` a
`θ`-plurisubharmonic function that is finite on an open set `U` and lies in `C^{1,1̄}_ω(U)`
(`HasBoundedMetricLaplacianOn`, continuous with bounded distributional `ω`-Laplacian on the compact
subsets of `U`).  Then near every point `y₀ ∈ U`, in the chart at `y₀`, `u` is the uniform limit of
smooth functions `a_j` whose Levi forms are bounded uniformly in `j`:
`|∂_ξ∂̄_ξ a_j| ≤ K |ξ|²` (`exists_chart_approximants`).

The proof reads the distributional bound in the chart (`integral_mul_laplacian_chartExtend`, with
Tietze's extension theorem since `u` is only continuous on `U`), turns Green's identity on `Y` into
the symmetry of the chart operator `V Δ_e` (`integral_chartLaplacian_symm`), and applies
`DN8Flat` to the plurisubharmonic function `u ∘ e⁻¹ + ρ`, `ρ` a smooth local potential of `θ`:
`a_j = (u ∘ e⁻¹ + ρ) * κ_j - ρ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal ComplexOrder

namespace SGPT.NPP.DN8

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart SGPT.Foundations.Analysis.Pending.ChartPartition
open SGPT.Foundations.Analysis.Pending.ClosedTopCurrents SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11 SGPT.Analysis.CZLp SGPT.Envelopes.LapClass

/-! ### Cutoffs -/

theorem contDiff_mul_of_tsupport_subset {n : ℕ} {ζ f : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hζ : ContDiff ℝ ∞ ζ) (hζU : tsupport ζ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun z => ζ z * f z) := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : z ∈ U
  · exact hζ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hz))
  · have hzt : z ∉ tsupport ζ := fun h => hz (hζU h)
    have h : (fun z => ζ z * f z) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem ((isClosed_tsupport ζ).isOpen_compl.mem_nhds hzt) fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy]
    exact contDiffAt_const.congr_of_eventuallyEq h

theorem plurisubharmonicOn_congr_open' {n : ℕ} {u w : ComplexModel n → EReal}
    {V : Set (ComplexModel n)} (hV : IsOpen V) (hu : PlurisubharmonicOn u V) (heq : EqOn u w V) :
    PlurisubharmonicOn w V := by
  intro x hx
  obtain ⟨U', hU', hxU', hdisc⟩ := hu x hx
  exact ⟨U' ∩ V, hU'.inter hV, ⟨hxU', hx⟩, (hdisc.mono inter_subset_left).congr
    fun y hy => heq hy.2⟩

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-! ### Green's identity and the distributional pairing, read in a chart -/

/-- **Green's identity in a chart**: `∫ f V Δ_e φ = ∫ φ V Δ_e f` for `φ` a test function
supported in `B̄(z₀, r₁)` and `f` smooth on `B(z₀, r₂)`, `r₁ < r₂`, `B̄(z₀, r₂)` in the chart. -/
theorem integral_chartLaplacian_symm (w : KahlerBackground (m + 1) Y)
    (e : ComplexChart (m + 1) Y) {z₀ : ComplexModel (m + 1)} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (hr : r₁ < r₂) (hB : closedBall z₀ r₂ ⊆ e.val.target) {f φ : ComplexModel (m + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball z₀ r₂)) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφK : tsupport φ ⊆ closedBall z₀ r₁) :
    ∫ z, f z * (volDensity w e z * chartLaplacian w.form.val e φ z) =
      ∫ z, φ z * (volDensity w e z * chartLaplacian w.form.val e f z) := by
  let ζ : ContDiffBump z₀ := ⟨(2 * r₁ + r₂) / 3, (r₁ + 2 * r₂) / 3, by linarith, by linarith⟩
  set g : ComplexModel (m + 1) → ℝ := fun z => ζ z * f z with hgdef
  have hζt : tsupport ζ ⊆ ball z₀ r₂ := by
    rw [ζ.tsupport_eq]
    exact closedBall_subset_ball (by show (r₁ + 2 * r₂) / 3 < r₂; linarith)
  have hg : ContDiff ℝ ∞ g := contDiff_mul_of_tsupport_subset isOpen_ball ζ.contDiff hζt hf
  have hgc : HasCompactSupport g := ζ.hasCompactSupport.mul_right
  have hgt : tsupport g ⊆ e.val.target :=
    (tsupport_mul_subset_left).trans (hζt.trans (ball_subset_closedBall.trans hB))
  have hφt : tsupport φ ⊆ e.val.target :=
    hφK.trans ((closedBall_subset_closedBall hr.le).trans hB)
  have hχg := chartSmooth_chartExtend e hg hgc.isCompact hgt
  have hχφ := chartSmooth_chartExtend e hφ hφc.isCompact hφt
  have hG := integral_mul_laplacian_comm w hχg hχφ
  rw [integral_mul_laplacian_chartExtend w e hφ hφc hφt
      (YauUniformEstimate.continuous_of_chartSmooth hχg),
    integral_mul_laplacian_chartExtend w e hg hgc hgt
      (YauUniformEstimate.continuous_of_chartSmooth hχφ)] at hG
  have hone : ∀ z ∈ ball z₀ ((2 * r₁ + r₂) / 3), ζ z = 1 := fun z hz =>
    ζ.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hφin : tsupport φ ⊆ ball z₀ ((2 * r₁ + r₂) / 3) :=
    hφK.trans (closedBall_subset_ball (by linarith))
  calc ∫ z, f z * (volDensity w e z * chartLaplacian w.form.val e φ z)
      = ∫ z, chartExtend e g (e.val.symm z) *
          (volDensity w e z * chartLaplacian w.form.val e φ z) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ tsupport φ
        · show f z * _ = chartExtend e g (e.val.symm z) * _
          rw [chartExtend_of_mem (e.val.map_target (hφt hz)), e.val.right_inv (hφt hz), hgdef]
          simp only
          rw [hone z (hφin hz), one_mul]
        · show f z * _ = chartExtend e g (e.val.symm z) * _
          rw [chartLaplacian_eq_zero_of_notMem_tsupport _ _ hz]
          simp
    _ = ∫ z, chartExtend e φ (e.val.symm z) *
          (volDensity w e z * chartLaplacian w.form.val e g z) := hG
    _ = ∫ z, φ z * (volDensity w e z * chartLaplacian w.form.val e f z) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hzt : z ∈ e.val.target
        · show chartExtend e φ (e.val.symm z) * _ = φ z * _
          rw [chartExtend_of_mem (e.val.map_target hzt), e.val.right_inv hzt]
          by_cases hz : z ∈ tsupport φ
          · have hev : g =ᶠ[𝓝 z] f := by
              filter_upwards [isOpen_ball.mem_nhds (hφin hz)] with y hy
              rw [hgdef]
              simp only
              rw [hone y hy, one_mul]
            simp only [chartLaplacian]
            rw [complexHessian_congr' hev]
          · rw [image_eq_zero_of_notMem_tsupport hz]
            simp
        · have hzg : z ∉ tsupport g := fun h => hzt (hgt h)
          have hzφ : z ∉ tsupport φ := fun h => hzt (hφt h)
          show chartExtend e φ (e.val.symm z) * _ = φ z * _
          rw [chartLaplacian_eq_zero_of_notMem_tsupport _ _ hzg, image_eq_zero_of_notMem_tsupport hzφ]
          simp

/-- **The pairing with `Δ_ω` read in a chart, for a function continuous on the support** (Tietze). -/
theorem integral_mul_laplacian_chartExtend_of_continuousOn (w : KahlerBackground (m + 1) Y)
    (e : ComplexChart (m + 1) Y) {φ : ComplexModel (m + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφt : tsupport φ ⊆ e.val.target) {f : Y → ℝ}
    (hf : ContinuousOn f (e.val.symm '' tsupport φ)) :
    ∫ x, f x * laplacian w.form.val (chartExtend e φ) x ∂(kahlerVolume w) =
      ∫ z, f (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z) := by
  set K := e.val.symm '' tsupport φ with hKdef
  have hKc : IsCompact K := hφc.isCompact.image_of_continuousOn (e.val.continuousOn_symm.mono hφt)
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hKc.isClosed ⟨K.domRestrict f, hf.domRestrict⟩
  have hFK : ∀ x ∈ K, F x = f x := fun x hx => by
    have := DFunLike.congr_fun hF ⟨x, hx⟩
    simpa using this
  have h1 := integral_mul_laplacian_chartExtend w e hφ hφc hφt F.continuous
  calc ∫ x, f x * laplacian w.form.val (chartExtend e φ) x ∂(kahlerVolume w)
      = ∫ x, F x * laplacian w.form.val (chartExtend e φ) x ∂(kahlerVolume w) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ K
        · show f x * _ = F x * _
          rw [hFK x hx]
        · show f x * _ = F x * _
          rw [KahlerLaplacianStokes.laplacian_eq_zero_of_notMem_tsupport _
            (fun h => hx (tsupport_chartExtend_subset e hφc hφt h))]
          simp
    _ = ∫ z, F (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z) := h1
    _ = ∫ z, f (e.val.symm z) * (volDensity w e z * chartLaplacian w.form.val e φ z) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ tsupport φ
        · show F (e.val.symm z) * _ = f (e.val.symm z) * _
          rw [hFK _ ⟨z, hz, rfl⟩]
        · show F (e.val.symm z) * _ = f (e.val.symm z) * _
          rw [chartLaplacian_eq_zero_of_notMem_tsupport _ _ hz]
          simp

/-! ### Local approximants -/

omit [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
/-- The continuity facts on the coefficient matrix of a Kähler form in a chart. -/
theorem continuousOn_trace_coeff (w : KahlerBackground (m + 1) Y) (e : ComplexChart (m + 1) Y) :
    ContinuousOn (fun z => (normalizedHermitianMatrix (w.form.val.coeff e z)).trace.re)
      e.val.target := by
  have hlin : Continuous fun A : CoordinateRealTwoForm (m + 1) =>
      (normalizedHermitianMatrix A).trace.re := by
    simp only [normalizedHermitianMatrix, Matrix.trace, Matrix.diag]
    fun_prop
  exact hlin.comp_continuousOn (w.form.val.smooth e).continuousOn

/-- **Local smooth approximants with uniformly bounded Levi forms.**  If `u` is
`θ`-plurisubharmonic, finite on the open set `U`, and `u ∈ C^{1,1̄}_ω(U)`, then at every `y₀ ∈ U`,
in the chart `e` at `y₀`, there are `r > 0` and smooth functions `a_j` on `B(e y₀, r)` converging
uniformly to `u ∘ e⁻¹` on `B̄(e y₀, r/2)` with `|∂_ξ∂̄_ξ a_j| ≤ K |ξ|²` on `B(e y₀, r)`. -/
theorem exists_chart_approximants (w : KahlerBackground (m + 1) Y)
    (θ : SmoothRealForm (m + 1) Y 2) {u : Y → EReal} (hu : ThetaPlurisubharmonic θ u)
    {U : Set Y} (hU : IsOpen U) (hfin : ∀ y ∈ U, u y = ((u y).toReal : EReal))
    (hY : HasBoundedMetricLaplacianOn w U (fun y => (u y).toReal)) {y₀ : Y} (hy₀ : y₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      closedBall ((complexChartAt (n := m + 1) y₀).val y₀) r ⊆
        (complexChartAt (n := m + 1) y₀).val.target ∧
      ∃ (a : ℕ → ComplexModel (m + 1) → ℝ) (K : ℝ), 0 ≤ K ∧
        (∀ j, ContDiffOn ℝ ∞ (a j) (ball ((complexChartAt (n := m + 1) y₀).val y₀) r)) ∧
        TendstoUniformlyOn a
          (fun z => (u ((complexChartAt (n := m + 1) y₀).val.symm z)).toReal) atTop
          (closedBall ((complexChartAt (n := m + 1) y₀).val y₀) (r / 2)) ∧
        ∀ j, ∀ z ∈ ball ((complexChartAt (n := m + 1) y₀).val y₀) r, ∀ ξ : ComplexModel (m + 1),
          |leviForm (a j) z ξ| ≤ K * ‖ξ‖ ^ 2 := by
  set e := complexChartAt (n := m + 1) y₀ with hedef
  set z₀ := e.val y₀ with hz₀def
  have hy₀e : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hy₀e
  obtain ⟨W, ρ, hz₀W, hρ, hpshW⟩ := hu e z₀ hz₀
  -- a ball inside `W ∩ e(U)`
  set O := W ∩ (e.val.target ∩ e.val.symm ⁻¹' U) with hOdef
  have hO : IsOpen O := hρ.1.inter (e.val.isOpen_inter_preimage_symm hU)
  have hz₀O : z₀ ∈ O := ⟨hz₀W, hz₀, by simp only [mem_preimage, hz₀def, e.val.left_inv hy₀e]; exact hy₀⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO z₀ hz₀O
  set R := ε / 10 with hRdef
  have hR : 0 < R := by positivity
  have hB9 : closedBall z₀ (9 * R) ⊆ O := (closedBall_subset_ball (by linarith)).trans hεO
  have hB9W : closedBall z₀ (9 * R) ⊆ W := hB9.trans inter_subset_left
  have hB9t : closedBall z₀ (9 * R) ⊆ e.val.target := hB9W.trans hρ.2.1
  have hB9U : ∀ z ∈ closedBall z₀ (9 * R), e.val.symm z ∈ U := fun z hz => (hB9 hz).2.2
  set Ω : Opens (ComplexModel (m + 1)) := ⟨ball z₀ (9 * R), isOpen_ball⟩ with hΩdef
  have hΩ : (Ω : Set (ComplexModel (m + 1))) = ball z₀ (9 * R) := rfl
  have hΩB : (Ω : Set (ComplexModel (m + 1))) ⊆ closedBall z₀ (9 * R) := ball_subset_closedBall
  set f : Y → ℝ := fun y => (u y).toReal with hfdef
  set v : ComplexModel (m + 1) → ℝ := fun z => f (e.val.symm z) + ρ z with hvdef
  have hfc : ContinuousOn (fun z => f (e.val.symm z)) (closedBall z₀ (9 * R)) :=
    hY.1.comp (e.val.continuousOn_symm.mono hB9t) fun z hz => hB9U z hz
  have hρc : ContinuousOn ρ (closedBall z₀ (9 * R)) := hρ.2.2.1.continuousOn.mono hB9W
  have hvc : ContinuousOn v Ω := (hfc.add hρc).mono hΩB
  -- plurisubharmonicity of `v`
  have hvpsh : IsLocallyBoundedPshOn Ω v := by
    refine ⟨?_, fun z hz => ?_⟩
    · refine plurisubharmonicOn_congr_open' Ω.isOpen (hpshW.mono (hΩB.trans hB9W)) fun z hz => ?_
      simp only [chartFunction, hvdef, hfdef, EReal.coe_add]
      rw [← hfin _ (hB9U z (hΩB hz))]
    · obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen z hz
      have hcb : closedBall z (δ / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hδΩ
      obtain ⟨C, -, hC⟩ := exists_le_of_continuousOn (isCompact_closedBall z (δ / 2))
        (hvc.mono hcb)
      exact ⟨⟨ball z (δ / 2), isOpen_ball⟩, mem_ball_self (by linarith),
        ball_subset_closedBall.trans hcb, C, fun y hy => hC y (ball_subset_closedBall hy)⟩
  -- the metric data
  set N : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    fun z => normalizedHermitianMatrix (w.form.val.coeff e z) with hNdef
  set V : ComplexModel (m + 1) → ℝ := volDensity w e with hVdef
  have hΩt : (Ω : Set (ComplexModel (m + 1))) ⊆ e.val.target := hΩB.trans hB9t
  have hNpd : ∀ z ∈ Ω, (N z).PosDef := fun z hz => posDef_coeff w.isKahler.1 (hΩt hz)
  have hNc : ContinuousOn (fun z => (N z).trace.re) Ω := (continuousOn_trace_coeff w e).mono hΩt
  have hNi : ContinuousOn (fun z => (N z)⁻¹) Ω :=
    (SGPT.Envelopes.LapClass3.continuousOn_inv_coeff w e).mono hΩt
  have hVc : ContinuousOn V Ω := (continuousOn_volDensity w e).mono hΩt
  have hVpos : ∀ z ∈ Ω, 0 < V z := fun z hz => volDensity_pos w e (hΩt hz)
  have hpl : ∀ φ z, pairLap N φ z = chartLaplacian w.form.val e φ z := fun _ _ => rfl
  have hR3 : (0 : ℝ) < 3 * R := by positivity
  have hsym : ∀ f' : ComplexModel (m + 1) → ℝ, ContDiff ℝ ∞ f' → ∀ φ : ComplexModel (m + 1) → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ closedBall z₀ (3 * R) →
        ∫ z, f' z * (V z * pairLap N φ z) = ∫ z, φ z * (V z * pairLap N f' z) := by
    intro f' hf' φ hφ hφc hφK
    simp only [hpl]
    exact integral_chartLaplacian_symm w e hR3 (by linarith) hB9t hf'.contDiffOn hφ hφc hφK
  -- the distributional bound for `v`
  set KY := e.val.symm '' closedBall z₀ (3 * R) with hKYdef
  have hKYc : IsCompact KY := (isCompact_closedBall _ _).image_of_continuousOn
    (e.val.continuousOn_symm.mono ((closedBall_subset_closedBall (by linarith)).trans hB9t))
  have hKYU : KY ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hB9U z ((closedBall_subset_closedBall (by linarith)) hz)
  obtain ⟨MK, hMK⟩ := hY.2 KY hKYU hKYc
  have hLρW : ContinuousOn (fun z => chartLaplacian w.form.val e ρ z) W := by
    have hH := SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.continuousOn_complexHessian hρ.1
      hρ.2.2.1
    exact Complex.continuous_re.comp_continuousOn ((continuous_id.matrix_trace).comp_continuousOn
      (((SGPT.Envelopes.LapClass3.continuousOn_inv_coeff w e).mono hρ.2.1).mul hH))
  have hB3W : closedBall z₀ (3 * R) ⊆ W :=
    (closedBall_subset_closedBall (by linarith)).trans hB9W
  have hLρ : ContinuousOn (fun z => chartLaplacian w.form.val e ρ z) (closedBall z₀ (3 * R)) :=
    hLρW.mono hB3W
  obtain ⟨Cρ, hCρ0, hCρ⟩ := exists_le_of_continuousOn (isCompact_closedBall _ _) hLρ
  have hbd : ∀ φ : ComplexModel (m + 1) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ closedBall z₀ (3 * R) → (∀ z, 0 ≤ φ z) →
        ∫ z, v z * (V z * pairLap N φ z) ≤ (MK + Cρ) * ∫ z, V z * φ z := by
    intro φ hφ hφc hφK hφ0
    have hφt : tsupport φ ⊆ e.val.target :=
      hφK.trans ((closedBall_subset_closedBall (by linarith)).trans hB9t)
    have hφΩ : tsupport φ ⊆ ball z₀ (9 * R) := hφK.trans (closedBall_subset_ball (by linarith))
    have hG : Continuous fun z => V z * pairLap N φ z :=
      continuous_mul_pairLap_self Ω.isOpen hNi hVc hφ hφΩ
    have hG0 : ∀ x ∉ tsupport φ, V x * pairLap N φ x = 0 := fun x hxt => by
      rw [hpl, chartLaplacian_eq_zero_of_notMem_tsupport _ _ hxt, mul_zero]
    have hGs : HasCompactSupport fun z => V z * pairLap N φ z :=
      hφc.mono' fun x hx => by
        by_contra hxt
        exact hx (hG0 x hxt)
    have hGK : tsupport (fun z => V z * pairLap N φ z) ⊆ ball z₀ (9 * R) := by
      refine (closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)).trans hφΩ
      by_contra hxt
      exact hx (hG0 x hxt)
    have hi1 : Integrable fun z => f (e.val.symm z) * (V z * pairLap N φ z) :=
      integrable_mul_of_continuousOn isOpen_ball (hfc.mono ball_subset_closedBall) hG hGs hGK
    have hi2 : Integrable fun z => ρ z * (V z * pairLap N φ z) :=
      integrable_mul_of_continuousOn isOpen_ball (hρc.mono ball_subset_closedBall) hG hGs hGK
    have hsplit : ∫ z, v z * (V z * pairLap N φ z) =
        (∫ z, f (e.val.symm z) * (V z * pairLap N φ z)) + ∫ z, ρ z * (V z * pairLap N φ z) := by
      rw [← integral_add hi1 hi2]
      congr 1; funext z; simp only [hvdef]; ring
    -- the first term
    have hχ := chartSmooth_chartExtend e hφ hφc.isCompact hφt
    have himg : e.val.symm '' tsupport φ ⊆ KY := image_mono hφK
    have h1 : ∫ z, f (e.val.symm z) * (V z * pairLap N φ z) ≤ MK * ∫ z, V z * φ z := by
      have hpair := integral_mul_laplacian_chartExtend_of_continuousOn w e hφ hφc hφt
        (f := f) (hY.1.mono (himg.trans hKYU))
      have hvol := integral_comp_chartExtend w e hφ hφc hφt (F := id) continuous_id rfl
      simp only [id] at hvol
      have hb := hMK (chartExtend e φ) hχ (chartExtend_nonneg hφ0)
        ((tsupport_chartExtend_subset e hφc hφt).trans himg)
      rw [hpair, hvol] at hb
      simp only [hpl]
      exact (le_abs_self _).trans hb
    -- the second term
    have hφc' : Continuous φ := hφ.continuous
    have hVφ : Continuous fun z => V z * φ z :=
      continuous_mul_of_continuousOn_of_tsupport Ω.isOpen hVc hφc' hφΩ
    have h2 : ∫ z, ρ z * (V z * pairLap N φ z) ≤ Cρ * ∫ z, V z * φ z := by
      have hs := integral_chartLaplacian_symm w e hR3 (by linarith : 3 * R < 9 * R) hB9t
        (f := ρ) (hρ.2.2.1.mono (ball_subset_closedBall.trans hB9W)) hφ hφc hφK
      simp only [hpl]
      rw [hs, ← integral_const_mul]
      have hVL : ContinuousOn (fun z => V z * chartLaplacian w.form.val e ρ z) (ball z₀ (9 * R)) :=
        hVc.mul (hLρW.mono (ball_subset_closedBall.trans hB9W))
      have hi : Integrable fun z => φ z * (V z * chartLaplacian w.form.val e ρ z) :=
        (integrable_mul_of_continuousOn isOpen_ball hVL hφc' hφc hφΩ).congr
          (Eventually.of_forall fun z => mul_comm _ _)
      refine integral_mono hi ((continuous_const.mul hVφ).integrable_of_hasCompactSupport
        hφc.mul_left.mul_left) fun z => ?_
      by_cases hz : z ∈ tsupport φ
      · have hzK := hφK hz
        have hVz := hVpos z (closedBall_subset_ball (by linarith) hzK)
        have hb := (abs_le.mp (hCρ z hzK)).2
        have := mul_le_mul_of_nonneg_left hb (mul_nonneg (hφ0 z) hVz.le)
        show φ z * (V z * chartLaplacian w.form.val e ρ z) ≤ Cρ * (V z * φ z)
        nlinarith
      · simp [image_eq_zero_of_notMem_tsupport hz]
    rw [hsplit, add_mul]
    linarith
  -- the flat Levi bound and the mollifications
  have hball8 : closedBall z₀ (8 * R) ⊆ Ω := closedBall_subset_ball (by linarith)
  have hball4 : closedBall z₀ (4 * R) ⊆ Ω := closedBall_subset_ball (by linarith)
  obtain ⟨C, hC0, hflat⟩ := integral_mul_leviForm_le hvpsh hvc hR hball8 hNpd hNc hNi hVc hVpos
    hsym hbd
  -- the Hessian of `ρ` on `B̄(z₀, 2R)`
  have hB2W : closedBall z₀ (2 * R) ⊆ W :=
    (closedBall_subset_closedBall (by linarith)).trans hB9W
  have hHρ := SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.continuousOn_complexHessian hρ.1
    hρ.2.2.1
  have hHs : ContinuousOn (fun z => ∑ p, ∑ q, ‖complexHessian ρ z p q‖) (closedBall z₀ (2 * R)) :=
    (continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun q _ =>
      ((continuous_id.matrix_elem p q).comp_continuousOn hHρ).norm).mono hB2W
  obtain ⟨Cρ₂, hCρ₂0, hCρ₂⟩ := exists_le_of_continuousOn (isCompact_closedBall _ _) hHs
  refine ⟨2 * R, by positivity, (closedBall_subset_closedBall (by linarith)).trans hB9t,
    fun j z => ContactLocal.mollified v z₀ R hR j z - ρ z, C + Cρ₂, by positivity,
    fun j => ((ContactLocal.contDiff_mollified hvpsh hball4 hR j).contDiffOn).sub
      (hρ.2.2.1.mono (ball_subset_closedBall.trans hB2W)), ?_, ?_⟩
  · have hU := tendstoUniformlyOn_mollified hvpsh hvc hR hball4
    rw [show 2 * R / 2 = R by ring]
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro δ hδ
    filter_upwards [hU δ hδ] with j hj z hz
    have := hj z hz
    rw [Real.dist_eq] at this ⊢
    simp only [hvdef, hfdef] at this
    convert this using 2
    ring
  · intro j z hz ξ
    have hzB : z ∈ closedBall z₀ (2 * R) := ball_subset_closedBall hz
    have hm2 : ContDiffAt ℝ 2 (ContactLocal.mollified v z₀ R hR j) z :=
      (contDiff_two_of_contDiff (ContactLocal.contDiff_mollified hvpsh hball4 hR j)).contDiffAt
    have hρ2 : ContDiffAt ℝ 2 ρ z :=
      ((hρ.2.2.1.contDiffAt (hρ.1.mem_nhds (hB2W hzB))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    rw [leviForm_sub' hm2 hρ2]
    obtain ⟨h0, h1⟩ := leviForm_mollified_le hvpsh hR hball4 hflat j hz ξ
    have hq := abs_hermQuad_le (complexHessian ρ z) ξ
    rw [hermQuad_complexHessian hρ2] at hq
    have hsum := (le_abs_self _).trans (hCρ₂ z hzB)
    have h3 : |leviForm ρ z ξ| ≤ Cρ₂ * ‖ξ‖ ^ 2 :=
      hq.trans (mul_le_mul_of_nonneg_right hsum (sq_nonneg _))
    rw [abs_le] at h3 ⊢
    constructor <;> nlinarith

end SGPT.NPP.DN8
