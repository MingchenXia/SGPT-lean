import SGPT.Foundations.Analysis.Pending.RawQuasiPshModificationPointOrderBound
import SGPT.Foundations.Analysis.Pending.FiniteGeneratorExponentialLelongBound
import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.FirstPass.IEnvelope

set_option autoImplicit false

/-! # Raw original ideal order gives the modification point comparison

All finite weighted families and actual source tests are generated internally.
A genuine fixed Jacobian error disappears with the original multiplier level.
No incoming Lelong comparison, order or generator/result certificate.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal NNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawIdealOrderModificationPointComparison

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.IEnvelope DemaillyApproximantDivisorialLelong DivisorialChangeOfVariables

noncomputable section

private theorem multiplierIntegrableAt_congr_borel {n : ℕ}
    (i₁ : MeasurableSpace (ComplexModel n)) (b₁ : @BorelSpace _ _ i₁)
    (i₂ : MeasurableSpace (ComplexModel n)) (b₂ : @BorelSpace _ _ i₂)
    (φ : ComplexModel n → EReal) (c : ℝ) (f : ComplexModel n → ℂ)
    (x : ComplexModel n) :
    (letI := i₁; letI := b₁; MultiplierIntegrableAt φ c f x volume) ↔
      (letI := i₂; letI := b₂; MultiplierIntegrableAt φ c f x volume) := by
  have h₁ : i₁ = borel (ComplexModel n) := b₁.measurable_eq
  have h₂ : i₂ = borel (ComplexModel n) := b₂.measurable_eq
  subst h₁
  subst h₂
  rfl

/-- The finite-reader proof branch internally produces every finite weighted
family and a fixed genuine Jacobian error before all generated levels. -/
theorem exists_level_error_bound_of_iOrder_finite
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hI : IOrderOnManifold (n := m + 1) u v)
    {E : Set Y} {y : Y} (hreg : RegularAtDim (n := m + 1) E y m)
    (hfinite : lelongNumber (n := m + 1) (fun t => u (π t)) y ≠ ⊤) :
    ∃ b : ℕ, ∀ p : ℕ, 0 < p →
      (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => v (π t)) z) ≤
        lelongNumber (n := m + 1) (fun t => u (π t)) y +
          ENNReal.ofReal (2 * ((b : ℝ) + 1) / (p : ℝ)) := by
  classical
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  obtain ⟨Φ, b, _, _, htests⟩ :=
    RawQuasiPshModificationPointOrderBound.exists_jacobian_order_uniform_original_test_bound
      hπ hv hreg
  let d := complexChartAt (n := m + 1) (π y)
  let w := chartFunction u d
  let z₀ := d.val (π y)
  have hwu : QuasiPlurisubharmonicAt w z₀ :=
    hu d z₀ (d.val.map_source (mem_complexChartAt_source (π y)))
  obtain ⟨P, h, ⟨Ω, hΩ, hzΩ, hdisc⟩, hh, heq⟩ := hwu
  have hP : PlurisubharmonicOn P Ω := hdisc.plurisubharmonicOn hΩ
  have hwu' : QuasiPlurisubharmonicAt w z₀ :=
    ⟨P, h, ⟨Ω, hΩ, hzΩ, hdisc⟩, hh, heq⟩
  have hhc : ContinuousAt h z₀ := hh.self_of_nhds.continuousAt
  have hD := Φ.isOpen_flatDomain hπ.1.continuous
  have hpD := Φ.zero_mem_flatDomain π
  have hfd := Φ.differentiableOn_flatCoordMap hπ.1
  have hfT : Tendsto (flatCoordMap π Φ) (𝓝 (0 : ComplexModel (m + 1))) (𝓝 z₀) := by
    simpa only [Φ.flatCoordMap_zero π] using
      (hfd.differentiableAt (hD.mem_nhds hpD)).continuousAt.tendsto
  have hchartgerm : (fun t => w (flatCoordMap π Φ t)) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      (fun t => u (π (Φ.point t))) := by
    filter_upwards [hD.mem_nhds hpD] with t ht
    change u (d.val.symm (flatCoordMap π Φ t)) = u (π (Φ.point t))
    rw [Φ.chartSymm_flatCoordMap π ht]
  have hreaderw : lelongNumber (n := m + 1) (fun t => w (flatCoordMap π Φ t)) 0 =
      lelongNumber (n := m + 1) (fun t => u (π t)) y := by
    rw [LelongNumberComparison.lelongNumber_congr hchartgerm,
      FlattenedGlobalGenericLelongComparison.lelongNumber_comp_point_eq Φ
        (fun t => u (π t)) Φ.zero_mem_target, Φ.point_zero]
  have hcompcont : ContinuousAt (fun t => h (flatCoordMap π Φ t)) 0 :=
    by
      simpa only [ContinuousAt, Function.comp_def, Φ.flatCoordMap_zero π] using hhc.tendsto.comp hfT
  have hreadercorrection : lelongNumber (n := m + 1)
      (fun t => P (flatCoordMap π Φ t)) 0 =
        lelongNumber (n := m + 1) (fun t => u (π t)) y := by
    have heqcomp := hfT.eventually heq
    have hcongr := LelongNumberComparison.lelongNumber_congr (n := m + 1) heqcomp
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
      (boundedRealGermAt_of_continuousAt hcompcont)] at hcongr
    exact hcongr.symm.trans hreaderw
  have hnear : ∀ᶠ t in 𝓝 z₀, |h t - h z₀| < 1 := by
    filter_upwards [hhc (Metric.ball_mem_nhds (h z₀) one_pos)] with t ht
    simpa only [mem_preimage, Metric.mem_ball, Real.dist_eq] using ht
  have hmore : MoreSingularAt P w z₀ := by
    refine ⟨-h z₀ + 1, ?_⟩
    filter_upwards [heq, hnear] with t ht hb
    rw [ht, add_assoc, ← EReal.coe_add]
    refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
    linarith [(abs_lt.mp hb).1]
  refine ⟨b, ?_⟩
  intro p hp
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  obtain ⟨O, hO, hzO, _, N, g, C, hC, hgan, hgL2, hdom⟩ :=
    DemaillyApproximation.exists_weightedL2_generators Ω P hΩ hP z₀ hzΩ p hp
  let F : Fin N → X → ℂ := fun i t => g i (d.val t)
  let G : Fin N → ComplexModel (m + 1) → ℂ :=
    fun i t => F i (d.val.symm (flatCoordMap π Φ t))
  have hGid : ∀ i, G i =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      fun t => g i (flatCoordMap π Φ t) := by
    intro i
    filter_upwards [hD.mem_nhds hpD] with t ht
    change g i (d.val (d.val.symm (flatCoordMap π Φ t))) = g i (flatCoordMap π Φ t)
    have htTarget : flatCoordMap π Φ t ∈ d.val.target := d.val.map_source ht.2
    rw [d.val.right_inv htTarget]
  have hG : ∀ i, ∀ᶠ t in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (G i) t := by
    intro i
    filter_upwards [hfT.eventually (hO.mem_nhds hzO), hD.mem_nhds hpD,
      (hGid i).eventually_nhds] with t htz ht heqi
    exact (((hgan i).differentiableOn.differentiableAt (hO.mem_nhds htz)).comp t
      (hfd.differentiableAt (hD.mem_nhds ht))).congr_of_eventuallyEq heqi
  have hdomG : ∀ᶠ t in 𝓝 (0 : ComplexModel (m + 1)),
      EReal.exp (((p : ℝ) : EReal) * P (flatCoordMap π Φ t)) ≤
        C * ∑ i, ENNReal.ofReal (‖G i t‖ ^ 2) := by
    filter_upwards [hfT.eventually (hO.mem_nhds hzO), Filter.eventually_all.mpr hGid]
      with t ht heqs
    simpa only [heqs, EReal.coe_natCast] using hdom (flatCoordMap π Φ t) ht
  have hreaderG :=
    FiniteGeneratorExponentialLelongBound.lelongNumber_generatorLog_le_scaled_of_exp_domination (n := m + 1)
      G hpr hC hdomG
  rw [hreadercorrection] at hreaderG
  have hGfinite : lelongNumber (n := m + 1) (generatorLog G) 0 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hreaderG
  have hGne : ∃ i, ¬ ∀ᶠ t in 𝓝 (0 : ComplexModel (m + 1)), G i t = 0 := by
    by_contra! hn
    have hzero : ∀ᶠ t in 𝓝 (0 : ComplexModel (m + 1)), generatorLog G t = ⊥ := by
      filter_upwards [Filter.eventually_all.mpr hn] with t ht
      exact (generatorLog_eq_bot_iff G t).mpr ht
    exact hGfinite (LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot
      (hzero.filter_mono nhdsWithin_le_nhds))
  obtain ⟨a, _, ⟨i, hi⟩, hjetbound⟩ :=
    FiniteGeneratorExponentialLelongBound.exists_point_order_le_scaled_of_exp_domination G hG hGne
  have ha : ENNReal.ofReal (2 * (a : ℝ)) ≤ ENNReal.ofReal (p : ℝ) *
      lelongNumber (n := m + 1) (fun t => u (π t)) y := by
    simpa only [hreadercorrection] using
      hjetbound (fun t => P (flatCoordMap π Φ t)) p hpr C hC hdomG
  have hGinon : ∃ᶠ t in 𝓝 (0 : ComplexModel (m + 1)), G i t ≠ 0 := by
    by_contra hn
    have hzero : G i =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [Filter.not_frequently.mp hn] with t ht
      exact not_ne_iff.mp ht
    have hjet := (hzero.iteratedFDeriv (𝕜 := ℂ) a).self_of_nhds
    exact hi (by simpa using hjet)
  have hgnear : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (g i) z := by
    filter_upwards [hO.mem_nhds hzO] with z hz
    exact (hgan i).differentiableOn.differentiableAt (hO.mem_nhds hz)
  have hFhol : HolomorphicAt (m + 1) (F i) (π y) :=
    MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart
      (mem_complexChartAt_source (π y)) hgnear
  have hdT : Tendsto d.val.symm (𝓝 z₀) (𝓝 (π y)) := by
    have ht := d.val.continuousAt_symm (d.val.map_source (mem_complexChartAt_source (π y)))
    rw [ContinuousAt, d.val.left_inv (mem_complexChartAt_source (π y))] at ht
    exact ht
  have hFinon : ∃ᶠ t in 𝓝 (π y), F i t ≠ 0 := by
    by_contra hn
    have hzero : ∀ᶠ t in 𝓝 (π y), F i t = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with t ht
      exact not_ne_iff.mp ht
    have hback := (hdT.comp hfT).eventually hzero
    exact (hGinon.and_eventually hback).exists.elim fun _ ht => ht.1 ht.2
  have hPint : MultiplierIntegrableAt P (p : ℝ) (g i) z₀ volume :=
    ⟨hpr, O, hO, hzO, (hgan i).differentiableOn, hgL2 i⟩
  have huInt : MultiplierIntegrableAt w (p : ℝ) (g i) z₀ volume :=
    multiplierIntegrableAt_of_moreSingularAt hwu' hmore hPint
  have hvInt := hI p hpr d z₀ (d.val.map_source (mem_complexChartAt_source (π y)))
    (g i) (hgan i z₀ hzO) huInt
  have hchartF : g i =ᶠ[𝓝 z₀] fun z => F i (d.val.symm z) := by
    filter_upwards [d.val.open_target.mem_nhds (d.val.map_source (mem_complexChartAt_source (π y)))]
      with z hz
    simp only [F, d.val.right_inv hz]
  have hFmem : (multiplierIdeal (n := m + 1) (p : ℝ) v).mem (π y) (F i) :=
    by
      refine ⟨hFhol, ?_⟩
      exact (multiplierIntegrableAt_congr_borel
        (WithLp.measurableSpace 2 (Fin (m + 1) → ℂ)) inferInstance
        (borel (ComplexModel (m + 1))) ⟨rfl⟩
        (chartFunction v d) p (fun z => F i (d.val.symm z)) z₀).mpr
          (hvInt.congr (EventuallyEq.refl _ _) hchartF)
  obtain ⟨aᵢ, hlowi, _, hboundi⟩ := htests (F i) hFhol hFinon
  have hai : aᵢ ≤ a := by
    by_contra hnot
    exact hi (hlowi a (lt_of_not_ge hnot))
  have hreal : 2 * (a : ℝ) ≤ (p : ℝ) *
      (lelongNumber (n := m + 1) (fun t => u (π t)) y).toReal := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) ha
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (a : ℝ)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hpr.le] using hh
  have hnum : 2 * ((aᵢ : ℝ) + (b : ℝ) + 1) / (p : ℝ) ≤
      (lelongNumber (n := m + 1) (fun t => u (π t)) y).toReal +
        2 * ((b : ℝ) + 1) / (p : ℝ) := by
    have hair : (aᵢ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hai
    apply (div_le_iff₀ hpr).mpr
    rw [add_mul, div_mul_cancel₀ _ hpr.ne']
    nlinarith
  calc
    _ ≤ ENNReal.ofReal (2 * ((aᵢ : ℝ) + (b : ℝ) + 1) / (p : ℝ)) := hboundi p hFmem
    _ ≤ ENNReal.ofReal ((lelongNumber (n := m + 1) (fun t => u (π t)) y).toReal +
        2 * ((b : ℝ) + 1) / (p : ℝ)) := ENNReal.ofReal_le_ofReal hnum
    _ = _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hfinite]

/-- Original raw all-level ideal order gives the whole-divisor point bound;
the finite-reader case and its vanishing error are produced internally. -/
theorem generic_lelong_le_point_of_iOrder
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hI : IOrderOnManifold (n := m + 1) u v)
    {E : Set Y} {y : Y} (hreg : RegularAtDim (n := m + 1) E y m) :
    (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => v (π t)) z) ≤
      lelongNumber (n := m + 1) (fun t => u (π t)) y := by
  classical
  by_cases hfinite : lelongNumber (n := m + 1) (fun t => u (π t)) y = ⊤
  · rw [hfinite]; exact le_top
  obtain ⟨b, hb⟩ := exists_level_error_bound_of_iOrder_finite hπ hu hv hI hreg hfinite
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal
      (2 * ((b : ℝ) + 1) / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    have hreal := (tendsto_const_nhds (x := 2 * ((b : ℝ) + 1))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have ht : Tendsto (fun j : ℕ => 2 * ((b : ℝ) + 1) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using hreal
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hlimadd := (tendsto_const_nhds
    (x := lelongNumber (n := m + 1) (fun t => u (π t)) y)).add hlim
  have hbound : ∀ j : ℕ,
      (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => v (π t)) z) ≤
        lelongNumber (n := m + 1) (fun t => u (π t)) y +
          ENNReal.ofReal (2 * ((b : ℝ) + 1) / ((j : ℝ) + 1)) := by
    intro j
    simpa only [Nat.cast_add, Nat.cast_one] using hb (j + 1) (by omega)
  simpa only [add_zero] using ge_of_tendsto' hlimadd hbound

end
end SGPT.Foundations.Analysis.Pending.RawIdealOrderModificationPointComparison
