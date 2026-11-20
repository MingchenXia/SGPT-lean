import SGPT.Foundations.Analysis.Pending.PositiveIntegerMultiplierOrder
import SGPT.Foundations.Analysis.Pending.PointJetNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealUpperBound

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.IEnvelope DemaillyApproximantDivisorialLelong DivisorialChangeOfVariables
  HironakaHolomorphicJetRankLoci FixedGermNormalOrder PointJetNormalOrder

open Metric MeasureTheory
open scoped ENNReal NNReal

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y} {y : Y}

/-- The literal original member's true germ occurs in the ENTIRE original stalk. -/
theorem originalStalkNormalOrder_le_member
    (Φ : DivisorFlattening (m := m) E y) (A : GermIdeal (m + 1) Y)
    {f : Y → ℂ} (hf : HolomorphicAt (m + 1) f y) (hmem : A.mem y f) :
    originalStalkNormalOrder Φ A ≤ functionNormalOrder Φ f hf := by
  have hg : chartTranslatedGerm y y (mem_chart_source _ y) f hf ∈
      wholeChartStalkIdeal A y y (mem_chart_source _ y) :=
    Ideal.subset_span ⟨f, hf, hmem, rfl⟩
  exact iInf_le (fun g : wholeChartStalkIdeal A y y (mem_chart_source _ y) =>
    normalOrder Φ g.val) ⟨_, hg⟩

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

/-- Every original positive integer has a SAME-weight original member with a
true nonzero flat point jet and the actual raw numerical bound. Finiteness is
only this producer's internal branch, never the whole-ideal theorem's premise. -/
theorem exists_original_member_nonzero_jet_bound_of_finite
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (Φ : DivisorFlattening (m := m) E y) (p : ℕ) (hp : 0 < p)
    (hfinite : lelongNumber (n := m + 1) (fun t => u (π t)) y ≠ ⊤) :
    ∃ (F : X → ℂ) (a : ℕ),
      (multiplierIdeal (n := m + 1) (p : ℝ) u).mem (π y) F ∧
      iteratedFDeriv ℂ a (fun z => F (π (Φ.point z))) (0 : ComplexModel (m + 1)) ≠ 0 ∧
      ENNReal.ofReal (2 * (a : ℝ)) ≤ ENNReal.ofReal (p : ℝ) *
        lelongNumber (n := m + 1) (fun t => u (π t)) y := by
  classical
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
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
  have hgnear : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (g i) z := by
    filter_upwards [hO.mem_nhds hzO] with z hz
    exact (hgan i).differentiableOn.differentiableAt (hO.mem_nhds hz)
  have hFhol : HolomorphicAt (m + 1) (F i) (π y) :=
    MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart
      (mem_complexChartAt_source (π y)) hgnear
  have hPint : MultiplierIntegrableAt P (p : ℝ) (g i) z₀ volume :=
    ⟨hpr, O, hO, hzO, (hgan i).differentiableOn, hgL2 i⟩
  have huInt : MultiplierIntegrableAt w (p : ℝ) (g i) z₀ volume :=
    multiplierIntegrableAt_of_moreSingularAt hwu' hmore hPint
  have hchartF : g i =ᶠ[𝓝 z₀] fun z => F i (d.val.symm z) := by
    filter_upwards [d.val.open_target.mem_nhds (d.val.map_source (mem_complexChartAt_source (π y)))]
      with z hz
    simp only [F, d.val.right_inv hz]
  have hFmem : (multiplierIdeal (n := m + 1) (p : ℝ) u).mem (π y) (F i) :=
    by
      refine ⟨hFhol, ?_⟩
      exact (multiplierIntegrableAt_congr_borel
        (WithLp.measurableSpace 2 (Fin (m + 1) → ℂ)) inferInstance
        (borel (ComplexModel (m + 1))) ⟨rfl⟩
        (chartFunction u d) p (fun z => F i (d.val.symm z)) z₀).mpr
          (huInt.congr (EventuallyEq.refl _ _) hchartF)
  have hGactual : G i =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      fun z => F i (π (Φ.point z)) := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    change F i (d.val.symm (flatCoordMap π Φ z)) = F i (π (Φ.point z))
    rw [Φ.chartSymm_flatCoordMap π hz]
  have hjetactual : iteratedFDeriv ℂ a (fun z => F i (π (Φ.point z))) 0 ≠ 0 := by
    intro hz
    exact hi (((hGactual.iteratedFDeriv (𝕜 := ℂ) a).self_of_nhds).trans hz)
  exact ⟨F i, a, hFmem, hjetactual, ha⟩

/-- The ENTIRE literal pullback of the SAME original integer multiplier ideal
obeys the raw point-reader upper bound. No finite-reader or selected order is an input. -/
theorem originalStalkNormalOrder_pullback_multiplierIdeal_le_point
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (Φ : DivisorFlattening (m := m) E y) (p : ℕ) (hp : 0 < p) :
    (2 : ℝ≥0∞) * ((originalStalkNormalOrder Φ
      (GermIdeal.pullback (m := m + 1) π (multiplierIdeal (n := m + 1) (p : ℝ) u))) : ℝ≥0∞) ≤
      ENNReal.ofReal (p : ℝ) * lelongNumber (n := m + 1) (fun t => u (π t)) y := by
  by_cases hfinite : lelongNumber (n := m + 1) (fun t => u (π t)) y = ⊤
  · have hp0 : ENNReal.ofReal (p : ℝ) ≠ 0 := by positivity
    simp only [hfinite, ENNReal.mul_top hp0, le_top]
  · obtain ⟨F, a, hFmem, hjet, hbound⟩ :=
      exists_original_member_nonzero_jet_bound_of_finite hπ hu Φ p hp hfinite
    have hFpull : HolomorphicAt (m + 1) (F ∘ π) y :=
      hFmem.1.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
    have hpullmem : (GermIdeal.pullback (m := m + 1) π
        (multiplierIdeal (n := m + 1) (p : ℝ) u)).mem y (F ∘ π) :=
      InvertibleIdealQuotient.isInSpanAt_self
        (S := fun s => ∃ f, (multiplierIdeal (n := m + 1) (p : ℝ) u).mem (π y) f ∧ s = f ∘ π)
        ⟨F, hFmem, rfl⟩ hFpull
    have horder := (originalStalkNormalOrder_le_member Φ _ hFpull hpullmem).trans
      (functionNormalOrder_le_of_flat_iteratedFDeriv_ne_zero Φ (F ∘ π) hFpull a hjet)
    calc
      _ ≤ (2 : ℝ≥0∞) * ((a : ℕ∞) : ℝ≥0∞) :=
        by simpa only [mul_comm] using mul_le_mul_left (ENat.toENNReal_mono horder) 2
      _ = ENNReal.ofReal (2 * (a : ℝ)) := by
        simp only [ENat.toENNReal_coe, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      _ ≤ _ := hbound

end SGPT.Foundations.Analysis.Pending.MultiplierIdealUpperBound
