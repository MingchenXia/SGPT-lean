import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1

/-!
# Ordered endpoint squeeze in chart-local L1

This file isolates the measure-theoretic endpoint argument used for ordered
finite geodesics.  The affine extended-real chord converges to its left
endpoint in the genuine chart-local `L1` topology.  A second theorem turns
pointwise order bounds between a small finite downward translate and that
chord into the same convergence.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- At finite endpoints, the distance from the affine chord to its left
endpoint is the ordinary real affine error. -/
theorem canonicalERealAbsDiff_eRealChord_left_of_finite
    {a b : EReal} (t : ℝ)
    (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥) :
    canonicalERealAbsDiff (eRealChord a b t) a =
      ENNReal.ofReal |t * (b.toReal - a.toReal)| := by
  rw [← EReal.coe_toReal ha_top ha_bot, ← EReal.coe_toReal hb_top hb_bot]
  simp only [eRealChord]
  norm_cast
  rw [canonicalERealAbsDiff_coe_coe]
  congr 2
  simp only [EReal.toReal_coe]
  ring_nf

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The ordinary real `L1` distance of two chart representatives, retained as
an `ENNReal` so that it can be used directly in estimates for
`chartL1EDistance`. -/
def chartEndpointRealL1 (u₀ u₁ : M → EReal) (e : ComplexChart n M)
    (K : Set (ComplexModel n)) : ENNReal :=
  ∫⁻ z in K, ENNReal.ofReal
    |(chartFunction u₁ e z).toReal - (chartFunction u₀ e z).toReal| ∂volume

/-- The real endpoint distance is finite on every compact chart subset for
genuine global quasi-PSH potentials. -/
theorem chartEndpointRealL1_ne_top
    {u₀ u₁ : M → EReal}
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    chartEndpointRealL1 u₀ u₁ e K ≠ ⊤ := by
  have hint : IntegrableOn
      (fun z => (chartFunction u₁ e z).toReal -
        (chartFunction u₀ e z).toReal) K volume :=
    (hu₁.integrableOn_chart_toReal e hK hKe).sub
      (hu₀.integrableOn_chart_toReal e hK hKe)
  have hfin := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at hfin
  simpa only [chartEndpointRealL1, Real.norm_eq_abs,
    lt_top_iff_ne_top] using hfin

/-- Exact local `L1` scaling of the affine chord from its left endpoint. -/
theorem chartL1EDistance_eRealChord_left
    {u₀ u₁ : M → EReal}
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hKe : K ⊆ e.val.target) (t : ℝ) :
    chartL1EDistance (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K =
      ENNReal.ofReal |t| * chartEndpointRealL1 u₀ u₁ e K := by
  rw [chartL1EDistance, chartEndpointRealL1,
    ← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_congr_ae
  have hfinite₀ : ∀ᵐ z ∂volume.restrict K,
      chartFunction u₀ e z ≠ ⊤ ∧ chartFunction u₀ e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hu₀.ae_finite_chart e)
  have hfinite₁ : ∀ᵐ z ∂volume.restrict K,
      chartFunction u₁ e z ≠ ⊤ ∧ chartFunction u₁ e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hu₁.ae_finite_chart e)
  filter_upwards [hfinite₀, hfinite₁] with z hz₀ hz₁
  change canonicalERealAbsDiff
      (eRealChord (chartFunction u₀ e z) (chartFunction u₁ e z) t)
      (chartFunction u₀ e z) = _
  rw [canonicalERealAbsDiff_eRealChord_left_of_finite t
    hz₀.1 hz₀.2 hz₁.1 hz₁.2, abs_mul,
    ENNReal.ofReal_mul (abs_nonneg t)]

/-- The affine extended-real chord converges to its left endpoint in
chart-local `L1` as time tends to zero (from either side, hence in particular
from the interior side). -/
theorem manifoldL1LocallyTendsto_eRealChord_left
    {u₀ u₁ : M → EReal}
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁) :
    ManifoldL1LocallyTendsto (n := n)
      (fun t x => eRealChord (u₀ x) (u₁ x) t)
      (𝓝[>] (0 : ℝ)) u₀ := by
  intro e K hK hKe
  have hformula :
      (fun t => chartL1EDistance
        (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K) =
        (fun t => ENNReal.ofReal |t| * chartEndpointRealL1 u₀ u₁ e K) := by
    funext t
    exact chartL1EDistance_eRealChord_left hu₀ hu₁ e hKe t
  rw [hformula]
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have habs : Tendsto (fun t : ℝ => |t|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.abs
  have hscalar : Tendsto (fun t : ℝ => ENNReal.ofReal |t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal habs
  simpa using ENNReal.Tendsto.mul_const hscalar
    (Or.inr (chartEndpointRealL1_ne_top hu₀ hu₁ e hK hKe))

/-- Theta-PSH endpoints satisfy the same left chord convergence. -/
theorem IsThetaPshPotential.manifoldL1LocallyTendsto_eRealChord_left
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) :
    ManifoldL1LocallyTendsto (n := n)
      (fun t x => eRealChord (u₀ x) (u₁ x) t)
      (𝓝[>] (0 : ℝ)) u₀ :=
  SGPT.Foundations.Analysis.FirstPass.manifoldL1LocallyTendsto_eRealChord_left
    hu₀.quasiPshPotential hu₁.quasiPshPotential

/-- A finite value squeezed between a small downward translate of the left
endpoint and the affine chord has absolute error bounded by the sum of the two
endpoint errors. -/
theorem canonicalERealAbsDiff_le_of_add_neg_mul_le_le_eRealChord
    {a b w : EReal} (C t : ℝ)
    (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥)
    (hw_top : w ≠ ⊤)
    (hlower : a + ((-(C * t) : ℝ) : EReal) ≤ w)
    (hupper : w ≤ eRealChord a b t) :
    canonicalERealAbsDiff w a ≤
      ENNReal.ofReal |C * t| +
        canonicalERealAbsDiff (eRealChord a b t) a := by
  rw [← EReal.coe_toReal ha_top ha_bot] at hlower hupper ⊢
  rw [← EReal.coe_toReal hb_top hb_bot] at hupper ⊢
  have hw_bot : w ≠ ⊥ := by
    intro hw
    rw [hw] at hlower
    have hfiniteLower :
        (↑a.toReal + ((-(C * t) : ℝ) : EReal)) ≠ ⊥ := by
      norm_cast
    exact (not_le_of_gt (bot_lt_iff_ne_bot.mpr hfiniteLower)) hlower
  rw [← EReal.coe_toReal hw_top hw_bot] at hlower hupper ⊢
  simp only [eRealChord] at hupper ⊢
  norm_cast at hlower hupper ⊢
  rw [canonicalERealAbsDiff_coe_coe,
    canonicalERealAbsDiff_coe_coe,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hright : w.toReal - a.toReal ≤
      |(1 - t) * a.toReal + t * b.toReal - a.toReal| := by
    calc
      w.toReal - a.toReal ≤
          (1 - t) * a.toReal + t * b.toReal - a.toReal := by linarith
      _ ≤ |(1 - t) * a.toReal + t * b.toReal - a.toReal| := le_abs_self _
  have hleft : -(w.toReal - a.toReal) ≤ |C * t| := by
    calc
      -(w.toReal - a.toReal) ≤ C * t := by linarith
      _ ≤ |C * t| := le_abs_self _
  apply abs_le.mpr
  constructor
  · have hleft' : -|C * t| ≤ w.toReal - a.toReal := by linarith
    exact (neg_le_neg (le_add_of_nonneg_right (abs_nonneg _))).trans hleft'
  · exact hright.trans (le_add_of_nonneg_left (abs_nonneg _))

/-- Integrating the pointwise ordered squeeze gives a chart-local `L1`
estimate.  No measurability of the squeezed family is required for this upper
bound. -/
theorem chartL1EDistance_le_of_add_neg_mul_le_le_eRealChord
    {u₀ u₁ : M → EReal} {w : ℝ → M → EReal} (C t : ℝ)
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁)
    (hw_top : ∀ x, w t x ≠ ⊤)
    (hlower : ∀ x, u₀ x + ((-(C * t) : ℝ) : EReal) ≤ w t x)
    (hupper : ∀ x, w t x ≤ eRealChord (u₀ x) (u₁ x) t)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hKe : K ⊆ e.val.target) :
    chartL1EDistance (w t) u₀ e K ≤
      ENNReal.ofReal |C * t| * volume K +
        chartL1EDistance (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K := by
  rw [chartL1EDistance, chartL1EDistance]
  have hfinite₀ : ∀ᵐ z ∂volume.restrict K,
      chartFunction u₀ e z ≠ ⊤ ∧ chartFunction u₀ e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hu₀.ae_finite_chart e)
  have hfinite₁ : ∀ᵐ z ∂volume.restrict K,
      chartFunction u₁ e z ≠ ⊤ ∧ chartFunction u₁ e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hu₁.ae_finite_chart e)
  calc
    (∫⁻ z in K, canonicalERealAbsDiff
        (chartFunction (w t) e z) (chartFunction u₀ e z) ∂volume) ≤
        ∫⁻ z in K, ENNReal.ofReal |C * t| +
          canonicalERealAbsDiff
            (chartFunction (fun x => eRealChord (u₀ x) (u₁ x) t) e z)
            (chartFunction u₀ e z) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [hfinite₀, hfinite₁] with z hz₀ hz₁
      change canonicalERealAbsDiff (w t (e.val.symm z)) (u₀ (e.val.symm z)) ≤ _
      change _ ≤ ENNReal.ofReal |C * t| +
        canonicalERealAbsDiff
          (eRealChord (u₀ (e.val.symm z)) (u₁ (e.val.symm z)) t)
          (u₀ (e.val.symm z))
      exact canonicalERealAbsDiff_le_of_add_neg_mul_le_le_eRealChord C t
        hz₀.1 hz₀.2 hz₁.1 hz₁.2 (hw_top _)
        (hlower _) (hupper _)
    _ = ENNReal.ofReal |C * t| * volume K +
        ∫⁻ z in K, canonicalERealAbsDiff
          (chartFunction (fun x => eRealChord (u₀ x) (u₁ x) t) e z)
          (chartFunction u₀ e z) ∂volume := by
      rw [lintegral_add_left measurable_const]
      rw [lintegral_const]
      simp

/-- A family squeezed between `u₀ - C t` and the affine chord from `u₀` to
`u₁`, and taking no `top` values, converges to `u₀` in chart-local `L1` as
`t → 0+`.  The endpoints may have different pole sets; their pole sets are
null separately, which is exactly what the chart proof uses. -/
theorem manifoldL1LocallyTendsto_of_add_neg_mul_le_le_eRealChord
    {u₀ u₁ : M → EReal} {w : ℝ → M → EReal} (C : ℝ)
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁)
    (hw_top : ∀ t x, w t x ≠ ⊤)
    (hlower : ∀ t x, u₀ x + ((-(C * t) : ℝ) : EReal) ≤ w t x)
    (hupper : ∀ t x, w t x ≤ eRealChord (u₀ x) (u₁ x) t) :
    ManifoldL1LocallyTendsto (n := n) w (𝓝[>] (0 : ℝ)) u₀ := by
  intro e K hK hKe
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hCabs : Tendsto (fun t : ℝ => |C * t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hid).abs
  have hscalar : Tendsto (fun t : ℝ => ENNReal.ofReal |C * t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hCabs
  have hvolume : volume K ≠ ∞ := hK.measure_ne_top
  have herr : Tendsto (fun t : ℝ => ENNReal.ofReal |C * t| * volume K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hscalar (Or.inr hvolume)
  have hchord : Tendsto
      (fun t => chartL1EDistance
        (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    manifoldL1LocallyTendsto_eRealChord_left hu₀ hu₁ e K hK hKe
  have hbound : Tendsto
      (fun t => ENNReal.ofReal |C * t| * volume K +
        chartL1EDistance
          (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using herr.add hchord
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) fun t => ?_
  exact chartL1EDistance_le_of_add_neg_mul_le_le_eRealChord C t hu₀ hu₁
    (hw_top t) (hlower t) (hupper t) e hKe

/-- Theta-PSH endpoint specialization of the ordered chart-local `L1`
squeeze theorem. -/
theorem IsThetaPshPotential.manifoldL1LocallyTendsto_of_ordered_chord_squeeze
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    {w : ℝ → M → EReal} (C : ℝ)
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hw_top : ∀ t x, w t x ≠ ⊤)
    (hlower : ∀ t x, u₀ x + ((-(C * t) : ℝ) : EReal) ≤ w t x)
    (hupper : ∀ t x, w t x ≤ eRealChord (u₀ x) (u₁ x) t) :
    ManifoldL1LocallyTendsto (n := n) w (𝓝[>] (0 : ℝ)) u₀ :=
  manifoldL1LocallyTendsto_of_add_neg_mul_le_le_eRealChord C
    hu₀.quasiPshPotential hu₁.quasiPshPotential hw_top hlower hupper

/-- Filter-local version of the ordered endpoint squeeze.  This is the form
used for Perron geodesics, whose chord bound and no-`top` property are supplied
only for interior times, hence eventually along `t → 0+`. -/
theorem manifoldL1LocallyTendsto_of_eventually_ordered_chord_squeeze
    {u₀ u₁ : M → EReal} {w : ℝ → M → EReal} (C : ℝ)
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁)
    (hw_top : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, w t x ≠ ⊤)
    (hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, u₀ x + ((-(C * t) : ℝ) : EReal) ≤ w t x)
    (hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, w t x ≤ eRealChord (u₀ x) (u₁ x) t) :
    ManifoldL1LocallyTendsto (n := n) w (𝓝[>] (0 : ℝ)) u₀ := by
  intro e K hK hKe
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hCabs : Tendsto (fun t : ℝ => |C * t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hid).abs
  have hscalar : Tendsto (fun t : ℝ => ENNReal.ofReal |C * t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hCabs
  have hvolume : volume K ≠ ∞ := hK.measure_ne_top
  have herr : Tendsto (fun t : ℝ => ENNReal.ofReal |C * t| * volume K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hscalar (Or.inr hvolume)
  have hchord : Tendsto
      (fun t => chartL1EDistance
        (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    manifoldL1LocallyTendsto_eRealChord_left hu₀ hu₁ e K hK hKe
  have hbound : Tendsto
      (fun t => ENNReal.ofReal |C * t| * volume K +
        chartL1EDistance
          (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using herr.add hchord
  have hsqueeze : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      chartL1EDistance (w t) u₀ e K ≤
        ENNReal.ofReal |C * t| * volume K +
          chartL1EDistance
            (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K := by
    filter_upwards [hw_top, hlower, hupper] with t ht hlow hup
    exact chartL1EDistance_le_of_add_neg_mul_le_le_eRealChord C t hu₀ hu₁
      ht hlow hup e hKe
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => zero_le) hsqueeze

/-- Theta-PSH specialization of the filter-local ordered squeeze. -/
theorem IsThetaPshPotential.manifoldL1LocallyTendsto_of_eventually_ordered_chord_squeeze
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    {w : ℝ → M → EReal} (C : ℝ)
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hw_top : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, w t x ≠ ⊤)
    (hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, u₀ x + ((-(C * t) : ℝ) : EReal) ≤ w t x)
    (hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, w t x ≤ eRealChord (u₀ x) (u₁ x) t) :
    ManifoldL1LocallyTendsto (n := n) w (𝓝[>] (0 : ℝ)) u₀ :=
  SGPT.Foundations.Analysis.FirstPass.manifoldL1LocallyTendsto_of_eventually_ordered_chord_squeeze C
    hu₀.quasiPshPotential hu₁.quasiPshPotential hw_top hlower hupper

end

end SGPT.Foundations.Analysis.FirstPass
