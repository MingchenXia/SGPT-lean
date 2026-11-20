import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound
import SGPT.Foundations.Analysis.FirstPass.FiniteVaryingTranslation
import SGPT.Foundations.Analysis.FirstPass.OrderedL1Squeeze

set_option autoImplicit false

/-!
# Rooftop lower competitors and endpoint `L¹` estimates

The general endpoint argument for Perron geodesics uses a theta-PSH rooftop
`w` satisfying `w ≤ u₀` and `w ≤ u₁ + C`.  The affine curve `w - Ct` is then
a genuine Perron competitor.  A value between that lower competitor and the
endpoint chord has `L¹` distance from `u₀` bounded by the sum of the distances
of the two bounds.

These are the formal order and measure-theoretic parts of the endpoint
argument in Xia, Proposition 4.2.1.  The separate rooftop convergence input
`P_θ(u₀,u₁+M) → u₀` is Proposition 3.1.24.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A theta-PSH potential below `u₀` and below `u₁ + C` supplies the affine
Perron lower competitor `w - Ct`. -/
theorem affineRooftopLower_le_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ w : M → EReal}
    (hw : IsThetaPshPotential θ w) (hw₀ : w ≤ u₀)
    {C : ℝ} (hw₁ : w ≤ fun x => u₁ x + (C : EReal)) (t : ℝ) :
    (fun x => w x + (((-C) * t : ℝ) : EReal)) ≤
      finiteGeodesic θ u₀ u₁ t := by
  let curve : ℝ → M → EReal :=
    affineTranslatedCurve (fun _ : ℝ => w) (-C) 0
  have hsub : IsSubgeodesicFrom θ curve w
      (fun x => w x + ((-C : ℝ) : EReal)) := by
    simpa [curve] using
      (isSubgeodesicFrom_const hw).affineTranslated (-C) 0
  have hright : (fun x => w x + ((-C : ℝ) : EReal)) ≤ u₁ := by
    intro x
    apply (EReal.addLECancellable_coe C).add_le_add_iff_right.mp
    calc
      (w x + ((-C : ℝ) : EReal)) + (C : EReal) = w x := by
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ u₁ x + (C : EReal) := hw₁ x
  have hmem : curve ∈ finiteGeodesicCompetitors θ u₀ u₁ :=
    ⟨w, (fun x => w x + ((-C : ℝ) : EReal)), hw,
      hw.add_const (-C), hw₀, hright, hsub⟩
  intro x
  simpa only [curve, affineTranslatedCurve_apply, add_zero] using
    competitor_slice_le_finiteGeodesic hmem t x

/-- If `l ≤ w ≤ chord(a,b;t)` and all displayed endpoint values are finite,
then the distance from `w` to `a` is bounded by the sum of the distances of
the lower and upper barriers from `a`. -/
theorem canonicalERealAbsDiff_le_add_of_le_le_eRealChord
    {a b l w : EReal} (t : ℝ)
    (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥)
    (hl_top : l ≠ ⊤) (hl_bot : l ≠ ⊥)
    (hw_top : w ≠ ⊤) (hlower : l ≤ w)
    (hupper : w ≤ eRealChord a b t) :
    canonicalERealAbsDiff w a ≤
      canonicalERealAbsDiff l a +
        canonicalERealAbsDiff (eRealChord a b t) a := by
  rw [← EReal.coe_toReal ha_top ha_bot] at hupper ⊢
  rw [← EReal.coe_toReal hb_top hb_bot] at hupper ⊢
  rw [← EReal.coe_toReal hl_top hl_bot] at hlower ⊢
  have hw_bot : w ≠ ⊥ := by
    intro hw
    rw [hw] at hlower
    exact (not_le_of_gt (bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot l.toReal)))
      hlower
  rw [← EReal.coe_toReal hw_top hw_bot] at hlower hupper ⊢
  simp only [eRealChord] at hupper ⊢
  norm_cast at hlower hupper ⊢
  rw [canonicalERealAbsDiff_coe_coe,
    canonicalERealAbsDiff_coe_coe,
    canonicalERealAbsDiff_coe_coe,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  let c : ℝ := (1 - t) * a.toReal + t * b.toReal
  have hleft : -|l.toReal - a.toReal| ≤ w.toReal - a.toReal := by
    calc
      -|l.toReal - a.toReal| ≤ l.toReal - a.toReal := neg_abs_le _
      _ ≤ w.toReal - a.toReal := sub_le_sub_right hlower _
  have hright : w.toReal - a.toReal ≤ |c - a.toReal| := by
    calc
      w.toReal - a.toReal ≤ c - a.toReal :=
        sub_le_sub_right hupper _
      _ ≤ |c - a.toReal| := le_abs_self _
  apply abs_le.mpr
  constructor
  · calc
      -(|l.toReal - a.toReal| + |c - a.toReal|) ≤
          -|l.toReal - a.toReal| := by
            exact neg_le_neg (le_add_of_nonneg_right (abs_nonneg _))
      _ ≤ w.toReal - a.toReal := hleft
  · exact hright.trans (le_add_of_nonneg_left (abs_nonneg _))

/-- Integrating the preceding interval estimate gives a chart-local `L¹`
bound.  No measurability of the middle function is needed. -/
theorem chartL1EDistance_le_add_of_le_le_eRealChord
    {u₀ u₁ l w : M → EReal} (t : ℝ)
    (hu₀ : IsGlobalQuasiPshPotential (n := n) u₀)
    (hu₁ : IsGlobalQuasiPshPotential (n := n) u₁)
    (hl : IsGlobalQuasiPshPotential (n := n) l)
    (hw_top : ∀ x, w x ≠ ⊤) (hlower : l ≤ w)
    (hupper : w ≤ fun x => eRealChord (u₀ x) (u₁ x) t)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hKe : K ⊆ e.val.target) :
    chartL1EDistance w u₀ e K ≤
      chartL1EDistance l u₀ e K +
        chartL1EDistance (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K := by
  rw [chartL1EDistance, chartL1EDistance, chartL1EDistance]
  have hfinite₀ : ∀ᵐ z ∂volume.restrict K,
      chartFunction u₀ e z ≠ ⊤ ∧ chartFunction u₀ e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hu₀.ae_finite_chart e)
  have hfinite₁ : ∀ᵐ z ∂volume.restrict K,
      chartFunction u₁ e z ≠ ⊤ ∧ chartFunction u₁ e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hu₁.ae_finite_chart e)
  have hfinite_l : ∀ᵐ z ∂volume.restrict K,
      chartFunction l e z ≠ ⊤ ∧ chartFunction l e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hl.ae_finite_chart e)
  calc
    (∫⁻ z in K, canonicalERealAbsDiff
        (chartFunction w e z) (chartFunction u₀ e z) ∂volume) ≤
        ∫⁻ z in K,
          canonicalERealAbsDiff (chartFunction l e z) (chartFunction u₀ e z) +
            canonicalERealAbsDiff
              (chartFunction (fun x => eRealChord (u₀ x) (u₁ x) t) e z)
              (chartFunction u₀ e z) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [hfinite₀, hfinite₁, hfinite_l] with z hz₀ hz₁ hzl
      change canonicalERealAbsDiff (w (e.val.symm z)) (u₀ (e.val.symm z)) ≤ _
      change _ ≤ canonicalERealAbsDiff (l (e.val.symm z)) (u₀ (e.val.symm z)) +
        canonicalERealAbsDiff
          (eRealChord (u₀ (e.val.symm z)) (u₁ (e.val.symm z)) t)
          (u₀ (e.val.symm z))
      exact canonicalERealAbsDiff_le_add_of_le_le_eRealChord t
        hz₀.1 hz₀.2 hz₁.1 hz₁.2 hzl.1 hzl.2
        (hw_top _) (hlower _) (hupper _)
    _ = (∫⁻ z in K,
          canonicalERealAbsDiff (chartFunction l e z) (chartFunction u₀ e z)
          ∂volume) +
        ∫⁻ z in K,
          canonicalERealAbsDiff
            (chartFunction (fun x => eRealChord (u₀ x) (u₁ x) t) e z)
            (chartFunction u₀ e z) ∂volume := by
      rw [lintegral_add_left']
      exact measurable_canonicalERealAbsDiff.comp_aemeasurable'
        ((hl.aemeasurable_chart_restrict e hKe).prodMk
          (hu₀.aemeasurable_chart_restrict e hKe))

/-- A two-scale squeeze for nonnegative extended-real errors.  If fixed
approximation errors can be made arbitrarily small, every corresponding
remainder tends to zero, and the target error is eventually bounded by their
sum, then the target error tends to zero. -/
theorem ennreal_tendsto_zero_of_approximation_bounds
    {α β : Type*} {l : Filter α} {d : α → ENNReal}
    {approx : β → ENNReal} {remainder : β → α → ENNReal}
    (happrox : ∀ ε : ENNReal, 0 < ε → ∃ b, approx b < ε)
    (hremainder : ∀ b, Tendsto (remainder b) l (𝓝 0))
    (hbound : ∀ b, ∀ᶠ a in l, d a ≤ approx b + remainder b a) :
    Tendsto d l (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => (ENNReal.not_lt_zero ha).elim, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨b, hb⟩ := happrox (ε / 2) hhalf
  have hr : ∀ᶠ a in l, remainder b a < ε / 2 :=
    (tendsto_order.1 (hremainder b)).2 (ε / 2) hhalf
  filter_upwards [hbound b, hr] with a hda hra
  refine hda.trans_lt ?_
  calc
    approx b + remainder b a < ε / 2 + ε / 2 :=
      ENNReal.add_lt_add hb hra
    _ = ε := ENNReal.add_halves ε

/-- The exact two-parameter endpoint argument.  A family of theta-PSH
rooftops below `u₀` and below `u₁ + C`, converging locally in `L¹` to `u₀` as
`C → ∞`, forces the Perron geodesic to recover `u₀` as `t → 0+`.

This theorem contains the complete order, finite-translation, chord, measure,
and two-scale limit argument.  Its only external analytic input is the stated
rooftop exhaustion hypothesis. -/
theorem finiteGeodesic_tendsto_left_of_rooftop_exhaustion
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {w : ℝ → M → EReal}
    (hwpsh : ∀ C, 0 < C → IsThetaPshPotential θ (w C))
    (hw₀ : ∀ C, 0 < C → w C ≤ u₀)
    (hw₁ : ∀ C, 0 < C → w C ≤ fun x => u₁ x + (C : EReal))
    (hexhaust : ManifoldL1LocallyTendsto (n := n) w atTop u₀) :
    ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic θ u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ := by
  intro e K hK hKe
  let PositiveReal := {C : ℝ // 0 < C}
  let approx : PositiveReal → ENNReal := fun C =>
    chartL1EDistance (w C.1) u₀ e K
  let remainder : PositiveReal → ℝ → ENNReal := fun C t =>
    ENNReal.ofReal |-(C.1 * t)| * volume K +
      chartL1EDistance (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K
  apply ennreal_tendsto_zero_of_approximation_bounds
      (β := PositiveReal) (approx := approx) (remainder := remainder)
  · intro ε hε
    have hsmall : ∀ᶠ C : ℝ in atTop,
        chartL1EDistance (w C) u₀ e K < ε :=
      (tendsto_order.1 (hexhaust e K hK hKe)).2 ε hε
    obtain ⟨C, hCsmall, hCpos⟩ :=
      (hsmall.and (eventually_gt_atTop (0 : ℝ))).exists
    exact ⟨⟨C, hCpos⟩, hCsmall⟩
  · intro C
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hCabs : Tendsto (fun t : ℝ => |-(C.1 * t)|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hid).neg.abs
    have hscalar : Tendsto (fun t : ℝ => ENNReal.ofReal |-(C.1 * t)|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hCabs
    have hvolume : volume K ≠ ∞ := hK.measure_ne_top
    have htranslation : Tendsto
        (fun t : ℝ => ENNReal.ofReal |-(C.1 * t)| * volume K)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hscalar (Or.inr hvolume)
    have hchord : Tendsto
        (fun t => chartL1EDistance
          (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      hu₀.manifoldL1LocallyTendsto_eRealChord_left hu₁ e K hK hKe
    simpa [remainder] using htranslation.add hchord
  · intro C
    have hIoo : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hIoo] with t ht
    have htop : ∀ x, finiteGeodesic θ u₀ u₁ t x ≠ ⊤ := by
      intro x htx
      have hle := finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
      rw [htx] at hle
      exact (eRealChord_ne_top
        (hu₀.quasiPshPotential.1.ne_top x)
        (hu₁.quasiPshPotential.1.ne_top x)
        ht.1.le ht.2.le) (top_unique hle)
    have hlower : (fun x => w C.1 x + (((-C.1) * t : ℝ) : EReal)) ≤
        finiteGeodesic θ u₀ u₁ t :=
      affineRooftopLower_le_finiteGeodesic
        (hwpsh C.1 C.2) (hw₀ C.1 C.2) (hw₁ C.1 C.2) t
    have hupper : finiteGeodesic θ u₀ u₁ t ≤
        fun x => eRealChord (u₀ x) (u₁ x) t :=
      finiteGeodesic_le_eRealChord hu₀ hu₁ ht
    have hsqueeze := chartL1EDistance_le_add_of_le_le_eRealChord t
      hu₀.quasiPshPotential hu₁.quasiPshPotential
      ((hwpsh C.1 C.2).add_const ((-C.1) * t)).quasiPshPotential
      htop hlower hupper e hKe
    have htranslate := chartL1EDistance_add_coe_add_coe_le
      (w C.1) u₀ ((-C.1) * t) 0 e K
    have htranslate' :
        chartL1EDistance
            (fun x => w C.1 x + (((-C.1) * t : ℝ) : EReal)) u₀ e K ≤
          chartL1EDistance (w C.1) u₀ e K +
            ENNReal.ofReal |(-C.1) * t - 0| * volume K := by
      simpa using htranslate
    calc
      chartL1EDistance (finiteGeodesic θ u₀ u₁ t) u₀ e K ≤
          chartL1EDistance
              (fun x => w C.1 x + (((-C.1) * t : ℝ) : EReal)) u₀ e K +
            chartL1EDistance
              (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K := hsqueeze
      _ ≤ (chartL1EDistance (w C.1) u₀ e K +
              ENNReal.ofReal |(-C.1) * t - 0| * volume K) +
            chartL1EDistance
              (fun x => eRealChord (u₀ x) (u₁ x) t) u₀ e K :=
        add_le_add htranslate' le_rfl
      _ = approx C + remainder C t := by
        simp only [approx, remainder, sub_zero, neg_mul, add_assoc]

end

end SGPT.Foundations.Analysis.FirstPass
