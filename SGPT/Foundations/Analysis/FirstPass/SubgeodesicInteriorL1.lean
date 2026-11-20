import SGPT.Foundations.Analysis.FirstPass.PshRealLipschitz
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1

/-!
# Interior chartwise L¹ continuity of subgeodesics

An interior strip subgeodesic is continuous in the genuine chart-local `L¹`
topology.  For an arbitrary sequence of times approaching an interior time,
we intersect the almost-everywhere finite loci of the countably many slices.
The invariant-PSH Lipschitz estimate then gives pointwise convergence and a
single integrable bound built from three fixed quasi-PSH slices.  Lebesgue
dominated convergence finishes the argument.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace IsSubgeodesicInterior

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}

/-- Every interior strip subgeodesic is chart-locally `L¹` continuous at each
interior time. -/
theorem manifoldL1LocallyContinuousAt
    (h : IsSubgeodesicInterior θ curve) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ManifoldL1LocallyTendsto (n := n) curve (𝓝 c) (curve c) := by
  intro e K hK hKe
  rw [Filter.tendsto_iff_seq_tendsto]
  intro s hs
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  let a : ℝ := c / 2
  let b : ℝ := (c + 1) / 2
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  have hcb : c < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  let r : ℕ → ℝ := fun k => if s k ∈ Ioo a b then s k else c
  have hcI : c ∈ Ioo a b := ⟨hac, hcb⟩
  have hrI (k : ℕ) : r k ∈ Ioo a b := by
    dsimp [r]
    split_ifs with hk
    · exact hk
    · exact hcI
  have hrs : r =ᶠ[atTop] s := by
    filter_upwards [hs.eventually (Ioo_mem_nhds hac hcb)] with k hk
    simp [r, hk]
  have hr : Tendsto r atTop (𝓝 c) := hs.congr' hrs.symm
  let μ : Measure (ComplexModel n) := volume.restrict K
  have habI : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ha0.trans_le ht.1, ht.2.trans_lt hb1⟩
  have hslice (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      IsGlobalQuasiPshPotential (n := n) (curve t) :=
    (h.thetaPshPotential ht).quasiPshPotential
  have hfinite (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      ∀ᵐ z ∂μ,
        chartFunction (curve t) e z ≠ ⊤ ∧
          chartFunction (curve t) e z ≠ ⊥ := by
    exact ae_restrict_of_ae_restrict_of_subset hKe
      ((hslice t ht).ae_finite_chart e)
  have hmeas (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      AEStronglyMeasurable
        (fun z => (chartFunction (curve t) e z).toReal) μ :=
    ((hslice t ht).aemeasurable_chart_restrict e hKe).ereal_toReal
      |>.aestronglyMeasurable
  have hint (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      Integrable (fun z => (chartFunction (curve t) e z).toReal) μ :=
    (hslice t ht).integrableOn_chart_toReal e hK hKe
  have haI : a ∈ Ioo (0 : ℝ) 1 := ⟨ha0, hac.trans hc.2⟩
  have hcI01 : c ∈ Ioo (0 : ℝ) 1 := hc
  have hbI : b ∈ Ioo (0 : ℝ) 1 := ⟨hc.1.trans hcb, hb1⟩
  have hrI01 (k : ℕ) : r k ∈ Ioo (0 : ℝ) 1 := habI (Ioo_subset_Icc_self (hrI k))
  have hfinite_a := hfinite a haI
  have hfinite_c := hfinite c hcI01
  have hfinite_b := hfinite b hbI
  have hfinite_r : ∀ᵐ z ∂μ, ∀ k,
      chartFunction (curve (r k)) e z ≠ ⊤ ∧
        chartFunction (curve (r k)) e z ≠ ⊥ :=
    ae_all_iff.mpr fun k => hfinite (r k) (hrI01 k)
  have hLip : ∀ᵐ z ∂μ, ∀ k,
      |(chartFunction (curve (r k)) e z).toReal -
          (chartFunction (curve c) e z).toReal| ≤
        |r k - c| *
          (|(chartFunction (curve a) e z).toReal -
              (chartFunction (curve c) e z).toReal| / (c - a) +
            |(chartFunction (curve b) e z).toReal -
              (chartFunction (curve c) e z).toReal| / (b - c)) := by
    filter_upwards [ae_restrict_mem hK.measurableSet, hfinite_a,
      hfinite_c, hfinite_b, hfinite_r]
      with z hzK hza hzc hzb hzr
    obtain ⟨W, ρ, hzW, _hρ, hstrip⟩ := h.complexified_psh e (hKe hzK)
    have htime := PlurisubharmonicOn.subgeodesic_time_line hstrip hzW
    change PlurisubharmonicOn
      (fun τ : ℂ => chartFunction (curve τ.re) e z + (ρ z : EReal))
      (Complex.re ⁻¹' Ioo (0 : ℝ) 1) at htime
    have hcorrFinite {t : ℝ}
        (ht : chartFunction (curve t) e z ≠ ⊤ ∧
          chartFunction (curve t) e z ≠ ⊥) :
        chartFunction (curve t) e z + (ρ z : EReal) ≠ ⊤ ∧
          chartFunction (curve t) e z + (ρ z : EReal) ≠ ⊥ := by
      constructor
      · exact (EReal.add_ne_top_iff_ne_top_left
          (EReal.coe_ne_bot (ρ z)) (EReal.coe_ne_top (ρ z))).mpr ht.1
      · rw [EReal.add_ne_bot_iff]
        exact ⟨ht.2, EReal.coe_ne_bot (ρ z)⟩
    have hcorrReal {t : ℝ}
        (ht : chartFunction (curve t) e z ≠ ⊤ ∧
          chartFunction (curve t) e z ≠ ⊥) :
        (chartFunction (curve t) e z + (ρ z : EReal)).toReal =
          (chartFunction (curve t) e z).toReal + ρ z :=
      EReal.toReal_add ht.1 ht.2 (EReal.coe_ne_top (ρ z))
        (EReal.coe_ne_bot (ρ z))
    intro k
    have hk := PlurisubharmonicOn.comp_re_toReal_abs_sub_le
      (v := fun t : ℝ => chartFunction (curve t) e z + (ρ z : EReal))
      (I := Ioo (0 : ℝ) 1) (a := a) (c := c) (b := b) (t := r k)
      htime hac hcb (hrI k).1 (hrI k).2
      habI (hcorrFinite hza).1 (hcorrFinite hza).2
      (hcorrFinite hzc).1 (hcorrFinite hzc).2
      (hcorrFinite hzb).1 (hcorrFinite hzb).2
      (hcorrFinite (hzr k)).1 (hcorrFinite (hzr k)).2
    rw [hcorrReal hza, hcorrReal hzc, hcorrReal hzb,
      hcorrReal (hzr k)] at hk
    simpa only [add_sub_add_right_eq_sub] using hk
  have hpointwise : ∀ᵐ z ∂μ,
      Tendsto (fun k => (chartFunction (curve (r k)) e z).toReal)
        atTop (𝓝 (chartFunction (curve c) e z).toReal) := by
    filter_upwards [hLip] with z hzLip
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let L : ℝ :=
      |(chartFunction (curve a) e z).toReal -
          (chartFunction (curve c) e z).toReal| / (c - a) +
        |(chartFunction (curve b) e z).toReal -
          (chartFunction (curve c) e z).toReal| / (b - c)
    have habs : Tendsto (fun k => |r k - c|) atTop (𝓝 0) := by
      simpa [sub_self, Real.norm_eq_abs] using (hr.sub_const c).norm
    have hscaled : Tendsto (fun k => |r k - c| * L) atTop (𝓝 0) := by
      simpa using habs.mul_const L
    simpa only [Real.norm_eq_abs] using
      squeeze_zero (fun k => abs_nonneg _)
        (fun k => by simpa [L] using hzLip k) hscaled
  let d : ℝ := max (c - a) (b - c)
  let bound : ComplexModel n → ℝ := fun z =>
    d *
        (|(chartFunction (curve a) e z).toReal -
            (chartFunction (curve c) e z).toReal| / (c - a) +
          |(chartFunction (curve b) e z).toReal -
            (chartFunction (curve c) e z).toReal| / (b - c)) +
      |(chartFunction (curve c) e z).toReal|
  have hca : 0 < c - a := sub_pos.mpr hac
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have hdist (k : ℕ) : |r k - c| ≤ d := by
    dsimp [d]
    rcases le_total (r k) c with hrc | hcr
    · rw [abs_of_nonpos (sub_nonpos.mpr hrc)]
      nlinarith [le_max_left (c - a) (b - c), (hrI k).1]
    · rw [abs_of_nonneg (sub_nonneg.mpr hcr)]
      nlinarith [le_max_right (c - a) (b - c), (hrI k).2]
  have hbound : ∀ k, ∀ᵐ z ∂μ,
      ‖(chartFunction (curve (r k)) e z).toReal‖ ≤ bound z := by
    intro k
    filter_upwards [hLip] with z hzLip
    have hLnonneg : 0 ≤
        |(chartFunction (curve a) e z).toReal -
            (chartFunction (curve c) e z).toReal| / (c - a) +
          |(chartFunction (curve b) e z).toReal -
            (chartFunction (curve c) e z).toReal| / (b - c) :=
      add_nonneg (div_nonneg (abs_nonneg _) hca.le)
        (div_nonneg (abs_nonneg _) hbc.le)
    have hdiff := hzLip k
    have hdiff' :
        |(chartFunction (curve (r k)) e z).toReal -
            (chartFunction (curve c) e z).toReal| ≤
          d *
            (|(chartFunction (curve a) e z).toReal -
                (chartFunction (curve c) e z).toReal| / (c - a) +
              |(chartFunction (curve b) e z).toReal -
                (chartFunction (curve c) e z).toReal| / (b - c)) :=
      hdiff.trans (mul_le_mul_of_nonneg_right (hdist k) hLnonneg)
    rw [Real.norm_eq_abs]
    change |(chartFunction (curve (r k)) e z).toReal| ≤ _
    calc
      |(chartFunction (curve (r k)) e z).toReal| =
          |((chartFunction (curve (r k)) e z).toReal -
              (chartFunction (curve c) e z).toReal) +
            (chartFunction (curve c) e z).toReal| := by ring_nf
      _ ≤ |(chartFunction (curve (r k)) e z).toReal -
            (chartFunction (curve c) e z).toReal| +
          |(chartFunction (curve c) e z).toReal| := abs_add_le _ _
      _ ≤ bound z := by
        dsimp [bound]
        linarith
  have hIa := hint a haI
  have hIc := hint c hcI01
  have hIb := hint b hbI
  have hAc : Integrable (fun z =>
      |(chartFunction (curve a) e z).toReal -
        (chartFunction (curve c) e z).toReal|) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hIa.sub hIc).norm
  have hBc : Integrable (fun z =>
      |(chartFunction (curve b) e z).toReal -
        (chartFunction (curve c) e z).toReal|) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hIb.sub hIc).norm
  have hCabs : Integrable
      (fun z => |(chartFunction (curve c) e z).toReal|) μ := by
    simpa only [Real.norm_eq_abs] using hIc.norm
  have hboundInt : Integrable bound μ := by
    dsimp [bound]
    exact ((hAc.div_const (c - a)).add (hBc.div_const (b - c))).const_mul d
      |>.add hCabs
  have hDCT : Tendsto
      (fun k => ∫⁻ z, ENNReal.ofReal
        ‖(chartFunction (curve (r k)) e z).toReal -
          (chartFunction (curve c) e z).toReal‖ ∂μ)
      atTop (𝓝 0) :=
    tendsto_lintegral_norm_of_dominated_convergence
      (fun k => hmeas (r k) (hrI01 k)) hboundInt.hasFiniteIntegral
      hbound hpointwise
  have hcanonical (k : ℕ) :
      chartL1EDistance (curve (r k)) (curve c) e K =
        ∫⁻ z, ENNReal.ofReal
          ‖(chartFunction (curve (r k)) e z).toReal -
            (chartFunction (curve c) e z).toReal‖ ∂μ := by
    rw [chartL1EDistance]
    apply lintegral_congr_ae
    filter_upwards [hfinite (r k) (hrI01 k), hfinite_c]
      with z hzr hzc
    conv_lhs =>
      rw [← EReal.coe_toReal hzr.1 hzr.2,
        ← EReal.coe_toReal hzc.1 hzc.2,
        canonicalERealAbsDiff_coe_coe]
    simp only [Real.norm_eq_abs]
  have hrL1 : Tendsto
      (fun k => chartL1EDistance (curve (r k)) (curve c) e K)
      atTop (𝓝 0) := by
    simpa only [hcanonical] using hDCT
  apply hrL1.congr'
  filter_upwards [hrs] with k hk
  simp [Function.comp_apply, hk]

end IsSubgeodesicInterior

namespace IsSubgeodesicFrom

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

/-- Interior chart-local `L¹` continuity for a subgeodesic with prescribed
endpoints. -/
theorem manifoldL1LocallyContinuousAt
    (h : IsSubgeodesicFrom θ curve u₀ u₁) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ManifoldL1LocallyTendsto (n := n) curve (𝓝 c) (curve c) :=
  h.interior.manifoldL1LocallyContinuousAt hc

end IsSubgeodesicFrom

end

end SGPT.Foundations.Analysis.FirstPass
