import SGPT.Envelopes.MADirichlet5Kolodziej

/-!
# Exhaustion of a bounded potential by Kołodziej solutions

Xia, *Foundations of pluripotential theory* (FPT), `thm:bounded-multifactor-common-measure`,
Step 1, on a polydisk `Q`: let `ũ` be plurisubharmonic on `Q` with `-B ≤ ũ ≤ 0`, boundary values
`0` and `(ddᶜũ)ⁿ(Q) < ∞`, and let `K_l ⊆ Q` be compact sets exhausting `Q`. Kołodziej's theorem
(`exists_kolodziej_polydisk`) gives `A_l ∈ ℰ₀(Q)` with `(ddᶜA_l)ⁿ = 𝟙_{K_l}(ddᶜũ)ⁿ`; by
maximality `ũ ≤ A_l ≤ 0`, and `A_l → ũ` in `L¹_loc(Q)` and in capacity on compact subsets of every
open `V ⊆ Q` (`exists_kolodziej_exhaustion`).

FPT proves `A_l ↓ ũ` through the decreasing limit `A_∞` and the continuity of Monge–Ampère measures
along decreasing sequences. We argue directly with the comparison principle: for `ε, s > 0`, on
`E_l = {ũ < A_l - s + ε(|z|² - M')}` (relatively compact),
`(ddᶜũ)ⁿ(E_l ∩ K_l) + cₙεⁿ|E_l| ≤ (ddᶜ(A_l + ε|z|²))ⁿ(E_l) ≤ (ddᶜũ)ⁿ(E_l)`, so
`cₙεⁿ|E_l| ≤ (ddᶜũ)ⁿ(Q \ K_l) → 0` (`volume_lt_le_of_ma_eq_restrict`); off `E_l`,
`0 ≤ A_l - ũ ≤ s + εM'`. This gives the `L¹_loc` convergence, and capacity convergence follows from
Hartogs' lemma and quasi-continuity (`tendsto_relCapacity_add_lt_of_localL1`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.NPP.LogConcavityDinew
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- **The volume estimate** (comparison principle): if `(ddᶜA)ⁿ = 𝟙_{K'}(ddᶜũ)ⁿ` on a bounded `Q`,
`(ddᶜũ)ⁿ(Q) < ∞` and `ũ - A → 0` at `∂Q`, then
`cₙεⁿ |{ũ < A - s + ε(|z|² - M')}| ≤ (ddᶜũ)ⁿ(Q \ K')` for `ε, s > 0`, `M' ≥ |z|²` on `Q`. -/
theorem volume_lt_le_of_ma_eq_restrict (hn : 0 < n) {Q : Opens (ComplexModel n)}
    (hQb : Bornology.IsBounded (Q : Set (ComplexModel n))) {v A : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Q v) (hA : IsLocallyBoundedPshOn Q A)
    (hfin : canonicalBedfordTaylorMeasure Q v hv (Q : Set (ComplexModel n)) < ⊤)
    {K' : Set (ComplexModel n)} (hK'm : MeasurableSet K')
    (hMA : canonicalBedfordTaylorMeasure Q A hA = (canonicalBedfordTaylorMeasure Q v hv).restrict K')
    (hbd : ∀ ζ ∈ frontier (Q : Set (ComplexModel n)),
      Tendsto (fun z => v z - A z) (𝓝[(Q : Set (ComplexModel n))] ζ) (𝓝 0))
    {M' : ℝ} (hM' : ∀ z ∈ Q, ‖z‖ ^ 2 ≤ M') {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    ENNReal.ofReal (mongeAmpereConst n * ε ^ n) *
        volume {z | z ∈ Q ∧ v z < (A z + -s) + ε * (‖z‖ ^ 2 - M')} ≤
      canonicalBedfordTaylorMeasure Q v hv ((Q : Set (ComplexModel n)) \ K') := by
  set ν := canonicalBedfordTaylorMeasure Q v hv with hνdef
  have hAs : IsLocallyBoundedPshOn Q fun z => A z + -s := IsLocallyBoundedPshOn.add_const hA _
  have hV : IsLocallyBoundedPshOn Q fun z => (A z + -s) + ε * (‖z‖ ^ 2 - M') := by
    have h := IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_linComb hA hA (a := 1) (b := 0)
      (c := ε) zero_le_one le_rfl hε.le) (-s - ε * M')
    have e : (fun z => 1 * A z + 0 * A z + ε * ‖z‖ ^ 2 + (-s - ε * M')) =
        fun z => (A z + -s) + ε * (‖z‖ ^ 2 - M') := by funext z; ring
    rwa [e] at h
  set E : Set (ComplexModel n) := {z | z ∈ Q ∧ v z < (A z + -s) + ε * (‖z‖ ^ 2 - M')} with hEdef
  -- `E` is relatively compact
  obtain ⟨hKc, hKcQ⟩ := exists_isCompact_sublevel hQb hbd (s := s) hs
  have hEK : E ⊆ closure {z | z ∈ Q ∧ v z - A z ≤ -s} := by
    rintro z ⟨hzQ, hz⟩
    refine subset_closure ⟨hzQ, ?_⟩
    have h1 : ε * (‖z‖ ^ 2 - M') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (by linarith [hM' z hzQ])
    linarith
  have hcomp := SGPT.PSH.BookDeepDomination.measure_lt_le_of_subset_compact hn hv hV
    (isBTLimit_canonicalBedfordTaylorMeasure hv) (isBTLimit_canonicalBedfordTaylorMeasure hV)
    hKc hKcQ hEK
  have hsum := ma_add_normSq_ge hn hAs hε M' hV
  rw [canonicalBedfordTaylorMeasure_add_const hA (-s) hAs, hMA] at hsum
  have hEQ : E ⊆ Q := fun z hz => hz.1
  have hEm : MeasurableSet E := by
    have hm1 := measurable_indicator_of_plurisubharmonicOn hv.1
    have hm2 := measurable_indicator_of_plurisubharmonicOn hV.1
    have : E = (Q : Set (ComplexModel n)) ∩ {z | (Q : Set (ComplexModel n)).indicator v z <
        (Q : Set (ComplexModel n)).indicator (fun z => (A z + -s) + ε * (‖z‖ ^ 2 - M')) z} := by
      ext z
      simp only [hEdef, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨hz, h⟩; exact ⟨hz, by rwa [indicator_of_mem hz, indicator_of_mem hz]⟩
      · rintro ⟨hz, h⟩; exact ⟨hz, by rwa [indicator_of_mem hz, indicator_of_mem hz] at h⟩
    rw [this]
    exact Q.isOpen.measurableSet.inter (measurableSet_lt hm1 hm2)
  have h1 := (hsum E).trans hcomp
  rw [Measure.add_apply, Measure.restrict_apply hEm, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' Q.isOpen.measurableSet, inter_eq_left.mpr hEQ] at h1
  have hsplit : ν E = ν (E ∩ K') + ν (E \ K') := (measure_inter_add_sdiff E hK'm).symm
  rw [hsplit] at h1
  have hfinEK : ν (E ∩ K') ≠ ⊤ :=
    ((measure_mono (inter_subset_left.trans hEQ)).trans_lt hfin).ne
  have h2 := (ENNReal.add_le_add_iff_left hfinEK).mp h1
  exact h2.trans (measure_mono (sdiff_subset_sdiff_left hEQ))

/-- **Exhaustion by Kołodziej solutions** (FPT `thm:bounded-multifactor-common-measure`, Step 1, on a
polydisk): for `v` plurisubharmonic on `Q = a + R·P` with `-B ≤ v ≤ 0`, boundary values `0` and
`(ddᶜv)ⁿ(Q) < ∞`, and compact sets `K_l ⊆ Q` increasing to `Q`, the Kołodziej solutions `A_l` of
`(ddᶜA_l)ⁿ = 𝟙_{K_l}(ddᶜv)ⁿ` satisfy `v ≤ A_l ≤ 0` and `A_l → v` in `L¹_loc(Q)` and in capacity. -/
theorem exists_kolodziej_exhaustion (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn (polydiskAtOpens a R) v) {B : ℝ}
    (hB : 0 ≤ B) (hvb : ∀ z ∈ polydiskAt a R, -B ≤ v z ∧ v z ≤ 0)
    (hbd : ∀ ζ ∈ frontier (polydiskAt a R), Tendsto v (𝓝[polydiskAt a R] ζ) (𝓝 0))
    (hfin : canonicalBedfordTaylorMeasure (polydiskAtOpens a R) v hv (polydiskAt a R) < ⊤)
    {K : ℕ → Set (ComplexModel n)} (hK : ∀ l, IsCompact (K l)) (hKQ : ∀ l, K l ⊆ polydiskAt a R)
    (hKmono : Monotone K) (hKcov : ∀ z ∈ polydiskAt a R, ∃ l, z ∈ K l) :
    ∃ (A : ℕ → ComplexModel n → ℝ) (hA : ∀ l, IsCegrellE0 (polydiskAtOpens a R) (A l)),
      (∀ l, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (A l) (hA l).psh =
        (canonicalBedfordTaylorMeasure (polydiskAtOpens a R) v hv).restrict (K l)) ∧
      (∀ l, ∀ z ∈ polydiskAt a R, v z ≤ A l z ∧ A l z ≤ 0) ∧
      (∀ L : Set (ComplexModel n), IsCompact L → L ⊆ polydiskAt a R →
        Tendsto (fun l => ∫⁻ x in L, ENNReal.ofReal |A l x - v x|) atTop (𝓝 0)) ∧
      ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ polydiskAt a R → ∀ b : ℝ, 0 < b →
        Tendsto (fun l => relCapacity (polydiskAtOpens a R) (L ∩ {z | b < |A l z - v z|}))
          atTop (𝓝 0) := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQQ : (Q : Set (ComplexModel n)) = polydiskAt a R := rfl
  set ν := canonicalBedfordTaylorMeasure Q v hv with hνdef
  have hfinK : ∀ l, IsFiniteMeasure (ν.restrict (K l)) := fun l =>
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono (hKQ l)).trans_lt hfin⟩
  have hsol := fun l => @exists_kolodziej_polydisk n hn a R hR (ν.restrict (K l)) (hfinK l) (K l)
    (hK l) (hKQ l) (by rw [Measure.restrict_apply (hK l).isClosed.measurableSet.compl,
      compl_inter_self, measure_empty]) v hv (-B) B hB (fun z hz => ⟨(hvb z hz).1, by
        linarith [(hvb z hz).2]⟩) (Measure.restrict_le_self.trans Measure.restrict_le_self)
  choose A hA hMA hAb hmax _huniq using hsol
  have hvA : ∀ l, ∀ z ∈ polydiskAt a R, v z ≤ A l z := fun l =>
    hmax l v hv (Measure.restrict_le_self.trans Measure.restrict_le_self) fun ζ hζ δ hδ =>
      (hbd ζ hζ).eventually (Iio_mem_nhds hδ)
  have hQb : Bornology.IsBounded (Q : Set (ComplexModel n)) := isBounded_polydiskAt a hR
  obtain ⟨ρ₀, hρ₀⟩ := hQb.subset_closedBall 0
  set M' : ℝ := ρ₀ ^ 2 + 1 with hM'def
  have hM' : ∀ z ∈ Q, ‖z‖ ^ 2 ≤ M' := fun z hz => by
    have h := hρ₀ hz
    rw [mem_closedBall, dist_zero_right] at h
    have := pow_le_pow_left₀ (norm_nonneg z) h 2
    linarith
  have hM'0 : 0 ≤ M' := by positivity
  -- the mass outside `K_l` tends to `0`
  have htail : Tendsto (fun l => ν ((Q : Set (ComplexModel n)) \ K l)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (s := fun l => (Q : Set (ComplexModel n)) \ K l)
      (fun l => (Q.isOpen.measurableSet.diff (hK l).isClosed.measurableSet).nullMeasurableSet)
      (fun l m hlm => sdiff_subset_sdiff_right (hKmono hlm)) ⟨0, ((measure_mono (fun x hx => hx.1 : (Q : Set (ComplexModel n)) \ K 0 ⊆ Q)).trans_lt hfin).ne⟩
    have hempty : (⋂ l, (Q : Set (ComplexModel n)) \ K l) = ∅ := by
      ext z
      simp only [mem_iInter, Set.mem_sdiff, mem_empty_iff_false, iff_false, not_forall]
      by_cases hz : z ∈ Q
      · obtain ⟨l, hl⟩ := hKcov z hz
        exact ⟨l, fun h => h.2 hl⟩
      · exact ⟨0, fun h => hz h.1⟩
    rw [hempty, measure_empty] at h
    exact h
  -- `L¹_loc` convergence
  have hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun l => ∫⁻ x in L, ENNReal.ofReal |A l x - v x|) atTop (𝓝 0) := by
    intro L hL hLQ
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨η', -, hη', hη'η⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
    have hη'0 : 0 < η' := ENNReal.ofReal_pos.mp hη'
    set vL : ℝ := (volume L).toReal with hvLdef
    have hvL0 : 0 ≤ vL := ENNReal.toReal_nonneg
    set s : ℝ := η' / (4 * (vL + 1)) with hsdef
    set ε : ℝ := η' / (4 * (vL + 1) * (M' + 1)) with hεdef
    have hs : 0 < s := by positivity
    have hε : 0 < ε := by positivity
    have hsεM : (s + ε * M') * vL ≤ η' / 2 := by
      have h1 : ε * M' ≤ η' / (4 * (vL + 1)) := by
        rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hη'0, hvL0, hM'0]
      have h2 : (s + ε * M') ≤ η' / (2 * (vL + 1)) := by
        have : η' / (4 * (vL + 1)) + η' / (4 * (vL + 1)) = η' / (2 * (vL + 1)) := by
          field_simp; ring
        linarith
      calc (s + ε * M') * vL ≤ η' / (2 * (vL + 1)) * vL :=
            mul_le_mul_of_nonneg_right h2 hvL0
        _ ≤ η' / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    set c : ℝ≥0∞ := ENNReal.ofReal (mongeAmpereConst n * ε ^ n) with hcdef
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by have := mongeAmpereConst_pos (n := n); positivity)).ne'
    have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlim2 : Tendsto (fun l => ENNReal.ofReal B * (c⁻¹ * ν ((Q : Set (ComplexModel n)) \ K l)))
        atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul htail (Or.inr (ENNReal.inv_ne_top.mpr hc0)) (a := c⁻¹)
      have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal B)
      simpa using h2
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp hlim2) (ENNReal.ofReal (η' / 2))
      (ENNReal.ofReal_pos.mpr (by positivity))] with l hl
    set E : Set (ComplexModel n) :=
      {z | z ∈ Q ∧ v z < (A l z + -s) + ε * (‖z‖ ^ 2 - M')} with hEdef
    have hvol := volume_lt_le_of_ma_eq_restrict hn hQb hv (hA l).psh hfin
      (hK l).isClosed.measurableSet (hMA l)
      (fun ζ hζ => by
        have h := (hbd ζ hζ).sub ((hA l).tendsto_frontier ζ hζ)
        rw [sub_zero] at h
        exact h) hM' hε hs
    have hvolE : ENNReal.ofReal B * volume E ≤ ENNReal.ofReal (η' / 2) :=
      (mul_le_mul' le_rfl ((ENNReal.mul_le_iff_le_inv hc0 hctop).mp hvol)).trans hl
    have hpt : ∀ x ∈ L, ENNReal.ofReal |A l x - v x| ≤
        ENNReal.ofReal (s + ε * M') + E.indicator (fun _ => ENNReal.ofReal B) x := by
      intro x hx
      have hxQ : x ∈ Q := hLQ hx
      rw [abs_of_nonneg (by linarith [hvA l x hxQ])]
      by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]
        refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
        linarith [(hvb x hxQ).1, (hAb l x hxQ).2]
      · rw [indicator_of_notMem hxE, add_zero]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ¬ v x < (A l x + -s) + ε * (‖x‖ ^ 2 - M') := fun h => hxE ⟨hxQ, h⟩
        have h2 : 0 ≤ ε * ‖x‖ ^ 2 := by positivity
        linarith [not_lt.mp h1]
    calc ∫⁻ x in L, ENNReal.ofReal |A l x - v x|
        ≤ ∫⁻ x in L, (ENNReal.ofReal (s + ε * M') + E.indicator (fun _ => ENNReal.ofReal B) x) :=
          setLIntegral_mono' hL.measurableSet hpt
      _ = ENNReal.ofReal (s + ε * M') * volume L +
            ∫⁻ x in L, E.indicator (fun _ => ENNReal.ofReal B) x := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (η' / 2) + ENNReal.ofReal (η' / 2) := by
          refine add_le_add ?_ ?_
          · rw [← ENNReal.ofReal_toReal (hL.measure_lt_top (μ := volume)).ne,
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hsεM
          · refine (lintegral_indicator_const_le E _).trans ?_
            exact (mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)).trans hvolE
      _ = ENNReal.ofReal η' := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
      _ ≤ η := hη'η.le
  refine ⟨A, hA, hMA, fun l z hz => ⟨hvA l z hz, (hAb l z hz).2⟩, hlim, fun L hL hLQ b hb => ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_relCapacity_add_lt_of_localL1 (fun l => (hA l).psh) hv hlim hL hLQ hb)
    (fun _ => zero_le) fun l => relCapacity_mono ?_
  rintro z ⟨hzL, hz⟩
  have hz' : b < |A l z - v z| := hz
  rw [abs_of_nonneg (by linarith [hvA l z (hLQ hzL)])] at hz'
  exact ⟨hzL, show v z + b < A l z by linarith⟩

/-- **Mixed products along the exhaustion** (FPT `thm:bounded-multifactor-common-measure`, end of
Step 2, via TN's bounded mixed capacity continuity instead of decreasing continuity): for a tuple
`v₁, …, vₙ` as in `exists_kolodziej_exhaustion`, the Kołodziej solutions `A_{l,i}` of
`(ddᶜA_{l,i})ⁿ = 𝟙_{K_l}(ddᶜvᵢ)ⁿ` satisfy `vᵢ ≤ A_{l,i} ≤ 0` and
`ddᶜA_{l,1} ∧ ⋯ ∧ ddᶜA_{l,n} → ddᶜv₁ ∧ ⋯ ∧ ddᶜvₙ` weakly on `Q`. -/
theorem exists_kolodziej_exhaustion_mixed (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {v : Fin n → ComplexModel n → ℝ} (hv : IsLocallyBoundedMixedPshOn (polydiskAtOpens a R) v)
    {B : ℝ} (hB : 0 ≤ B) (hvb : ∀ i, ∀ z ∈ polydiskAt a R, -B ≤ v i z ∧ v i z ≤ 0)
    (hbd : ∀ i, ∀ ζ ∈ frontier (polydiskAt a R), Tendsto (v i) (𝓝[polydiskAt a R] ζ) (𝓝 0))
    (hfin : ∀ i, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (v i) (hv i) (polydiskAt a R) < ⊤)
    {K : ℕ → Set (ComplexModel n)} (hK : ∀ l, IsCompact (K l)) (hKQ : ∀ l, K l ⊆ polydiskAt a R)
    (hKmono : Monotone K) (hKcov : ∀ z ∈ polydiskAt a R, ∃ l, z ∈ K l) :
    ∃ (A : ℕ → Fin n → ComplexModel n → ℝ) (hA : ∀ l i, IsCegrellE0 (polydiskAtOpens a R) (A l i)),
      (∀ l i, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (A l i) (hA l i).psh =
        (canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (v i) (hv i)).restrict (K l)) ∧
      (∀ l i, ∀ z ∈ polydiskAt a R, v i z ≤ A l i z ∧ A l i z ≤ 0) ∧
      ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ polydiskAt a R →
        Tendsto (fun l => ∫ z, φ z ∂MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure
          (polydiskAtOpens a R) (A l) (fun i => (hA l i).psh)) atTop
          (𝓝 (∫ z, φ z ∂MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure
            (polydiskAtOpens a R) v hv)) := by
  choose A hA hMA hAb _hlim hcap using fun i => exists_kolodziej_exhaustion hn a hR (hv i) hB
    (hvb i) (hbd i) (hfin i) hK hKQ hKmono hKcov
  refine ⟨fun l i => A i l, fun l i => hA i l, fun l i => hMA i l, fun l i => hAb i l,
    fun φ hφ hφc hφQ => ?_⟩
  have hQb : Bornology.IsBounded (polydiskAt a R) := isBounded_polydiskAt a hR
  refine tendsto_integral_mixed_of_relCapacity hφc.isCompact hφQ (fun l i => (hA i l).psh) hv
    (by linarith : (0 : ℝ) ≤ B) (fun l i z hz => ⟨(hvb i z hz).1.trans (hAb i l z hz).1,
      (hAb i l z hz).2.trans hB⟩) (fun i z hz => ⟨(hvb i z hz).1, (hvb i z hz).2.trans hB⟩)
    (fun i V hVQ T hT hTV b hb => ?_) hφ hφc subset_rfl
  have h := tendsto_relCapacity_of_le_opens hVQ hQb hT hTV
    (hcap i T hT (hTV.trans hVQ) b hb)
  refine h.congr fun l => ?_
  rfl

end SGPT.Envelopes.MADirichlet
