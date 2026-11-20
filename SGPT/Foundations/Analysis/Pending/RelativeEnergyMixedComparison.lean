import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy
import SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction

/-!
# Mixed integral comparison for singular same-type potentials

The mixed-integral bounds underlying Xia SGPT (3.33), PDF0119. Actual
same-singularity total-mass invariance supplies the one-slot comparison;
pole-nullness transports its level sets to the canonical signed difference.
Neither the model nor any potential is required to be globally bounded.
The energy cocycle itself is not assumed or concluded here.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativeEnergyMixedComparison

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  RelativeEnergyIntegrability BoundedMongeAmpereEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual one-slot superlevel comparison for a common-pole-corrected
difference. Active-slot measures give no mass to the common pole locus. -/
theorem measure_lt_le_measure_le_of_sameSingularityType
    (omega : KahlerBackground n M)
    {eta : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal}
    (i₀ : Fin n) {x y : M → EReal}
    (hx : ∀ i, IsThetaPshPotential (eta i).val (Function.update w i₀ x i))
    (hy : ∀ i, IsThetaPshPotential (eta i).val (Function.update w i₀ y i))
    (hxy : SameSingularityTypeOn x y univ) (t : ℝ) :
    globalMixedMeasure eta (Function.update w i₀ y) (fun i => (hy i).1)
        {p | t < canonicalERealDiffToReal (y p) (x p)} ≤
      globalMixedMeasure eta (Function.update w i₀ x) (fun i => (hx i).1)
        {p | t ≤ canonicalERealDiffToReal (y p) (x p)} := by
  classical
  let c : M → EReal := fun p => x p - ((-t : ℝ) : EReal)
  have hxi : IsThetaPshPotential (eta i₀).val x := by simpa using hx i₀
  have hyi : IsThetaPshPotential (eta i₀).val y := by simpa using hy i₀
  have hci : IsThetaPshPotential (eta i₀).val c := hxi.sub_const (-t)
  have hc : ∀ i, IsThetaPshPotential (eta i).val (Function.update w i₀ c i) := by
    intro i
    by_cases hi : i = i₀
    · subst i; simpa using hci
    · simpa [Function.update_of_ne hi] using hx i
  have hm : ∀ i, IsThetaPshPotential (eta i).val
      (Function.update w i₀ (fun p => max (c p) (y p)) i) := by
    intro i
    by_cases hi : i = i₀
    · subst i; simpa using SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hci hyi
    · simpa [Function.update_of_ne hi] using hx i
  have hcy : SameSingularityTypeOn c y univ := by
    have hshift : SameSingularityTypeOn c x univ := by
      simpa only [c, sub_eq_add_neg, ← EReal.coe_neg, neg_neg] using
        sameSingularityTypeOn_add_const x univ t
    exact hshift.trans hxy
  have hmaxc : SameSingularityTypeOn (fun p => max (c p) (y p)) c univ :=
    ⟨DominationPrincipleReduction.moreSingularOn_max (MoreSingularOn.refl c univ) hcy.2,
      MoreSingularOn.of_le fun _ _ => le_max_left _ _⟩
  have hmass : globalMixedMeasure eta (Function.update w i₀ (fun p => max (c p) (y p)))
        (fun i => (hm i).1) univ =
      globalMixedMeasure eta (Function.update w i₀ c) (fun i => (hc i).1) univ := by
    apply MixedMass.globalMixedMass_eq_of_sameSingularityType
      (lt_of_le_of_lt (Nat.zero_le _) i₀.isLt) omega hm hc
    intro i
    by_cases hi : i = i₀
    · subst i; simpa using hmaxc
    · simpa [Function.update_of_ne hi] using SameSingularityTypeOn.refl (w i) univ
  have hcmp := GlobalSlotComparison.globalMixedMeasure_comparison omega w i₀
    (fun i => (hc i).1) (fun i => (hy i).1) (fun i => (hm i).1) hmass
  rw [globalMixedMeasure_update_sub_const i₀ (-t) (fun i => (hx i).1)
    (fun i => (hc i).1)] at hcmp
  have hxne : ∀ᵐ p ∂globalMixedMeasure eta (Function.update w i₀ x) (fun i => (hx i).1),
      x p ≠ ⊥ := by
    apply ae_iff.mpr
    simpa [Function.update] using
      GlobalSlotComparison.globalMixedMeasure_pole_null (fun i => (hx i).1) i₀
  have hyne : ∀ᵐ p ∂globalMixedMeasure eta (Function.update w i₀ y) (fun i => (hy i).1),
      y p ≠ ⊥ := by
    apply ae_iff.mpr
    simpa [Function.update] using
      GlobalSlotComparison.globalMixedMeasure_pole_null (fun i => (hy i).1) i₀
  have hs₁ : globalMixedMeasure eta (Function.update w i₀ y) (fun i => (hy i).1)
        {p | c p < y p} =
      globalMixedMeasure eta (Function.update w i₀ y) (fun i => (hy i).1)
        {p | t < canonicalERealDiffToReal (y p) (x p)} := by
    apply measure_congr
    filter_upwards [hyne] with p hyp
    have hxp : x p ≠ ⊥ := fun h => hyp ((sameSingularityTypeOn_eq_bot_iff hxy (mem_univ p)).mp h)
    apply propext
    change (x p - ((-t : ℝ) : EReal) < y p) ↔
      t < canonicalERealDiffToReal (y p) (x p)
    rw [canonicalDiff_eq_sub_toReal (hyi.1.quasiPlurisubharmonic.ne_top p)
      (hxi.1.quasiPlurisubharmonic.ne_top p)
      (sameSingularityTypeOn_eq_bot_iff hxy.symm (mem_univ p))]
    exact sub_coe_neg_lt_iff hxp (hxi.1.quasiPlurisubharmonic.ne_top p) hyp
      (hyi.1.quasiPlurisubharmonic.ne_top p) t
  have hs₂ : globalMixedMeasure eta (Function.update w i₀ x) (fun i => (hx i).1)
        {p | c p ≤ y p} =
      globalMixedMeasure eta (Function.update w i₀ x) (fun i => (hx i).1)
        {p | t ≤ canonicalERealDiffToReal (y p) (x p)} := by
    apply measure_congr
    filter_upwards [hxne] with p hxp
    have hyp : y p ≠ ⊥ := fun h => hxp ((sameSingularityTypeOn_eq_bot_iff hxy (mem_univ p)).mpr h)
    apply propext
    change (x p - ((-t : ℝ) : EReal) ≤ y p) ↔
      t ≤ canonicalERealDiffToReal (y p) (x p)
    rw [canonicalDiff_eq_sub_toReal (hyi.1.quasiPlurisubharmonic.ne_top p)
      (hxi.1.quasiPlurisubharmonic.ne_top p)
      (sameSingularityTypeOn_eq_bot_iff hxy.symm (mem_univ p))]
    exact sub_coe_neg_le_iff hxp (hxi.1.quasiPlurisubharmonic.ne_top p) hyp
      (hyi.1.quasiPlurisubharmonic.ne_top p) t
  rwa [hs₁, hs₂] at hcmp

/-- Replacing one potential slot by a same-type potential decreases the
integral of the genuine bounded signed difference, even for singular slots. -/
theorem integral_canonicalDiff_le_of_update
    (omega : KahlerBackground n M)
    {eta : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal}
    (i₀ : Fin n) {u v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential (eta i).val (Function.update w i₀ u i))
    (hv : ∀ i, IsThetaPshPotential (eta i).val (Function.update w i₀ v i))
    (huv : SameSingularityTypeOn u v univ) :
    (∫ p, canonicalERealDiffToReal (u p) (v p)
      ∂globalMixedMeasure eta (Function.update w i₀ u) (fun i => (hu i).1)) ≤
    ∫ p, canonicalERealDiffToReal (u p) (v p)
      ∂globalMixedMeasure eta (Function.update w i₀ v) (fun i => (hv i).1) := by
  classical
  let := globalMixedMeasure_isFiniteMeasure omega (fun i => (hu i).1)
  let := globalMixedMeasure_isFiniteMeasure omega (fun i => (hv i).1)
  let μu := globalMixedMeasure eta (Function.update w i₀ u) (fun i => (hu i).1)
  let μv := globalMixedMeasure eta (Function.update w i₀ v) (fun i => (hv i).1)
  let f : M → ℝ := fun p => canonicalERealDiffToReal (u p) (v p)
  have hui : IsThetaPshPotential (eta i₀).val u := by simpa using hu i₀
  have hvi : IsThetaPshPotential (eta i₀).val v := by simpa using hv i₀
  have hfm : Measurable f := measurable_canonicalERealDiffToReal.comp
    ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hui.1).prodMk
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hvi.1))
  obtain ⟨C, _, hC⟩ := exists_abs_canonicalDiff_le_of_sameSingularityType huv
    hui.1.quasiPlurisubharmonic.ne_top hvi.1.quasiPlurisubharmonic.ne_top
  have hfb : ∃ Q : ℝ, ∀ p, |f p| ≤ Q := ⟨C, hC⟩
  have hfb' : ∃ Q : ℝ, ∀ p, |-f p| ≤ Q := ⟨C, fun p => by rw [abs_neg]; exact hC p⟩
  have hint : ∀ (μ : Measure M) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
    (integrable_const C).mono' hfm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC p)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint μu),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint μv)]
  have hpos : ∫⁻ p, ENNReal.ofReal (f p) ∂μu ≤ ∫⁻ p, ENNReal.ofReal (f p) ∂μv := by
    rw [lintegral_ofReal_eq_max_zero μu f, lintegral_ofReal_eq_max_zero μv f,
      lintegral_eq_lintegral_meas_lt (f := fun p => max (f p) 0) μu
        (ae_of_all _ fun p => le_max_right _ _) (hfm.max measurable_const).aemeasurable,
      lintegral_eq_lintegral_meas_le (f := fun p => max (f p) 0) μv
        (ae_of_all _ fun p => le_max_right _ _) (hfm.max measurable_const).aemeasurable]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [setOf_lt_max_zero ht, setOf_le_max_zero ht]
    exact measure_lt_le_measure_le_of_sameSingularityType omega i₀ hv hu huv.symm t
  have hneg : ∫⁻ p, ENNReal.ofReal (-f p) ∂μv ≤ ∫⁻ p, ENNReal.ofReal (-f p) ∂μu := by
    have hfm' : Measurable fun p => -f p := hfm.neg
    rw [lintegral_ofReal_eq_max_zero μv (fun p => -f p),
      lintegral_ofReal_eq_max_zero μu (fun p => -f p),
      lintegral_eq_lintegral_meas_lt (f := fun p => max (-f p) 0) μv
        (ae_of_all _ fun p => le_max_right _ _) (hfm'.max measurable_const).aemeasurable,
      lintegral_eq_lintegral_meas_le (f := fun p => max (-f p) 0) μu
        (ae_of_all _ fun p => le_max_right _ _) (hfm'.max measurable_const).aemeasurable]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [setOf_lt_max_zero ht, setOf_le_max_zero ht]
    have e : ∀ p, -f p = canonicalERealDiffToReal (v p) (u p) := fun p => by
      dsimp [f]
      exact (canonicalERealDiffToReal_swap (v p) (u p)).symm
    simp only [e]
    exact measure_lt_le_measure_le_of_sameSingularityType omega i₀ hu hv huv t
  have h₁ := ENNReal.toReal_mono (lintegral_ofReal_ne_top hfb) hpos
  have h₂ := ENNReal.toReal_mono (lintegral_ofReal_ne_top hfb') hneg
  linarith

/-- Every mixed signed integral lies between the two endpoint integrals.
This proves the mixed-integral bounds used in Xia (3.33) for singular endpoints. -/
theorem integral_endpointMixedMeasure_bounds
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : SameSingularityTypeOn u v univ)
    (j : Fin (n + 1)) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => u) (fun _ => hu.1)) ≤
      (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂endpointMixedMeasure theta v u hv hu j) ∧
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂endpointMixedMeasure theta v u hv hu j) ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => v) (fun _ => hv.1) := by
  classical
  let S : Fin n → M → EReal := fun _ => v
  let g : ℕ → ℝ := fun k => ∫ x, canonicalERealDiffToReal (u x) (v x)
    ∂layMeasure theta n k u v S hu.1 hv.1 (fun _ => hv.1)
  have hgen (k : ℕ) : ∀ i, IsThetaPshPotential theta.val (lay n k u v S i) := by
    intro i
    unfold lay
    split_ifs
    · exact hu
    · exact hv
    · exact hv
  have hstep : ∀ k, k < n → g (k + 1) ≤ g k := by
    intro k hk
    obtain ⟨e₁, e₂⟩ := update_lay_at hk hk u v S
    have hu' : ∀ i, IsThetaPshPotential ((fun _ : Fin n => theta) i).val
        (Function.update (lay n k u v S) ⟨k, hk⟩ u i) := by
      rw [e₁]; exact hgen (k + 1)
    have hv' : ∀ i, IsThetaPshPotential ((fun _ : Fin n => theta) i).val
        (Function.update (lay n k u v S) ⟨k, hk⟩ v i) := by
      rw [e₂]; exact hgen k
    have h := integral_canonicalDiff_le_of_update omega ⟨k, hk⟩ hu' hv' huv
    rwa [BoundedIntegrationByParts.globalMixedMeasure_congr' rfl e₁ (fun i => (hu' i).1)
        (lay_psh hu.1 hv.1 fun _ => hv.1),
      BoundedIntegrationByParts.globalMixedMeasure_congr' rfl e₂ (fun i => (hv' i).1)
        (lay_psh hu.1 hv.1 fun _ => hv.1)] at h
  have hup : ∀ k, k ≤ n → g k ≤ g 0 := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih => intro hk; exact (hstep k (by omega)).trans (ih (by omega))
  have hdown : ∀ m k, k + m = n → g n ≤ g k := by
    intro m
    induction m with
    | zero => intro k hk; simp only [add_zero] at hk; rw [hk]
    | succ m ih => intro k hk; exact (ih (k + 1) (by omega)).trans (hstep k (by omega))
  have hgn : g n = ∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => u) (fun _ => hu.1) := by
    dsimp [g]
    congr 1
    exact BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
      (by funext i; simp [lay, i.isLt]) _ _
  have hg₀ : g 0 = ∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => v) (fun _ => hv.1) := by
    dsimp [g]
    congr 1
    exact BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
      (by funext i; simp [lay, i.isLt]) _ _
  have hgj : (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂endpointMixedMeasure theta v u hv hu j) = g j.val := by
    rw [endpointMixedMeasure_eq_layMeasure]
  rw [← hgn, ← hg₀, hgj]
  exact ⟨hdown (n - j.val) j.val (by omega), hup j.val (by omega)⟩

/-- The actual arithmetic mean defining the finite-type energy with reference
`v` lies between the two endpoint integrals. Relating it to energy differences
with a third reference still requires the separate singular-model cocycle. -/
theorem integral_le_relativeEnergyOfMinimalType_le
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : SameSingularityTypeOn u v univ) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => u) (fun _ => hu.1)) ≤
        relativeEnergyOfMinimalType theta v u hv hu ∧
    relativeEnergyOfMinimalType theta v u hv hu ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => v) (fun _ => hv.1) := by
  have hbounds := integral_endpointMixedMeasure_bounds omega theta hu hv huv
  have hpos : (0 : ℝ) < n + 1 := by positivity
  unfold relativeEnergyOfMinimalType relativeEnergyTerm
  constructor
  · apply (le_div_iff₀ hpos).mpr
    have h := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin (n + 1)))
      (fun j => ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂endpointMixedMeasure theta v u hv hu j)
      (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => u) (fun _ => hu.1))
      (fun j _ => (hbounds j).1)
    simpa [nsmul_eq_mul, mul_comm] using h
  · apply (div_le_iff₀ hpos).mpr
    have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin (n + 1)))
      (fun j => ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂endpointMixedMeasure theta v u hv hu j)
      (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => v) (fun _ => hv.1))
      (fun j _ => (hbounds j).2)
    simpa [nsmul_eq_mul, mul_comm] using h

end

end SGPT.Foundations.Analysis.Pending.RelativeEnergyMixedComparison
