import SGPT.NPP.LogConcavityDinewBounded
import SGPT.MongeAmpere.LocalSmoothDensityBoundedMaxApproximation

/-!
# Dinew's inequality for non-pluripolar products in coordinates

FPT `prop:nonpluripolar-multifactor-common-measure` for a common measure with continuous
density with respect to Lebesgue measure: let `u₁, …, uₙ` be plurisubharmonic (possibly
unbounded, extended-real valued) on an open set `Ω ⊆ ℂⁿ`, `f ≥ 0` continuous on `Ω`, and
`cᵢ ≥ 0` with `⟨(ddᶜuᵢ)ⁿ⟩ ≥ cᵢ f dV` on `Ω` (non-pluripolar Monge–Ampère measures, i.e. TN's
truncation limits). Then `⟨ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ⟩ ≥ (∏ᵢ cᵢ^{1/n}) f dV` on `Ω`
(`mixedTruncationLimitMeasure_ge_withDensity`).

Proof.
* Constant densities on a ball (`mixedTruncationLimitMeasure_ge_on_ball`): the maxima
  `max(uᵢ, ρᵢ - cᵢⱼ)` with strictly psh quadratics `ρᵢ` and generic levels `cᵢⱼ ↑ ∞` are locally
  bounded and keep the lower bound `aᵢ dV` (`SGPT.MongeAmpere.exists_quadratic_lower_bound_
  preserving_bounded_maxima`); Dinew's inequality for bounded functions
  (`mixedBedfordTaylor_ge_on_ball`) applies to them; on the plurifine open set
  `{ρᵢ - cᵢⱼ < uᵢ ∀ i}` the mixed non-pluripolar products of the maxima and of the `uᵢ` agree
  (TN `mixedTruncationLimitMeasure_restrict_max_eq`); these sets exhaust the complement of the
  pole sets, which are Lebesgue-null because `⟨(ddᶜuᵢ)ⁿ⟩ ≥ aᵢ dV` and non-pluripolar measures do
  not charge pole sets.
* Continuous densities: on small balls `f` is within `δ` of a constant; the local estimates are
  glued by a Lindelöf covering (`restrict_le_restrict_of_isLindelof`) and `δ → 0` by monotone
  convergence.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder ContDiff ENNReal
open TopologicalSpace

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

variable {n : ℕ}

/-! ### Local-to-global for measure inequalities -/

/-- Inequalities of restrictions to countably many measurable sets glue. -/
theorem restrict_le_restrict_iUnion_of_le {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    {U : ℕ → Set X} (hU : ∀ k, MeasurableSet (U k))
    (h : ∀ k, μ.restrict (U k) ≤ ν.restrict (U k)) :
    μ.restrict (⋃ k, U k) ≤ ν.restrict (⋃ k, U k) := by
  rw [← iUnion_disjointed, Measure.restrict_iUnion (disjoint_disjointed U)
    (MeasurableSet.disjointed hU), Measure.restrict_iUnion (disjoint_disjointed U)
    (MeasurableSet.disjointed hU)]
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  refine ENNReal.tsum_le_tsum fun k => ?_
  have hD : MeasurableSet (disjointed U k) := MeasurableSet.disjointed hU k
  have hsub : disjointed U k ⊆ U k := disjointed_subset U k
  calc μ.restrict (disjointed U k) s = μ.restrict (U k) (s ∩ disjointed U k) := by
        rw [Measure.restrict_apply hs, Measure.restrict_apply (hs.inter hD), inter_assoc,
          inter_eq_left.mpr hsub]
    _ ≤ ν.restrict (U k) (s ∩ disjointed U k) := h k _
    _ = ν.restrict (disjointed U k) s := by
        rw [Measure.restrict_apply hs, Measure.restrict_apply (hs.inter hD), inter_assoc,
          inter_eq_left.mpr hsub]

/-- **Local inequalities of measures glue** over a Lindelöf set. -/
theorem restrict_le_restrict_of_isLindelof {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ ν : Measure X} {S : Set X} (hS : IsLindelof S)
    (h : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ.restrict U ≤ ν.restrict U) :
    μ.restrict S ≤ ν.restrict S := by
  choose U hUo hxU hle using h
  obtain ⟨r, hr, hSr⟩ := hS.elim_countable_subcover (fun x : S => U x.1 x.2)
    (fun x => hUo x.1 x.2) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU x hx⟩)
  rcases r.eq_empty_or_nonempty with hr0 | hrne
  · have : S = ∅ := by
      rw [hr0] at hSr
      simpa using hSr
    rw [this, Measure.restrict_empty, Measure.restrict_empty]
  obtain ⟨φ, hφ⟩ := hr.exists_eq_range hrne
  set T : ℕ → Set X := fun k => U (φ k).1 (φ k).2 with hT
  have hST : S ⊆ ⋃ k, T k := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hSr hx)
    rw [hφ] at hy
    obtain ⟨k, rfl⟩ := hy
    exact mem_iUnion.mpr ⟨k, hxy⟩
  have hglue := restrict_le_restrict_iUnion_of_le (μ := μ) (ν := ν) (U := T)
    (fun k => (hUo _ _).measurableSet) (fun k => hle _ _)
  calc μ.restrict S = (μ.restrict (⋃ k, T k)).restrict S :=
        (Measure.restrict_restrict_of_subset hST).symm
    _ ≤ (ν.restrict (⋃ k, T k)).restrict S := Measure.restrict_mono subset_rfl hglue
    _ = ν.restrict S := Measure.restrict_restrict_of_subset hST

/-! ### Bounded maxima keeping a constant lower bound -/

/-- The maxima `max(u, ρ - cⱼ)` with a strictly psh quadratic `ρ` and generic levels `cⱼ ↑ ∞` are
locally bounded psh and keep a constant lower bound of the non-pluripolar Monge–Ampère measure
(a restatement of `SGPT.MongeAmpere.exists_quadratic_lower_bound_preserving_bounded_maxima`). -/
theorem exists_bounded_maxima_of_const (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) {a : ℝ} (ha : 0 ≤ a)
    (hμ : ENNReal.ofReal a • volume.restrict (Ω : Set (ComplexModel n)) ≤
      truncationLimitMeasure Ω u hu) :
    ∃ (ρ : ComplexModel n → ℝ) (c : ℕ → ℝ), IsSmoothPshOn Ω ρ ∧ Monotone c ∧
      Tendsto c atTop atTop ∧
      ∃ hb : ∀ j, IsLocallyBoundedPshOn Ω
          (fun z => (max (u z) ((ρ z - c j : ℝ) : EReal)).toReal),
        (∀ j z, z ∈ Ω → (((max (u z) ((ρ z - c j : ℝ) : EReal)).toReal : ℝ) : EReal) =
            max (u z) ((ρ z - c j : ℝ) : EReal)) ∧
        ∀ j, ENNReal.ofReal a • volume.restrict (Ω : Set (ComplexModel n)) ≤
          canonicalBedfordTaylorMeasure Ω
            (fun z => (max (u z) ((ρ z - c j : ℝ) : EReal)).toReal) (hb j) := by
  have hf : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun _ => ENNReal.ofReal a) ≤ truncationLimitMeasure Ω u hu := by
    rwa [withDensity_const]
  obtain ⟨-, hρ, -, -, c, hcm, -, hct, -, hmax, hb, heq, -, hlim⟩ :=
    SGPT.MongeAmpere.exists_quadratic_lower_bound_preserving_bounded_maxima hn hu
      (f := fun _ => a) measurable_const (fun _ => ha) ha (fun _ _ => le_rfl) hf
  refine ⟨_, c, hρ, hcm.monotone, hct, hb, heq, fun j => ?_⟩
  rw [← (hlim j).1, ← withDensity_const]
  exact (hlim j).2

/-! ### Constant densities on a ball -/

theorem prod_rpow_div (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {κ : ℝ} (hκ : 0 < κ) :
    κ * ∏ i, (a i / κ) ^ ((n : ℝ)⁻¹) = ∏ i, a i ^ ((n : ℝ)⁻¹) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [Real.div_rpow (ha _) hκ.le]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast, ← Real.rpow_mul hκ.le, inv_mul_cancel₀ hn', Real.rpow_one]
  field_simp

/-- **Dinew's inequality for non-pluripolar products, constant densities, on a ball.** -/
theorem mixedTruncationLimitMeasure_ge_on_ball (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hμ : ∀ i, ENNReal.ofReal (a i) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      truncationLimitMeasure Ω (u i) (hu i))
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ R ⊆ Ω) :
    ENNReal.ofReal (∏ i, a i ^ ((n : ℝ)⁻¹)) • volume.restrict (Metric.ball x₀ (R / 4)) ≤
      (mixedTruncationLimitMeasure Ω u hu).restrict (Metric.ball x₀ (R / 4)) := by
  by_cases ha0 : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := ha0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [hi, Real.zero_rpow (inv_ne_zero (by exact_mod_cast hn.ne'))]),
      ENNReal.ofReal_zero, zero_smul]
    exact Measure.zero_le _
  push Not at ha0
  have hapos : ∀ i, 0 < a i := fun i => lt_of_le_of_ne (ha i) (ha0 i).symm
  choose ρ c hρ hcm hct hb heq hge using fun i => exists_bounded_maxima_of_const hn (hu i) (ha i) (hμ i)
  set B : Set (ComplexModel n) := Metric.ball x₀ (R / 4) with hB
  set P : ℝ := ∏ i, a i ^ ((n : ℝ)⁻¹) with hP
  set κ : ℝ := mongeAmpereConst n with hκ
  have hκpos : 0 < κ := mongeAmpereConst_pos
  have hBΩ : B ⊆ Ω := fun z hz =>
    hball (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hz))
  -- the obstacles
  set w : ℕ → Fin n → ComplexModel n → EReal := fun j i z => ((ρ i z - c i j : ℝ) : EReal)
    with hw
  have hwpsh : ∀ j i, PlurisubharmonicOn (w j i) Ω := fun j i =>
    ((SGPT.MongeAmpere.truncationLimitMeasure_smooth_sub_const (hρ i)).2 (c i j)).1.2.1
  set G : ℕ → Set (ComplexModel n) := fun j => {z | z ∈ Ω ∧ ∀ i, w j i z < u i z} with hG
  -- the estimate on each `G j`
  have hstep : ∀ j, ∀ s, MeasurableSet s →
      ENNReal.ofReal P * volume (s ∩ B ∩ G j) ≤ mixedTruncationLimitMeasure Ω u hu (s ∩ B) := by
    intro j s hs
    set v : Fin n → ComplexModel n → ℝ :=
      fun i z => (max (u i z) ((ρ i z - c i j : ℝ) : EReal)).toReal with hv
    have hvb : IsLocallyBoundedMixedPshOn Ω v := fun i => hb i j
    have hmax : ∀ i, PlurisubharmonicOn (fun z => max (u i z) (w j i z)) Ω := fun i =>
      (hu i).max (hwpsh j i)
    have hBT := mixedBedfordTaylor_ge_on_ball hn hvb (c := fun i => a i / κ)
      (fun i => div_pos (hapos i) hκpos)
      (fun i => by
        rw [mul_div_cancel₀ _ hκpos.ne']
        exact hge i j) hR hball
    rw [prod_rpow_div hn ha hκpos] at hBT
    have hNP : mixedTruncationLimitMeasure Ω (fun i z => max (u i z) (w j i z)) hmax =
        canonicalMixedBedfordTaylorMeasure Ω v hvb :=
      mixedTruncationLimitMeasure_eq_canonical_of_eqOn hvb hmax fun i z hz =>
        (heq i j z hz).symm
    have hloc := mixedTruncationLimitMeasure_restrict_max_eq hu (hwpsh j) hmax
    have hsB : MeasurableSet (s ∩ B) := hs.inter Metric.isOpen_ball.measurableSet
    calc ENNReal.ofReal P * volume (s ∩ B ∩ G j)
        = (ENNReal.ofReal P • volume.restrict B) (s ∩ G j) := by
          rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' Metric.isOpen_ball.measurableSet,
            inter_right_comm]
      _ ≤ ((canonicalMixedBedfordTaylorMeasure Ω v hvb).restrict B) (s ∩ G j) := hBT _
      _ = canonicalMixedBedfordTaylorMeasure Ω v hvb (s ∩ B ∩ G j) := by
          rw [Measure.restrict_apply' Metric.isOpen_ball.measurableSet, inter_right_comm]
      _ = ((mixedTruncationLimitMeasure Ω (fun i z => max (u i z) (w j i z)) hmax).restrict
            (G j)) (s ∩ B) := by
          rw [Measure.restrict_apply hsB, hNP]
      _ = ((mixedTruncationLimitMeasure Ω u hu).restrict (G j)) (s ∩ B) := by
          rw [hG, hloc]
      _ ≤ mixedTruncationLimitMeasure Ω u hu (s ∩ B) := by
          rw [Measure.restrict_apply hsB]
          exact measure_mono inter_subset_left
  -- the sets `G j` increase
  have hGmono : Monotone G := by
    intro j k hjk z hz
    refine ⟨hz.1, fun i => lt_of_le_of_lt ?_ (hz.2 i)⟩
    simp only [hw]
    exact EReal.coe_le_coe_iff.mpr (by linarith [hcm i hjk])
  -- the pole sets are Lebesgue-null
  have hpole : ∀ i, volume ({z | u i z = ⊥} ∩ (Ω : Set (ComplexModel n))) = 0 := by
    intro i
    have h1 := (hμ i) {z | u i z = ⊥}
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' Ω.isOpen.measurableSet,
      truncationLimitMeasure_poleSet] at h1
    have h2 : ENNReal.ofReal (a i) * volume ({z | u i z = ⊥} ∩ (Ω : Set (ComplexModel n))) = 0 :=
      le_antisymm h1 zero_le
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (ENNReal.ofReal_pos.mpr (hapos i)).ne'
    · exact h
  have hcomp : B \ ⋃ j, G j ⊆ ⋃ i, ({z | u i z = ⊥} ∩ (Ω : Set (ComplexModel n))) := by
    intro z ⟨hzB, hzG⟩
    by_contra hcon
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, not_exists, not_and] at hcon
    have hfin : ∀ i, ⊥ < u i z := fun i => bot_lt_iff_ne_bot.mpr fun h => hcon i h (hBΩ hzB)
    have hev : ∀ᶠ j in atTop, ∀ i, w j i z < u i z := by
      refine eventually_all.mpr fun i => ?_
      obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.mp (hfin i)
      filter_upwards [(hct i).eventually_gt_atTop (ρ i z - r)] with j hj
      refine lt_of_lt_of_le ?_ hr.le
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨j, hj⟩ := hev.exists
    exact hzG (mem_iUnion.mpr ⟨j, hBΩ hzB, hj⟩)
  have hnull : volume (B \ ⋃ j, G j) = 0 := by
    refine measure_mono_null hcomp ?_
    exact (measure_iUnion_null_iff).mpr hpole
  -- assemble
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, Measure.restrict_apply hs]
  have hsplit : volume (s ∩ B) ≤ volume (s ∩ B ∩ ⋃ j, G j) := by
    calc volume (s ∩ B) ≤ volume (s ∩ B ∩ ⋃ j, G j) + volume (B \ ⋃ j, G j) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro z hz
          by_cases hzG : z ∈ ⋃ j, G j
          · exact Or.inl ⟨hz, hzG⟩
          · exact Or.inr ⟨hz.2, hzG⟩
      _ = volume (s ∩ B ∩ ⋃ j, G j) := by rw [hnull, add_zero]
  have hunion : volume (s ∩ B ∩ ⋃ j, G j) = ⨆ j, volume (s ∩ B ∩ G j) := by
    rw [inter_iUnion]
    exact Directed.measure_iUnion (Monotone.directed_le fun j k hjk =>
      inter_subset_inter_right _ (hGmono hjk))
  calc ENNReal.ofReal P * volume (s ∩ B) ≤ ENNReal.ofReal P * ⨆ j, volume (s ∩ B ∩ G j) := by
        rw [← hunion]; gcongr
    _ = ⨆ j, ENNReal.ofReal P * volume (s ∩ B ∩ G j) := ENNReal.mul_iSup _ _
    _ ≤ _ := iSup_le fun j => hstep j s hs

end SGPT.NPP.LogConcavityDinew
