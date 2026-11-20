import SGPT.NPP.LogConcavityDinewBounded
import SGPT.NPP.LogConcavityDinewLocal
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Measure-theoretic tools for Monge–Ampère subsolutions

Three general facts about measures on an open set `Ω ⊆ ℂⁿ`, used to pass between local and
global lower bounds for Monge–Ampère measures and to take limits in them.

* `restrict_le_of_isCompact_le`: a measure `α` finite on the compact subsets of `Ω` with
  `α K ≤ ν K` for every compact `K ⊆ Ω` satisfies `α|_Ω ≤ ν` (every measure on `ℂⁿ` is inner
  regular on sets of finite measure).
* `restrict_le_of_tendsto_integral`: lower bounds pass to vague limits: if `α|_Ω ≤ μ k` for all
  `k` and `∫ φ dμ k → ∫ φ dν` for every continuous `φ` with compact support in `Ω`, then
  `α|_Ω ≤ ν`.
* `withDensity_le_of_forall_lt`: a continuous density lower bound may be checked locally with
  constants: if, near every `x ∈ Ω`, `ν ≥ c · dV` for every `c < g x`, then `ν ≥ g dV` on `Ω`.
* `exists_antitone_level_null`: for a measurable `g` and a measure that is finite on the compact
  subsets of `Ω`, there are levels `t k ↓ 0`, `t k > 0`, with `α (Ω ∩ {g = t k}) = 0` (only
  countably many level sets of a σ-finite measure have positive mass).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- **Lower bounds on compact sets give lower bounds on Borel sets.** -/
theorem restrict_le_of_isCompact_le {Ω : Opens (ComplexModel n)} {α ν : Measure (ComplexModel n)}
    (hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤)
    (hle : ∀ K, IsCompact K → K ⊆ Ω → α K ≤ ν K) :
    α.restrict (Ω : Set (ComplexModel n)) ≤ ν := by
  obtain ⟨U, hUmono, hUrc, hUabs⟩ := exists_exhaustion Ω
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.restrict_apply hs]
  have hunion : s ∩ (Ω : Set (ComplexModel n)) =
      ⋃ m, s ∩ closure (U m : Set (ComplexModel n)) := by
    ext z
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨hzs, hzΩ⟩
      obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hzΩ)
      exact ⟨m, hzs, subset_closure (hm rfl)⟩
    · rintro ⟨m, hzs, hzm⟩
      exact ⟨hzs, (hUrc m).2 hzm⟩
  have hmono : Monotone fun m => s ∩ closure (U m : Set (ComplexModel n)) :=
    fun m m' hmm' => inter_subset_inter_right _ (closure_mono (hUmono hmm'))
  rw [hunion, hmono.measure_iUnion]
  refine iSup_le fun m => ?_
  have hm : MeasurableSet (s ∩ closure (U m : Set (ComplexModel n))) :=
    hs.inter isClosed_closure.measurableSet
  have hfin : α (s ∩ closure (U m : Set (ComplexModel n))) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt (hα _ (hUrc m).1 (hUrc m).2)).ne
  rw [hm.measure_eq_iSup_isCompact_of_ne_top hfin]
  refine iSup₂_le fun K hKs => iSup_le fun hK => ?_
  exact (hle K hK (hKs.trans (inter_subset_right.trans (hUrc m).2))).trans
    (measure_mono (hKs.trans inter_subset_left))

/-- Integrals of a nonnegative test function are monotone in the measure. -/
theorem integral_le_integral_of_le {μ ν : Measure (ComplexModel n)} (hle : μ ≤ ν)
    {U : Set (ComplexModel n)} (hνU : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤)
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφ0 : ∀ z, 0 ≤ φ z) : ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν :=
  SGPT.NPP.LogConcavityDinew.integral_le_of_measure_le_of_compactSupport hle hνU hφ hφc hφU hφ0

/-- **Lower bounds pass to vague limits.** -/
theorem restrict_le_of_tendsto_integral {Ω : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} (hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤)
    {μ : ℕ → Measure (ComplexModel n)} {ν : Measure (ComplexModel n)}
    (hμ : ∀ k K, IsCompact K → K ⊆ Ω → μ k K < ⊤) (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (hle : ∀ k, α.restrict (Ω : Set (ComplexModel n)) ≤ μ k)
    (hlim : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (Ω : Set (ComplexModel n)) →
      Tendsto (fun k => ∫ z, φ z ∂(μ k)) atTop (𝓝 (∫ z, φ z ∂ν))) :
    α.restrict (Ω : Set (ComplexModel n)) ≤ ν := by
  have hαΩ : ∀ K, IsCompact K → K ⊆ Ω → α.restrict (Ω : Set (ComplexModel n)) K < ⊤ :=
    fun K hK hKΩ => (Measure.restrict_apply_le _ _).trans_lt (hα K hK hKΩ)
  have htest : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (Ω : Set (ComplexModel n)) → (∀ z, 0 ≤ φ z) →
      ∫ z, φ z ∂(α.restrict (Ω : Set (ComplexModel n))) ≤ ∫ z, φ z ∂ν := by
    intro φ hφ hφc hφΩ hφ0
    exact ge_of_tendsto' (hlim φ hφ hφc hφΩ) fun k =>
      integral_le_integral_of_le (hle k) (hμ k) hφ hφc hφΩ hφ0
  have hK : ∀ K, IsCompact K → K ⊆ Ω → α K ≤ ν K := by
    intro K hK hKΩ
    have h := measure_le_of_testFunction_integral_le hαΩ hν htest hK hKΩ
    rwa [Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKΩ] at h
  exact restrict_le_of_isCompact_le hα hK

/-- **A local lower bound with an additive error `2δ`, glued over `Ω`.** -/
theorem withDensity_le_of_forall_lt_sub {Ω : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
    (hg : ContinuousOn g Ω) {ν : Measure (ComplexModel n)}
    (h : ∀ x ∈ Ω, ∀ c : ℝ, c < g x → ∃ r > 0, Metric.ball x r ⊆ Ω ∧
      ENNReal.ofReal c • volume.restrict (Metric.ball x r) ≤ ν.restrict (Metric.ball x r))
    {δ : ℝ} (hδ : 0 < δ) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (g z - 2 * δ)) ≤ ν := by
  have hglue := SGPT.NPP.LogConcavityDinew.restrict_le_restrict_of_isLindelof
    (μ := (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (g z - 2 * δ))) (ν := ν)
    (HereditarilyLindelofSpace.isLindelof (Ω : Set (ComplexModel n))) fun x hx => by
      have hgc : ContinuousAt g x := hg.continuousAt (Ω.isOpen.mem_nhds hx)
      obtain ⟨δ₁, hδ₁, hgδ⟩ := Metric.continuousAt_iff.mp hgc δ hδ
      obtain ⟨r, hr, hrΩ, hle⟩ := h x hx (g x - δ) (by linarith)
      set ρ : ℝ := min r δ₁ with hρ
      have hρpos : 0 < ρ := lt_min hr hδ₁
      have hρr : Metric.ball x ρ ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
      refine ⟨Metric.ball x ρ, Metric.isOpen_ball, Metric.mem_ball_self hρpos, ?_⟩
      rw [restrict_withDensity Metric.isOpen_ball.measurableSet,
        Measure.restrict_restrict_of_subset (hρr.trans hrΩ)]
      calc (volume.restrict (Metric.ball x ρ)).withDensity
            (fun z => ENNReal.ofReal (g z - 2 * δ))
          ≤ (volume.restrict (Metric.ball x ρ)).withDensity
            (fun _ => ENNReal.ofReal (g x - δ)) := by
            refine withDensity_mono ?_
            filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
            have hz' : dist z x < δ₁ := lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
            have := hgδ hz'
            rw [Real.dist_eq] at this
            exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp this).2])
        _ = (ENNReal.ofReal (g x - δ) • volume.restrict (Metric.ball x r)).restrict
              (Metric.ball x ρ) := by
            rw [withDensity_const, Measure.restrict_smul,
              Measure.restrict_restrict_of_subset hρr]
        _ ≤ (ν.restrict (Metric.ball x r)).restrict (Metric.ball x ρ) :=
            Measure.restrict_mono subset_rfl hle
        _ = ν.restrict (Metric.ball x ρ) := Measure.restrict_restrict_of_subset hρr
  rw [restrict_withDensity Ω.isOpen.measurableSet,
    Measure.restrict_restrict Ω.isOpen.measurableSet, inter_self] at hglue
  exact hglue.trans Measure.restrict_le_self

/-- **Continuous density lower bounds are local and may be tested with constants.** If near
every point `x ∈ Ω` and for every `c < g x` the measure `ν` dominates `c · dV` on a ball around
`x`, then `ν ≥ g dV` on `Ω`. -/
theorem withDensity_le_of_forall_lt {Ω : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
    (hg : ContinuousOn g Ω) {ν : Measure (ComplexModel n)}
    (h : ∀ x ∈ Ω, ∀ c : ℝ, c < g x → ∃ r > 0, Metric.ball x r ⊆ Ω ∧
      ENNReal.ofReal c • volume.restrict (Metric.ball x r) ≤ ν.restrict (Metric.ball x r)) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (g z)) ≤ ν := by
  set ρ := volume.restrict (Ω : Set (ComplexModel n)) with hρ
  have hgm : AEMeasurable g ρ := hg.aemeasurable Ω.isOpen.measurableSet
  refine Measure.le_iff.mpr fun s hs => ?_
  set F : ℕ → ComplexModel n → ℝ≥0∞ :=
    fun k z => ENNReal.ofReal (g z - 2 * (1 / ((k : ℝ) + 1))) with hF
  have hFle : ∀ k, ∫⁻ z in s, F k z ∂ρ ≤ ν s := fun k => by
    have := withDensity_le_of_forall_lt_sub hg h (δ := 1 / ((k : ℝ) + 1)) (by positivity) s
    rwa [withDensity_apply _ hs] at this
  have hFmono : ∀ z, Monotone fun k => F k z := by
    intro z j k hjk
    refine ENNReal.ofReal_le_ofReal ?_
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
    linarith
  have hFsup : ∀ z, ⨆ k, F k z = ENNReal.ofReal (g z) := by
    intro z
    refine iSup_eq_of_tendsto (hFmono z) ?_
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun k : ℕ => g z - 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 (g z)) := by
      simpa using (h0.const_mul (2 : ℝ)).const_sub (g z)
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  have hFm : ∀ k, AEMeasurable (F k) (ρ.restrict s) := fun k =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hgm.sub aemeasurable_const).mono_measure Measure.restrict_le_self)
  calc ρ.withDensity (fun z => ENNReal.ofReal (g z)) s
      = ∫⁻ z in s, ENNReal.ofReal (g z) ∂ρ := withDensity_apply _ hs
    _ = ∫⁻ z in s, ⨆ k, F k z ∂ρ := by simp_rw [hFsup]
    _ = ⨆ k, ∫⁻ z in s, F k z ∂ρ := lintegral_iSup' hFm (ae_of_all _ hFmono)
    _ ≤ ν s := iSup_le hFle

/-- A measure finite on the compact subsets of an open set `Ω` is σ-finite on `Ω`. -/
theorem sigmaFinite_restrict {Ω : Opens (ComplexModel n)} {α : Measure (ComplexModel n)}
    (hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤) :
    SigmaFinite (α.restrict (Ω : Set (ComplexModel n))) := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  refine ⟨⟨⟨fun m => closure (U m : Set (ComplexModel n)) ∪ (Ω : Set (ComplexModel n))ᶜ,
    fun _ => trivial, fun m => ?_, ?_⟩⟩⟩
  · refine (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact (Measure.restrict_apply_le _ _).trans_lt (hα _ (hUrc m).1 (hUrc m).2)
    · rw [Measure.restrict_apply' Ω.isOpen.measurableSet, compl_inter_self, measure_empty]
      exact ENNReal.zero_lt_top
  · refine eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ (Ω : Set (ComplexModel n))
    · obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hz)
      exact mem_iUnion.mpr ⟨m, Or.inl (subset_closure (hm rfl))⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr hz⟩

/-- **Generic levels.** For a measurable `g` and a measure finite on the compact subsets of `Ω`,
there are levels `t k ↓ 0` with `t k > 0` such that `Ω ∩ {g = t k}` is a null set. -/
theorem exists_antitone_level_null {Ω : Opens (ComplexModel n)} {α : Measure (ComplexModel n)}
    (hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤) {g : ComplexModel n → ℝ} (hg : Measurable g) :
    ∃ t : ℕ → ℝ, Antitone t ∧ (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
      ∀ k, α ((Ω : Set (ComplexModel n)) ∩ {z | g z = t k}) = 0 := by
  have := sigmaFinite_restrict hα
  have hcount := Measure.countable_meas_level_set_pos
    (μ := α.restrict (Ω : Set (ComplexModel n))) hg
  -- in every interval `(0, ε)` there is a good level
  have hgood : ∀ ε : ℝ, 0 < ε → ∃ t, 0 < t ∧ t < ε ∧
      α ((Ω : Set (ComplexModel n)) ∩ {z | g z = t}) = 0 := by
    intro ε hε
    have hI : ¬ (Ioo (0 : ℝ) ε).Countable := by
      intro hc
      have h0 := hc.measure_zero volume
      rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h0
      linarith
    obtain ⟨t, htI, htn⟩ := not_subset.mp fun hsub => hI (hcount.mono hsub)
    refine ⟨t, htI.1, htI.2, ?_⟩
    have h0 : ¬ 0 < α.restrict (Ω : Set (ComplexModel n)) {z | g z = t} := htn
    rw [not_lt, nonpos_iff_eq_zero, Measure.restrict_apply' Ω.isOpen.measurableSet,
      inter_comm] at h0
    exact h0
  -- choose them inductively, each below the previous one and below `1/(k+1)`
  choose T hT0 hTε hTnull using hgood
  let s : ℕ → {t : ℝ // 0 < t} := fun k => Nat.rec ⟨T 1 one_pos, hT0 _ _⟩
    (fun k tk => ⟨T (min tk.1 (1 / ((k : ℝ) + 2))) (lt_min tk.2 (by positivity)), hT0 _ _⟩) k
  have hs0 : s 0 = ⟨T 1 one_pos, hT0 _ _⟩ := rfl
  have hsucc : ∀ k, (s (k + 1)).1 = T (min (s k).1 (1 / ((k : ℝ) + 2)))
      (lt_min (s k).2 (by positivity)) := fun k => rfl
  have hlt : ∀ k, (s (k + 1)).1 < min (s k).1 (1 / ((k : ℝ) + 2)) := fun k => by
    rw [hsucc]; exact hTε _ _
  have hbound : ∀ k, (s k).1 ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    cases k with
    | zero => rw [hs0]; simpa using (hTε 1 one_pos).le
    | succ k =>
        have := (hlt k).trans_le (min_le_right _ _)
        have e : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) = 1 / ((k : ℝ) + 2) := by push_cast; ring
        rw [e]
        exact this.le
  refine ⟨fun k => (s k).1, antitone_nat_of_succ_le fun k => ((hlt k).trans_le
    (min_le_left _ _)).le, fun k => (s k).2, ?_, fun k => ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (s k).2.le) hbound
  · dsimp only
    cases k with
    | zero => rw [hs0]; exact hTnull _ _
    | succ k => rw [hsucc]; exact hTnull _ _

end SGPT.Envelopes.MADirichlet
