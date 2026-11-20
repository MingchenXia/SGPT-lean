import SGPT.Foundations.Analysis.Pending.ActualBoundedScalarCurrentIdentity
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization
import SGPT.Foundations.Analysis.GermPshLeviPositivity

set_option autoImplicit false

/-! # Genuine unbounded scalar currents under actual biholomorphisms

Complete mathematical statements and proofs preceded this module.
The original extended-valued potential is retained, including its poles.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualUnboundedScalarCurrentPullback
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorLocality LocalBedfordTaylorContinuity
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing LocalCurrentPullback
  LocalCurrentPullbackDdc BedfordTaylor ActualBoundedScalarCurrentIdentity

variable {n : ℕ} {B : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

private theorem finite_ae_of_noncollapse (hu : PlurisubharmonicOn u B)
    (hnd : ∀ x ∈ B, ∀ W : Set (ComplexModel n), IsOpen W → x ∈ W →
      ∃ y ∈ (B : Set (ComplexModel n)) ∩ W, u y ≠ ⊥) :
    ∀ᵐ x ∂volume.restrict (B : Set (ComplexModel n)), u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  apply ae_restrict_of_open_neighborhood_ae
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp B.isOpen x hx
  obtain ⟨y, hy, hyfin⟩ := hnd x hx (ball x r) isOpen_ball (mem_ball_self hr)
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr,
    (hu.mono hball).ae_finite volume (convex_ball x r).isPreconnected
      ⟨y, hy.2, hyfin⟩⟩

private theorem integrable_of_finite_ae (hu : PlurisubharmonicOn u B)
    (hfin : ∀ᵐ x ∂volume.restrict (B : Set (ComplexModel n)), u x ≠ ⊤ ∧ u x ≠ ⊥) :
    LocallyIntegrableOn (fun x => (u x).toReal) B volume := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp B.isOpen x hx
  have hxball : x ∈ ball x r := mem_ball_self hr
  have hne : ∃ y ∈ ball x r, u y ≠ ⊥ := by
    by_contra h
    push Not at h
    have hzero : (volume.restrict (B : Set (ComplexModel n))) (ball x r) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hfin] with y hy hyball
      exact hy.2 (h y hyball)
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hball] at hzero
    exact (isOpen_ball.measure_pos volume ⟨x, hxball⟩).ne' hzero
  have hL := (hu.mono hball).locallyIntegrableOn_toReal volume
    (convex_ball x r).isPreconnected hne
  simpa only [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hxball),
    nhdsWithin_eq_nhds.mpr (B.isOpen.mem_nhds hx)] using hL x hxball

private theorem weak_truncations (hu : PlurisubharmonicOn u B)
    (hL : LocallyIntegrableOn (fun x => (u x).toReal) B volume)
    (hfin : ∀ᵐ x ∂volume.restrict (B : Set (ComplexModel n)), u x ≠ ⊤ ∧ u x ≠ ⊥) :
    let hLj := fun j : ℕ => locallyIntegrableOn_of_plurisubharmonicOn_real
      (PshRadialRegularization.isLocallyBoundedPshOn_truncation B.isOpen hu (-(j : ℝ))).1
    WeakTendsto (fun j => scalarTopCurrent (regularDistribution volume
      (fun x => (max (u x) ((-(j : ℝ)) : EReal)).toReal) (hLj j)))
      (scalarTopCurrent (regularDistribution volume (fun x => (u x).toReal) hL)) := by
  dsimp only
  apply weakTendsto_scalarTopCurrent
  intro φ
  simp_rw [regularDistribution_apply]
  have hvalues :
      (fun j : ℕ => (regularDistribution volume
        (fun x => (max (u x) ((-(j : ℝ)) : EReal)).toReal)
        (locallyIntegrableOn_of_plurisubharmonicOn_real
          (PshRadialRegularization.isLocallyBoundedPshOn_truncation B.isOpen hu
            (-(j : ℝ))).1)) φ) =
      (fun j : ℕ => ∫ x, φ x * (max (u x) ((-(j : ℝ)) : EReal)).toReal) := by
    funext j
    exact regularDistribution_apply volume _ _ φ
  rw [hvalues]
  have hfin' : ∀ᵐ x ∂volume, x ∈ B → u x ≠ ⊤ ∧ u x ≠ ⊥ :=
    (ae_restrict_iff' B.isOpen.measurableSet).mp hfin
  have hint : Integrable (fun x => φ x * (u x).toReal) volume :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hL
  refine tendsto_integral_of_dominated_convergence
    (F := fun (j : ℕ) (x : ComplexModel n) =>
      φ x * (max (u x) ((-(j : ℝ)) : EReal)).toReal)
    (f := fun x => φ x * (u x).toReal)
    (fun x => ‖φ x * (u x).toReal‖) (fun j => ?_) hint.norm (fun j => ?_) ?_
  · exact (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrableOn_of_plurisubharmonicOn_real
        (PshRadialRegularization.isLocallyBoundedPshOn_truncation B.isOpen hu
          (-(j : ℝ))).1)).aestronglyMeasurable
  · filter_upwards [hfin'] with x hx
    by_cases hxB : x ∈ B
    · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (PshRadialRegularization.abs_toReal_max_le (hx hxB).1 (hx hxB).2
          (Nat.cast_nonneg j)) (norm_nonneg (φ x))
    · simp only [testFunction_eq_zero_of_notMem φ hxB, zero_mul, norm_zero, le_refl]
  · filter_upwards [hfin'] with x hx
    by_cases hxB : x ∈ B
    · obtain ⟨N, hN⟩ := exists_nat_ge (-(u x).toReal)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with j hj
      have hcut : -(j : ℝ) ≤ (u x).toReal := by
        have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      rw [← EReal.coe_neg,
        PshRadialRegularization.toReal_max_coe (hx hxB).1 (hx hxB).2,
        max_eq_left hcut]
    · simp only [testFunction_eq_zero_of_notMem φ hxB, zero_mul]
      exact tendsto_const_nhds

/-- Every original noncollapsed PSH component internally supplies L1, a.e.
finiteness and the actual scalar-current truncation limit, in every dimension. -/
theorem exists_integrable_psh_truncation_currents (hu : PlurisubharmonicOn u B)
    (hnd : ∀ x ∈ B, ∀ W : Set (ComplexModel n), IsOpen W → x ∈ W →
      ∃ y ∈ (B : Set (ComplexModel n)) ∩ W, u y ≠ ⊥) :
    ∃ hL : LocallyIntegrableOn (fun x => (u x).toReal) B volume,
      (∀ᵐ x ∂volume.restrict (B : Set (ComplexModel n)), u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
      let hLj := fun j : ℕ => locallyIntegrableOn_of_plurisubharmonicOn_real
        (PshRadialRegularization.isLocallyBoundedPshOn_truncation B.isOpen hu (-(j : ℝ))).1
      WeakTendsto (fun j => scalarTopCurrent (regularDistribution volume
        (fun x => (max (u x) ((-(j : ℝ)) : EReal)).toReal) (hLj j)))
        (scalarTopCurrent (regularDistribution volume (fun x => (u x).toReal) hL)) := by
  have hfin := finite_ae_of_noncollapse hu hnd
  have hL := integrable_of_finite_ae hu hfin
  exact ⟨hL, hfin, weak_truncations hu hL hfin⟩

private theorem bounded_scalar_whole {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn B w) :
    scalarTopCurrent (regularDistribution volume w
      (locallyIntegrableOn_of_plurisubharmonicOn_real hw.1)) =
      mulBorel (oneCurrent B) ((B : Set (ComplexModel n)).indicator w) := by
  ext γ φ
  obtain ⟨V₀, hVo, hKV, hVcl, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport B.isOpen φ.tsupport_subset
  let V : Opens (ComplexModel n) := ⟨V₀, hVo⟩
  have hVB : V ≤ B := subset_closure.trans hVcl
  have hVrc : RelativelyCompactIn V B := ⟨hVc, hVcl⟩
  let φ' : 𝓓(V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKV⟩
  have hext : extTest hVB φ' = φ := by ext x; rw [extTest_apply]; rfl
  have hleft : restrict hVB
      (scalarTopCurrent (regularDistribution volume w
        (locallyIntegrableOn_of_plurisubharmonicOn_real hw.1))) =
      scalarTopCurrent (regularDistribution volume w
        (locallyIntegrableOn_of_plurisubharmonicOn_real
          (isLocallyBoundedPshOn_mono hw hVB).1)) := by
    rw [scalarTopCurrent_restrict, restrictDistribution_regularDistribution]
  have hright : restrict hVB
      (mulBorel (oneCurrent B) ((B : Set (ComplexModel n)).indicator w)) =
      mulBorel (oneCurrent V) ((V : Set (ComplexModel n)).indicator w) := by
    rw [← mulBorel_restrict isPositive_oneCurrent hVB
      (measurable_indicator_of_isLocallyBoundedPshOn hw)
      (isLocallyBoundedOn_indicator hw), restrict_oneCurrent]
    apply mulBorel_congr isPositive_oneCurrent
      (measurable_indicator_of_isLocallyBoundedPshOn hw)
      (isLocallyBoundedOn_mono (isLocallyBoundedOn_indicator hw) hVB)
      (measurable_indicator_of_isLocallyBoundedPshOn (isLocallyBoundedPshOn_mono hw hVB))
      (isLocallyBoundedOn_indicator (isLocallyBoundedPshOn_mono hw hVB))
    intro x hx
    rw [indicator_of_mem (hVB hx), indicator_of_mem hx]
  have heq := scalarTopCurrent_regularDistribution_eq_mulBorel_of_locallyBoundedPsh hw hVrc
  have hev := congrArg (fun S : LocalProductCurrent n V n => S γ φ') heq
  rw [← hleft, ← hright, LocalBedfordTaylorLocality.restrict_apply,
    LocalBedfordTaylorLocality.restrict_apply, hext] at hev
  exact hev

/-- The same genuinely unbounded potential internally supplies both L1
readers and full positive differentials; actual biholomorphic pullback
preserves the entire complementary current, not merely its trace. -/
theorem exists_unbounded_psh_current_pullback {m : ℕ}
    {A B : Opens (ComplexModel (m + 1))}
    {τ σ : ComplexModel (m + 1) → ComplexModel (m + 1)}
    (h : IsBiholomorphicPair A B τ σ) {u : ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u B)
    (hnd : ∀ x ∈ B, ∀ W : Set (ComplexModel (m + 1)), IsOpen W → x ∈ W →
      ∃ y ∈ (B : Set (ComplexModel (m + 1))) ∩ W, u y ≠ ⊥) :
    ∃ hLB : LocallyIntegrableOn (fun x => (u x).toReal) B volume,
      ∃ hLA : LocallyIntegrableOn (fun x => (u (τ x)).toReal) A volume,
        let CB := ddc (scalarTopCurrent (regularDistribution volume
          (fun x => (u x).toReal) hLB))
        let CA := ddc (scalarTopCurrent (regularDistribution volume
          (fun x => (u (τ x)).toReal) hLA))
        IsPositive CA ∧ ∃ hPB : IsPositive CB, pullback h hPB = CA := by
  obtain ⟨hLB, hfinB, hweakB⟩ := exists_integrable_psh_truncation_currents hu hnd
  have huA : PlurisubharmonicOn (fun x => u (τ x)) A :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen
      (h.holo.differentiableOn (by simp)) h.mapsTo hu
  have hfinB' : ∀ᵐ x ∂volume, x ∈ B → u x ≠ ⊤ ∧ u x ≠ ⊥ :=
    (ae_restrict_iff' B.isOpen.measurableSet).mp hfinB
  have hfinA : ∀ᵐ x ∂volume.restrict (A : Set (ComplexModel (m + 1))),
      u (τ x) ≠ ⊤ ∧ u (τ x) ≠ ⊥ :=
    (ae_restrict_iff' A.isOpen.measurableSet).mpr (ae_comp_of_ae h hfinB')
  have hLA := integrable_of_finite_ae huA hfinA
  let CB := ddc (scalarTopCurrent (regularDistribution volume (fun x => (u x).toReal) hLB))
  let CA := ddc (scalarTopCurrent (regularDistribution volume (fun x => (u (τ x)).toReal) hLA))
  have hPB : IsPositive CB := isPositive_ddc_scalarTopCurrent
    (hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable hLB hfinB)
  have hPA : IsPositive CA := isPositive_ddc_scalarTopCurrent
    (huA.hasNonnegativeDistributionalLevi_of_locallyIntegrable hLA hfinA)
  let w (j : ℕ) (x : ComplexModel (m + 1)) : ℝ :=
    (max (u x) ((-(j : ℝ)) : EReal)).toReal
  let hw (j : ℕ) : IsLocallyBoundedPshOn B (w j) :=
    PshRadialRegularization.isLocallyBoundedPshOn_truncation B.isOpen hu (-(j : ℝ))
  let hjL (j : ℕ) := locallyIntegrableOn_of_plurisubharmonicOn_real (hw j).1
  let Cj (j : ℕ) := ddc (scalarTopCurrent (regularDistribution volume (w j) (hjL j)))
  have hPj (j : ℕ) : IsPositive (Cj j) := isPositive_ddc_scalarTopCurrent
    (hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real (hw j).1)
  have heqB (j : ℕ) : Cj j = ddcMul (oneCurrent B) (w j) := by
    dsimp only [Cj, hjL]
    rw [bounded_scalar_whole (hw j)]
    rfl
  have hstage (j : ℕ) : pullback h (hPj j) =
      ddc (scalarTopCurrent (regularDistribution volume
        (fun x => (max (u (τ x)) ((-(j : ℝ)) : EReal)).toReal)
        (locallyIntegrableOn_of_plurisubharmonicOn_real
          (PshRadialRegularization.isLocallyBoundedPshOn_truncation A.isOpen huA
            (-(j : ℝ))).1))) := by
    calc
      pullback h (hPj j) = pullback h (isPositive_ddcMul_oneCurrent (hw j)) :=
        pullback_congr h (hPj j) (isPositive_ddcMul_oneCurrent (hw j)) (heqB j)
      _ = ddcMul (oneCurrent A) (fun x => w j (τ x)) := pullback_ddcMul h (hw j)
      _ = _ := by
        rw [bounded_scalar_whole (isLocallyBoundedPshOn_comp h (hw j))]
        rfl
  have hconvB : WeakTendsto Cj CB := weakTendsto_ddc hweakB
  have hpb := weakTendsto_pullback h hPj hPB hconvB
  have hconvA := weakTendsto_ddc (weak_truncations huA hLA hfinA)
  refine ⟨hLB, hLA, hPA, hPB, ?_⟩
  ext γ φ
  exact tendsto_nhds_unique (hpb γ φ) (by simpa only [hstage] using hconvA γ φ)

end SGPT.Foundations.Analysis.Pending.ActualUnboundedScalarCurrentPullback
