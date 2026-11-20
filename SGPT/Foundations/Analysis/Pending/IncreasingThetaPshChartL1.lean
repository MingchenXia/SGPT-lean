import SGPT.Foundations.Analysis.Pending.IncreasingPshBallSubmean
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.FirstPass.OrderedL1Squeeze
import SGPT.Foundations.Analysis.FirstPass.PotentialL1
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

set_option autoImplicit false

/-!
# Increasing families of theta-PSH potentials converge in chart-local `L¹`

An increasing sequence of normalized `theta`-PSH potentials whose regularized
supremum is `u` converges to `u` in the chart-local `L¹` topology of
`FirstPass.PotentialL1`.

Two classical ingredients are already available in this workspace and are
assembled here.  First, in a chart with a smooth local potential `rho` the
corrected representatives are an increasing sequence of plurisubharmonic
functions whose regularized supremum is the corrected representative of `u`,
so `Pending.ae_uscRegularization_iSup_eq_on_ball` (the sharp moving-centre
submean plus Lebesgue differentiation) identifies the *unregularized*
supremum with it Lebesgue-almost everywhere.  Second, the real chart
representatives are locally integrable (`FirstPass.QuasiPshChartL1`), which
supplies the dominating function for the dominated convergence theorem.

No new analytic input is used.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1

open SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Adding a real constant on the right is injective on `EReal`. -/
theorem eReal_add_coe_right_cancel {a b : EReal} {c : ℝ}
    (h : a + (c : EReal) = b + (c : EReal)) : a = b := by
  have hcanc := EReal.addLECancellable_coe c
  refine le_antisymm ?_ ?_
  · rw [← hcanc.add_le_add_iff_right]
    exact h.le
  · rw [← hcanc.add_le_add_iff_right]
    exact h.ge

/-- For ordered real values the canonical extended absolute difference is the
ordinary difference. -/
theorem canonicalERealAbsDiff_coe_coe_of_le {a b : ℝ} (hab : a ≤ b) :
    canonicalERealAbsDiff (a : EReal) (b : EReal) = ENNReal.ofReal (b - a) := by
  rw [canonicalERealAbsDiff_coe_coe, abs_sub_comm, abs_of_nonneg (by linarith)]

/-- Raising the lower value of an ordered pair shrinks the canonical extended
absolute difference to the fixed upper value. -/
theorem canonicalERealAbsDiff_antitone_left {a b c : EReal}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≠ ⊤) :
    canonicalERealAbsDiff b c ≤ canonicalERealAbsDiff a c := by
  rcases eq_or_ne c ⊥ with rfl | hcb
  · have hb : b = ⊥ := le_bot_iff.mp hbc
    have ha : a = ⊥ := le_bot_iff.mp (hab.trans hbc)
    simp [ha, hb]
  · rcases eq_or_ne a ⊥ with rfl | habot
    · rw [canonicalERealAbsDiff_bot_left hcb]
      exact le_top
    · have hbbot : b ≠ ⊥ := fun h => habot (le_bot_iff.mp (h ▸ hab))
      have hbtop : b ≠ ⊤ := fun h => hc (top_le_iff.mp (h ▸ hbc))
      have hatop : a ≠ ⊤ := fun h => hbtop (top_le_iff.mp (h ▸ hab))
      have e1 : ((a.toReal : ℝ) : EReal) = a := EReal.coe_toReal hatop habot
      have e2 : ((b.toReal : ℝ) : EReal) = b := EReal.coe_toReal hbtop hbbot
      have e3 : ((c.toReal : ℝ) : EReal) = c := EReal.coe_toReal hc hcb
      have hle1 : a.toReal ≤ b.toReal := EReal.toReal_le_toReal hab habot hbtop
      have hle2 : b.toReal ≤ c.toReal := EReal.toReal_le_toReal hbc hbbot hc
      have h1 := canonicalERealAbsDiff_coe_coe_of_le hle2
      have h2 := canonicalERealAbsDiff_coe_coe_of_le (hle1.trans hle2)
      rw [e2, e3] at h1
      rw [e1, e3] at h2
      rw [h1, h2]
      exact ENNReal.ofReal_le_ofReal (by linarith)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- In every holomorphic chart, the unregularized supremum of an increasing
sequence of normalized `theta`-PSH potentials agrees Lebesgue-almost
everywhere with the chart representative of the regularized supremum. -/
theorem ae_chartFunction_iSup_eq {theta : ClosedRealOneOneForm n M}
    {g : ℕ → M → EReal} {u : M → EReal}
    (hg : ∀ j, IsThetaPshPotential theta.val (g j))
    (hg0 : ∀ j, g j ≤ 0) (hmono : Monotone g)
    (heq : uscRegularization (⨆ j, g j) = u)
    (e : ComplexChart n M) :
    ∀ᵐ z ∂(volume.restrict e.val.target),
      (⨆ j, chartFunction (g j) e z) = chartFunction u e z := by
  refine ae_restrict_of_open_neighborhood_ae ?_
  intro z hz
  obtain ⟨W, rho, hzW, hrho⟩ := (hg 0).1.hasSmoothLocalPotentials e z hz
  -- the corrected chart representatives
  set v : ℕ → ComplexModel n → EReal :=
    fun j y => chartFunction (g j) e y + (rho y : EReal) with hv
  have hpsh : ∀ {w : M → EReal}, IsThetaPshPotential theta.val w →
      PlurisubharmonicOn (fun y => chartFunction w e y + (rho y : EReal)) W :=
    fun {w} hw =>
      chartCorrectedFamily_plurisubharmonicOn (F := {w})
        (fun _ h => by rw [mem_singleton_iff.mp h]; exact hw) e hrho _
        ⟨w, mem_singleton _, rfl⟩
  have hrhoc : ∀ y ∈ W, ContinuousAt rho y := fun y hy =>
    ((hrho.2.2.1 y hy).contDiffAt (hrho.1.mem_nhds hy)).continuousAt
  have hsup : (⨆ j, v j) = fun y => chartFunction (⨆ j, g j) e y + (rho y : EReal) := by
    funext y
    simp only [iSup_apply, chartFunction, hv]
    exact iSup_add_coe (fun j => g j (e.val.symm y)) (rho y)
  have hVeq : EqOn (fun y => chartFunction u e y + (rho y : EReal))
      (uscRegularization (⨆ j, v j)) W := by
    intro y hy
    change chartFunction u e y + (rho y : EReal) = _
    rw [hsup, uscRegularization_add_coe_continuousAt_apply _ (hrhoc y hy),
      uscRegularization_chartFunction_apply _ e (hrho.2.1 hy), heq]
  -- a ball around `z` inside `W`, on which `rho` is bounded
  obtain ⟨S, hS, hSW⟩ := Metric.isOpen_iff.mp hrho.1 z hzW
  have hclosed : closedBall z (S / 2) ⊆ W :=
    (closedBall_subset_ball (by linarith)).trans hSW
  have hrhoCont : ContinuousOn rho (closedBall z (S / 2)) := fun y hy =>
    (hrhoc y (hclosed hy)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (S / 2)).exists_bound_of_continuousOn hrhoCont
  refine ⟨ball z (S / 4), isOpen_ball, mem_ball_self (by linarith), ?_⟩
  have hbound : ∀ j, ∀ y ∈ ball z (S / 2), v j y ≤ (C : EReal) := by
    intro j y hy
    have hyc : y ∈ closedBall z (S / 2) := ball_subset_closedBall hy
    have h1 : chartFunction (g j) e y ≤ 0 := hg0 j _
    have h2 : (rho y : EReal) ≤ (C : EReal) :=
      EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hC y hyc))
    calc v j y ≤ 0 + (rho y : EReal) := add_le_add h1 le_rfl
      _ = (rho y : EReal) := zero_add _
      _ ≤ (C : EReal) := h2
  have hae := ae_uscRegularization_iSup_eq_on_ball
    (u := v) (U := W)
    (fun j => (hpsh (hg j)).discPshOn)
    (fun y _ j k hjk => add_le_add (hmono hjk _) le_rfl)
    (volume : Measure (ComplexModel n)) z (S := S / 2) (by linarith)
    ((ball_subset_ball (by linarith)).trans hSW) hbound
  have hquarter : (S / 2) / 2 = S / 4 := by ring
  rw [hquarter] at hae
  filter_upwards [ae_restrict_of_ae hae,
    ae_restrict_mem (measurableSet_ball (x := z) (ε := S / 4))] with y hy hymem
  have hyW : y ∈ W := hSW (ball_subset_ball (by linarith) hymem)
  have h1 : uscRegularization (fun t => ⨆ j, v j t) y = ⨆ j, v j y := hy hymem
  have h2 : (fun t => ⨆ j, v j t) = (⨆ j, v j) := by
    funext t
    simp [iSup_apply]
  rw [h2] at h1
  have hVy : chartFunction u e y + (rho y : EReal) =
      uscRegularization (⨆ j, v j) y := hVeq hyW
  have h3 : chartFunction u e y + (rho y : EReal) = ⨆ j, v j y := hVy.trans h1
  have h4 : (⨆ j, v j y) = (⨆ j, chartFunction (g j) e y) + (rho y : EReal) :=
    iSup_add_coe (fun j => chartFunction (g j) e y) (rho y)
  exact (eReal_add_coe_right_cancel (h3.trans h4)).symm

/-- **Increasing families converge in chart-local `L¹`.**  If `g` is a
nondecreasing sequence of normalized `theta`-PSH potentials whose regularized
supremum is `u`, then `g j → u` in the chart-local `L¹` topology. -/
theorem manifoldL1LocallyTendsto_of_monotone_uscRegularization
    {theta : ClosedRealOneOneForm n M} {g : ℕ → M → EReal} {u : M → EReal}
    (hg : ∀ j, IsThetaPshPotential theta.val (g j))
    (hg0 : ∀ j, g j ≤ 0) (hmono : Monotone g)
    (hu : IsThetaPshPotential theta.val u)
    (heq : uscRegularization (⨆ j, g j) = u) :
    ManifoldL1LocallyTendsto (n := n) g atTop u := by
  have hgle : ∀ j, g j ≤ u := by
    intro j x
    have h1 : g j x ≤ (⨆ k, g k) x := le_iSup (fun k => g k) j x
    have h2 : (⨆ k, g k) x ≤ uscRegularization (⨆ k, g k) x :=
      le_uscRegularization _ x
    rw [← heq]
    exact h1.trans h2
  intro e K hK hKe
  set F : ℕ → ComplexModel n → ℝ≥0∞ := fun j z =>
    canonicalERealAbsDiff (chartFunction (g j) e z) (chartFunction u e z) with hF
  -- almost-everywhere finiteness of every member and of the limit
  have hfinu : ∀ᵐ z ∂(volume.restrict K),
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe
      (hu.quasiPshPotential.ae_finite_chart e)
  have hfing : ∀ᵐ z ∂(volume.restrict K), ∀ j,
      chartFunction (g j) e z ≠ ⊤ ∧ chartFunction (g j) e z ≠ ⊥ := by
    rw [ae_all_iff]
    intro j
    exact ae_restrict_of_ae_restrict_of_subset hKe
      ((hg j).quasiPshPotential.ae_finite_chart e)
  have hsupeq : ∀ᵐ z ∂(volume.restrict K),
      (⨆ j, chartFunction (g j) e z) = chartFunction u e z :=
    ae_restrict_of_ae_restrict_of_subset hKe
      (ae_chartFunction_iSup_eq hg hg0 hmono heq e)
  -- the good set, on which everything is an ordinary real computation
  have hgood : ∀ᵐ z ∂(volume.restrict K),
      (chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) ∧
      (∀ j, chartFunction (g j) e z ≠ ⊤ ∧ chartFunction (g j) e z ≠ ⊥) ∧
      (⨆ j, chartFunction (g j) e z) = chartFunction u e z := by
    filter_upwards [hfinu, hfing, hsupeq] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hvalue : ∀ z, (chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) →
      (∀ j, chartFunction (g j) e z ≠ ⊤ ∧ chartFunction (g j) e z ≠ ⊥) →
      ∀ j, F j z = ENNReal.ofReal
        ((chartFunction u e z).toReal - (chartFunction (g j) e z).toReal) := by
    intro z hu' hg' j
    have hle : (chartFunction (g j) e z).toReal ≤ (chartFunction u e z).toReal :=
      EReal.toReal_le_toReal (hgle j (e.val.symm z)) (hg' j).2 hu'.1
    have e1 : (((chartFunction (g j) e z).toReal : ℝ) : EReal) =
        chartFunction (g j) e z := EReal.coe_toReal (hg' j).1 (hg' j).2
    have e2 : (((chartFunction u e z).toReal : ℝ) : EReal) =
        chartFunction u e z := EReal.coe_toReal hu'.1 hu'.2
    have hcalc := canonicalERealAbsDiff_coe_coe_of_le hle
    rw [e1, e2] at hcalc
    exact hcalc
  -- measurability
  have hF_meas : ∀ j, AEMeasurable (F j) (volume.restrict K) := by
    intro j
    exact measurable_canonicalERealAbsDiff.comp_aemeasurable
      (((hg j).quasiPshPotential.aemeasurable_chart_restrict e hKe).prodMk
        (hu.quasiPshPotential.aemeasurable_chart_restrict e hKe))
  -- domination by the first member
  have hbound : ∀ j, F j ≤ᵐ[volume.restrict K] F 0 := by
    intro j
    filter_upwards [hgood] with z ⟨hu', hg', _⟩
    rw [hvalue z hu' hg' j, hvalue z hu' hg' 0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep : (chartFunction (g 0) e z).toReal ≤
        (chartFunction (g j) e z).toReal :=
      EReal.toReal_le_toReal (hmono (Nat.zero_le j) (e.val.symm z))
        (hg' 0).2 (hg' j).1
    linarith
  -- finiteness of the dominating integral
  have hfin : ∫⁻ z in K, F 0 z ∂volume ≠ ⊤ := by
    have heqint : ∫⁻ z in K, F 0 z ∂volume = chartEndpointRealL1 (g 0) u e K := by
      rw [chartEndpointRealL1]
      refine lintegral_congr_ae ?_
      filter_upwards [hgood] with z ⟨hu', hg', _⟩
      have hle0 : (chartFunction (g 0) e z).toReal ≤
          (chartFunction u e z).toReal :=
        EReal.toReal_le_toReal (hgle 0 (e.val.symm z)) (hg' 0).2 hu'.1
      rw [hvalue z hu' hg' 0, abs_of_nonneg (by linarith)]
    rw [heqint]
    exact chartEndpointRealL1_ne_top (hg 0).quasiPshPotential hu.quasiPshPotential
      e hK hKe
  -- pointwise convergence to zero on the good set
  have hlim : ∀ᵐ z ∂(volume.restrict K),
      Tendsto (fun j => F j z) atTop (𝓝 0) := by
    filter_upwards [hgood] with z ⟨hu', hg', hsup'⟩
    have hEtend : Tendsto (fun j => chartFunction (g j) e z) atTop
        (𝓝 (chartFunction u e z)) := by
      rw [← hsup']
      exact tendsto_atTop_iSup fun j k hjk => hmono hjk (e.val.symm z)
    have hRtend : Tendsto (fun j => (chartFunction (g j) e z).toReal) atTop
        (𝓝 (chartFunction u e z).toReal) :=
      ((EReal.tendsto_toReal hu'.1 hu'.2).comp hEtend)
    have hdiff : Tendsto
        (fun j => (chartFunction u e z).toReal -
          (chartFunction (g j) e z).toReal) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (chartFunction u e z).toReal) atTop
          (𝓝 (chartFunction u e z).toReal) := tendsto_const_nhds
      simpa using hconst.sub hRtend
    have := ENNReal.tendsto_ofReal hdiff
    simp only [ENNReal.ofReal_zero] at this
    refine this.congr ?_
    intro j
    exact (hvalue z hu' hg' j).symm
  have hmain := tendsto_lintegral_of_dominated_convergence'
    (F := F) (f := fun _ => (0 : ℝ≥0∞)) (bound := F 0)
    (μ := volume.restrict K) hF_meas hbound hfin hlim
  simpa [chartL1EDistance, hF] using hmain


/-- The real-parameter form: a nondecreasing family of normalized `theta`-PSH
potentials indexed by `ℝ`, whose regularized supremum along the integer
parameters is `u`, converges to `u` in chart-local `L¹` as the parameter tends
to `+∞`. -/
theorem manifoldL1LocallyTendsto_real_of_monotone_uscRegularization
    {theta : ClosedRealOneOneForm n M} {w : ℝ → M → EReal} {u : M → EReal}
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (w C))
    (hw0 : ∀ C : ℝ, w C ≤ 0) (hmono : Monotone w)
    (hu : IsThetaPshPotential theta.val u)
    (heq : uscRegularization (⨆ j : ℕ, w (j : ℝ)) = u) :
    ManifoldL1LocallyTendsto (n := n) w atTop u := by
  have hseqmono : Monotone (fun j : ℕ => w (j : ℝ)) :=
    fun j k hjk => hmono (by exact_mod_cast hjk)
  have hseq := manifoldL1LocallyTendsto_of_monotone_uscRegularization
    (fun j : ℕ => hw (j : ℝ)) (fun j => hw0 (j : ℝ)) hseqmono hu heq
  have hwle : ∀ C : ℝ, w C ≤ u := by
    intro C x
    obtain ⟨j, hj⟩ := exists_nat_ge C
    have h1 : w C x ≤ w (j : ℝ) x := hmono hj x
    have h2 : w (j : ℝ) x ≤ (⨆ k : ℕ, w (k : ℝ)) x :=
      le_iSup (fun k : ℕ => w (k : ℝ)) j x
    have h3 : (⨆ k : ℕ, w (k : ℝ)) x ≤ uscRegularization (⨆ k : ℕ, w (k : ℝ)) x :=
      le_uscRegularization _ x
    rw [← heq]
    exact h1.trans (h2.trans h3)
  intro e K hK hKe
  have hanti : ∀ C D : ℝ, C ≤ D →
      chartL1EDistance (w D) u e K ≤ chartL1EDistance (w C) u e K := by
    intro C D hCD
    refine lintegral_mono fun z => ?_
    exact canonicalERealAbsDiff_antitone_left (hmono hCD _) (hwle D _)
      (hu.1.quasiPlurisubharmonic.ne_top _)
  have hfloor : Tendsto (fun C : ℝ => (⌊C⌋₊ : ℕ)) atTop atTop :=
    tendsto_nat_floor_atTop
  have hcomp : Tendsto
      (fun C : ℝ => chartL1EDistance (w ((⌊C⌋₊ : ℕ) : ℝ)) u e K) atTop (𝓝 0) :=
    (hseq e K hK hKe).comp hfloor
  have hlow : ∀ᶠ C : ℝ in atTop,
      (0 : ℝ≥0∞) ≤ chartL1EDistance (w C) u e K :=
    Eventually.of_forall fun _ => bot_le
  have hhigh : ∀ᶠ C : ℝ in atTop,
      chartL1EDistance (w C) u e K ≤
        chartL1EDistance (w ((⌊C⌋₊ : ℕ) : ℝ)) u e K := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with C hC
    exact hanti _ _ (Nat.floor_le hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp
    hlow hhigh


end

end SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1
