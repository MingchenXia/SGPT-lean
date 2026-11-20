import SGPT.Foundations.Analysis.Pending.IncreasingDiagonalWeakConvergence
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

set_option autoImplicit false

/-!
# Increasing diagonal products with variable total mass

Xia's Corollary 2.4.1, diagonal sequence case. Actual mass monotonicity
and actual increasing open-set semicontinuity produce convergence of
the masses and native weak convergence, without a bounded-gap assumption
or semipositivity of the smooth background.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingDiagonalContinuity

open FirstPass FirstPass.PositiveClasses DiagonalMass GlobalNonPluripolar
open IncreasingLimitMass IncreasingLimitOpenMeasure IncreasingDiagonalWeakConvergence

noncomputable section

/-- Finite-measure portmanteau when the finite masses converge, including zero mass. -/
theorem finiteMeasure_tendsto_of_tendsto_mass_of_isOpen_le_liminf
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {mu : ℕ → FiniteMeasure X} {nu : FiniteMeasure X}
    (hmass : Tendsto (fun j => (mu j).mass) atTop (𝓝 nu.mass))
    (hopen : ∀ G : Set X, IsOpen G →
      (nu : Measure X) G ≤ liminf (fun j => (mu j : Measure X) G) atTop) :
    Tendsto mu atTop (𝓝 nu) := by
  by_cases hnu : nu = 0
  · subst nu
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
  rcases isEmpty_or_nonempty X with hX | hX
  · exact (hnu (Subtype.ext (Subsingleton.elim _ _))).elim
  have haux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 nu.mass :=
    isOpen_compl_singleton.mem_nhds (nu.mass_nonzero_iff.mpr hnu)
  have hmu : ∀ᶠ j in atTop, mu j ≠ 0 := by
    simp_rw [← FiniteMeasure.mass_nonzero_iff]
    exact hmass haux
  have hinv : Tendsto (fun j => (((mu j).mass⁻¹ : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 ((nu.mass⁻¹ : ℝ≥0) : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp
      ((continuousOn_inv₀.continuousAt haux).tendsto.comp hmass)
  have hnorm : Tendsto (fun j => (mu j).normalize) atTop (𝓝 nu.normalize) := by
    apply tendsto_of_forall_isOpen_le_liminf_nat'
    intro G hG
    rw [nu.toMeasure_normalize_eq_of_nonzero hnu, Measure.coe_nnreal_smul_apply]
    have hscaled := mul_le_mul_of_nonneg_left (hopen G hG)
      (show (0 : ℝ≥0∞) ≤ (nu.mass⁻¹ : ℝ≥0) from zero_le)
    have hproduct := ENNReal.le_liminf_mul
      (u := fun j : ℕ => (((mu j).mass⁻¹ : ℝ≥0) : ℝ≥0∞))
      (v := fun j => (mu j : Measure X) G) (f := atTop)
    rw [hinv.liminf_eq] at hproduct
    refine (hscaled.trans hproduct).trans_eq ?_
    apply liminf_congr
    filter_upwards [hmu] with j hj
    rw [(mu j).toMeasure_normalize_eq_of_nonzero hj, Measure.coe_nnreal_smul_apply]
    rfl
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass hnorm hmass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Produce mass monotonicity from pointwise monotonicity of genuine potentials. -/
theorem diagonalPotentialMass_monotone (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u : ℕ → M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u) :
    Monotone (fun j => diagonalPotentialMass theta (u j) (hu j)) := by
  intro i j hij
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
    (fun _ => hu i) (fun _ => hu j)
    (fun _ => ⟨0, fun x _ => by simpa only [EReal.coe_zero, add_zero] using hmono hij x⟩)

/-- The actual regularized limit mass equals the supremum of the actual increasing masses. -/
theorem diagonalPotentialMass_eq_iSup (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u : ℕ → M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j))) :
    diagonalPotentialMass theta (uscRegularization (⨆ j, u j)) hU =
      ⨆ j, diagonalPotentialMass theta (u j) (hu j) := by
  refine le_antisymm (diagonalPotentialMass_le_iSup_of_monotone u hu hmono hU) ?_
  refine iSup_le fun j => ?_
  have hdom : u j ≤ uscRegularization (⨆ i, u i) :=
    (le_iSup u j).trans (le_uscRegularization _)
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
    (fun _ => hu j) (fun _ => hU)
    (fun _ => ⟨0, fun x _ => by simpa only [EReal.coe_zero, add_zero] using hdom x⟩)

/-- Actual unrestricted increasing diagonal weak continuity, with all mass inputs produced. -/
theorem weakTendsto_diagonal_of_monotone (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u : ℕ → M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j))) :
    Tendsto (fun j => finiteDiagonalMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteDiagonalMeasure omega theta (uscRegularization (⨆ j, u j)) hU)) := by
  let : IsFiniteMeasure
      (diagonalPotentialMeasure theta (uscRegularization (⨆ j, u j)) hU) :=
    globalMixedMeasure_isFiniteMeasure omega (fun _ : Fin n => hU.1)
  have hm := tendsto_atTop_iSup (diagonalPotentialMass_monotone omega hu hmono)
  rw [← diagonalPotentialMass_eq_iSup omega hu hmono hU] at hm
  apply finiteMeasure_tendsto_of_tendsto_mass_of_isOpen_le_liminf
  · exact (ENNReal.tendsto_toNNReal
      (measure_lt_top (diagonalPotentialMeasure theta (uscRegularization (⨆ j, u j)) hU)
        univ).ne).comp hm
  · intro G hG
    exact diagonalPotentialMeasure_isOpen_le_liminf u hu hmono hU hG

/-- Actual continuous-test convergence for the unrestricted increasing diagonal sequence. -/
theorem tendsto_integral_diagonal_of_monotone (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u : ℕ → M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j))) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂diagonalPotentialMeasure theta (u j) (hu j)) atTop
      (𝓝 (∫ x, chi x ∂diagonalPotentialMeasure theta (uscRegularization (⨆ j, u j)) hU)) :=
  (FiniteMeasure.continuous_integral_continuousMap chi).tendsto _ |>.comp
    (weakTendsto_diagonal_of_monotone omega hu hmono hU)

end

end SGPT.Foundations.Analysis.Pending.IncreasingDiagonalContinuity
