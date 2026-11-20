import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelInfimum

set_option autoImplicit false

/-! # Positive mass of actual decreasing model infima

SGPT PDF0231 Corollary 6.2.7, the decreasing fixed-background sequence
precursor. Actual contact semicontinuity transfers a uniform lower bound
on stage masses to the internally produced genuine infimum. Positive
infimum mass is established before invoking mass convergence. Arbitrary
decreasing nets, varying backgrounds, and general Cauchy completeness are
not asserted here.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualDecreasingModelPositiveInfimum

open FirstPass FirstPass.PositiveClasses DiagonalMass MixedMass
  ActualDecreasingModelInfimum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem contact_mass_eq_mass_of_model (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsModelPotential θ u) :
    diagonalPotentialMeasure θ u hu.plurisubharmonic {x | u x = 0} =
      diagonalPotentialMass θ u hu.plurisubharmonic := by
  have hu0 : u ≤ 0 := by
    rw [hu.envelope_eq]
    exact singularityEnvelope_le_zero θ.val u
  have hnull := RooftopMassDiamondModel.measure_lt_zero_eq_zero_of_model
    omega θ hu.plurisubharmonic hu.envelope_eq
  have hrestrict : (diagonalPotentialMeasure θ u hu.plurisubharmonic).restrict {x | u x = 0} =
      diagonalPotentialMeasure θ u hu.plurisubharmonic := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply measure_mono_null ?_ hnull
    intro x hx
    change u x ≠ 0 at hx
    exact lt_of_le_of_ne (hu0 x) hx
  have h := congrArg (fun μ : Measure M => μ univ) hrestrict
  simpa only [Measure.restrict_apply_univ, diagonalPotentialMass] using h

/-- A uniform actual lower bound passes to the genuine infimum through
contact semicontinuity, before using any positive-limit mass convergence. -/
theorem le_diagonalPotentialMass_iInf_of_le_stage_masses
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u) {d : ℝ≥0∞}
    (hbound : ∀ k, d ≤ diagonalPotentialMass θ (u k) (hu k).plurisubharmonic) :
    d ≤ diagonalPotentialMass θ (⨅ k, u k)
      (isThetaPshPotential_iInf_of_antitone_model hu hanti) := by
  have hu0 (k : ℕ) : u k ≤ 0 := by
    rw [(hu k).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (u k)
  have hlim (x : M) : Tendsto (fun k => u k x) atTop (𝓝 ((⨅ k, u k) x)) := by
    simpa only [iInf_apply] using
      tendsto_atTop_iInf (show Antitone (fun k => u k x) from fun _ _ hab => hanti hab x)
  have hcontact := DecreasingContactMassLimit.contactMeasure_limsup_le_of_antitone_of_tendsto
    omega θ u (fun k => (hu k).plurisubharmonic) (fun k x => hu0 k x) (⨅ k, u k)
    (isThetaPshPotential_iInf_of_antitone_model hu hanti) hanti hlim
  have hlow : d ≤ liminf (fun k => diagonalPotentialMeasure θ (u k)
      (hu k).plurisubharmonic {x | u k x = 0}) atTop :=
    le_liminf_of_le (h := Eventually.of_forall fun k =>
      (hbound k).trans_eq (contact_mass_eq_mass_of_model omega (hu k)).symm)
  have hmiddle : liminf (fun k => diagonalPotentialMeasure θ (u k)
      (hu k).plurisubharmonic {x | u k x = 0}) atTop ≤
      limsup (fun k => diagonalPotentialMeasure θ (u k)
        (hu k).plurisubharmonic {x | u k x = 0}) atTop := liminf_le_limsup
  exact hlow.trans (hmiddle.trans (hcontact.trans (measure_mono (subset_univ _))))

/-- A single natural uniform positive stage bound supplies the positive
mass field of the actual genuine envelope-fixed infimum. -/
theorem isModelPotential_iInf_of_uniform_positive_stage_mass
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ k, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (u k)
      (hu k).plurisubharmonic) : IsModelPotential θ (⨅ k, u k) := by
  exact ⟨isThetaPshPotential_iInf_of_antitone_model hu hanti,
    singularityEnvelope_iInf_of_antitone_model hu hanti,
    (ENNReal.ofReal_pos.mpr hδ).trans_le
      (le_diagonalPotentialMass_iInf_of_le_stage_masses omega hu hanti hbound)⟩

/-- Actual positive infimum mass and the genuine pointwise limit are
produced from a uniform positive stage bound before deriving mass convergence. -/
theorem tendsto_diagonalPotentialMass_iInf_of_uniform_positive_stage_mass
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ k, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (u k)
      (hu k).plurisubharmonic) :
    Tendsto (fun k => diagonalPotentialMass θ (u k) (hu k).plurisubharmonic) atTop
      (𝓝 (diagonalPotentialMass θ (⨅ k, u k)
        (isThetaPshPotential_iInf_of_antitone_model hu hanti))) := by
  exact tendsto_diagonalPotentialMass_iInf_of_antitone_model omega hu hanti
    (isModelPotential_iInf_of_uniform_positive_stage_mass omega hu hanti hδ hbound).positive_mass

/-- Uniform positive stage bounds independently produce every infimum
mass and hence the actual full mixed-mass limit in the fixed backgrounds. -/
theorem tendsto_globalMixedMass_iInf_of_uniform_positive_stage_mass
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} (hu : ∀ k i, IsModelPotential (θ i) (u k i))
    (hanti : ∀ i, Antitone (fun k => u k i)) {δ : Fin n → ℝ} (hδ : ∀ i, 0 < δ i)
    (hbound : ∀ k i, ENNReal.ofReal (δ i) ≤ diagonalPotentialMass (θ i) (u k i)
      (hu k i).plurisubharmonic) :
    Tendsto (fun k => globalMixedMass θ (u k) (fun i => (hu k i).plurisubharmonic.1))
      atTop (𝓝 (globalMixedMass θ (fun i => ⨅ k, u k i)
        (fun i => (isThetaPshPotential_iInf_of_antitone_model
          (fun k => hu k i) (hanti i)).1))) := by
  apply tendsto_globalMixedMass_iInf_of_antitone_model omega hu hanti
  intro i
  exact (isModelPotential_iInf_of_uniform_positive_stage_mass omega (fun k => hu k i)
    (hanti i) (hδ i) (fun k => hbound k i)).positive_mass

end

end SGPT.Foundations.Analysis.Pending.ActualDecreasingModelPositiveInfimum
