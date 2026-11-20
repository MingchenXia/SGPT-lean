import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination

set_option autoImplicit false

/-! # Full original-background QEA from an actual positive current margin -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.CalibratedQuasiEquisingularApproximation

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.NonKahlerLocus
  DiagonalMass ThetaPshL1Topology SingularCanonicalSingularityDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Demailly's genuine full QEA, calibrated by an actual smaller-background
current margin, retains every field and a common half-margin at every stage. -/
theorem exists_full_qea_with_original_background_stage_margin
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} {δ : ℝ} (hδ : 0 < δ)
    (hu : IsThetaPshPotential (θ - δ • omega.form).val u) :
    ∃ (ε : ℕ → ℝ) (U : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ u ε U ∧
      (∀ j, IsThetaPshPotential θ.val (U j)) ∧
      ∀ j, IsThetaPshPotential (θ - (δ / 2) • omega.form).val (U j) := by
  obtain ⟨ε, U, happ⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation
      omega (θ - δ • omega.form) hu
  have hsemi : (θ - (θ - δ • omega.form)).val.IsSemipositive := by
    rw [sub_sub_cancel]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive hδ.le
  have happθ :=
    QuasiEquisingularBackgroundDomination.isQuasiEquisingularApproximation_of_background_domination
      happ hsemi
  have hsmall : ∀ᶠ j in atTop, ε j < δ / 2 :=
    happ.error_tendsto.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < δ / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  have htail : Tendsto (fun j : ℕ => j + N) atTop atTop := tendsto_add_atTop_nat N
  have hUstrict (j : ℕ) :
      IsThetaPshPotential (θ - (δ / 2) • omega.form).val (U (j + N)) := by
    have hsj : ((δ / 2 - ε (j + N)) • omega.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul omega.isSemipositive
        (sub_nonneg.mpr (hN (j + N) (Nat.le_add_left N j)).le)
    have hform : θ - δ • omega.form + ε (j + N) • omega.form +
        (δ / 2 - ε (j + N)) • omega.form = θ - (δ / 2) • omega.form := by module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (happ.term (j + N)) hsj
  have hUθ (j : ℕ) : IsThetaPshPotential θ.val (U (j + N)) := by
    have hh := LocalPotentials.isThetaPshPotential_add_of_semipositive (hUstrict j)
      (KahlerDomination.isSemipositive_smul omega.isSemipositive
        (by linarith : 0 ≤ δ / 2))
    simpa only [sub_add_cancel] using hh
  refine ⟨fun j => ε (j + N), fun j => U (j + N), ?_, hUθ, hUstrict⟩
  refine ⟨happθ.target, ⟨fun j => happθ.error_nonneg (j + N),
    fun i j hij => happθ.error_antitone (Nat.add_le_add_right hij N),
    happθ.error_tendsto.comp htail⟩,
    fun j => happθ.term (j + N), fun j => happθ.term_hasAnalyticSingularityType (j + N),
    ⟨fun x i j hij => happθ.term_antitone x (Nat.add_le_add_right hij N),
      fun x => (happθ.term_tendsto x).comp htail⟩, ?_⟩
  intro c d hc hcd
  exact htail.eventually (happθ.eventually_multiplierIdealIncluded hc hcd)

/-- The actual current margin internally supplies original bigness and mass
positivity before the genuine calibrated stages converge to the I-envelope. -/
theorem exists_iEnvelope_native_analytic_approximation_of_current_margin [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} {δ : ℝ} (hδ : 0 < δ)
    (hu : IsThetaPshPotential (θ - δ • omega.form).val u) :
    ∃ (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
      (ε : ℕ → ℝ) (U : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ u ε U ∧
      (∀ j, IsThetaPshPotential (θ - (δ / 2) • omega.form).val (U j)) ∧
      ∃ (hU : ∀ j, IsThetaPshPotential θ.val (U j))
        (hI : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u)),
        IGoodWith θ (iSingularityEnvelope θ.val u) hI ∧
        Tendsto (fun j => (⟨U j, hU j⟩ : ThetaPshL1 θ.val)) atTop
          (@nhds (ThetaPshL1 θ.val)
            (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
            ⟨iSingularityEnvelope θ.val u, hI⟩) := by
  have hbig : IsBigClass (RealBottChern.ofRepresentative θ) := by
    simpa only [sub_add_cancel] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
        omega (θ - δ • omega.form) hu hδ
  obtain ⟨ε, U, happ, hU, hstrict⟩ :=
    exists_full_qea_with_original_background_stage_margin omega θ hδ hu
  have hpos : HasPositivePotentialMass θ u happ.target := by
    simpa only [sub_add_cancel] using
      SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul omega hu hδ
  obtain ⟨_, hI, hIG, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit
      omega θ hbig happ hU hpos
  exact ⟨hbig, ε, U, happ, hstrict, hU, hI, hIG, hlim⟩

end

end SGPT.Foundations.Analysis.Pending.CalibratedQuasiEquisingularApproximation
