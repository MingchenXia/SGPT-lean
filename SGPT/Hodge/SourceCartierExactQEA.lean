import SGPT.PSH.SourceGentleApproximation
import SGPT.Okounkov.PartialBodyKahler
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
  SGPT.Foundations.Analysis.Pending SGPT.PSH
open scoped Topology

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Eventual genuine Kähler positivity without discarding an input-dependent
tail: every untouched j retains the SAME literal dyadic coefficient and the
actual multiplier ideal of the original full potential, including all poles. -/
theorem exists_eventuallyKahler_exactDyadicQEA {θ : ClosedRealOneOneForm n X}
    {u : X → EReal} (hK : IsKahlerCurrentPotential θ u) :
    ∃ (U : ℕ → X → EReal) (j₀ : ℕ),
      SourceQuasiEquisingularApproximation θ u U ∧
      (∀ j : ℕ, SourceGentleAnalyticSingularities (U j)
        (((2 ^ (j + 1) : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := n) ((2 ^ (j + 1) : ℕ) : ℝ) u)) ∧
      ∀ j : ℕ, j₀ ≤ j →
        IsThetaPshPotential θ.val (U j) ∧ IsKahlerCurrentPotential θ (U j) := by
  obtain ⟨κ, hκ⟩ := hK
  have hhalf : IsThetaPshPotential (θ - (1 / 2 : ℝ) • κ.form).val u := by
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hκ ?_
    have heq : θ - (1 / 2 : ℝ) • κ.form - (θ - κ.form) = (1 / 2 : ℝ) • κ.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  obtain ⟨U, hqea, hgentle⟩ :=
    exists_sourceGentleQuasiEquisingularApproximation κ _ hhalf
  obtain ⟨ω₀, ε, hnat⟩ := native_of_sourceQuasiEquisingularApproximation hqea
  obtain ⟨C, hC, hdom⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul κ (-ω₀.form)
  have hev : ∀ᶠ j in atTop, ε j < 1 / (4 * C) :=
    hnat.error_tendsto.eventually (gt_mem_nhds (by positivity))
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  refine ⟨U, j₀, SGPT.Okounkov.PartialBody.sourceQuasiEquisingularApproximation_of_le hqea ?_, hgentle, ?_⟩
  · have heq : θ - (θ - (1 / 2 : ℝ) • κ.form) = (1 / 2 : ℝ) • κ.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  · intro j hj
    have hquarter : IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val (U j) := by
      refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hnat.term j) ?_
      have hεj := hj₀ j hj
      have heq : θ - (1 / 4 : ℝ) • κ.form -
          (θ - (1 / 2 : ℝ) • κ.form + ε j • ω₀.form) =
          ε j • (-ω₀.form + C • κ.form) + (1 / 4 - ε j * C) • κ.form := by module
      rw [heq]
      refine UniformPerturbedKahlerLowerBound.isSemipositive_add
        (KahlerDomination.isSemipositive_smul hdom (hnat.error_nonneg j))
        (KahlerDomination.isSemipositive_smul κ.isSemipositive ?_)
      have : ε j * C < 1 / 4 := by
        rw [lt_div_iff₀ (by positivity)] at hεj
        nlinarith
      linarith
    refine ⟨?_, KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 4) κ, ?_⟩
    · refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hquarter ?_
      have heq : θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form := by module
      rw [heq]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
    · simpa only [KahlerBackground.smul_form] using hquarter

/-- Exact original multiplier-ideal equivalence forces same-j analytic
singularity type, independently of the auxiliary geometry/background used
by the two genuine approximations. No simultaneous-QEA certificate is assumed. -/
theorem sameDyadicType_of_IEquivalent {u v : X → EReal}
    (hI : SGPT.Foundations.Analysis.FirstPass.IEnvelope.IEquivalentOnManifold (n := n) u v)
    {U V : ℕ → X → EReal}
    (hU : ∀ j, SourceGentleAnalyticSingularities (U j)
      (((2 ^ (j + 1) : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ (j + 1) : ℕ) : ℝ) u))
    (hV : ∀ j, SourceGentleAnalyticSingularities (V j)
      (((2 ^ (j + 1) : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ (j + 1) : ℕ) : ℝ) v)) :
    ∀ j, SameSingularityTypeOn (U j) (V j) univ := by
  intro j
  refine ⟨IdealWeightComparison.moreSingularOn_univ_of_le (hU j).2.2.1 (hV j).2.2.1 ?_,
    IdealWeightComparison.moreSingularOn_univ_of_le (hV j).2.2.1 (hU j).2.2.1 ?_⟩
  · exact PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hI.1 (by positivity)
  · exact PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hI.2 (by positivity)

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
