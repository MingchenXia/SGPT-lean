import SGPT.PSH.SourceQuasiEquisingularCriterion

/-!
A source-facing wrapper for the whole source theorem
`thm:equising_cond_general`, revision 69360cfd,
author/chapter_comp.tex:1768--1773, with standing hypotheses :669--670.

The proof already exists in the imported production native module. This
wrapper only transports the exact original dS topology through its proved
source/native equivalence. Every potential function and every actual
multiplier germ remains unchanged, and no positive mass is assumed.
Validation status and exact source hashes are recorded separately.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Whole source strict-gap inclusion, strengthened to arbitrary filters.
The background is big by the original standing source hypothesis :670. -/
theorem sourceMultiplierIdeal_eventually_le_of_dS_tendsto
    (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ui : I → SourceThetaPotentialL1 θ)
    (u : SourceThetaPotentialL1 θ) {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlim : Tendsto ui F (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology omega θ hbig) u)) :
    ∀ᶠ i in F, (multiplierIdeal (n := n) q (ui i).val).Le
      (multiplierIdeal (n := n) p u.val) := by
  have hn := (sourceSingularity_tendsto_iff_native F omega θ hbig ui u).mp hlim
  exact NativeStrictGapMultiplierInclusion.eventually_multiplierIdeal_le_of_native_limit
    omega (atlasClosedFormToNative θ) hbig F
    (fun i => sourceThetaPotentialL1EquivNative θ (ui i))
    (sourceThetaPotentialL1EquivNative θ u) hp hpq hn

/-- Literal positive-integer cutoff of the whole printed theorem. Degree zero
of a totalized sequence is irrelevant and the produced cutoff is positive. -/
theorem sourceMultiplierIdeal_le_of_dS_sequence
    (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (ui : ℕ → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlim : Tendsto ui atTop (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology omega θ hbig) u)) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∀ j, j₀ ≤ j →
      (multiplierIdeal (n := n) q (ui j).val).Le
        (multiplierIdeal (n := n) p u.val) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (sourceMultiplierIdeal_eventually_le_of_dS_tendsto omega θ hbig atTop ui u hp hpq hlim)
  exact ⟨N + 1, Nat.succ_pos _, fun j hj => hN j (Nat.le_trans (Nat.le_succ N) hj)⟩

end SGPT.PSH.VariableComplexAtlas
