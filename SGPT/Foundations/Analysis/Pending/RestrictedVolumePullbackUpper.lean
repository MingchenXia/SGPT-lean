import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackEnvelope

set_option autoImplicit false

/-!
# The hard half of CT22, Lemma 4.3, for one blowup

`Pending.RestrictedVolumePullbackLower` proves the elementary inequality
`⟨α^k⟩_{Y|W} ≤ ⟨(g^*α)^k⟩_{Z|W̃}` by PULLING BACK an admissible presentation
along the blowup.  The reverse inequality cannot be obtained that way: it needs
to PUSH an upstairs admissible current forward across the centre, using the
exceptional correction `ω̃ = g^*ω - δ([E] - ddᶜψ)`, Demailly regularization of
the pushforward, and Fatou's lemma.

This module carries the envelope form of that step and derives from it the
numerical inequality on the branch where the downstairs subvariety is not
contained in its non-nef locus.  The complementary branch is already proved
(`RestrictedVolumeOneBlowup.numericalRestrictedVolume_pullback_eq_zero_of_subset_nonNef`),
so the two together discharge
`RestrictedVolumeOneBlowup.numericalRestrictedVolume_pullback_le`.

`exists_restrictedMassEnvelope_pullback_le_at_error` is no longer a bare
`sorry`.  It is
`Pending.RestrictedVolumePullbackEnvelope.exists_restrictedMassEnvelope_le_at_error`,
where the exceptional correction `ω̃ = g^*ω - Θ_E` (sorry-free, from
`Pending.ExceptionalMetric.exists_exceptionalMetric`), the Kähler domination
constant on the compact `Z`, the change of background
(`Pending.RestrictedMassBackgroundChange`) and the supremum over upstairs
presentations are all discharged.  The one-current comparison it rests on is in
turn proved in `Pending.ExceptionalPushforwardFatouReduction` from the single
NAMED classical input `exists_pushforwardRegularization`: the pushforward
`g_*(T' - ε₀Θ_E)` of ONE admissible current across the centre together with its
Demailly regularization.  The Fatou comparison itself is discharged.

What this module removes from the obligation: the unfolding of both numerical
restricted volumes as infima of mass envelopes (which needs the two off-non-nef
certificates and `StrictTransformLocus.not_strictTransform_subset_nonNefLocus`)
and the cofinal change of error.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackUpper

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **At every prescribed downstairs error there is an upstairs error whose
entire restricted mass envelope is bounded by the downstairs one** (CT22's hard
direction).

Statement unchanged; it is now PROVED from the single named classical input
`Pending.ExceptionalPushforwardFatouReduction.exists_pushforwardRegularization`
(the pushforward of one admissible current across the centre together with its
Demailly regularization; the Fatou comparison is proved).  The quantifier order — the pushforward naturally
produces, for a given UPSTAIRS error, a dominated downstairs one, whereas this
statement fixes the downstairs error first — is settled by the change of
background of `Pending.RestrictedMassBackgroundChange`: the corrected Kähler
form `ω̃ = g^*ω - Θ_E` satisfies `ω_Z ≤ A ω̃`, so `ε' = ε/(2A)` upstairs for
`ω_Z` is dominated by `ε/2` upstairs for `ω̃`. -/
theorem exists_restrictedMassEnvelope_pullback_le_at_error [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (ε : PositiveError) :
    ∃ ε' : PositiveError,
      restrictedMassEnvelope (acTopMassData omegaZ)
          (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
          (Wt.withDim W.dim hdim) ε' ≤
        restrictedMassEnvelope (acTopMassData omega)
          (RealBottChern.ofRepresentative θ) W ε :=
  RestrictedVolumePullbackEnvelope.exists_restrictedMassEnvelope_le_at_error θ hbig hg W
    hdim_pos hW Wt hWt hdim omega omegaZ ε

/-- **The reverse restricted-volume inequality off the downstairs non-nef
locus.**  Both volumes unfold as infima of mass envelopes, and the interface
above supplies, for each downstairs error, a dominated upstairs one. -/
theorem numericalRestrictedVolume_pullback_le_of_not_subset_nonNef [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (hWnn : ¬ W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    numericalRestrictedVolume omegaZ
        (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
        (Wt.withDim W.dim hdim) ≤
      numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W := by
  have hn : 0 < n := hdim_pos.trans_le W.dim_le
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  have hWtnn : ¬ (Wt.withDim W.dim hdim).carrier ⊆ nonNefLocus omegaZ
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ)) := by
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact StrictTransformLocus.not_strictTransform_subset_nonNefLocus hn omega omegaZ θ hbig hg
      W hW hWnn
  rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega _ W hWnn,
    RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omegaZ _ _ hWtnn]
  refine le_iInf fun ε => ?_
  obtain ⟨ε', hε'⟩ := exists_restrictedMassEnvelope_pullback_le_at_error θ hbig hg W hdim_pos
    hW Wt hWt hdim omega omegaZ ε
  exact (iInf_le _ ε').trans hε'

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackUpper
