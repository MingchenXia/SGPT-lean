import SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardFatouReduction
import SGPT.Foundations.Analysis.Pending.RestrictedMassBackgroundChange
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.BlowupCompact

set_option autoImplicit false

/-!
# The envelope form of CT22, Lemma 4.3, routed through the Fatou reduction

`Pending.ExceptionalPushforwardMass.exists_restrictedMassEnvelope_le_at_error`
assembles the envelope form of CT22's Lemma 4.3 from the one-current comparison
`acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection`, which is a bare
`sorry` in that module.  `Pending.ExceptionalPushforwardFatouReduction` proves
that comparison's exact statement from the single NAMED classical input
`exists_pushforwardRegularization` (the pushforward `g_*(T' - ε₀Θ_E)` and its
Demailly regularization) together with the Fatou comparison across the centre.

`Pending.ExceptionalPushforwardMass` is in NO live lane's write set -- neither this
one's nor TN23-ENVELOPES's -- so the one-line substitution cannot be made
there by any agent; it is a human decision.

DUPLICATION NOTICE.  `exists_restrictedMassEnvelope_le_at_error` below and
`Pending.ExceptionalPushforwardMass.exists_restrictedMassEnvelope_le_at_error` are
the same statement with the same proof script, differing only in the final `refine`;
`isBlowupSequence_of_isBlowupAlong` is duplicated too.  The one in
`ExceptionalPushforwardMass` is the ORIGINAL.  Nothing enforces that the two stay in
sync, so if that module is ever edited, edit this one to match -- or, better, carry
out I-0386 and delete this module.  This module
therefore re-runs the assembly — which is pure inequality bookkeeping about the
exceptional correction, the Kähler domination constant and the change of
background, with no analysis in it — on top of the Fatou reduction.  The
statement is byte-identical to the one in `ExceptionalPushforwardMass`; only its
single analytic input changes, from a bare `sorry` to the named interface.

The assembly itself:

* `Pending.ExceptionalMetric.exists_exceptionalMetric` (sorry-free) supplies the
  correction `ω̃ = g^*ω - Θ_E`, Kähler on `Z`, with `E` supported on the
  exceptional locus;
* `Pending.KahlerDomination.exists_pos_isSemipositive_add_smul` on the compact
  `Z` supplies the constant `A` with `A ω̃ ≥ ω_Z`;
* `Pending.RestrictedMassBackgroundChange.restrictedMassEnvelope_le_of_isSemipositive`
  changes the background at `ε' = ε₀ / A`, which is what settles the quantifier
  order: the pushforward produces, for a given UPSTAIRS error, a dominated
  downstairs one, while the statement fixes the downstairs error first.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackEnvelope

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- A single blowup along a smooth centre is a blowup sequence. -/
theorem isBlowupSequence_of_isBlowupAlong {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) : IsBlowupSequence n Y Z g := by
  simpa using IsBlowupSequence.step (X := Y) (id : Y → Y) C g IsBlowupSequence.refl hg

/-- **The envelope form of CT22's Lemma 4.3, hard direction, with no bare
`sorry` above it.**  For every downstairs error there is an upstairs error whose
whole restricted mass envelope is dominated.

The statement is that of
`Pending.ExceptionalPushforwardMass.exists_restrictedMassEnvelope_le_at_error`;
the proof is the same assembly, run on
`Pending.ExceptionalPushforwardFatouReduction.acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection`
instead.  Its only unproved ingredient is the named classical input
`ExceptionalPushforwardFatouReduction.exists_pushforwardRegularization`. -/
theorem exists_restrictedMassEnvelope_le_at_error [CompactSpace Y]
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
          (RealBottChern.ofRepresentative θ) W ε := by
  have hZc := BlowupCompact.compactSpace_of_isBlowupAlong hg
  have hseq : IsBlowupSequence n Y Z g := isBlowupSequence_of_isBlowupAlong hg
  obtain ⟨E, hEsupp, hkahler, -⟩ := ExceptionalMetric.exists_exceptionalMetric omega g hseq
  set omegaTilde : KahlerBackground n Z :=
    ⟨ClosedRealOneOneForm.pullback hseq.contMDiff omega.form - E.curvature, hkahler⟩ with hOT
  obtain ⟨A, hApos, hAsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omegaTilde (-omegaZ.form)
  set ε₀ : PositiveError := ⟨(ε : ℝ) / 2, div_pos ε.2 two_pos⟩ with hε₀
  set ε' : PositiveError := ⟨(ε₀ : ℝ) / A, div_pos ε₀.2 hApos⟩ with hε'
  have hε'val : (ε' : ℝ) = (ε₀ : ℝ) / A := rfl
  have hε₀val : (ε₀ : ℝ) = (ε : ℝ) / 2 := rfl
  have hAmul : (ε' : ℝ) * A = (ε₀ : ℝ) := by
    rw [hε'val]
    field_simp
  have hsemi : ((ε₀ : ℝ) • omegaTilde.form - (ε' : ℝ) • omegaZ.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hAsemi (A := (ε' : ℝ)) ε'.2.le
    have hform : (ε' : ℝ) • (-omegaZ.form + A • omegaTilde.form) =
        (ε₀ : ℝ) • omegaTilde.form - (ε' : ℝ) • omegaZ.form := by
      rw [smul_add, smul_neg, smul_smul, hAmul]
      abel
    rwa [hform] at h
  refine ⟨ε', le_trans
    (RestrictedMassBackgroundChange.restrictedMassEnvelope_le_of_isSemipositive
      omegaZ omegaTilde _ _ hsemi) ?_⟩
  refine iSup_le fun q => ?_
  refine ExceptionalPushforwardFatouReduction.acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection
    θ hbig hg W hdim_pos hW Wt hWt hdim omega E ?_ omegaTilde rfl ε₀ ε ?_ q
  · exact hEsupp
  · rw [hε₀val]
    linarith

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackEnvelope
