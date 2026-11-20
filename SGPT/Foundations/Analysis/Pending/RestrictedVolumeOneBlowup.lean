import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.Pending.StrictTransformSubvariety
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackUpper

set_option autoImplicit false

/-!
# Restricted volumes under one blowup

Source: CT22, Lemma 4.3 (`ct22-restricted-volumes:invar`), analogous to
Ein--Lazarsfeld--Mustaţă--Nakamaye--Popa, Lemma 2.4; Copy-4, `it:rv-birational`;
blueprint `ana:rv-birational-blowup`.

Let `g : Z → Y` be the blowup of a compact Kähler manifold along a smooth centre,
`α = {θ}` a big class on `Y`, and `W ⊆ Y` a positive-dimensional irreducible
subvariety with `W ⊄ g(Exc g)`.  CT22's proof has three independent parts, recorded
here as three separate explicit interfaces:

* `exists_strictTransform_subvariety_of_isBlowupAlong` (geometry): the strict
  transform `W̃` is a closed irreducible analytic subvariety of dimension `dim W`.
  PROVED in `Pending.StrictTransformSubvariety`.
* `numericalRestrictedVolume_le_pullback` (the elementary inequality
  `⟨α^k⟩_{Y|W} ≤ ⟨(g^*α)^k⟩_{Z|W̃}`): pull back an admissible presentation, use
  `g^*ω ≤ Cω_Z`, and identify absolutely continuous masses through the biholomorphism
  `W̃ \ E ≅ W \ g(E)` off Lebesgue-null analytic sets.  PROVED in
  `Pending.RestrictedVolumePullbackLower`, from CT22 Lemma 4.2
  (`ModificationInputs.nonNefLocus_pullback_of_isBlowupAlong`) and Demailly regularization
  (through analyticity of non-Kähler loci).
* `numericalRestrictedVolume_pullback_le` (the hard inequality): the exceptional
  correction `ω̃ = g^*ω - δ([E] - ddᶜψ)`, pushforward of currents across the centre,
  Demailly regularization and Fatou's lemma.  PROVED here from the single named
  interface `Pending.RestrictedVolumePullbackUpper.exists_restrictedMassEnvelope_pullback_le_at_error`,
  which carries exactly that analytic content; the `W ⊆ E_nn(α)` branch and all
  the envelope bookkeeping are discharged.

`numericalRestrictedVolume_pullback_eq_of_isBlowupAlong` combines them;
`Pending.LocusProperties.exists_strictTransform_numericalRestrictedVolume_eq` is
PROVED from it for every blowup sequence by induction.  The one-blowup statement
is an instance of the sequence statement: the induction is bookkeeping, and the
analytic content sits in the three interfaces above.  No module in the root import
closure imports this file.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumeOneBlowup

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Strict transforms under one blowup** (`Pending.StrictTransformSubvariety`).  The
strict transform of an irreducible subvariety not contained in the image of the exceptional
locus is an irreducible subvariety of the same dimension. -/
theorem exists_strictTransform_subvariety_of_isBlowupAlong [CompactSpace Y]
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) :
    ∃ Wt : ClosedIrreducibleAnalyticSubvariety n Z,
      Wt.carrier = strictTransform n g W.carrier ∧ Wt.dim = W.dim :=
  StrictTransformSubvariety.exists_strictTransform_subvariety_of_isBlowupAlong hg W hW

/-- **CT22, Lemma 4.3, first inequality, one blowup** (`Pending.RestrictedVolumePullbackLower`).
Restricted volumes do not decrease under pullback to the strict transform. -/
theorem numericalRestrictedVolume_le_pullback [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z) :
    numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W ≤
      numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt :=
  RestrictedVolumePullbackLower.numericalRestrictedVolume_le_pullback θ hbig hg W hdim_pos hW Wt
    hWt hdim omega omegaZ

/-- At every prescribed upstairs error, pullback supplies a cofinal downstairs
error whose entire restricted mass envelope is bounded by the upstairs one.

This is the mass-comparison part available without pushing an upstairs current
forward.  It combines the actual pullback presentation, the scalar cofinal
error change, and the already-proved restricted-mass comparison. -/
theorem exists_restrictedMassEnvelope_le_pullback_at_error [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (ε' : PositiveError) :
    ∃ ε : PositiveError,
      restrictedMassEnvelope (acTopMassData omega)
        (RealBottChern.ofRepresentative θ) W ε ≤
      restrictedMassEnvelope (acTopMassData omegaZ)
        (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
        (Wt.withDim W.dim hdim) ε' := by
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  obtain ⟨c, hc, hD⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaZ
    (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form))
  let ε : PositiveError := ⟨c⁻¹ * ε', mul_pos (inv_pos.mpr hc) ε'.2⟩
  refine ⟨ε, ?_⟩
  refine iSup_le fun p => ?_
  have hpole : ¬ (Wt.withDim W.dim hdim).carrier ⊆ g ⁻¹' poleSet p.potential := by
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact StrictTransformLocus.not_strictTransform_subset_preimage hg W hW
      (StrictTransformLocus.isComplexAnalyticSubset_poleSet_of_smoothOffPole
        p.smoothAnalyticSingularities)
      p.not_carrier_subset_poleSet
  have heq : (⟨c * ε, mul_pos hc ε.2⟩ : PositiveError) = ε' := by
    apply Subtype.ext
    simp only [ε]
    field_simp
  refine (RestrictedVolumePullbackLower.acTopMass_le_pullbackPresentation hg W hW Wt hWt hdim
    hc hD p hpole).trans ?_
  rw [← heq]
  exact le_iSup (fun q : AdmissibleRestrictedCurrentPresentation omegaZ _ _ _ =>
    (acTopMassData omegaZ).topMass q)
    (AdmissiblePresentationPullback.pullbackPresentation hg hc hD p
      (Wt.withDim W.dim hdim) hpole)

/-- Off both non-nef loci, cofinal pullback of admissible presentations gives
one direction of the numerical restricted-volume comparison.

The two off-locus hypotheses are explicit: the first is needed to unfold the
downstairs volume as an infimum, and the second does the same for the strict
transform upstairs.  The latter is supplied from the non-nef pullback theorem
in the existing big-class corollary above; this lemma itself uses no such
interface. -/
theorem numericalRestrictedVolume_le_pullback_of_not_subset_nonNef
    [CompactSpace Y] (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (hWnn : ¬ W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hWtnn : ¬ (Wt.withDim W.dim hdim).carrier ⊆ nonNefLocus omegaZ
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))) :
    numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W ≤
      numericalRestrictedVolume omegaZ
        (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
        (Wt.withDim W.dim hdim) := by
  rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega _ W hWnn,
    RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omegaZ _ _ hWtnn]
  refine le_iInf fun ε' => ?_
  obtain ⟨ε, hε⟩ := exists_restrictedMassEnvelope_le_pullback_at_error θ hg W hW Wt
    hWt hdim omega omegaZ ε'
  exact (iInf_le _ ε).trans hε

/-- The strict transform has zero restricted volume whenever the original
subvariety is contained in the non-nef locus.

This is the zero-volume branch of the reverse inequality.  Once the existing
pullback rule for `E_nn` is available, it puts the strict transform in the
upper non-nef locus, so no comparison of admissible-current masses is needed
in this branch. -/
theorem numericalRestrictedVolume_pullback_eq_zero_of_subset_nonNef [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (hWnn : W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt = 0 := by
  apply numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus
  rw [ModificationInputs.nonNefLocus_pullback_of_isBlowupAlong omega omegaZ θ hbig hg]
  rw [hWt]
  exact (closure_minimal sdiff_subset (W.isClosed_carrier.preimage hg.contMDiff.continuous)).trans
    (preimage_mono hWnn)

/-- **The zero-volume branch of CT22, Lemma 4.3, for one blowup.**  If the
downstairs subvariety is already contained in the non-nef locus, both restricted
volumes vanish.  This uses the non-nef pullback rule rather than the hard
pushforward-and-regularization argument needed away from that locus. -/
theorem numericalRestrictedVolume_pullback_eq_of_subset_nonNef [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (hWnn : W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt =
      numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W := by
  rw [numericalRestrictedVolume_pullback_eq_zero_of_subset_nonNef θ hbig hg W Wt hWt omega
      omegaZ hWnn,
    numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus omega
      (RealBottChern.ofRepresentative θ) W hWnn]

/-- The reverse restricted-volume inequality is automatic on an upstairs
non-nef component: its numerical restricted volume is zero by definition.

This is deliberately the *upstairs* zero branch.  The preceding theorem
handles the more useful downstairs branch by transporting the non-nef locus;
away from both branches, no order argument can manufacture the needed
pushforward-and-mass comparison. -/
theorem numericalRestrictedVolume_pullback_le_of_subset_nonNef
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (hWt_nn : Wt.carrier ⊆ nonNefLocus omegaZ
      (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ))) :
    numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt ≤
      numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W := by
  rw [numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus omegaZ
    (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt hWt_nn]
  exact zero_le

/-- **CT22, Lemma 4.3, second inequality, one blowup.**  Restricted volumes do
not increase under pullback to the strict transform.

Now assembled from two branches.  If `W ⊆ E_nn(α)` the strict transform lies in
the upstairs non-nef locus and both volumes vanish
(`numericalRestrictedVolume_pullback_eq_zero_of_subset_nonNef`).  Otherwise both
volumes unfold as infima of mass envelopes and the inequality follows from the
single NAMED interface
`RestrictedVolumePullbackUpper.exists_restrictedMassEnvelope_pullback_le_at_error`
(pushforward of an upstairs admissible current across the centre), through
`RestrictedVolumePullbackUpper.numericalRestrictedVolume_pullback_le_of_not_subset_nonNef`. -/
theorem numericalRestrictedVolume_pullback_le [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z) :
    numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt ≤
      numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W := by
  by_cases hV : W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)
  · rw [numericalRestrictedVolume_pullback_eq_zero_of_subset_nonNef θ hbig hg W Wt hWt omega
      omegaZ hV]
    exact zero_le
  · rw [← Wt.withDim_eq W.dim hdim]
    exact RestrictedVolumePullbackUpper.numericalRestrictedVolume_pullback_le_of_not_subset_nonNef
      θ hbig hg W hdim_pos hW Wt hWt hdim omega omegaZ hV

/-- **Bimeromorphic invariance of restricted volumes for one blowup**, assembled from
the three interfaces above. -/
theorem exists_strictTransform_numericalRestrictedVolume_eq_of_isBlowupAlong [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) :
    ∃ Wt : ClosedIrreducibleAnalyticSubvariety n Z,
      Wt.carrier = strictTransform n g W.carrier ∧ Wt.dim = W.dim ∧
      ∀ (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z),
        numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
            (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt =
          numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W := by
  obtain ⟨Wt, hWt, hdim⟩ := exists_strictTransform_subvariety_of_isBlowupAlong hg W hW
  exact ⟨Wt, hWt, hdim, fun omega omegaZ => by
    by_cases hWnn : W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)
    · exact numericalRestrictedVolume_pullback_eq_of_subset_nonNef θ hbig hg W Wt hWt omega
        omegaZ hWnn
    · exact
        (numericalRestrictedVolume_pullback_le θ hbig hg W hdim_pos hW Wt hWt hdim omega
          omegaZ).antisymm
        (numericalRestrictedVolume_le_pullback θ hbig hg W hdim_pos hW Wt hWt hdim omega
          omegaZ)⟩

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumeOneBlowup
