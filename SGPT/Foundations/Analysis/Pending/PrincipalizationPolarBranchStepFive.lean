import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.PrincipalizationCopy4StepFiveCoreReduction

set_option autoImplicit false

/-!
# Copy-4 Steps 3--5 with the polar branch CONSTRUCTED, not received

Source: Copy-4, `prop:principalization`, Steps 1--5 and `sec:fixed-data`
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1845-1984`);
blueprint `ana:principalization-data`.

## Why this module exists

`PrincipalizationGluingLocalInterface.ct22Copy4_nonempty_copy4StepFiveExceptionalWeightData`
takes the global polar branch `φ_G` as a **universally quantified input**: for
*every* Kähler-current potential `φ_G` of `θ_Y`, it asserts a Step-5 datum with
that `φ_G`.  Two of the fields of `Copy4StepFiveExceptionalWeightData` constrain
`φ_G` rather than being constrained by it,

* `polar_split  : ∀ x, φ_G x = φ_{Q,π} x + τ ψ_E x`,
* `phiQpi_def   : ∀ x, φ_{Q,π} x = convexComb (1 - L/ℓ) U_M Φ_R (π x)`,

and the accompanying fields force `U_M` to be bounded below by an ideal weight
(`ambientUM_lower` together with `ambientGM_source.BM_presentation`) and `Φ_R`
to *have* analytic singularities (`ambientPhiR_source.PhiR_presentation`).  So
the structure pins the singularities of `φ_G` to the divisorial/ideal data of
Steps 1--4.  Copy-4 **builds** `φ_G` that way; it never accepts an arbitrary
Kähler current of the class.  The universally quantified form is therefore
stronger than the source, and there is no reason to expect it to be true: a
Kähler current of a big class may have singularities that are not of analytic
type at all, and no choice of the ambient data absorbs them.

Under the workspace's rule 1 the existing statement is left byte-identical; this
module states the **faithful** interface instead, with `φ_G` existentially
quantified, and proves the two halves that connect it to the consumer:

* `eq_bot_on_strictTransform_of_isKahlerCurrentPotential` — the pole clause
  `φ_G = -∞` on the strict transform is *not* source data.  It follows from
  bigness, `nonKahlerLocus_pullback` and `eq_bot_of_lelongNumber_pos`.  This
  argument already existed, but only inside the body of a theorem that ends in
  `sorry`; here it is a reusable sorry-free lemma.
* (deleted, human decision I-0739 item 2) the universally-quantified-`π` interface
  `ct22Copy4_exists_polarBranch_copy4StepFiveExceptionalWeightData` and its only consumer
  `exists_polarBranch_localBranch_with_compactComparison`: superseded since I-0661 by
  `PrincipalizationStepOneInterface` (existential `π`, Steps 3--6 proved), zero consumers.

`exists_polarBranch_of_forall_polarBranch` measures the split in the sense of
`I-0578`: the faithful interface follows from the universally quantified one by
instantiation at a single potential, so it is genuinely *weaker*; the converse
instantiation does not exist, because a universal statement cannot be recovered
from one witness.

A second, smaller discrepancy is repaired at the same time.  Copy-4's standing
hypothesis `V ⊄ E_nn(α)` reaches
`PrincipalizationGluingLocalInterface.ct22Copy4_exists_localBranch_with_compactComparison`
and is then discarded (`_hnonNef`), so the interface chain asks for Steps 1--5
without one of the hypotheses the source has.  The interface here takes it, which
makes the obligation weaker and keeps the hypothesis load-bearing on the route.

Nothing here constructs or resolves a modification: `π`, its strict transform
`W`, and the positive restricted volume are inputs, exactly as in the interface
this module replaces.

## What this interface itself still needs

The fields listed above require `φ_G` to have *analytic* singularities near the
smooth point (`Φ_R` is an analytic-singularity weight and `U_M` is bounded below
by an ideal weight).  Producing such a `φ_G` is target 5,
`KahlerCurrentRegularization`.  So the faithful interface is true in the source
but is not independent of that target; it is not "one Lean hole away".
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.PrincipalizationPolarBranchStepFive

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.BlowupSequences FirstPass.AnalyticGluingData
  PrincipalizationCopy4StepFiveCoreReduction PrincipalizationSourceDataReduction

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The strict transform of a non-Kähler-locus component lies in the
non-Kähler locus of the pulled-back class. -/
theorem strictTransform_subset_nonKahlerLocus_pullback [CompactSpace X]
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {V : ClosedIrreducibleAnalyticSubvariety n X}
    (hcomponent : IsIrreducibleComponent V
      (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (π : Y → X)
    (hπ : IsAdaptedBlowupSequence n X V.carrier Y π) :
    strictTransform n π V.carrier ⊆
      nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hπ.contMDiff θ)) := by
  have hstrict : strictTransform n π V.carrier ⊆ π ⁻¹' V.carrier := by
    rw [strictTransform]
    exact closure_minimal sdiff_subset
      (V.isClosed_carrier.preimage hπ.contMDiff.continuous)
  rw [LocusProperties.nonKahlerLocus_pullback ⟨omega⟩ θ hbig π hπ.isBlowupSequence]
  exact fun y hy => Or.inl (hcomponent.1 (hstrict hy))

/-- **The pole clause is not source data.**  Any Kähler-current potential of
the pulled-back class is `-∞` at every point of the strict transform of a
non-Kähler-locus component.

The strict transform lies in the non-Kähler locus of `θ_Y`, so every Kähler
current of `{θ_Y}` has positive Lelong number there, and a potential with a
positive Lelong number is `-∞` at that point. -/
theorem eq_bot_on_strictTransform_of_isKahlerCurrentPotential [CompactSpace X]
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {V : ClosedIrreducibleAnalyticSubvariety n X} (hdim_pos : 0 < V.dim)
    (hcomponent : IsIrreducibleComponent V
      (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (π : Y → X)
    (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
    {φG : Y → EReal}
    (hφG : IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG) :
    ∀ y ∈ strictTransform n π V.carrier, φG y = ⊥ := by
  have hn : 0 < n := lt_of_lt_of_le hdim_pos V.dim_le
  have hWnonKahler :=
    strictTransform_subset_nonKahlerLocus_pullback omega hbig hcomponent π hπ
  obtain ⟨omegaY, hpsh⟩ := hφG
  intro y hy
  exact eq_bot_of_lelongNumber_pos hn hpsh.1
    (hWnonKahler hy
      { representative := ClosedRealOneOneForm.pullback hπ.contMDiff θ
        represents := rfl
        potential := φG
        lowerBound := omegaY
        strictlyPsh := hpsh })

/-- **The split is a genuine weakening.**  The faithful interface
follows from the universally quantified one at any single potential, so it is
weaker; a universal statement cannot be recovered from one witness, so the
converse instantiation does not exist.  Sorry-free: the universally quantified
conclusion enters as a hypothesis, not through the interface that carries it. -/
theorem exists_polarBranch_of_forall_polarBranch
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {θY : ClosedRealOneOneForm n Y} {W : Set Y}
    {φG₀ : Y → EReal} (hφG₀ : IsKahlerCurrentPotential θY φG₀)
    (hforall : ∀ φG : Y → EReal, IsKahlerCurrentPotential θY φG →
      Nonempty (Copy4StepFiveExceptionalWeightData θY W φG)) :
    ∃ φG : Y → EReal, IsKahlerCurrentPotential θY φG ∧
      Nonempty (Copy4StepFiveExceptionalWeightData θY W φG) :=
  ⟨φG₀, hφG₀, hforall φG₀ hφG₀⟩

end

end SGPT.Foundations.Analysis.Pending.PrincipalizationPolarBranchStepFive
