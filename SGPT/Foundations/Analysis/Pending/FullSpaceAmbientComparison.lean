import SGPT.Foundations.Analysis.Pending.FullSpaceCountableLocalization
import SGPT.Foundations.Analysis.Pending.NonBigVolumeReduction

set_option autoImplicit false

/-!
# From the restricted absolutely continuous mass to the ambient diagonal mass

`Pending.NonBigVolumeReduction` reduces the full-space non-big volume branch to
two independent inputs.  The first one is the *local* comparison

  `acTopMass p ≤ perturbedDiagonalPotentialMass p`

for a full-space admissible presentation.  This module isolates exactly the one
statement that is still missing for it, and derives the comparison from that
statement alone.

**The localization theorem (now proved).**
`lintegral_patchDensity_eq_globalMixedMeasure_image` says: on the full space, a
measurable parameter piece of a regular patch whose image is regular and avoids
the pole set has a measurable image, and its parameter density integral is the
ambient diagonal non-pluripolar measure of that image.  It is a *localization*
statement: the same identity is already PROVED, without any hypothesis on the
dimension, for a closed parameter ball contained in one automatic patch
neighbourhood
(`Pending.FullSpaceGeneralClosedBall.exists_fullSpace_closedBall_lintegral_eq_globalMixedMeasure`).
The passage from such a ball to an arbitrary measurable piece — a countable
cover of the parameter domain by those balls, a measurable disjointification,
and countable additivity on both sides, together with the measurability of the
image — is carried out in `Pending.FullSpaceMeasurablePiece` and
`Pending.FullSpaceCountableLocalization`.

Everything else on this branch is bookkeeping and is proved here:
`acTopMass_le_perturbedDiagonalPotentialMass` and the envelope form
`restrictedMassEnvelope_le_perturbedDiagonalPotentialEnvelope`.  No bound on the
ambient mass itself is assumed anywhere; that is the separate Demailly--Păun
input recorded in `NonBigVolumeReduction`.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.FullSpaceAmbientComparison

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open FullSpaceAmbientMass NonBigVolumeReduction GlobalNonPluripolar MixedMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- **The localization statement.**  On the full space, the parameter density
integral over a measurable regular pole-free piece is the ambient diagonal
non-pluripolar measure of its image, and that image is measurable.

**PROVED.**  The closed-ball case is `FullSpaceGeneralClosedBall`, in every
complex dimension; `FullSpaceMeasurablePiece` weakens its compactness
hypothesis to measurability (the only use of compactness there was measurability
of the coordinate image, which is a preimage under the inverse biholomorphism);
and `FullSpaceCountableLocalization` performs the countable-cover,
disjointification and countable-additivity passage to an arbitrary measurable
piece.  The statement is transported from the canonical full-dimensional
presentation `fullSpaceSubvariety V hcarrier hdim` back to `V` itself, which is
propositionally equal to it. -/
theorem lintegral_patchDensity_eq_globalMixedMeasure_image
    (hcarrier : V.carrier = univ) (hdim : V.dim = n)
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S)
    (hSdom : S ⊆ P.parameterDomain)
    (hSreg : P.toManifold '' S ⊆ regularLocus (n := n) V.carrier V.dim)
    (hSpole : Disjoint (P.toManifold '' S) (poleSet p.potential)) :
    MeasurableSet (P.toManifold '' S) ∧
      ∫⁻ w in S, ENNReal.ofReal (patchDensity p P w) =
        globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
          (fun _ => p.potential) (fun _ => p.potential_psh.1) (P.toManifold '' S) := by
  revert hSpole hSreg hSdom hS S P p
  rw [FullSpaceRegularPatch.fullSpaceSubvariety_eq V hcarrier hdim]
  intro p P S hS hSdom _ hSpole
  exact FullSpaceCountableLocalization.measurableSet_and_lintegral_patchDensity_eq_globalMixedMeasure
    p P hS hSdom hSpole

omit [BorelSpace M] in
/-- The total ambient diagonal mass of a presentation is the ambient measure of
the whole manifold. -/
theorem perturbedDiagonalPotentialMass_eq_globalMixedMeasure_univ
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) :
    perturbedDiagonalPotentialMass p =
      globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
        (fun _ => p.potential) (fun _ => p.potential_psh.1) univ := rfl

/-- Every finite regular-piece sum of a full-space presentation is bounded by
the ambient diagonal non-pluripolar mass.  Only the localization interface is
used; the rest is finite additivity of a measure on pairwise disjoint pieces. -/
theorem finitePieceMass_le_perturbedDiagonalPotentialMass
    (hcarrier : V.carrier = univ) (hdim : V.dim = n)
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (F : RegularPieceFamily V (poleSet p.potential)) :
    (∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w)) ≤
      perturbedDiagonalPotentialMass p := by
  classical
  set mu : Measure M := globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
    (fun _ => p.potential) (fun _ => p.potential_psh.1) with hmu
  set A : Fin F.size → Set M := fun i => (F.patch i).toManifold '' F.piece i with hA
  have hkey : ∀ i, MeasurableSet (A i) ∧
      ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w) = mu (A i) := fun i =>
    lintegral_patchDensity_eq_globalMixedMeasure_image hcarrier hdim p (F.patch i)
      (F.measurableSet_piece i) (F.piece_subset i) (F.image_subset_regularLocus i)
      (F.image_disjoint_avoid i)
  have hsum : (∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w)) =
      ∑ i, mu (A i) :=
    Finset.sum_congr rfl fun i _ => (hkey i).2
  have hdisj : Set.Pairwise (↑(Finset.univ : Finset (Fin F.size)))
      (Function.onFun Disjoint A) :=
    fun i _ j _ hij => F.pairwise_disjoint_image hij
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin F.size)), MeasurableSet (A i) :=
    fun i _ => (hkey i).1
  have hunion : mu (⋃ i ∈ (Finset.univ : Finset (Fin F.size)), A i) = ∑ i, mu (A i) :=
    measure_biUnion_finset hdisj hmeas
  rw [hsum, ← hunion, perturbedDiagonalPotentialMass_eq_globalMixedMeasure_univ p, ← hmu]
  exact measure_mono (subset_univ _)

/-- **The restricted absolutely continuous mass of a full-space presentation is
at most its ambient diagonal non-pluripolar mass.**  This is the first of the
two inputs `NonBigVolumeReduction` needs; the second, a vanishing bound on the
ambient masses themselves, is the Demailly--Păun volume theorem. -/
theorem acTopMass_le_perturbedDiagonalPotentialMass
    (hcarrier : V.carrier = univ) (hdim : V.dim = n)
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) :
    acTopMass p ≤ perturbedDiagonalPotentialMass p := by
  unfold acTopMass
  exact iSup_le fun F => finitePieceMass_le_perturbedDiagonalPotentialMass hcarrier hdim p F

/-- The envelope form of the comparison: on the full space every restricted mass
envelope is bounded by the corresponding ambient diagonal envelope. -/
theorem restrictedMassEnvelope_le_perturbedDiagonalPotentialEnvelope
    (hcarrier : V.carrier = univ) (hdim : V.dim = n) :
    restrictedMassEnvelope (acTopMassData omega) alpha V epsilon ≤
      perturbedDiagonalPotentialEnvelope omega alpha V epsilon :=
  NonBigVolumeReduction.restrictedMassEnvelope_le_perturbedDiagonalPotentialEnvelope
    omega alpha V epsilon
    (fun p => acTopMass_le_perturbedDiagonalPotentialMass hcarrier hdim p)

end SGPT.Foundations.Analysis.Pending.FullSpaceAmbientComparison
