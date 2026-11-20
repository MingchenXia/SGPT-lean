import SGPT.Foundations.Analysis.Pending.BigClassSupremumContact

set_option autoImplicit false

/-!
# For a big class the non-Kähler locus is pluripolar

Xia's Theorem 2.4.4 concludes on `X \ nK({theta})` and then says "since
`nK({theta}) ⊆ X` is a proper analytic subset" (`xia-sgpt:page-0081`), i.e. the
locus is negligible for the measure.  What the argument actually needs is less
than analyticity: `nK({theta})` is the pole set of the normalized big-class
reference of `Pending.BigClassSupremumContact`, hence pluripolar, hence null for
every non-pluripolar product.  That is what this module records.

Both statements inherit the `sorryAx` of the big-class reference chain
(Boucksom's Theorem 3.17 through `Pending.KahlerCurrentRegularization`,
I-0173); nothing new is assumed here.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open FirstPass.NumericalRestrictedVolumeScaffold
open GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BigClassSupremumContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- **The non-Kähler locus of a big class is pluripolar.**  It is the pole set
of the normalized reference of `exists_normalized_reference_of_isBigClass`, and
the pole set of a nondegenerate quasi-PSH potential is pluripolar. -/
theorem manifoldLocallyPluripolar_nonKahlerLocus (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta)) :
    ManifoldLocallyPluripolar (n := n)
      (nonKahlerLocus (RealBottChern.ofRepresentative theta)) := by
  obtain ⟨psi, hpsi, -, hpole, -⟩ := exists_normalized_reference_of_isBigClass hn theta hbig
  rw [← hpole]
  exact quasiPsh_poles_manifoldLocallyPluripolar hpsi.quasiPshPotential

/-- **The non-Kähler locus of a big class carries no non-pluripolar mass.**
This is the step Xia writes as "since `nK({theta})` is a proper analytic
subset". -/
theorem diagonalPotentialMeasure_nonKahlerLocus_eq_zero (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {w : M → EReal} (hw : IsThetaPshPotential theta.val w) :
    diagonalPotentialMeasure theta w hw
      (nonKahlerLocus (RealBottChern.ofRepresentative theta)) = 0 :=
  globalMixedMeasure_doesNotChargeManifoldPluripolar (fun _ : Fin n => hw.1) _
    (manifoldLocallyPluripolar_nonKahlerLocus hn theta hbig)

/-- The poles of the potential itself are also null, so the union of the two
exceptional sets of the local concentration theorem is null. -/
theorem diagonalPotentialMeasure_nonKahlerLocus_union_poleSet_eq_zero (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {w : M → EReal} (hw : IsThetaPshPotential theta.val w) :
    diagonalPotentialMeasure theta w hw
      (nonKahlerLocus (RealBottChern.ofRepresentative theta) ∪ poleSet w) = 0 := by
  refine measure_union_null (diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hw) ?_
  exact globalMixedMeasure_doesNotChargeManifoldPluripolar (fun _ : Fin n => hw.1) _
    (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential)

end

end SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
