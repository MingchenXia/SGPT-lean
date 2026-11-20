import SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# Kähler currents in complex dimension zero

The zero-dimensional branches used by the full-space ambient-volume argument
need no mass or envelope theory.  An alternating real two-form on the
zero-dimensional complex model vanishes, hence is semipositive.  The zero
potential therefore turns every closed real `(1,1)` representative into a
Kähler current relative to any supplied Kähler background.
-/

namespace SGPT.Foundations.Analysis.Pending.DimZeroKahler

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- In complex dimension zero every smooth real two-form is semipositive: the
tangent model is a subsingleton, so the two arguments of the alternating
coefficient coincide and it vanishes. -/
theorem isSemipositive_of_dim_zero (hn : n = 0) (a : SmoothRealForm n M 2) :
    a.IsSemipositive := by
  subst hn
  intro e z _ v
  have hv : v = Complex.I • v := Subsingleton.elim _ _
  have hzero : a.coeff e z ![v, Complex.I • v] = 0 := by
    refine (a.coeff e z).map_eq_zero_of_eq ![v, Complex.I • v]
      (i := 0) (j := 1) ?_ (by decide)
    simpa using hv
  rw [hzero]

/-- In complex dimension zero every class with a Kähler background is big.
The zero function is a potential of a Kähler current because the difference of
the representative and the background is semipositive. -/
theorem isBigClass_of_dim_zero (hn : n = 0) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) :
    IsBigClass (RealBottChern.ofRepresentative theta) :=
  ⟨{ representative := theta
     represents := rfl
     potential := fun _ => 0
     lowerBound := omega
     strictlyPsh :=
       (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff
           (theta - omega.form)).mpr
         (isSemipositive_of_dim_zero hn (theta - omega.form).val) }⟩

end

end SGPT.Foundations.Analysis.Pending.DimZeroKahler
