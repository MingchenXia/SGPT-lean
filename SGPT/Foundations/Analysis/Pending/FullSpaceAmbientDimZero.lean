import SGPT.Foundations.Analysis.Pending.DimZeroKahler

set_option autoImplicit false

/-!
# The zero-dimensional branch of full-space ambient-volume vanishing

The Demailly--Păun volume theorem is only substantive in positive complex
dimension.  In dimension zero every Bott--Chern class is big in the project's
potential-based convention: represent the class by a closed real `(1,1)`-form
and use the zero potential.  The representative-level statement lives in the
lightweight `DimZeroKahler` module; this file transports it through the actual
Bott--Chern quotient.
-/

namespace SGPT.Foundations.Analysis.Pending.FullSpaceAmbientDimZero

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DimZeroKahler

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- In complex dimension zero, every real Bott--Chern class contains a Kähler
current.  This is the quotient-level form needed to remove the degenerate
branch before invoking the positive-dimensional volume theorem. -/
theorem isBigClass_of_dim_zero (hn : n = 0) (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) :
    IsBigClass alpha := by
  refine Quotient.inductionOn alpha ?_
  intro theta
  exact DimZeroKahler.isBigClass_of_dim_zero hn omega theta

end

end SGPT.Foundations.Analysis.Pending.FullSpaceAmbientDimZero
