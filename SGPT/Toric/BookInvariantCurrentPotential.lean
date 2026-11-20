import SGPT.Toric.InvariantCurrentPotential
import SGPT.PSH.BookCurrentPositivity

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame CurrentBottChernClass NaturalThetaPshGeometricCurrent
open GlobalPositiveCurrentACRestriction

variable {m : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + 1) → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "X" => PolytopeToricVariety γ hs

/-- The actual source positivity supplies full geometric positivity internally. -/
theorem bookCurrent_full_positive (T : BookCurrent.ClosedPositiveCurrent m X) :
    IsFullPositive T.current :=
  BookCurrent.isFullPositive_of_isPositiveCurrent T.current
    T.isClosed T.isTypeOneOne T.isPositive

/-- Actual compact-torus pullback invariance of the ORIGINAL book current. -/
def IsCompactTorusInvariantBookCurrent (T : BookCurrent.ClosedPositiveCurrent m X) : Prop :=
  IsCompactTorusInvariantCurrent T.val (bookCurrent_full_positive T)

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- EXACT source current class subtype, with the original positivity convention:
there is no additional full-positivity or invariant-presentation hypothesis. -/
theorem exists_mem_PSHTor_of_invariant_bookCurrent
    (T : BookCurrent.ClosedPositiveCurrentIn m X (RealBottChern.ofRepresentative h.form))
    (hinv : IsCompactTorusInvariantBookCurrent T.val) :
    ∃ (u : X → EReal) (hu : IsThetaPshPotential h.form.val u),
      T.val.current = thetaPotentialCurrent h.form.val u hu ∧ u ∈ h.PSHTor := by
  apply h.exists_mem_PSHTor_of_invariant_current_class T.val.val
    (bookCurrent_full_positive T.val)
  · exact T.property
  · exact hinv

end BigToricMetric
end SGPT.Toric
