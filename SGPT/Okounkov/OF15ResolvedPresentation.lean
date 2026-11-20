import SGPT.Okounkov.OF12ValCurrNormal
import SGPT.Okounkov.OF14Algebraization
import SGPT.Okounkov.OF15Presentation

/-!
# Current-valuation presentations over a supplied resolution

A surjective valuation admits an OF12 presentation over any supplied resolution. The
smooth flag is on a finite blow-up tower of that resolution's analytification, as permitted
by `OF12.Presentation`.
-/

set_option autoImplicit false

namespace SGPT.Okounkov.OF15

open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] {m : ℕ}

/-- Every surjective lexicographic valuation has a smooth-flag presentation over a supplied
resolution, using a finite tower of blow-ups of the resolution's analytification. -/
theorem nonempty_presentation_of_resolution (R : OF12.Resolution f m)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) : Nonempty (OF12.Presentation f m ν) := by
  have htransport : Function.Surjective (R.transport ν) := by
    intro value
    obtain ⟨q, hq⟩ := hν value
    refine ⟨R.φ q, ?_⟩
    change ν (R.φ.symm (R.φ q)) = value
    simpa only [RingEquiv.symm_apply_apply] using hq
  have halg : TowersAlgebraize R.fY (m := m) := by
    intro Y _ _ _ π hseq
    exact OF14.hasRationalAlgebraization_of_isBlowupSequence R.fY R.E hseq
  obtain ⟨P⟩ :=
    exists_blowupPresentation_of_towersAlgebraize R.fY R.E halg (R.transport ν) htransport
  exact ⟨⟨R, P⟩⟩

end SGPT.Okounkov.OF15
