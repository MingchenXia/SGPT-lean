import SGPT.Okounkov.SourceCurrentValuationWhole

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceValuativeClosure
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.Valuative

/-- Every original I-below current's actual whole real vector belongs to
the SAME original body, with no analyticity or supplied value hypothesis. -/
theorem valuationsBelow_subset_generalPartialBody {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    valuationsBelow F θ φ ⊆ generalPartialBody F θ φ := by
  rintro _ ⟨ψ, hψ, hI, rfl⟩
  exact (generalPartialBody_subset_of_iOrder hψ hφ hI hbig).1
    (SourceCurrentValuation.flagValuation_mem_generalPartialBody F hψ)

/-- The entire original reverse inclusion of eq:DeltaTequalallval,
for ALL original currents and dimensions n>0. -/
theorem closure_valuationsBelow_subset_generalPartialBody {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    closure (valuationsBelow F θ φ) ⊆ generalPartialBody F θ φ :=
  closure_minimal (valuationsBelow_subset_generalPartialBody F hφ hbig)
    (isClosed_generalPartialBody θ φ)

/-- WHOLE second printed formula eq:TPOB_val: the actual traditional body
is the closure of ALL original positive-current valuations in its big class.
The vectors and currents may be arbitrary real/nonanalytic ones. -/
theorem tradOkounkovBody_eq_closure_classValuations {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody F θ = closure (classValuations F θ) := by
  refine (tradOkounkovBody_subset_closure_valuations θ).antisymm
    (closure_minimal ?_ (isClosed_tradOkounkovBody θ))
  rintro _ ⟨ψ, hψ, rfl⟩
  exact generalPartialBody_subset_tradOkounkovBody hψ hbig
    (SourceCurrentValuation.flagValuation_mem_generalPartialBody F hψ)

end SGPT.Okounkov.SourceValuativeClosure
