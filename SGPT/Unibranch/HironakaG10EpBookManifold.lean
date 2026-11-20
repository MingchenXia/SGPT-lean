import SGPT.Unibranch.HironakaG10EpChowBridge
import SGPT.Unibranch.UnibNSPrimeRealization
import SGPT.BDivisor.BlowupModelSystem

/-!
# The SGPT book's manifold Chow consumers, from the general Chow lemma

Run 0081 lane G10EP (SGPT consumer contract G10-05-01.sgpt).  Blueprint:
`hironaka-g10ep-chow-bridge.tex`.

Two existing SGPT book formalizations take the TN manifold Chow lemma `HironakaChowLemmaManifold`
as a named hypothesis: `cor:primerealization` over a compact complex manifold
(`SGPT.Unibranch.PrimeRealization.exists_blowupSequence_realization_of_chow`) and the cofinality of
the book's blowup model system (`SGPT.BDivisor.ModelSystem.blowup_isCofinal_of_chow`).  Through
`HironakaG10EpChowBridge.hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral` both now hold
from goal G10's endpoint `HironakaChowLemmaGeneral` (for manifolds in `Type`, the universe of the
native category).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace SGPT.Unibranch.HironakaG10EpBookManifold

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending HironakaG10GenStatement HironakaG10EpChowBridge
  SGPT.PSH.CompactPrimeOver

noncomputable section

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **`cor:primerealization` over a compact complex manifold, from the general Chow lemma.**
Every prime divisor over a compact complex manifold `X` is equivalent to one realized on a finite
blowup sequence of `X` by a connected smooth hypersurface. -/
theorem exists_blowupSequence_realization (H : HironakaChowLemmaGeneral) [CompactSpace X]
    (p : PrimePresentation n X) :
    ∃ q : PrimePresentation n X,
      IsBlowupSequence n X q.model q.projection ∧ commonResolutionRelation p q :=
  PrimeRealization.exists_blowupSequence_realization_of_chow
    (hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral H) p

/-- **Cofinality of the book's blowup models, from the general Chow lemma.**  Every modification
of a compact complex manifold is dominated by a finite composition of smooth-centre blowups. -/
theorem blowup_isCofinal (H : HironakaChowLemmaGeneral) [CompactSpace X] :
    (SGPT.BDivisor.ModelSystem.blowup n X).IsCofinal :=
  SGPT.BDivisor.ModelSystem.blowup_isCofinal_of_chow
    (hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral H)

end

end SGPT.Unibranch.HironakaG10EpBookManifold
