import SGPT.PSH.HermitianGlobalCurrents
import SGPT.Foundations.Analysis.Pending.PatchOverlap

/-!
# Geometric overlap descent for actual coordinate product measures

The chart/domain geometry is independent of every background and potential.
The ordinary coordinate pushforward identity descends to literal equality
of transported measures on manifold overlaps. Analytic covariance of the
nonclosed-background products must supply that identity separately.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

namespace CoordinatePatch

/-- The actual coordinate image of the common manifold source. -/
def overlapDomain (P Q : CoordinatePatch (m + 1) M) : Opens (ComplexModel (m + 1)) :=
  PatchOverlap.overlapDomain P.zeroPotentialPatch Q.zeroPotentialPatch

/-- The actual holomorphic chart transition between the two patches. -/
def transition (P Q : CoordinatePatch (m + 1) M) :
    ComplexModel (m + 1) → ComplexModel (m + 1) :=
  PatchOverlap.transition P.zeroPotentialPatch Q.zeroPotentialPatch

theorem overlapDomain_le (P Q : CoordinatePatch (m + 1) M) :
    P.overlapDomain Q ≤ P.domain :=
  PatchOverlap.overlapDomain_le P.zeroPotentialPatch Q.zeroPotentialPatch

/-- Holomorphicity and inverse laws are internally produced from the
actual manifold atlas and the two coordinate-domain inclusions. -/
theorem isBiholomorphicPair (P Q : CoordinatePatch (m + 1) M) :
    BedfordTaylor.IsBiholomorphicPair (P.overlapDomain Q) (Q.overlapDomain P)
      (P.transition Q) (Q.transition P) :=
  PatchOverlap.isBiholomorphicPair P.zeroPotentialPatch Q.zeroPotentialPatch

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
private theorem zeroPotentialPatch_pushMeasure (P : CoordinatePatch (m + 1) M)
    (μ : Measure (ComplexModel (m + 1))) : P.zeroPotentialPatch.pushMeasure μ = P.pushMeasure μ := rfl

/-- Ordinary coordinate covariance of the original measures yields genuine
equality on the manifold overlap, without exact-potential assumptions. -/
theorem pushMeasure_restrict_inter_eq (P Q : CoordinatePatch (m + 1) M)
    {μ ν : Measure (ComplexModel (m + 1))}
    (h : μ.restrict (P.overlapDomain Q) =
      (ν.restrict (Q.overlapDomain P)).map (Q.transition P)) :
    (P.pushMeasure μ).restrict ((P.source : Set M) ∩ Q.source) =
      (Q.pushMeasure ν).restrict ((P.source : Set M) ∩ Q.source) := by
  simpa only [zeroPotentialPatch_source, zeroPotentialPatch_pushMeasure] using
    PatchOverlap.pushMeasure_restrict_inter_eq P.zeroPotentialPatch Q.zeroPotentialPatch h

end CoordinatePatch

variable [MeasurableSpace M] [BorelSpace M] {a : ℕ}

/-- The actual coordinate trace transport law discharges the ordinary
overlap condition used by genuine global measure gluing. -/
theorem traceMeasuresAgree_of_coordinate_covariance
    (P : Fin a → CoordinatePatch (m + 1) M)
    (T : ∀ i, LocalProductCurrents.LocalProductCurrent (m + 1) (P i).domain 0)
    (hT : ∀ i, LocalProductCurrents.IsPositive (T i))
    (hcov : ∀ i j, (hT i).traceMeasure.restrict ((P i).overlapDomain (P j)) =
      ((hT j).traceMeasure.restrict ((P j).overlapDomain (P i))).map ((P j).transition (P i))) :
    TraceMeasuresAgree P T hT :=
  fun i j => (P i).pushMeasure_restrict_inter_eq (P j) (hcov i j)

end SGPT.PSH.HermitianGlobalProducts
