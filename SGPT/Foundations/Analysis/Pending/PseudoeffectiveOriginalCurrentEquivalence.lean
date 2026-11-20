import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

set_option autoImplicit false

/-!
# Pseudoeffectivity of the original current cone

On a compact complex manifold of positive dimension, the actual potential
predicate equals existence of an original closed fully positive current in the
same smooth Bott--Chern quotient class. The entire blueprint proof precedes
this source. No analytic singularity, potential or class calibration is supplied.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentEquivalence

open FirstPass FirstPass.PositiveClasses CurrentBottChernClass CanonicalCurrentFrame
  ThetaPotentialCurrentBottChernClass NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent GlobalPositiveCurrentACRestriction

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X]

/-- The natural potential cone is exactly the cone containing an original
closed fully positive current. All scalar representations are internal. -/
theorem classPseudoeffectiveViaPotentials_iff_exists_original_current
    (α : RealBottChern (m + 1) X) :
    ClassPseudoeffectiveViaPotentials α ↔
      ∃ (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)),
        IsFullPositive T.val ∧
          bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T = α := by
  constructor
  · refine Quotient.inductionOn α ?_
    intro θ hθ
    obtain ⟨u, hu⟩ := hθ
    refine ⟨thetaClosedCurrent θ u hu, thetaPotentialCurrent_full_positive θ.val u hu, ?_⟩
    exact bottChernClass_thetaClosedCurrent θ u hu
  · rintro ⟨T, hT, hclass⟩
    obtain ⟨θ, u, hu, hread, _⟩ :=
      OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
        T.val T.property.1 T.property.2 hT
    have heq : T = thetaClosedCurrent θ u hu := Subtype.ext hread
    have hα : α = RealBottChern.ofRepresentative θ := by
      rw [← hclass, heq]
      exact bottChernClass_thetaClosedCurrent θ u hu
    rw [hα, classPseudoeffectiveViaPotentials_ofRepresentative]
    exact ⟨u, hu⟩

end SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentEquivalence
