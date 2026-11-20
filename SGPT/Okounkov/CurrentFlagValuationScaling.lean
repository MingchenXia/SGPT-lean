import SGPT.Okounkov.PotentialFlagValuationScaling
import SGPT.Okounkov.CurrentFlagValuationAdd

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
open GlobalPositiveCurrentACRestriction NaturalThetaPshClosedCurrent

/-- Every original nonnegative scalar produces actual whole-current
closedness, type and full positivity, and the literal valuation formula.
The zero current is included by the genuine zero potential producer. -/
theorem exists_currentFlagValuation_nonneg_smul {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hTc : T.IsClosed (canonicalBasis (m + 1)))
    (hT11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) (c : ℝ≥0) :
    ∃ (hCc : ((c : ℝ) • T).IsClosed (canonicalBasis (m + 1)))
      (hC11 : ((c : ℝ) • T).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
      (hC : IsFullPositive ((c : ℝ) • T)),
      currentFlagValuation F ((c : ℝ) • T) hCc hC11 hC =
        c • currentFlagValuation F T hTc hT11 hT := by
  obtain ⟨θ, u, hu, hreadT, _hνT⟩ := currentFlagValuation_spec F T hTc hT11 hT
  obtain ⟨hcu, hscale⟩ := exists_thetaPotentialCurrent_nonneg_smul hu c.coe_nonneg
  have hreadC : (c : ℝ) • T =
      thetaPotentialCurrent ((c : ℝ) • θ).val
        (fun x => ((c : ℝ) : EReal) * u x) hcu := by
    rw [hreadT]
    exact hscale.symm
  obtain ⟨hclosed, htype, hpositive⟩ :=
    thetaPotentialCurrent_closed_type_positive ((c : ℝ) • θ).val
      (fun x => ((c : ℝ) : EReal) * u x) hcu
  have hCc : ((c : ℝ) • T).IsClosed (canonicalBasis (m + 1)) := hreadC.symm ▸ hclosed
  have hC11 : ((c : ℝ) • T).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
    hreadC.symm ▸ htype
  have hC : IsFullPositive ((c : ℝ) • T) := hreadC.symm ▸ hpositive
  refine ⟨hCc, hC11, hC, ?_⟩
  rw [currentFlagValuation_eq_potentialFlagValuation F ((c : ℝ) • T) hCc hC11 hC hcu hreadC,
    currentFlagValuation_eq_potentialFlagValuation F T hTc hT11 hT hu hreadT]
  obtain ⟨_hcu, hval⟩ := exists_potentialFlagValuation_nonneg_smul F hu c
  exact hval

/-- The genuine source dimension-zero assignment is additive for any
actual additive input type; no positive-degree current is formed. -/
theorem zeroDimensionCurrentFlagValuation_add {C : Type u} [Add C] (T S : C) :
    zeroDimensionCurrentFlagValuation (T + S) =
      zeroDimensionCurrentFlagValuation T + zeroDimensionCurrentFlagValuation S :=
  (zeroDimensionCurrentFlagValuation_unique (T + S) _).symm

/-- Every original nonnegative scalar also obeys the source formula in
dimension zero, by the already-proved unique empty-index assignment. -/
theorem zeroDimensionCurrentFlagValuation_nonneg_smul {C : Type u} [SMul ℝ C]
    (T : C) (c : ℝ≥0) :
    zeroDimensionCurrentFlagValuation ((c : ℝ) • T) =
      c • zeroDimensionCurrentFlagValuation T :=
  (zeroDimensionCurrentFlagValuation_unique ((c : ℝ) • T) _).symm

end SGPT.Okounkov
