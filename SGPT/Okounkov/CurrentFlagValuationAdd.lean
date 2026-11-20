import SGPT.Okounkov.PotentialFlagValuationAdd

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

/-- Actual original closed fully positive currents produce their actual
sum's closedness, type and full positivity internally, together with the
literal original valuation addition formula. -/
theorem exists_currentFlagValuation_add {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hTc : T.IsClosed (canonicalBasis (m + 1)))
    (hT11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T)
    (hSc : S.IsClosed (canonicalBasis (m + 1)))
    (hS11 : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hS : IsFullPositive S) :
    ∃ (hAc : (T + S).IsClosed (canonicalBasis (m + 1)))
      (hA11 : (T + S).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
      (hA : IsFullPositive (T + S)),
      currentFlagValuation F (T + S) hAc hA11 hA =
        currentFlagValuation F T hTc hT11 hT + currentFlagValuation F S hSc hS11 hS := by
  obtain ⟨θ, u, hu, hreadT, _hνT⟩ := currentFlagValuation_spec F T hTc hT11 hT
  obtain ⟨σ, v, hv, hreadS, _hνS⟩ := currentFlagValuation_spec F S hSc hS11 hS
  obtain ⟨huv, hsum⟩ := exists_thetaPotentialCurrent_add hu hv
  have hreadA : T + S = thetaPotentialCurrent (θ + σ).val (fun x => u x + v x) huv := by
    rw [hreadT, hreadS]
    exact hsum.symm
  obtain ⟨hclosed, htype, hpositive⟩ :=
    thetaPotentialCurrent_closed_type_positive (θ + σ).val (fun x => u x + v x) huv
  have hAc : (T + S).IsClosed (canonicalBasis (m + 1)) := hreadA.symm ▸ hclosed
  have hA11 : (T + S).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
    hreadA.symm ▸ htype
  have hA : IsFullPositive (T + S) := hreadA.symm ▸ hpositive
  refine ⟨hAc, hA11, hA, ?_⟩
  rw [currentFlagValuation_eq_potentialFlagValuation F (T + S) hAc hA11 hA huv hreadA,
    currentFlagValuation_eq_potentialFlagValuation F T hTc hT11 hT hu hreadT,
    currentFlagValuation_eq_potentialFlagValuation F S hSc hS11 hS hv hreadS]
  exact potentialFlagValuation_add F hu hv

end SGPT.Okounkov
