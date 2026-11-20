import SGPT.Foundations.Analysis.Pending.HironakaG8LocalCoeff
import SGPT.Foundations.Analysis.Pending.HironakaG8ClassStepCut
import SGPT.Foundations.Analysis.Pending.HironakaG11PresM8EmptyCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SGPT.Foundations.Analysis.Pending.HironakaG8CoefficientBoundaryLocal

open Set TopologicalSpace
open FirstPass FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.BlowupTowers
open SGPT.Foundations.Analysis.Pending.MarkedIdeals
open SGPT.Foundations.Analysis.Pending.ResolutionInvariantSpec (IsInvDomain)
open SGPT.Foundations.Analysis.Pending.HomogenizedIdealAlong (coeffMarkedAlong)
open SGPT.Foundations.Analysis.Pending.HironakaG8LocalHistory
open SGPT.Foundations.Analysis.Pending.HironakaG8LocalCoeff
open SGPT.Foundations.Analysis.Pending.HironakaG8ClassStepCut
open SGPT.Foundations.Analysis.Pending.HironakaG11PresM8EmptyCore

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

theorem coefficient_local_any_boundary {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) :
    LocWPEquiv P (coeffMarkedAlong P) := by
  let P₀ : MarkedIdeal n X := { P with E := [] }
  have hP₀ : IsInvDomain r P₀ := isInvDomain_withE_of_sublist hP (List.nil_sublist _)
  have h₀ : LocWPEquiv P₀ (coeffMarkedAlong P₀) :=
    locWPEquiv_coeffMarkedAlong_of_nil P₀ hP₀ rfl
  have h := locEquiv_addE (κ := Kinds.wp) rfl h₀ P.E
  simpa [P₀, coeffMarkedAlong, HomogenizedIdealAlong.derivMarkedAlong,
    CoefficientIdeal.msum] using h

end
end SGPT.Foundations.Analysis.Pending.HironakaG8CoefficientBoundaryLocal
