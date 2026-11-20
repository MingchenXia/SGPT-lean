import SGPT.Okounkov.PotentialFlagValuationAdd

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open scoped Manifold ContDiff NNReal ENNReal

/-- The actual original zero potential and its true recursive valuation
are produced. Genuine proved addition forces every finite entry to zero,
without a separate trace or zero-valuation certificate. -/
theorem exists_potentialFlagValuation_zero {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    ∃ hzero : IsThetaPshPotential (0 : ClosedRealOneOneForm n F.carrier).val
        (fun _ : F.carrier => (0 : EReal)),
      potentialFlagValuation F hzero = 0 := by
  let hzero : IsThetaPshPotential (0 : ClosedRealOneOneForm n F.carrier).val
      (fun _ : F.carrier => (0 : EReal)) :=
    (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff
      (0 : ClosedRealOneOneForm n F.carrier)).mpr (by intro e z hz w; simp)
  have hadd := potentialFlagValuation_add F hzero hzero
  have hI : IEquivalentOnManifold (n := n)
      (fun _ : F.carrier => (0 : EReal) + 0) (fun _ : F.carrier => (0 : EReal)) := by
    simpa only [zero_add] using IEquivalentOnManifold.refl (fun _ : F.carrier => (0 : EReal))
  have hvalue := potentialFlagValuation_eq_of_iEquivalent F
    (isThetaPshPotential_add_from_positive_sum hzero hzero) hzero hI
  have haddzero := hvalue.symm.trans hadd
  refine ⟨hzero, ?_⟩
  funext i
  have hi := congrFun haddzero i
  have hr := congrArg (fun a : ℝ≥0 => (a : ℝ)) hi
  change (potentialFlagValuation F hzero i : ℝ) =
    (potentialFlagValuation F hzero i : ℝ) + (potentialFlagValuation F hzero i : ℝ) at hr
  apply NNReal.coe_injective
  change (potentialFlagValuation F hzero i : ℝ) = 0
  linarith

end SGPT.Okounkov
