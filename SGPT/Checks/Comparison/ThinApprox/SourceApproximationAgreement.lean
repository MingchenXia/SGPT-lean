import SGPT.Checks.Comparison.ThinApprox.BJRelAmpleAppSeq
import SGPT.Checks.Comparison.SourceApproximationData

/-! The actual original approximation predicate, produced without a caller witness.
Blueprint: thin-source-approximation-agreement.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.ThinApprox.BJ.SourceApproximationAgreement
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

theorem statement_iff : SGPT.NAPotential.BJ.SourceApproximationData.Statement.{u} p ↔
    SGPT.NAPotential.ThinApprox.BJ.AppSeq.BJAppSeqStatement.{u} p := Iff.rfl

theorem original_approximation [IsIntegral X] :
    SGPT.NAPotential.BJ.SourceApproximationData.Statement.{u} p :=
  SGPT.NAPotential.ThinApprox.BJ.bjAppSeq_holds p
end SGPT.NAPotential.ThinApprox.BJ.SourceApproximationAgreement
