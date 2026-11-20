import SGPT.Checks.Comparison.OperationFSSystemScaling
import SGPT.Checks.Comparison.ThinApprox.SourcePSHComparison

/-! Genuine original numerical REAL-class PSH scaling, without nef.
All actual presentation geometry is produced internally.
Blueprint: operation-real-class-scaling.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory Scheme.Modules SGPT.Foundations.Envelope
open SGPT.Foundations.Envelope.Variety SGPT.Foundations.Envelope.NativeRealNumericalClasses

/-- EVERY existing actual numerical real-class PSH function on EVERY
original integral projective variety scales by EVERY positive real.
No nef, caller presentation, dictionary or closure certificate is supplied. -/
theorem nativePSH_positiveScale {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] [IsIntegral X]
    {θ : NativeRealNumericalClasses.Space p} {φ : Variety.An p → EReal}
    (hφ : Variety.IsPSH p θ φ) {c : ℝ} (hc : 0 < c) :
    Variety.IsPSH p (c • θ) (fun v => (c : EReal) * φ v) := by
  obtain ⟨r,d,q,hq,h0,θm,hθ⟩ := Variety.exists_presentation p θ
  let : IsClosedImmersion (q 0) := h0
  let := p.stalkAlgebra (genericPoint X)
  have hφm := (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation
    d q p hq θm φ).mp (by rwa [← hθ])
  have hm := fsSystemC_positiveScale
    (FiniteProjectiveNativeFieldModels.model q p hq).fsSystem hφm hc
  have hout := (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation
    d q p hq (c • θm) (fun v => (c : EReal) * φ v)).mpr hm
  have he : lineFamilyMap p (presentationFactorLine d q)
      (presentationFactorLine_isInvertible d q) (c • θm) = c • θ := by
    exact ((lineFamilyMap p (presentationFactorLine d q)
      (presentationFactorLine_isInvertible d q)).map_smul c θm).trans
        (congrArg (fun η => c • η) hθ.symm)
  rwa [he] at hout

end SGPT.NAPotential.OperationComparison
