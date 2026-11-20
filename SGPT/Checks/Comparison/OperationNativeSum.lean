import SGPT.Checks.Comparison.ThinApprox.BJPair3DivFinitePresentation
import SGPT.Checks.Comparison.ThinApprox.SourcePSHComparison

/-! Genuine actual native sums in numerical REAL classes. The SAME
actual simultaneous presentation is produced internally.
Blueprint: operation-sum-native-frontier.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory Scheme.Modules SGPT.Foundations.Envelope
open SGPT.Foundations.Envelope.Variety SGPT.Foundations.Envelope.NativeRealNumericalClasses

/-- Literal sum in the EXISTING genuine native numerical real-class PSH
predicate; no nef/presentation/dictionary/output certificate. -/
theorem nativePSH_add {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    [IsProjective p] [IsIntegral X]
    {θ σ : NativeRealNumericalClasses.Space p} {φ ψ : Variety.An p → EReal}
    (hφ : Variety.IsPSH p θ φ) (hψ : Variety.IsPSH p σ ψ) :
    Variety.IsPSH p (θ+σ) (fun v => φ v + ψ v) := by
  obtain ⟨r,d,q,hq,h0,a,ha⟩ :=
    SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability.exists_simultaneous_presentation p
      (fun b : Bool => if b then θ else σ)
  let : IsClosedImmersion (q 0) := h0
  let := p.stalkAlgebra (genericPoint X)
  have hθ : θ = lineFamilyMap p (presentationFactorLine d q)
      (presentationFactorLine_isInvertible d q) (a true) := ha true
  have hσ : σ = lineFamilyMap p (presentationFactorLine d q)
      (presentationFactorLine_isInvertible d q) (a false) := ha false
  have hφm := (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation
    d q p hq (a true) φ).mp (by rwa [← hθ])
  have hψm := (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation
    d q p hq (a false) ψ).mp (by rwa [← hσ])
  have hm := hφm.add hψm
  have hout := (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation
    d q p hq (a true + a false) (fun v => φ v + ψ v)).mpr hm
  have he : lineFamilyMap p (presentationFactorLine d q)
      (presentationFactorLine_isInvertible d q) (a true + a false) = θ+σ := by
    exact ((lineFamilyMap p (presentationFactorLine d q)
      (presentationFactorLine_isInvertible d q)).map_add _ _).trans
        (congrArg₂ (fun x y => x+y) hθ.symm hσ.symm)
  rwa [he] at hout

end SGPT.NAPotential.OperationComparison
