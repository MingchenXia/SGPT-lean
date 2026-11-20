import SGPT.Checks.Comparison.OperationNativeSum
import SGPT.Checks.Comparison.BJTopology
import SGPT.Checks.Comparison.BJPair3DivNativeOriginalDivisorialReverse
import SGPT.Foundations.Envelope.Global.Comparison

/-! Actual existing numerical REAL-class native PSH is determined by
ORIGINAL source divisorial tests, all actual dictionaries internal.
Blueprint: operation-sum-native-frontier.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory Topology SGPT.Foundations.Envelope
open SGPT.Foundations.Envelope.NativeRealNumericalClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ

/-- Genuine native PSH comparison against an arbitrary actual original
USC non-top function, on all original points from original prime tests.
No rational-class membership/converse or supplied point dictionary. -/
theorem nativePSH_le_of_sourceDivisorial_le {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
    {θ : NativeRealNumericalClasses.Space p} {φ ψ : BerkovichPoint p → EReal}
    (hφ : Variety.IsPSH p θ (fun y => φ ((pointEquiv p).symm y)))
    (hψ : UpperSemicontinuous ψ) (hψtop : ∀ v, ψ v ≠ ⊤)
    (hle : ∀ v ∈ sourceDivisorialSet p, φ v ≤ ψ v) : φ ≤ ψ := by
  obtain ⟨r,d,q,hq,h0,a,ha⟩ :=
    SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability.exists_simultaneous_presentation p
      (fun _ : Fin 1 => θ)
  let : IsClosedImmersion (q 0) := h0
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hq
  let e := OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hq
  let back : P.an → BerkovichPoint p := fun v => (pointEquiv p).symm (e.symm v)
  have hback : Continuous back :=
    (pointHomeomorph p).symm.continuous.comp e.symm.continuous
  have hmodel : P.IsPSH (a 0) (φ ∘ back) := by
    apply (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation
      d q p hq (a 0) (fun y => φ ((pointEquiv p).symm y))).mp
    rw [← ha 0]
    exact hφ
  have hdiv (v : P.an) (hv : P.IsDivisorial v) :
      (φ ∘ back) v ≤ (ψ ∘ back) v :=
    hle (back v)
      (SGPT.NAPotential.BJ.Pair3Div.nativeDivisorial_original_mem_source p q hq v hv)
  have hout := hmodel.le_of_forall_isDivisorial_le
    (hψ.comp hback) (fun v => hψtop (back v)) hdiv
  intro v
  have h := hout (e (pointEquiv p v))
  simpa only [back,Function.comp_apply,Homeomorph.symm_apply_apply,
    Equiv.symm_apply_apply] using h

end SGPT.NAPotential.OperationComparison
