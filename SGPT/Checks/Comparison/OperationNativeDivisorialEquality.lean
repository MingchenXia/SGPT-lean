import SGPT.Checks.Comparison.OperationNativeDivisorialComparison

/-! Actual real-class native functions agree on ALL original points
from their actual original divisorial tests; all regularity internal.
Blueprint: operation-native-divisorial-equality.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory Topology SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ

/-- Genuine EXISTING numerical real-class PSH equality on ALL original
points, from SAME original augmented divisorial tests. Regularity and
native dictionaries are internally produced; classes can differ. -/
theorem nativePSH_eq_of_sourceDivisorial_eq {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
    {θ σ : NativeRealNumericalClasses.Space p} {φ ψ : BerkovichPoint p → EReal}
    (hφ : Variety.IsPSH p θ (fun y => φ ((pointEquiv p).symm y)))
    (hψ : Variety.IsPSH p σ (fun y => ψ ((pointEquiv p).symm y)))
    (heq : ∀ v ∈ sourceDivisorialSet p, φ v = ψ v) : φ = ψ := by
  have hφusc : UpperSemicontinuous φ := by
    have h := hφ.upperSemicontinuous.comp (pointHomeomorph p).continuous
    change UpperSemicontinuous (fun v => φ ((pointEquiv p).symm ((pointEquiv p) v))) at h
    simpa only [Equiv.symm_apply_apply] using h
  have hψusc : UpperSemicontinuous ψ := by
    have h := hψ.upperSemicontinuous.comp (pointHomeomorph p).continuous
    change UpperSemicontinuous (fun v => ψ ((pointEquiv p).symm ((pointEquiv p) v))) at h
    simpa only [Equiv.symm_apply_apply] using h
  have hφtop (v : BerkovichPoint p) : φ v ≠ ⊤ := by
    simpa only [Equiv.symm_apply_apply] using hφ.ne_top (pointEquiv p v)
  have hψtop (v : BerkovichPoint p) : ψ v ≠ ⊤ := by
    simpa only [Equiv.symm_apply_apply] using hψ.ne_top (pointEquiv p v)
  exact le_antisymm
    (nativePSH_le_of_sourceDivisorial_le p hφ hψusc hψtop (fun v hv => (heq v hv).le))
    (nativePSH_le_of_sourceDivisorial_le p hψ hφusc hφtop (fun v hv => (heq v hv).ge))

end SGPT.NAPotential.OperationComparison
