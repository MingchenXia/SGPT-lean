import SGPT.Projective.FiniteFinsuppMultilinearExtension
import SGPT.Projective.OriginalMixedEulerDifference

/-! Real multilinear extension of the independent ORIGINAL mixed Euler
integers. The definition contains no metric, Chern class or integral.
Blueprint: original-real-mixed-euler.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped BigOperators
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  (n : ℕ) (B : IntrinsicLineBundle X)

/-- The actual independent original INTEGER coefficients, extended to
finite REAL original lines in every slot. No analytic definition. -/
def originalRealMixedEuler :
    MultilinearMap ℝ (fun _ : Fin n => IntrinsicLineBundle X →₀ ℝ) ℝ :=
  finsuppMultilinearExtension (fun A =>
    (originalMixedEulerDifference f E (List.ofFn A) B : ℝ))

theorem originalRealMixedEuler_single (A : Fin n → IntrinsicLineBundle X)
    (r : Fin n → ℝ) :
    originalRealMixedEuler f E n B (fun i => Finsupp.single (A i) (r i)) =
      (∏ i, r i) * (originalMixedEulerDifference f E (List.ofFn A) B : ℝ) :=
  finsuppMultilinearExtension_single _ A r

/-- Literal finite sum of independent ORIGINAL mixed INTEGER coefficients
with actual real support weights. The entire original support is retained. -/
theorem originalRealMixedEuler_finiteSum (v : Fin n → IntrinsicLineBundle X →₀ ℝ) :
    originalRealMixedEuler f E n B v =
      ∑ A ∈ Fintype.piFinset (fun i => (v i).support),
        (∏ i, v i (A i)) * (originalMixedEulerDifference f E (List.ofFn A) B : ℝ) :=
  finsuppMultilinearExtension_apply _ v
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
