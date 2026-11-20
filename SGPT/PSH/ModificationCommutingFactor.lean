import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination

set_option autoImplicit false

/-! The full chosen proof was written before this body and before the
additive public parent interface. The genuine original geometric proof
is reused with exactly its original parameters. -/

open scoped Manifold ContDiff

universe u

namespace SGPT.PSH

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

theorem isAnalyticModification_of_commuting_factor
    {π : Y → X} {q : Z → X} {ℓ : Z → Y}
    (hπ : IsAnalyticModification (n := n) π)
    (hq : IsAnalyticModification (n := n) q)
    (hℓ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hsquare : π ∘ ℓ = q) : IsAnalyticModification (n := n) ℓ :=
  SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ hq hℓ hsquare

end SGPT.PSH
