import SGPT.Foundations.Analysis.Pending.ProperImageAnalyticInterface

-- Literal numeric private-name component. The macro expands ONLY to this
-- exact pinned generic kernel theorem, with no theorem search or synthesis.
open Lean in
local macro "pinnedAnalyticImageIrreducibilityKernel" : term =>
  pure (mkIdent (Name.append
    (Name.num `_private.SGPT.Foundations.Analysis.Pending.ProperImageAnalyticInterface 0)
    `SGPT.Foundations.Analysis.Pending.ProperImageAnalytic.image_irreducible_of_isComplexAnalyticSubset))

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M Z : Type u} [TopologicalSpace M] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Exact generic analytic-image irreducibility mother. There is NO
compactness, properness, metric, current or potential premise. Actual image
analyticity is an honest generic hypothesis, internally supplied later by
biholomorphic transport. Exact origin/body hashes and canonical private-name
maintenance dependency: holomorphic-image-irreducibility-mother-pin.json. -/
theorem holomorphic_analytic_image_irreducible {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (W : ClosedIrreducibleAnalyticSubvariety n Z)
    (himage : IsComplexAnalyticSubset (n := n) (f '' W.carrier)) :
    IsComplexAnalyticallyIrreducible (n := n) (f '' W.carrier) :=
  pinnedAnalyticImageIrreducibilityKernel hf W himage

end SGPT.PSH
