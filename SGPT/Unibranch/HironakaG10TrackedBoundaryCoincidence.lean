import SGPT.Unibranch.HironakaG10TrackedBoundaryCSet
import SGPT.Unibranch.HironakaG10BoundaryGermCoincidence

/-! # Source 4.5.2: tracked boundary scheme ideals agree locally -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10TrackedBoundaryCoincidence

open SGPT.Foundations.Analysis.Pending HironakaIntrinsicReducedCentreOpenPullback
open SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10LocallyAnalyticTrace
  SGPT.Unibranch.HironakaG10RelativeNonflatStrata
  SGPT.Unibranch.HironakaG10AnalyticStratumBoundary
  SGPT.Unibranch.HironakaG10SourceCSet
  SGPT.Unibranch.HironakaG10TrackedBoundaryCSet
  SGPT.Unibranch.HironakaG10BoundaryGermCoincidence

/-- If the auxiliary flattener contains the actual `C_{i+1}`, its original
  scheme boundary and each tracked scheme boundary agree locally at every
  tracked boundary point. -/
theorem tracked_boundary_scheme_agrees {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f)
    (Zaux : LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hC : Cset f B (fun p => (Z p).support) (i + 1) ⊆ Zaux.support) :
    ∀ p x, x ∈ stratumBoundary f B (Z p).V (Z p).support i →
      ∀ᶠ y in 𝓝 x,
        intrinsicCentreStalkRange X.obj.left
          (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) y ⊔ Zaux.H y =
        intrinsicCentreStalkRange X.obj.left
          (closure ((strata f B (i + 1) ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y := by
  intro p x hx
  have hxC := tracked_boundary_subset_cset f B Z i hS N hN hcover p hx
  exact eventually_scheme_boundary_eq f Zaux (Z p) (strata f B (i + 1)) (hC hxC) hx.2

end SGPT.Unibranch.HironakaG10TrackedBoundaryCoincidence
