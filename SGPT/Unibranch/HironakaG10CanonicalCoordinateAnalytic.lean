import SGPT.Unibranch.HironakaG10CanonicalCoordinateStrict
import SGPT.Foundations.Analysis.Pending.HironakaG10ArbitraryBaseStrict
import SGPT.Foundations.Analysis.Pending.HironakaActualFlatCoordinateIntrinsicHS

/-! The original analytic graph in the same genuine recentered target chart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff SGPT.Foundations.Analysis.Pending.ProductComplexManifold
namespace SGPT.Unibranch.HironakaG10CanonicalCoordinateAnalytic
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  BlowupFlatCoordinates HironakaActualFlatCoordinateIntrinsicHS HironakaG10ArbitraryBaseRecenter
  HironakaG10ArbitraryBaseStrict
  SGPT.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  SGPT.Unibranch.HironakaG10CanonicalRecenteredChart
  SGPT.Unibranch.HironakaG10CanonicalCoordinateStrict
variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]
variable (a : ProductNormalCharts n r P) (j : Fin r)

/-- The actual inverse flat target chart retains the entire analytic subset. -/
theorem coordinateSubset_analytic (W : Set (P × ComplexModel r))
    (hW : IsComplexAnalyticSubset (n := n+r) W) :
    IsComplexAnalyticSubset (n := n+r) (coordinateSubset a j W) := by
  let c := productNormalChart (n := n) a.base j
  let e := actualFlatCoordinateDiffeomorph c.Φ c.hsrc
  have h := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_subtype_val.comp e.symm.contMDiff) hW
  change IsComplexAnalyticSubset (n := n+r) (coordinateSubset a j W) at h
  exact h

variable (v : ComplexModel (n+r))

private theorem targetMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞
      (arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) := by
  exact BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.add contMDiff_const) (fun z => z.property)

/-- Translation retains analyticity on the actual recentered target. -/
theorem recenteredCoordinateSubset_analytic (W : Set (P × ComplexModel r))
    (hW : IsComplexAnalyticSubset (n := n+r) W) :
    IsComplexAnalyticSubset (n := n+r)
      ((arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' (coordinateSubset a j W)) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (targetMap_holomorphic a j v) (coordinateSubset_analytic a j W hW)

end
end SGPT.Unibranch.HironakaG10CanonicalCoordinateAnalytic
