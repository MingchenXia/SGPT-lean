import SGPT.Unibranch.HironakaG10CanonicalArbitraryBaseChart
import SGPT.Unibranch.HironakaG10CanonicalCoordinateStrict
import SGPT.Foundations.Analysis.Pending.HironakaG10ArbitraryBaseStrict

/-! The original strict carrier in an arbitrary recentered canonical product chart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff SGPT.Foundations.Analysis.Pending.ProductComplexManifold
namespace SGPT.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaG10RecenteredMonomialDomain HironakaG10ArbitraryBaseRecenter
  HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  SGPT.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  SGPT.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  SGPT.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  SGPT.Unibranch.HironakaG10CanonicalRecenteredChart
  SGPT.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  SGPT.Unibranch.HironakaG10CanonicalCoordinateStrict
variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]
variable (a : ProductNormalCharts n r P) (j : Fin r)
variable (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)

/-- No supplied comparison: the full source strict subset is the original canonical carrier. -/
theorem original_strict_carrier_conjugacy (W : Set (P × ComplexModel r)) :
    realOpenStrictTransform n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      ((arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' (coordinateSubset a j W)) =
      (arbitraryCanonicalRecenteredChart a j v hvj) ⁻¹' (strictChartCarrier a W j) := by
  rw [arbitraryBaseStrictTransform n r j v hvj (canonicalTargetOpen a j) (coordinateSubset a j W),
    strict_carrier_coordinates a j W]
  ext z
  simp only [Set.mem_preimage]
  have h := (productChartDiffeomorph a j).apply_symm_apply
    (arbitraryBaseSourceDiffeomorph n r j v hvj (canonicalTargetOpen a j) z)
  change (productChartDiffeomorph a j) (arbitraryCanonicalRecenteredChart a j v hvj z) = _ at h
  rw [h]
  rfl

end
end SGPT.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
