import SGPT.Foundations.Analysis.FirstPass.SubgeodesicInteriorL1

set_option autoImplicit false

/-!
# Convexity, interior continuity, and restriction of subgeodesics

The complex-affine strip restriction, vertical-line endpoint chord bound, and
interior chart-local `L¹` continuity are proved in `FirstPass`.  The full
subinterval restriction follows by transporting the two one-sided filters
through the affine time map.

Sources: `xia-sgpt:page-0150`, `xia-sgpt:page-0151`,
`xia-sgpt:page-0152`, `xia-sgpt:page-0153`.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every spatial slice of a strip subgeodesic lies below the extended-real
chord joining its two endpoint values.  The core proof restricts the
complexified PSH function to a vertical complex line, obtains a common
almost-everywhere endpoint subsequence from chart-local `L¹` convergence, and
uses upper semicontinuity to upgrade the resulting a.e. inequality. -/
theorem IsSubgeodesicFrom.le_eRealChord
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    curve t x ≤ eRealChord (u₀ x) (u₁ x) t :=
  FirstPass.IsSubgeodesicFrom.le_eRealChord h ht x

/-- A strip subgeodesic is chart-locally `L¹` continuous at every interior
time.  The core proof combines the pointwise convexity estimate with genuine
chartwise quasi-PSH integrability and dominated convergence. -/
theorem manifoldL1LocallyContinuousAt_of_isSubgeodesicFrom
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ManifoldL1LocallyTendsto (n := n) curve (𝓝 c) (curve c) :=
  FirstPass.IsSubgeodesicFrom.manifoldL1LocallyContinuousAt h hc

/-- A subgeodesic restricts to every nondegenerate compact subinterval of its
interior.  Its strip-PSH, interior-continuity, and filter-reparametrization
dependencies are all proved in the core. -/
theorem IsSubgeodesicFrom.affineReparametrized
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) :
    IsSubgeodesicFrom theta (affineReparametrizedCurve curve a b)
      (curve a) (curve b) := by
  apply h.interior.affineReparametrized_isSubgeodesicFrom ha hb hab
  · exact (manifoldL1LocallyContinuousAt_of_isSubgeodesicFrom h ha).mono_left
      nhdsWithin_le_nhds
  · exact (manifoldL1LocallyContinuousAt_of_isSubgeodesicFrom h hb).mono_left
      nhdsWithin_le_nhds

end

end SGPT.Foundations.Analysis.Pending
