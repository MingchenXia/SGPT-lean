import SGPT.Foundations.Analysis.Pending.CompactProductPshExtension
import SGPT.Foundations.Analysis.Pending.CompactAffineCurveRegions
import SGPT.Foundations.Analysis.Pending.SingularPerronUniformRelativeBound
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim

set_option autoImplicit false

/-! # Actual Perron curve, affine time chart and compact global singular extension -/

open Set
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularPerronCompactification

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses CompactAffineCurveCharts
  CompactAffineCurveRegions ProductComplexManifold

noncomputable section

/-- Genuine finite-type endpoints internally supply the Perron joint PSH and
uniform relative bounds; compact affine chart placement and the true compact
collar producer then supply the actual global potential with zero-background core. -/
theorem exists_singular_perron_compactification {n : ℕ} {M T : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [Nonempty M]
    [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
    [CompactSpace T]
    (θ : ClosedRealOneOneForm n M) (ωT : KahlerBackground 1 T) (p : T)
    {φ u₀ u₁ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu₀ : RelativeEInfinity θ φ u₀) (hu₁ : RelativeEInfinity θ φ u₁)
    {K : Set ℂ} (hK : IsCompact K) (hKS : K ⊆ complexTimeStrip) :
    ∃ (e : ComplexChart 1 T) (z0 : ComplexModel 1) (δ C : ℝ)
      (κ : ClosedRealOneOneForm 1 T) (W : M × T → EReal) (N : Set T),
      z0 ∈ e.val.target ∧ 0 < δ ∧ 0 ≤ C ∧
      (∀ ζ ∈ K, z0 + δ • curveModelEquiv.symm ζ ∈ e.val.target) ∧
      IsCompact ((fun ζ => e.val.symm (z0 + δ • curveModelEquiv.symm ζ)) '' K) ∧
      IsOpen N ∧ ((fun ζ => e.val.symm (z0 + δ • curveModelEquiv.symm ζ)) '' K) ⊆ N ∧
      N ⊆ e.val.source ∧
      (∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1) ∧
      κ.val.IsSemipositive ∧
      IsThetaPshPotential (prodForm θ κ).val (fun q : M × T => φ q.1) ∧
      IsThetaPshPotential (prodForm θ κ).val W ∧
      SameSingularityTypeOn W (fun q : M × T => φ q.1) univ ∧
      (∀ (b : ComplexChart 1 T) z, z ∈ b.val.target → b.val.symm z ∈ N →
        κ.val.coeff b z = 0) ∧
      (∀ x y, y ∈ N → W (x, y) =
        finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x) ∧
      ∀ q : M × T, φ q.1 + ((-C - 1 : ℝ) : EReal) ≤ W q ∧
        W q ≤ φ q.1 + (C : EReal) := by
  obtain ⟨w, hw, hw₀, hw₁, -⟩ := exists_common_thetaPsh_lower_of_sameSingularityType
    θ φ u₀ u₁ hφ hu₀.2 hu₁.2 0
  have hU := FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicInterior_of_common_lower
    hu₀.1 hu₁.1 hw hw₀ (by simpa using hw₁)
  obtain ⟨C, hC, hbound⟩ :=
    SingularPerronUniformRelativeBound.exists_uniform_extended_bounds_of_relativeEInfinity hφ hu₀ hu₁
  obtain ⟨e, z0, δ, V1, V2, V3, hz0, hδ, hfit, hKT, hV1, hV2, hV3,
    hKV1, hcl1, hcl2, hcl3, htime3⟩ :=
    exists_compact_affine_curve_regions p hK isOpen_complexTimeStrip hKS
  let τ : T → ℂ := fun y => curveModelEquiv (δ⁻¹ • (e.val y - z0))
  have hτ : ∀ b : ComplexChart 1 T, DifferentiableOn ℂ (τ ∘ b.val.symm)
      (b.val.target ∩ b.val.symm ⁻¹' V3) := by
    intro b
    exact (differentiableOn_affine_chart_time e b z0 δ).mono
      (fun _ hz => ⟨hz.1, hcl3 (subset_closure hz.2)⟩)
  have htime : ∀ y ∈ V3, (τ y).re ∈ Ioo (0 : ℝ) 1 :=
    fun y hy => htime3 y (subset_closure hy)
  obtain ⟨κ, W, N, hκ, hreference, hW, hsame, hN, hKN, hNV3, hzero, hcore, hWB⟩ :=
    CompactProductPshExtension.exists_compact_product_psh_extension θ ωT hφ hU hC hbound
      hKT hV1 hV2 hV3 hKV1 hcl1 hcl2 hτ htime
  exact ⟨e, z0, δ, C, κ, W, N, hz0, hδ, hC, hfit, hKT, hN, hKN,
    fun y hy => hcl3 (subset_closure (hNV3 hy)),
    fun y hy => htime y (hNV3 hy), hκ, hreference, hW, hsame, hzero, hcore, hWB⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPerronCompactification
