import SGPT.Foundations.Analysis.Pending.SingularProductCoreDiagonalZero
import SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalZero
import SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalizedChartStokes

set_option autoImplicit false

/-! # Actual core homogeneous NP equations produce the localized compact Stokes zero -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularProductCoreTestStokesZero

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  ProductComplexManifold CompactAffineCurveCharts GlobalSlotStokes GlobalNonPluripolar
  FiniteGeodesicMaximality MixedNonPluripolar RelativePreceqClasses
  SingularProductCoreDiagonalZero SingularSmoothTestLocalZero
  SingularSmoothTestLastSlot SingularSmoothTestChartStokes SingularSmoothTestLocalizedChartStokes

noncomputable section

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T]
  {θ : ClosedRealOneOneForm n M}

/-- Genuine core patches internally produced from actual Perron and affine geometry force the actual compact-host diagonal test integral to vanish. -/
theorem integral_core_perron_diagonal_eq_zero
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : ThetaPlurisubharmonic (prodForm θ κ).val W)
    {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1)
    (hcore : ∀ x y, y ∈ N → W (x, y) =
      finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x)
    (g : M × T → ℝ)
    (hgs : ∀ p ∈ tsupport g, p.2 ∈ e.val.source ∧ p.2 ∈ N) :
    (∫ p, g p ∂globalMixedMeasure (fun _ => prodForm θ κ) (fun _ => W)
      (fun _ : Fin (n + 1) => hW)) = 0 := by
  have hgc : HasCompactSupport g :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (subset_univ _)
  apply integral_eq_zero_of_local_np_zero (fun _ : Fin (n + 1) => hW) g hgc
  intro p hp
  obtain ⟨J, hJ⟩ := SlotChart.exists_mem_source (fun _ : Fin n => θ) θ p.1
  refine ⟨coreDiagonalPatch J e N κ hκzero hW, ?_, ?_⟩
  · exact (mem_source_coreDiagonalPatch J e N κ hκzero hW p).mpr ⟨hJ, hgs p hp⟩
  · exact mixedTruncationLimitMeasure_core_perron_eq_zero J e N κ hκzero hW
      hsub z0 hδ htime hcore

/-- Independently produced actual base-only reference core NP zero forces its own actual compact-host diagonal test integral to vanish. -/
theorem integral_core_reference_diagonal_eq_zero
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    (hΦ : ThetaPlurisubharmonic (prodForm θ κ).val (fun p : M × T => φ p.1))
    (g : M × T → ℝ)
    (hgs : ∀ p ∈ tsupport g, p.2 ∈ e.val.source ∧ p.2 ∈ N) :
    (∫ p, g p ∂globalMixedMeasure (fun _ => prodForm θ κ) (fun _ => fun p : M × T => φ p.1)
      (fun _ : Fin (n + 1) => hΦ)) = 0 := by
  have hgc : HasCompactSupport g :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (subset_univ _)
  apply integral_eq_zero_of_local_np_zero (fun _ : Fin (n + 1) => hΦ) g hgc
  intro p hp
  obtain ⟨J, hJ⟩ := SlotChart.exists_mem_source (fun _ : Fin n => θ) θ p.1
  refine ⟨coreDiagonalPatch J e N κ hκzero hΦ, ?_, ?_⟩
  · exact (mem_source_coreDiagonalPatch J e N κ hκzero hΦ p).mpr ⟨hJ, hgs p hp⟩
  · exact mixedTruncationLimitMeasure_core_reference_eq_zero J e N κ hκzero hφ hΦ

/-- Genuine core equations and actual compact singular Stokes internally produce the exact zero localized finite canonical NP pairing. -/
theorem sum_localized_core_chart_defect_eq_zero
    (omega : KahlerBackground (n + 1) (M × T))
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {φ u₀ u₁ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    {W : M × T → EReal} (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun p : M × T => φ p.1))
    (hWΦ : SameSingularityTypeOn W (fun p : M × T => φ p.1) univ)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1)
    (hcore : ∀ x y, y ∈ N → W (x, y) =
      finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x)
    {β : ClosedRealOneOneForm (n + 1) (M × T)} {g : M × T → ℝ}
    (hp : IsThetaPshPotential β.val fun p => (g p : EReal))
    (hq : IsThetaPshPotential β.val fun _ => 0) (hg : ChartSmooth (n := n + 1) g)
    (hgs : ∀ p ∈ tsupport g, p.2 ∈ e.val.source ∧ p.2 ∈ N)
    {m : ℕ} (χ : Fin m → M × T → ℝ)
    (J : Fin m → SlotChart (lastHybridForms (prodForm θ κ) β) (prodForm θ κ))
    (hχs : ∀ a, ChartSmooth (n := n + 1) (χ a))
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set (M × T)))
    {ζ : M × T → ℝ} (hζ : Continuous ζ) (hζ1 : EqOn ζ (fun _ => 1) (tsupport g))
    (hχsum : ∀ p, ∑ a, χ a p = ζ p) :
    (∑ k : Fin (n + 1), ∑ a : Fin m,
      ((∫ z, chartWeight (J a) (χ a) W (fun p : M × T => φ p.1) z
          ∂lastHybridChartMeasure hW hΦ hp (J a) k) -
       (∫ z, chartWeight (J a) (χ a) W (fun p : M × T => φ p.1) z
          ∂lastHybridChartMeasure hW hΦ hq (J a) k))) = 0 := by
  have hIW := integral_core_perron_diagonal_eq_zero e N κ hκzero hW.1 hsub
    z0 hδ htime hcore g hgs
  have hIΦ := integral_core_reference_diagonal_eq_zero e N κ hκzero hφ hΦ.1 g hgs
  exact (sum_localized_chart_defect_eq_smooth_test_stokes omega hW hΦ hWΦ hp hq hg χ J
    hχs hχJ hζ hζ1 hχsum).trans (by rw [hIW, hIΦ, sub_self])

variable [ConnectedSpace M]

/-- Genuine full singularity-order endpoint classes supply all Perron and base reference witnesses for the actual zero finite core pairing, without a target equation or affinity input. -/
theorem sum_localized_core_chart_defect_of_relativeFullMassPreceq_eq_zero
    (omegaBase : KahlerBackground n M) (omega : KahlerBackground (n + 1) (M × T))
    {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ) (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun p : M × T => φ p.1))
    (hWΦ : SameSingularityTypeOn W (fun p : M × T => φ p.1) univ)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1)
    (hcore : ∀ x y, y ∈ N → W (x, y) =
      finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x)
    {β : ClosedRealOneOneForm (n + 1) (M × T)} {g : M × T → ℝ}
    (hp : IsThetaPshPotential β.val fun p => (g p : EReal))
    (hq : IsThetaPshPotential β.val fun _ => 0) (hg : ChartSmooth (n := n + 1) g)
    (hgs : ∀ p ∈ tsupport g, p.2 ∈ e.val.source ∧ p.2 ∈ N)
    {m : ℕ} (χ : Fin m → M × T → ℝ)
    (J : Fin m → SlotChart (lastHybridForms (prodForm θ κ) β) (prodForm θ κ))
    (hχs : ∀ a, ChartSmooth (n := n + 1) (χ a))
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set (M × T)))
    {ζ : M × T → ℝ} (hζ : Continuous ζ) (hζ1 : EqOn ζ (fun _ => 1) (tsupport g))
    (hχsum : ∀ p, ∑ a, χ a p = ζ p) :
    (∑ k : Fin (n + 1), ∑ a : Fin m,
      ((∫ z, chartWeight (J a) (χ a) W (fun p : M × T => φ p.1) z
          ∂lastHybridChartMeasure hW hΦ hp (J a) k) -
       (∫ z, chartWeight (J a) (χ a) W (fun p : M × T => φ p.1) z
          ∂lastHybridChartMeasure hW hΦ hq (J a) k))) = 0 :=
  sum_localized_core_chart_defect_eq_zero omega e N κ hκzero hφ.plurisubharmonic.1 hW hΦ hWΦ
    (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omegaBase hu₀ hu₁)
    z0 hδ htime hcore hp hq hg hgs χ J hχs hχJ hζ hζ1 hχsum

end

end SGPT.Foundations.Analysis.Pending.SingularProductCoreTestStokesZero
