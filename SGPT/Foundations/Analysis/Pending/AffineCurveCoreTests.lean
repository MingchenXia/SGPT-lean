import SGPT.Foundations.Analysis.Pending.AffineCurveSmoothTests
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData
import SGPT.Foundations.Analysis.Pending.CompactCollarCutoff

set_option autoImplicit false

/-! # Actual affine product tests and genuine core cutoffs

Geometric producers for the zero-background core route supporting Xia SGPT
page 171. Genuine fitted support gives compact raw test support in the core;
the true product atlas reads the actual curve test as the raw time lift.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.AffineCurveCoreTests

open scoped ProductComplexManifold

open FirstPass CompactAffineCurveCharts CompactAffineCurveRegions AffineCurveSmoothTests
  ProductComplexManifold FiniteGeodesicMaximality BedfordTaylorTimeSlot
  SingularModelEnergyCoreChartData CompactCollarCutoff

noncomputable section

/-- The actual original signed time test in raw complex curve coordinates. -/
def rawTimeTest (z0 : ComplexModel 1) (δ : ℝ) (ψ : ℂ → ℝ) : ℂ → ℝ :=
  fun σ => ψ (δ⁻¹ • (σ - curveModelEquiv z0))

variable {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
  [IsComplexManifold 1 T]

omit [IsComplexManifold 1 T] in
/-- The genuine nonzero affine inverses and actual target/core fit produce compact raw test support in the actual core time domain. -/
theorem rawTimeTest_compact_support_core (e : ComplexChart 1 T) (z0 : ComplexModel 1)
    {δ : ℝ} (hδ : δ ≠ 0) {ψ : ℂ → ℝ} (hψc : IsCompact (tsupport ψ))
    (N : Opens T)
    (hfit : ∀ τ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target)
    (hcore : ∀ τ ∈ tsupport ψ, e.val.symm (z0 + δ • curveModelEquiv.symm τ) ∈ N) :
    HasCompactSupport (rawTimeTest z0 δ ψ) ∧
      tsupport (rawTimeTest z0 δ ψ) ⊆ (coreTimeDomain e N : Set ℂ) := by
  let H : ℂ → ℂ := fun τ => curveModelEquiv z0 + δ • τ
  have hH : Continuous H := by fun_prop
  have hHc : IsCompact (H '' tsupport ψ) := hψc.image hH
  have hHA (σ : ℂ) : H (δ⁻¹ • (σ - curveModelEquiv z0)) = σ := by
    dsimp only [H]
    rw [smul_inv_smul₀ hδ]
    abel
  have hs : Function.support (rawTimeTest z0 δ ψ) ⊆ H '' tsupport ψ := by
    intro σ hσ
    exact ⟨δ⁻¹ • (σ - curveModelEquiv z0), subset_tsupport ψ hσ, hHA σ⟩
  have hts : tsupport (rawTimeTest z0 δ ψ) ⊆ H '' tsupport ψ :=
    closure_minimal hs hHc.isClosed
  refine ⟨hHc.of_isClosed_subset (isClosed_tsupport _) hts, ?_⟩
  intro σ hσ
  obtain ⟨τ, hτ, rfl⟩ := hts hσ
  have heq : curveModelEquiv.symm (H τ) = z0 + δ • curveModelEquiv.symm τ := by
    dsimp only [H]
    rw [map_add, map_real_smul curveModelEquiv.symm curveModelEquiv.symm.continuous,
      ContinuousLinearEquiv.symm_apply_apply]
  change curveModelEquiv.symm (H τ) ∈ e.val.target ∧ e.val.symm (curveModelEquiv.symm (H τ)) ∈ N
  rw [heq]
  exact ⟨hfit τ hτ, hcore τ hτ⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The true holomorphic product projection transports actual affine curve-test smoothness to every actual product chart. -/
theorem chartSmooth_product_affineCurveTest (e : ComplexChart 1 T) (z0 : ComplexModel 1)
    {δ : ℝ} (hδ : δ ≠ 0) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : IsCompact (tsupport ψ))
    (hfit : ∀ τ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target) :
    ChartSmooth (n := n + 1) (fun q : M × T => affineCurveTest e z0 δ ψ q.2) :=
  ProductTestForms.chartSmooth_comp contMDiff_snd
    (chartSmooth_affineCurveTest e z0 hδ hψ hψc hfit)

omit [IsComplexManifold 1 T] [IsComplexManifold n M] in
/-- Actual target membership and the genuine inverse product chart identify the curve test with the actual raw time lift, even at zero scale. -/
theorem product_affineCurveTest_eq_timeLift (a : ComplexChart n M) (e : ComplexChart 1 T)
    (z0 : ComplexModel 1) (δ : ℝ) (ψ : ℂ → ℝ) (q : ComplexModel (n + 1))
    (hq : ((prodModelEquiv n 1).symm q).2 ∈ e.val.target) :
    affineCurveTest e z0 δ ψ ((productComplexChart a e).val.symm q).2 =
      timeLift n (rawTimeTest z0 δ ψ) q := by
  rw [productComplexChart, prodChart_symm_apply]
  change affineCurveTest e z0 δ ψ (e.val.symm (((prodModelEquiv n 1).symm q).2)) = _
  unfold affineCurveTest
  rw [ChartPartition.chartExtend_of_mem (e.val.map_target hq), e.val.right_inv hq]
  rw [map_real_smul curveModelEquiv curveModelEquiv.continuous, map_sub]
  change ψ (δ⁻¹ • (curveModelEquiv (((prodModelEquiv n 1).symm q).2) - curveModelEquiv z0)) =
    ψ (δ⁻¹ • (q (Fin.last n) - curveModelEquiv z0))
  rfl

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A true compact curve support in an actual open core has a chart-smooth nonnegative compact cutoff equal to one on a genuine open neighborhood. -/
theorem exists_chartSmooth_core_cutoff [CompactSpace T] {K : Set T} (hK : IsCompact K)
    (N : Opens T) (hKN : K ⊆ N) :
    ∃ ζ : T → ℝ, ChartSmooth (n := 1) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ (N : Set T) ∧
      (∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1) ∧
      ∃ O : Set T, IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ζ y = 1 := by
  obtain ⟨V, hV, hKV, hcl⟩ := hK.exists_isOpen_closure_subset (N.isOpen.mem_nhdsSet.mpr hKN)
  obtain ⟨ρ, hρ, hlo, hup, ⟨O, hO, hKO, hone⟩, hoff⟩ :=
    exists_chartSmooth_collar (n := 1) hK hV hKV
  have hs : Function.support (fun y => 1 + ρ y) ⊆ V := by
    intro y hy
    by_contra hyV
    have hz : 1 + ρ y = 0 := by rw [hoff y hyV]; ring
    exact hy hz
  refine ⟨fun y => 1 + ρ y, (fun e => contDiffOn_const.add (hρ e)),
    isClosed_tsupport _ |>.isCompact, (closure_mono hs).trans hcl, ?_, O, hO, hKO, ?_⟩
  · intro y
    constructor <;> linarith [hlo y, hup y]
  · intro y hy
    change 1 + ρ y = 1
    rw [hone y hy]
    ring

end

end SGPT.Foundations.Analysis.Pending.AffineCurveCoreTests
