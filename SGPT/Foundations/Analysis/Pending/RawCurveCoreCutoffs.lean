import SGPT.Foundations.Analysis.Pending.AffineCurveCoreTests

set_option autoImplicit false

/-! # Genuine raw-coordinate curve cutoff properties

Actual chart readers transport compact smooth core cutoffs to the genuine
raw complex coordinate used by signed NP fibre pairings. Support and equality
to one on the transformed test support are proved from actual affine fit.
-/

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.RawCurveCoreCutoffs

open FirstPass CompactAffineCurveCharts AffineCurveCoreTests
  FiniteGeodesicStripCharts SingularModelEnergyCoreChartData

noncomputable section

/-- The actual raw signed time test is globally smooth by real affine composition, including zero scale. -/
theorem contDiff_rawTimeTest (z0 : ComplexModel 1) (δ : ℝ) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (rawTimeTest z0 δ ψ) :=
  hψ.comp ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)

private theorem raw_test_support_image (z0 : ComplexModel 1) {δ : ℝ} (hδ : δ ≠ 0)
    {ψ : ℂ → ℝ} (hψc : IsCompact (tsupport ψ)) :
    tsupport (rawTimeTest z0 δ ψ) ⊆ (fun τ => curveModelEquiv z0 + δ • τ) '' tsupport ψ := by
  have hc : IsCompact ((fun τ => curveModelEquiv z0 + δ • τ) '' tsupport ψ) :=
    hψc.image (by fun_prop)
  apply closure_minimal ?_ hc.isClosed
  intro σ hσ
  refine ⟨δ⁻¹ • (σ - curveModelEquiv z0), subset_tsupport ψ hσ, ?_⟩
  change curveModelEquiv z0 + δ • (δ⁻¹ • (σ - curveModelEquiv z0)) = σ
  rw [smul_inv_smul₀ hδ]
  abel

variable {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]

/-- Actual zero-extended curve chart reader in the genuine complex raw model. -/
def rawCurveCutoff (e : ComplexChart 1 T) (ζ : T → ℝ) : ℂ → ℝ :=
  fun σ => chartRead e ζ (curveModelEquiv.symm σ)

/-- Genuine curve smoothness, compact support and actual source/core membership produce all raw cutoff properties, with no inverse-chart ghost assumption. -/
theorem rawCurveCutoff_properties [IsComplexManifold 1 T] (e : ComplexChart 1 T)
    (N : Opens T) {ζ : T → ℝ} (hζ : ChartSmooth (n := 1) ζ) (hζc : HasCompactSupport ζ)
    (hζe : tsupport ζ ⊆ e.val.source) (hζN : tsupport ζ ⊆ (N : Set T))
    (hζ0 : ∀ y, 0 ≤ ζ y) :
    ContDiff ℝ ∞ (rawCurveCutoff e ζ) ∧ HasCompactSupport (rawCurveCutoff e ζ) ∧
      tsupport (rawCurveCutoff e ζ) ⊆ (coreTimeDomain e N : Set ℂ) ∧
      ∀ σ, 0 ≤ rawCurveCutoff e ζ σ := by
  have hr : HasCompactSupport (chartRead e ζ) := hasCompactSupport_chartRead hζc hζe
  have hc : IsCompact (curveModelEquiv '' tsupport (chartRead e ζ)) :=
    hr.image curveModelEquiv.continuous
  have hs : Function.support (rawCurveCutoff e ζ) ⊆
      curveModelEquiv '' tsupport (chartRead e ζ) := by
    intro σ hσ
    exact ⟨curveModelEquiv.symm σ, subset_tsupport (chartRead e ζ) hσ,
      curveModelEquiv.apply_symm_apply σ⟩
  have hts : tsupport (rawCurveCutoff e ζ) ⊆
      curveModelEquiv '' tsupport (chartRead e ζ) := closure_minimal hs hc.isClosed
  refine ⟨(contDiff_chartRead hζ hζc hζe).comp
      (curveModelEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff,
    hc.of_isClosed_subset (isClosed_tsupport _) hts, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨z, hz, rfl⟩ := hts hσ
    obtain ⟨y, hy, rfl⟩ := tsupport_chartRead_subset hζc hζe hz
    change curveModelEquiv.symm (curveModelEquiv (e.val y)) ∈ e.val.target ∧
      e.val.symm (curveModelEquiv.symm (curveModelEquiv (e.val y))) ∈ N
    rw [curveModelEquiv.symm_apply_apply, e.val.left_inv (hζe hy)]
    exact ⟨e.val.map_source (hζe hy), hζN hy⟩
  · intro σ
    change 0 ≤ chartRead e ζ (curveModelEquiv.symm σ)
    by_cases hσ : curveModelEquiv.symm σ ∈ e.val.target
    · rw [chartRead_of_mem hσ]
      exact hζ0 _
    · rw [chartRead_of_notMem hσ]

/-- Actual inverse-affine support transport and fitted target membership make the raw cutoff one on the entire transformed topological test support. -/
theorem rawCurveCutoff_eq_one_on_test_support (e : ComplexChart 1 T) (z0 : ComplexModel 1)
    {δ : ℝ} (hδ : δ ≠ 0) {ψ : ℂ → ℝ} (hψc : IsCompact (tsupport ψ)) (ζ : T → ℝ)
    (hfit : ∀ τ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target)
    (hζ1 : ∀ τ ∈ tsupport ψ, ζ (e.val.symm (z0 + δ • curveModelEquiv.symm τ)) = 1) :
    ∀ σ ∈ tsupport (rawTimeTest z0 δ ψ), rawCurveCutoff e ζ σ = 1 := by
  intro σ hσ
  obtain ⟨τ, hτ, rfl⟩ := raw_test_support_image z0 hδ hψc hσ
  have heq : curveModelEquiv.symm (curveModelEquiv z0 + δ • τ) =
      z0 + δ • curveModelEquiv.symm τ := by
    rw [map_add, map_real_smul curveModelEquiv.symm curveModelEquiv.symm.continuous,
      curveModelEquiv.symm_apply_apply]
  change chartRead e ζ (curveModelEquiv.symm (curveModelEquiv z0 + δ • τ)) = 1
  rw [heq, chartRead_of_mem (hfit τ hτ)]
  exact hζ1 τ hτ

end

end SGPT.Foundations.Analysis.Pending.RawCurveCoreCutoffs
