import SGPT.Foundations.Analysis.Pending.SingularTopFormLocalization
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.GenuineSingularTopFormFunctional

open FirstPass ProductTestForms TopDegreeDensity ThetaPshChartLimitGluing
  XiaoChartLocalization SingularTopFormLocalization ChartPartition

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original singular potential integrates every localized global top form linearly. -/
def localizedTopFormPairing (hn : 0 < n) (θ : SmoothRealForm n M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) : SmoothRealForm n M (2 * n) →ₗ[ℝ] ℝ where
  toFun Φ := ∫ z, topDensity (localizedCoeff e χ Φ z) * (chartFunction u e z).toReal
  map_add' Φ Ψ := by
    have hΦ := genuine_theta_potential_localized_top_form_integrable hn θ u hu e χ hχ Φ hc hs
    have hΨ := genuine_theta_potential_localized_top_form_integrable hn θ u hu e χ hχ Ψ hc hs
    calc
      _ = ∫ z, topDensity (localizedCoeff e χ Φ z) * (chartFunction u e z).toReal +
          topDensity (localizedCoeff e χ Ψ z) * (chartFunction u e z).toReal := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ e.val.target
        · simp only [localizedCoeff, indicator_of_mem hz, coeff_add, smul_add,
            topDensity_add, add_mul]
        · simp only [localizedCoeff, indicator_of_notMem hz, topDensity_zero, zero_mul,
            add_zero]
      _ = _ := integral_add hΦ hΨ
  map_smul' c Φ := by
    calc
      _ = ∫ z, c * (topDensity (localizedCoeff e χ Φ z) *
          (chartFunction u e z).toReal) := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ e.val.target
        · simp only [localizedCoeff, indicator_of_mem hz, coeff_smul, smul_smul,
            topDensity_smul]
          ring
        · simp only [localizedCoeff, indicator_of_notMem hz, topDensity_zero, zero_mul,
            mul_zero]
      _ = _ := integral_const_mul c _

/-- Geometric zero is sufficient; no equality of arbitrary off-target extensions is needed. -/
theorem localizedTopFormPairing_geometric_zero
    (hn : 0 < n) (θ : SmoothRealForm n M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) (Φ : SmoothRealForm n M (2 * n))
    (hΦ : Φ.GeometricallyEq 0) : localizedTopFormPairing hn θ u hu e χ hχ hc hs Φ = 0 := by
  change (∫ z, topDensity (localizedCoeff e χ Φ z) * (chartFunction u e z).toReal) = 0
  have hz : ∀ z, localizedCoeff e χ Φ z = 0 := by
    intro z
    by_cases ht : z ∈ e.val.target
    · rw [localizedCoeff, indicator_of_mem ht, hΦ e ht, coeff_zero, smul_zero]
    · exact indicator_of_notMem ht _
  simp only [hz, topDensity_zero, zero_mul, integral_zero]

/-- A finite chart partition internally produces a functional on the whole top-form space. -/
theorem exists_genuine_singular_top_form_functional [CompactSpace M]
    (hn : 0 < n) (θ : SmoothRealForm n M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) :
    ∃ L : SmoothRealForm n M (2 * n) →ₗ[ℝ] ℝ,
      (∀ Φ, Φ.GeometricallyEq 0 → L Φ = 0) ∧
      ∀ (e : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
        (_ : IsCompact (tsupport χ)) (_ : tsupport χ ⊆ e.val.source)
        (Φ : SmoothRealForm n M (2 * n)),
        L (smulFun χ hχ Φ) = ∫ z, topDensity (localizedCoeff e χ Φ z) *
          (chartFunction u e z).toReal := by
  classical
  let S : ComplexChart n M → Opens M := fun e => ⟨e.val.source, e.val.open_source⟩
  have hcover : ∀ x : M, ∃ e, x ∈ S e := fun x =>
    ⟨complexChartAt (n := n) x, mem_complexChartAt_source x⟩
  obtain ⟨m, ψ, idx, hψ, -, hsψ, hcψ, h1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  let L : SmoothRealForm n M (2 * n) →ₗ[ℝ] ℝ :=
    ∑ i : Fin m, localizedTopFormPairing hn θ u hu (idx i) (ψ i) (hψ i) (hcψ i) (hsψ i)
  refine ⟨L, ?_, ?_⟩
  · intro Φ hΦ
    change (∑ i : Fin m, localizedTopFormPairing hn θ u hu (idx i) (ψ i)
      (hψ i) (hcψ i) (hsψ i)) Φ = 0
    simp only [LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ =>
      localizedTopFormPairing_geometric_zero hn θ u hu (idx i) (ψ i)
        (hψ i) (hcψ i) (hsψ i) Φ hΦ
  · intro e χ hχ hc hs Φ
    have hm (i : Fin m) : ChartSmooth (n := n) (fun x => ψ i x * χ x) :=
      fun f => (hψ i f).mul (hχ f)
    have hcp (i : Fin m) : IsCompact (tsupport (fun x => ψ i x * χ x)) :=
      (hcψ i).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
    have hsi (i : Fin m) : tsupport (fun x => ψ i x * χ x) ⊆ (idx i).val.source :=
      tsupport_mul_subset_left.trans (hsψ i)
    have hse (i : Fin m) : tsupport (fun x => ψ i x * χ x) ⊆ e.val.source :=
      tsupport_mul_subset_right.trans hs
    have heq (i : Fin m) :
        localizedTopFormPairing hn θ u hu (idx i) (ψ i) (hψ i) (hcψ i) (hsψ i)
          (smulFun χ hχ Φ) =
        ∫ z, topDensity (localizedCoeff e (fun x => ψ i x * χ x) Φ z) *
          (chartFunction u e z).toReal := by
      change (∫ z, topDensity (localizedCoeff (idx i) (ψ i) (smulFun χ hχ Φ) z) *
        (chartFunction u (idx i) z).toReal) = _
      calc
        _ = ∫ z, topDensity (localizedCoeff (idx i) (fun x => ψ i x * χ x) Φ z) *
            (chartFunction u (idx i) z).toReal := by
          apply integral_congr_ae
          filter_upwards [] with z
          by_cases hz : z ∈ (idx i).val.target
          · simp only [localizedCoeff, indicator_of_mem hz, smulFun_coeff, smul_smul]
          · simp only [localizedCoeff, indicator_of_notMem hz]
        _ = _ := (genuine_theta_potential_localized_top_form_chart_independent
          hn θ u hu (idx i) e (fun x => ψ i x * χ x) (hm i) Φ (hcp i) (hsi i) (hse i)).2.2
    have hi (i : Fin m) : Integrable (fun z =>
        topDensity (localizedCoeff e (fun x => ψ i x * χ x) Φ z) *
          (chartFunction u e z).toReal) volume :=
      genuine_theta_potential_localized_top_form_integrable
        hn θ u hu e (fun x => ψ i x * χ x) (hm i) Φ (hcp i) (hse i)
    change (∑ i : Fin m, localizedTopFormPairing hn θ u hu (idx i) (ψ i)
      (hψ i) (hcψ i) (hsψ i)) (smulFun χ hχ Φ) = _
    simp only [LinearMap.sum_apply, heq]
    calc
      _ = ∫ z, ∑ i : Fin m, topDensity (localizedCoeff e (fun x => ψ i x * χ x) Φ z) *
          (chartFunction u e z).toReal :=
        (integral_finsetSum Finset.univ (fun i _ => hi i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ e.val.target
        · simp only [localizedCoeff, indicator_of_mem hz, topDensity_smul, mul_assoc]
          rw [← Finset.sum_mul, h1]
          exact one_mul _
        · simp [localizedCoeff, indicator_of_notMem hz]

end SGPT.Foundations.Analysis.Pending.GenuineSingularTopFormFunctional
