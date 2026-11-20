import SGPT.Foundations.Analysis.Pending.GenuineSingularTopFormFunctional
import SGPT.Foundations.Analysis.Pending.LocalizedFullDdcBridge

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.GenuineSingularDdcFunctional

open FirstPass ProductTestForms StronglyPositiveForms LocalProductCurrents
  GenuineSingularTopFormFunctional LocalizedFullDdcBridge SingularTopFormLocalization
  CompactDifferentialTests CompactDdcCoordinateExpansion ScalarFullTestTranspose
  TopDegreeDensity ConstantFormProducts ChartPartition
  XiaoComplexDifferential ThetaPshChartLimitGluing XiaoChartLocalization

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A linear functional annihilating geometric zero respects the actual geometric forms. -/
theorem linearFunctional_congr_of_geometricallyEq
    (L : SmoothRealForm n M k →ₗ[ℝ] ℝ)
    (hL : ∀ Φ, Φ.GeometricallyEq 0 → L Φ = 0)
    {A B : SmoothRealForm n M k} (h : A.GeometricallyEq B) : L A = L B := by
  have hz : (A - B).GeometricallyEq 0 := by
    intro e z he
    rw [coeff_sub, h e he, coeff_zero, sub_self]
  have hp := hL (A - B) hz
  rw [map_sub] at hp
  exact sub_eq_zero.mp hp

/-- The functional and the full compact scalar-transpose formula come from the genuine potential. -/
theorem exists_genuine_singular_ddc_functional
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] (θ : SmoothRealForm (m + 1) X 2) (u : X → EReal)
    (hu : IsThetaPshPotential θ u) :
    ∃ L : SmoothRealForm (m + 1) X (2 * (m + 1)) →ₗ[ℝ] ℝ,
      (∀ Φ, Φ.GeometricallyEq 0 → L Φ = 0) ∧
      ∀ (e : ComplexChart (m + 1) X) (χ : X → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
        (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source)
        (G : SmoothRealForm (m + 1) X (2 * m)),
        (∀ z ∈ e.val.target, G.coeff e z ∈ formSpan (m + 1) m) →
        L (XiaoComplexDifferential.ddc (smulFun χ hχ G)) =
          ∫ z, scalarAdjointTest (localizedTensorTest e χ hχ G hc hs) z *
            (chartFunction u e z).toReal := by
  obtain ⟨L, hzero, hloc⟩ := exists_genuine_singular_top_form_functional
    (Nat.succ_pos m) θ u hu
  refine ⟨L, hzero, ?_⟩
  intro e χ hχ hc hs G hG
  let α := localizedTensorTest e χ hχ G hc hs
  let B := localDdcTestCLM α
  let D := XiaoComplexDifferential.ddc (smulFun χ hχ G)
  have hα : ∀ z, α z ∈ formSpan (m + 1) m := by
    intro z
    change localizedCoeff e χ G z ∈ formSpan (m + 1) m
    by_cases hz : z ∈ e.val.target
    · rw [localizedCoeff, indicator_of_mem hz]
      exact (formSpan (m + 1) m).smul_mem _ (hG z hz)
    · rw [localizedCoeff, indicator_of_notMem hz]
      exact (formSpan (m + 1) m).zero_mem
  obtain ⟨β, hβ1, -⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := chartTarget e) B.hasCompactSupport B.tsupport_subset
  let κ := chartExtend e β
  have hκ : ChartSmooth (n := m + 1) κ :=
    chartSmooth_chartExtend e β.contDiff β.hasCompactSupport β.tsupport_subset
  have hκc : IsCompact (tsupport κ) := (isClosed_tsupport κ).isCompact
  have hKc : IsCompact (e.val.symm '' tsupport (β : ComplexModel (m + 1) → ℝ)) :=
    β.hasCompactSupport.image_of_continuousOn (e.val.symm.continuousOn.mono β.tsupport_subset)
  have hκs : tsupport κ ⊆ e.val.source := by
    refine (support_chartExtend_subset e).trans ?_
    rw [hKc.isClosed.closure_eq]
    rintro _ ⟨z, hz, rfl⟩
    exact e.val.map_target (β.tsupport_subset hz)
  have hκval (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target) :
      κ (e.val.symm z) = β z := by
    change chartExtend e β (e.val.symm z) = β z
    rw [chartExtend_of_mem (e.val.map_target hz), e.val.right_inv hz]
  have hBD (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target) : D.coeff e z = B z :=
    (localDdc_localizedTensorTest_eq_global_coeff e χ hχ G hc hs hz).symm
  have hgeom : (smulFun κ hκ D).GeometricallyEq D := by
    intro f z hz
    by_cases he : f.val.symm z ∈ e.val.source
    · have hy : e.val (f.val.symm z) ∈ e.val.target := e.val.map_source he
      by_cases hb : e.val (f.val.symm z) ∈ tsupport B
      · have hv : κ (f.val.symm z) = 1 := by
          change chartExtend e β (f.val.symm z) = 1
          rw [chartExtend_of_mem he]
          exact hβ1.self_of_nhdsSet _ hb
        rw [smulFun_coeff, hv, one_smul]
      · have hd : D.coeff e (e.val (f.val.symm z)) = 0 :=
          (hBD _ hy).trans (image_eq_zero_of_notMem_tsupport hb)
        have hf : D.coeff f z = 0 := by
          ext v
          have hp := D.compatible f e z ⟨hz, he⟩ v
          change D.coeff f z v = D.coeff e (e.val (f.val.symm z))
            (fun i => chartTransitionDerivative f e z (v i)) at hp
          rw [hd] at hp
          exact hp
        rw [smulFun_coeff, hf, smul_zero]
    · have hnot : f.val.symm z ∉ tsupport χ := fun h => he (hs h)
      have hd : D.coeff f z = 0 := ddc_coeff_eq_zero_of_notMem_cutoff_support f χ hχ G hz hnot
      rw [smulFun_coeff, hd, smul_zero]
  have hdensity (z : ComplexModel (m + 1)) :
      topDensity (localizedCoeff e κ D z) = scalarAdjointTest α z := by
    rw [scalarAdjointTest_apply_eq_actual_density α hα]
    change topDensity (localizedCoeff e κ D z) = topDensity (B z)
    by_cases hz : z ∈ e.val.target
    · rw [localizedCoeff, indicator_of_mem hz, hκval z hz, hBD z hz]
      by_cases hb : z ∈ tsupport B
      · rw [hβ1.self_of_nhdsSet z hb, one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hb, smul_zero]
    · have hb : z ∉ tsupport B := fun h => hz (B.tsupport_subset h)
      rw [localizedCoeff, indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hb]
  calc
    L D = L (smulFun κ hκ D) :=
      (linearFunctional_congr_of_geometricallyEq L hzero hgeom).symm
    _ = ∫ z, topDensity (localizedCoeff e κ D z) * (chartFunction u e z).toReal :=
      hloc e κ hκ hκc hκs D
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hdensity]

end SGPT.Foundations.Analysis.Pending.GenuineSingularDdcFunctional
