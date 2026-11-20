import SGPT.Foundations.Analysis.Pending.NaturalHermitianChartGraphEnergy
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Genuine native chart localization on the actual closed graph-energy space -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianCompleteChartLocalization

open FirstPass FirstPass.MongeAmpere NaturalHermitianSmoothFormMetric
  NaturalHermitianFirstOrderCoefficients NaturalHermitianHodgePrincipalSymbol
  NaturalHermitianMetricCoefficients NaturalHermitianCodifferential
  NaturalHermitianLocalGarding NaturalHermitianWeightedLocalGarding
  NaturalHermitianCutoffDifferentialEnergy NaturalChartCutoffCoefficientTests
  NaturalHermitianFrozenCoefficientSobolev NaturalVectorCoefficientSobolev
  NaturalScalarSobolevBasisGradient NaturalHermitianOrthonormalFormBasis
  NaturalHermitianChartSobolevLocalization NaturalHermitianVolumeMeasure NaturalHermitianFormL2
  NaturalHermitianGraphEnergy FirstPass.PositiveClasses NaturalHermitianHodgeStar
  NaturalHermitianChartGraphEnergy NaturalCoefficientSobolevRellich
  NaturalOriginalGradedExteriorProduct ProductTestForms

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formBilinearNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formBilinearNormedSpace (q : ℕ) :
    NormedSpace ℝ (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The literal original whole native cutoff, with its existing test-space operations. -/
def chartCutoffLinear (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) :
    SmoothRealForm n M q →ₗ[ℝ] 𝓓_{K}(ComplexModel n, FormCoefficients n q) where
  toFun := chartCutoffTest e K hK φ
  map_add' α β := by
    apply ContDiffMapSupportedIn.ext
    intro x
    change φ x • (α + β).coeff e x = φ x • α.coeff e x + φ x • β.coeff e x
    rw [coeff_add, smul_add]
  map_smul' c α := by
    apply ContDiffMapSupportedIn.ext
    intro x
    change φ x • (c • α).coeff e x = c • (φ x • α.coeff e x)
    simp only [coeff_smul, smul_smul, mul_comm]

theorem chartCutoffLinear_apply (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q) :
    chartCutoffLinear e q K hK φ α = chartCutoffTest e K hK φ α := rfl

/-- The literal earlier frozen-form native coefficient jet on original representatives. -/
def nativeChartJetLinear (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) :
    SmoothRealForm n M q →ₗ[ℝ] CoefficientJetHilbert volume K b (FormIndex n q) :=
  (fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
    (w.isKahler.1 e z hz).2 b q volume K).comp (chartCutoffLinear e q K hK φ)

theorem nativeChartJetLinear_apply (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q) :
    nativeChartJetLinear w e q z hz b K hK φ α =
      fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
        (w.isKahler.1 e z hz).2 b q volume K (chartCutoffTest e K hK φ α) := rfl

theorem nativeChartJetLinear_eq_of_geometricallyEq (w : KahlerBackground n M)
    (e : ComplexChart n M) (q : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α β : SmoothRealForm n M q) (h : α.GeometricallyEq β) :
    nativeChartJetLinear w e q z hz b K hK φ α = nativeChartJetLinear w e q z hz b K hK φ β := by
  simp only [nativeChartJetLinear_apply, chartCutoffTest_eq_of_geometricallyEq e K hK φ α β h]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

local instance graphNormedAddCommGroup (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance graphInnerProductSpace (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

local instance coefficientJetCompleteSpace (q : ℕ) (K : Compacts (ComplexModel n))
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) :
    CompleteSpace (CoefficientJetHilbert (volume : Measure (ComplexModel n)) K b (FormIndex n q)) := by
  let : CompleteSpace (NaturalScalarSobolevJet.SobolevFirstJet volume K b) :=
    NaturalScalarSobolevJet.sobolevFirstJet_complete volume K b
  exact PiLp.completeSpace 2
    (fun _ : FormIndex n q => NaturalScalarSobolevJet.SobolevFirstJet volume K b)

/-- Actual bounded-range extension along the existing dense original smooth graph, preserving all old smooth norms. -/
def completeChartJetCLM (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) :
    GraphEnergy w q →L[ℝ] CoefficientJetHilbert volume K b (FormIndex n q) :=
  (nativeChartJetLinear w e q z hz b K hK φ).extendOfNorm (smoothEnergyLinear w q)

/-- The literal same compact native value projection after the actual completed graph localization. -/
def completeChartValueCLM (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) :
    GraphEnergy w q →L[ℝ] CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q) :=
  (fixedFormValueCLM b q volume K).comp (completeChartJetCLM w e q z hz b K hK φ)

private theorem nativeChartJetLinear_norm_le_of_sq_bound
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ α : SmoothRealForm n M q,
      ‖fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
        (w.isKahler.1 e z hz).2 b q volume K (chartCutoffTest e K hK φ α)‖ ^ 2 ≤
          C * ‖smoothGraph w α‖ ^ 2) (α : SmoothRealForm n M q) :
    ‖nativeChartJetLinear w e q z hz b K hK φ α‖ ≤ Real.sqrt C * ‖smoothEnergyLinear w q α‖ := by
  have hgraph : ‖smoothEnergyLinear w q α‖ = ‖smoothGraph w α‖ := rfl
  rw [hgraph, nativeChartJetLinear_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hC]
  exact hbound α

private theorem completeChartJetCLM_readback_of_bound
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (L : ℝ)
    (hbound : ∀ α : SmoothRealForm n M q,
      ‖nativeChartJetLinear w e q z hz b K hK φ α‖ ≤ L * ‖smoothEnergyLinear w q α‖)
    (α : SmoothRealForm n M q) :
    completeChartJetCLM w e q z hz b K hK φ (smoothEnergyLinear w q α) =
      nativeChartJetLinear w e q z hz b K hK φ α :=
  LinearMap.extendOfNorm_eq
    (f := nativeChartJetLinear w e q z hz b K hK φ) (e := smoothEnergyLinear w q)
    (smoothEnergy_denseRange w q) ⟨L, hbound⟩ α

private theorem completeChartJetCLM_norm_le_of_bound
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (L : ℝ)
    (hbound : ∀ α : SmoothRealForm n M q,
      ‖nativeChartJetLinear w e q z hz b K hK φ α‖ ≤ L * ‖smoothEnergyLinear w q α‖)
    (u : GraphEnergy w q) :
    ‖completeChartJetCLM w e q z hz b K hK φ u‖ ≤ L * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    (f := nativeChartJetLinear w e q z hz b K hK φ) (e := smoothEnergyLinear w q)
    (smoothEnergy_denseRange w q) L hbound u

private theorem completeChartJetCLM_unique_of_bound
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (L : ℝ)
    (hbound : ∀ α : SmoothRealForm n M q,
      ‖nativeChartJetLinear w e q z hz b K hK φ α‖ ≤ L * ‖smoothEnergyLinear w q α‖)
    (G : GraphEnergy w q →L[ℝ] CoefficientJetHilbert volume K b (FormIndex n q))
    (hG : ∀ α : SmoothRealForm n M q,
      G (smoothEnergyLinear w q α) = nativeChartJetLinear w e q z hz b K hK φ α) :
    G = completeChartJetCLM w e q z hz b K hK φ := by
  have heq : G.toLinearMap.comp (smoothEnergyLinear w q) = nativeChartJetLinear w e q z hz b K hK φ := by
    apply LinearMap.ext
    intro α
    exact hG α
  exact (LinearMap.extendOfNorm_unique
    (f := nativeChartJetLinear w e q z hz b K hK φ) (e := smoothEnergyLinear w q)
    (smoothEnergy_denseRange w q) L hbound G heq).symm

private theorem chart_jet_localization_of_squared_bounds
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (r : ℝ)
    (hball : Metric.ball z r ⊆ e.val.target)
    (hjet : ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
      (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ C > 0, ∀ α : SmoothRealForm n M q,
      ‖fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
        (w.isKahler.1 e z hz).2 b q volume K (chartCutoffTest e K (hK.trans hball) φ α)‖ ^ 2 ≤
          C * ‖smoothGraph w α‖ ^ 2) :
    ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
      (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ L > 0,
      (∀ α : SmoothRealForm n M q,
        completeChartJetCLM w e q z hz b K (hK.trans hball) φ (smoothEnergyLinear w q α) =
          nativeChartJetLinear w e q z hz b K (hK.trans hball) φ α) ∧
      (∀ u : GraphEnergy w q,
        ‖completeChartJetCLM w e q z hz b K (hK.trans hball) φ u‖ ≤ L * ‖u‖) ∧
      (∀ G : GraphEnergy w q →L[ℝ] CoefficientJetHilbert volume K b (FormIndex n q),
        (∀ α : SmoothRealForm n M q,
          G (smoothEnergyLinear w q α) = nativeChartJetLinear w e q z hz b K (hK.trans hball) φ α) →
          G = completeChartJetCLM w e q z hz b K (hK.trans hball) φ) := by
  intro K hK φ
  obtain ⟨C, hC, hbound⟩ := hjet K hK φ
  have hnorm : ∀ α : SmoothRealForm n M q,
      ‖nativeChartJetLinear w e q z hz b K (hK.trans hball) φ α‖ ≤
        Real.sqrt C * ‖smoothEnergyLinear w q α‖ :=
    nativeChartJetLinear_norm_le_of_sq_bound w e q z hz b K (hK.trans hball) φ C hC.le hbound
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, ?_, ?_, ?_⟩
  · exact completeChartJetCLM_readback_of_bound w e q z hz b K (hK.trans hball) φ (Real.sqrt C) hnorm
  · exact completeChartJetCLM_norm_le_of_bound w e q z hz b K (hK.trans hball) φ (Real.sqrt C) hnorm
  · exact completeChartJetCLM_unique_of_bound w e q z hz b K (hK.trans hball) φ (Real.sqrt C) hnorm

/-- The original geometry supplies the genuine norm bound, exact dense smooth readback and uniqueness on the full closed graph. -/
theorem exists_complete_chart_jet_localization
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.form.val.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
        ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
          (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ L > 0,
          (∀ α : SmoothRealForm n M q,
            completeChartJetCLM w e q z hz b K (hK.trans hball) φ (smoothEnergyLinear w q α) =
              nativeChartJetLinear w e q z hz b K (hK.trans hball) φ α) ∧
          (∀ u : GraphEnergy w q,
            ‖completeChartJetCLM w e q z hz b K (hK.trans hball) φ u‖ ≤ L * ‖u‖) ∧
          (∀ G : GraphEnergy w q →L[ℝ] CoefficientJetHilbert volume K b (FormIndex n q),
            (∀ α : SmoothRealForm n M q,
              G (smoothEnergyLinear w q α) = nativeChartJetLinear w e q z hz b K (hK.trans hball) φ α) →
              G = completeChartJetCLM w e q z hz b K (hK.trans hball) φ) := by
  obtain ⟨b, hb, ho, r, hr, hball, hjet⟩ :=
    exists_original_chart_graph_coefficient_jet_bound w e q z hz
  exact ⟨b, hb, ho, r, hr, hball,
    chart_jet_localization_of_squared_bounds w e q z hz b r hball hjet⟩

/-- The literal native compact value projection is compact on the actual whole closed graph domain. -/
theorem completeChartValueCLM_isCompactOperator
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) :
    IsCompactOperator (completeChartValueCLM w e q z hz b K hK φ) :=
  (isCompactOperator_fixedFormValue b q volume K).comp_clm
    (completeChartJetCLM w e q z hz b K hK φ)

/-- Genuine compact completed chart values with exact original smooth coefficient readback and internally supplied local geometry. -/
theorem exists_compact_complete_chart_localization
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.form.val.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
        ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
          (φ : 𝓓_{K}(ComplexModel n, ℝ)),
          IsCompactOperator (completeChartValueCLM w e q z hz b K (hK.trans hball) φ) ∧
          (∀ α : SmoothRealForm n M q,
            completeChartValueCLM w e q z hz b K (hK.trans hball) φ (smoothEnergyLinear w q α) =
              fixedFormValueCLM b q volume K (fixedFormCoefficientJet
                (w.form.val.coeff e z) (w.isKahler.1 e z hz).1 (w.isKahler.1 e z hz).2
                b q volume K (chartCutoffTest e K (hK.trans hball) φ α))) := by
  obtain ⟨b, hb, ho, r, hr, hball, hjet⟩ := exists_complete_chart_jet_localization w e q z hz
  refine ⟨b, hb, ho, r, hr, hball, ?_⟩
  intro K hK φ
  obtain ⟨L, hL, hread, hnorm, hunique⟩ := hjet K hK φ
  refine ⟨completeChartValueCLM_isCompactOperator w e q z hz b K (hK.trans hball) φ, ?_⟩
  intro α
  change fixedFormValueCLM b q volume K
    (completeChartJetCLM w e q z hz b K (hK.trans hball) φ (smoothEnergyLinear w q α)) = _
  rw [hread α, nativeChartJetLinear_apply]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianCompleteChartLocalization
