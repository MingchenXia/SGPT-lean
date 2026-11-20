import SGPT.Foundations.Analysis.Pending.RawQuasiPshProductPointOrderBound
import SGPT.Foundations.Analysis.Pending.RawQuasiPshModificationUniformNecessity
import SGPT.Foundations.Analysis.Pending.DerivativeIdeal

set_option autoImplicit false

/-! # Actual Jacobian order before all original tests on a modification

Genuine geometry chooses the flattening and supplies the actual Jacobian
holomorphic nonzero germ. Its least point order precedes all tests/levels.
Only whole-divisor infimum <= local piece is used; no prime dictionary.
Reference: genuine local supplementary raw multiplier necessary estimate.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal NNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshModificationPointOrderBound

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  DemaillyApproximantDivisorialLelong DivisorialChangeOfVariables

noncomputable section

/-- Natural global modification geometry supplies a fixed actual Jacobian
point order before all original nonzero tests and actual multiplier levels. -/
theorem exists_jacobian_order_uniform_original_test_bound
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := m + 1) π)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {E : Set Y} {y : Y} (hreg : RegularAtDim (n := m + 1) E y m) :
    ∃ (Φ : DivisorFlattening (m := m) E y) (b : ℕ),
      (∀ k < b, iteratedFDeriv ℂ k (complexJacobian (flatCoordMap π Φ)) 0 = 0) ∧
      iteratedFDeriv ℂ b (complexJacobian (flatCoordMap π Φ)) 0 ≠ 0 ∧
      ∀ (F : X → ℂ), HolomorphicAt (m + 1) F (π y) →
        (∃ᶠ z in 𝓝 (π y), F z ≠ 0) →
        ∃ a : ℕ,
          (∀ k < a, iteratedFDeriv ℂ k
            (fun z => F ((complexChartAt (n := m + 1) (π y)).val.symm
              (flatCoordMap π Φ z))) 0 = 0) ∧
          iteratedFDeriv ℂ a
            (fun z => F ((complexChartAt (n := m + 1) (π y)).val.symm
              (flatCoordMap π Φ z))) 0 ≠ 0 ∧
          ∀ c : ℝ, (multiplierIdeal (n := m + 1) c u).mem (π y) F →
            (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) ≤
              ENNReal.ofReal (2 * ((a : ℝ) + (b : ℝ) + 1) / c) := by
  obtain ⟨A, Φ, k, J', _, hJ', hJfactor, _⟩ :=
    AnalyticModificationLocalDiscrepancy.exists_logDiscrepancyLE_of_isAnalyticModification_regular
      hπ hreg
  let d := complexChartAt (n := m + 1) (π y)
  let w := chartFunction u d
  let p := d.val (π y)
  have hw : QuasiPlurisubharmonicAt w p :=
    hu d p (d.val.map_source (mem_complexChartAt_source (π y)))
  have hD := Φ.isOpen_flatDomain hπ.1.continuous
  have hfd := Φ.differentiableOn_flatCoordMap hπ.1
  have hfs := contDiffOn_of_differentiableOn_complex hfd hD
  have hpD := Φ.zero_mem_flatDomain π
  have hw0 : QuasiPlurisubharmonicAt w (flatCoordMap π Φ 0) := by
    simpa only [Φ.flatCoordMap_zero π] using hw
  have hψ := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic hD hfs hpD hw0
  have hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (complexJacobian (flatCoordMap π Φ)) z := by
    filter_upwards [hJ', hJfactor.eventually_nhds] with z hz heq
    exact (((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiableAt.pow k).mul hz).congr_of_eventuallyEq heq
  have hJnon :=
    AnalyticModificationLocalDiscrepancy.frequently_complexJacobian_ne_zero_of_isAnalyticModification
      hπ Φ
  obtain ⟨b, hJlow, hJb, htests⟩ :=
    RawQuasiPshProductPointOrderBound.exists_factor_order_uniform_test_bound hψ hJ hJnon
  refine ⟨Φ, b, hJlow, hJb, ?_⟩
  intro F hF hFnon
  let g : ComplexModel (m + 1) → ℂ := fun z => F (d.val.symm z)
  have hg : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ g z :=
    DerivativeIdeal.eventually_differentiableAt_comp_symm d (mem_complexChartAt_source (π y)) hF
  have he : Tendsto d.val (𝓝 (π y)) (𝓝 p) :=
    (d.val.continuousAt (mem_complexChartAt_source (π y))).tendsto
  have hgnon : ∃ᶠ z in 𝓝 p, g z ≠ 0 := by
    by_contra hn
    have hzero : ∀ᶠ z in 𝓝 p, g z = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with z hz
      exact not_ne_iff.mp hz
    have hback : ∀ᶠ z in 𝓝 (π y), F z = 0 := by
      filter_upwards [he.eventually hzero,
        d.val.open_source.mem_nhds (mem_complexChartAt_source (π y))] with z hz hzs
      simpa only [g, d.val.left_inv hzs] using hz
    exact (hFnon.and_eventually hback).exists.elim fun _ h => h.1 h.2
  have hfT : Tendsto (flatCoordMap π Φ) (𝓝 (0 : ComplexModel (m + 1))) (𝓝 p) := by
    simpa only [Φ.flatCoordMap_zero π] using
      (hfd.differentiableAt (hD.mem_nhds hpD)).continuousAt.tendsto
  have hG : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun t => g (flatCoordMap π Φ t)) z := by
    filter_upwards [hfT.eventually hg, hD.mem_nhds hpD] with z hgz hz
    exact hgz.comp z (hfd.differentiableAt (hD.mem_nhds hz))
  have hweightednon :=
    HolomorphicJacobianTestNonzeroPullback.frequently_flat_jacobian_test_ne_zero hπ Φ hg hgnon
  have hGnon : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), g (flatCoordMap π Φ z) ≠ 0 :=
    hweightednon.mono fun _ hz => (mul_ne_zero_iff.mp hz).1
  obtain ⟨a, hGlow, hGa, hbound⟩ := htests (fun z => g (flatCoordMap π Φ z)) hG hGnon
  refine ⟨a, hGlow, hGa, ?_⟩
  intro c hint
  have hintc : MultiplierIntegrableAt w c g (flatCoordMap π Φ 0) volume := by
    simpa only [Φ.flatCoordMap_zero π] using hint.2
  have hn := AnalyticModificationLocalDiscrepancy.isInjectiveOffNull_of_isAnalyticModification hπ
  obtain ⟨N, hN, hinj⟩ := Φ.exists_null_injOn hn
  have hpull := BlowupJacobianMultiplierGermEquivalence.multiplierIntegrableAt_comp_mul_complexJacobian
    hD hfs hpD hN hinj hw0 hintc
  obtain ⟨R, hR, hRD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hpD)
  have hwhole : (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) ≤
      (⨅ z ∈ ball (0 : ComplexModel (m + 1)) R ∩ {z | z (Fin.last m) = 0},
        lelongNumber (n := m + 1) (fun t => w (flatCoordMap π Φ t)) z) := by
    refine le_iInf fun z => le_iInf fun hz => ?_
    have hzD := hRD hz.1
    have hpoint := Φ.point_mem hzD.1 hz.2
    have hgerm : (fun t => w (flatCoordMap π Φ t)) =ᶠ[𝓝 z]
        (fun t => u (π (Φ.point t))) := by
      filter_upwards [hD.mem_nhds hzD] with t ht
      change u (d.val.symm (flatCoordMap π Φ t)) = u (π (Φ.point t))
      rw [Φ.chartSymm_flatCoordMap π ht]
    have hreader := (LelongNumberComparison.lelongNumber_congr hgerm).trans
      (FlattenedGlobalGenericLelongComparison.lelongNumber_comp_point_eq Φ
        (fun t => u (π t)) hzD.1)
    calc
      _ ≤ lelongNumber (n := m + 1) (fun t => u (π t)) (Φ.point z) :=
        iInf_le_of_le (Φ.point z) (iInf_le_of_le hpoint le_rfl)
      _ = _ := hreader.symm
  exact hwhole.trans (hbound c hpull R hR)

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshModificationPointOrderBound
