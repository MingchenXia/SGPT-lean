import SGPT.Foundations.Analysis.Pending.RawQuasiPshUniformStrictGenericNecessity
import SGPT.Foundations.Analysis.Pending.HolomorphicJacobianTestNonzeroPullback
import SGPT.Foundations.Analysis.Pending.FlattenedGlobalGenericLelongComparison
import SGPT.Foundations.Analysis.Pending.BlowupJacobianMultiplierGermEquivalence
import SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

set_option autoImplicit false

/-! # One original strict margin for all genuine modification readers

The original raw germ supplies the improved exponent before any modification.
Actual geometry supplies the weighted lift and its nonzero germ. Only the
whole-divisor infimum bounded by a local piece is used; no generic minimum,
local-to-global prime identification or sufficient membership certificate.
Reference: Guan--Zhou strong openness; Xia valuative discussion, necessary
direction with the repository's logarithmic norm reader and factor two.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal NNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshModificationUniformNecessity

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus HolomorphicGermReducednessBridge
  DemaillyApproximantDivisorialLelong DivisorialChangeOfVariables

noncomputable section

/-- One margin is selected on the original raw germ before every actual
modification over the same whole manifold, source point and flattening. -/
theorem exists_uniform_strict_modification_bound
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {x : X} {c : ℝ} {F : X → ℂ}
    (hint : (multiplierIdeal (n := m + 1) c u).mem x F)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
      (π : Y → X)
      (_hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
      (y : Y) (_hy : π y = x) (E : Set Y) (Φ : DivisorFlattening (m := m) E y),
      ∃ (a : Fin (m + 1) → ℕ) (H : ComplexModel (m + 1) → ℂ)
        (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z),
        (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), H z ≠ 0) ∧
        (fun z => F ((complexChartAt (n := m + 1) x).val.symm (flatCoordMap π Φ z)) *
          complexJacobian (flatCoordMap π Φ) z) =ᶠ[𝓝 0]
          (fun z => H z * ∏ j : Fin (m + 1), z j ^ a j) ∧
        (∀ j : Fin (m + 1), ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
          (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) ∧
        ENNReal.ofReal ((1 + δ) * c) *
          (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) <
          ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1)) := by
  let d := complexChartAt (n := m + 1) x
  let w := chartFunction u d
  let g : ComplexModel (m + 1) → ℂ := fun z => F (d.val.symm z)
  let p := d.val x
  have hw : QuasiPlurisubharmonicAt w p :=
    hu d p (d.val.map_source (mem_complexChartAt_source x))
  have hintc : MultiplierIntegrableAt w c g p volume := hint.2
  have hc : 0 < c := hintc.1
  have he : Tendsto d.val (𝓝 x) (𝓝 p) :=
    (d.val.continuousAt (mem_complexChartAt_source x)).tendsto
  have hgnon : ∃ᶠ z in 𝓝 p, g z ≠ 0 := by
    by_contra hn
    have hzero : ∀ᶠ z in 𝓝 p, g z = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with z hz
      exact not_ne_iff.mp hz
    have hback : ∀ᶠ z in 𝓝 x, F z = 0 := by
      filter_upwards [he.eventually hzero,
        d.val.open_source.mem_nhds (mem_complexChartAt_source x)] with z hz hzs
      simpa only [g, d.val.left_inv hzs] using hz
    exact (hFnon.and_eventually hback).exists.elim fun _ h => h.1 h.2
  obtain ⟨q, hcq, hq⟩ :=
    RawQuasiPshUniformStrictGenericNecessity.exists_gt_multiplierIntegrableAt hw hintc
  have hqpos : 0 < q := hc.trans hcq
  have hg : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ g z := by
    obtain ⟨_, U, hU, hpU, hgU, _⟩ := hq
    filter_upwards [hU.mem_nhds hpU] with z hz
    exact (hgU z hz).differentiableAt (hU.mem_nhds hz)
  let δ : ℝ := (q - c) / (2 * c)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hcq) (by positivity)
  have hcoeff : (1 + δ) * c = (q + c) / 2 := by
    dsimp only [δ]
    field_simp
    ring
  have hκpos : 0 < (1 + δ) * c := by rw [hcoeff]; positivity
  have hκq : (1 + δ) * c < q := by rw [hcoeff]; linarith
  refine ⟨δ, hδ, ?_⟩
  intro Y _ _ _ π hπ y hy E Φ
  subst x
  have hD := Φ.isOpen_flatDomain hπ.1.continuous
  have hfd := Φ.differentiableOn_flatCoordMap hπ.1
  have hfs := contDiffOn_of_differentiableOn_complex hfd hD
  have hpD := Φ.zero_mem_flatDomain π
  have hn := AnalyticModificationLocalDiscrepancy.isInjectiveOffNull_of_isAnalyticModification hπ
  obtain ⟨N, hN, hinj⟩ := Φ.exists_null_injOn hn
  have hw0 : QuasiPlurisubharmonicAt w (flatCoordMap π Φ 0) := by
    simpa only [Φ.flatCoordMap_zero π] using hw
  have hq0 : MultiplierIntegrableAt w q g (flatCoordMap π Φ 0) volume := by
    simpa only [Φ.flatCoordMap_zero π] using hq
  have hpull := BlowupJacobianMultiplierGermEquivalence.multiplierIntegrableAt_comp_mul_complexJacobian
    hD hfs hpD hN hinj hw0 hq0
  have hψ := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic hD hfs hpD hw0
  have htestnon := HolomorphicJacobianTestNonzeroPullback.frequently_flat_jacobian_test_ne_zero
    hπ Φ hg hgnon
  obtain ⟨a, H, hH, hHnon, heq, hnot, hbound⟩ :=
    RawQuasiPshTestGenericLelongBound.exists_orders_and_generic_bound hψ hpull htestnon
  refine ⟨a, H, hH, hHnon, heq, hnot, ?_⟩
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
  have hB : 0 < 2 * ((a (Fin.last m) : ℝ) + 1) := by positivity
  have hprod : (1 + δ) * c * (2 * ((a (Fin.last m) : ℝ) + 1) / q) <
      2 * ((a (Fin.last m) : ℝ) + 1) := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hqpos).mpr
    nlinarith [mul_lt_mul_of_pos_right hκq hB]
  calc
    _ ≤ ENNReal.ofReal ((1 + δ) * c) *
        ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1) / q) := by
      gcongr
      exact hwhole.trans (hbound R hR)
    _ = ENNReal.ofReal ((1 + δ) * c * (2 * ((a (Fin.last m) : ℝ) + 1) / q)) :=
      (ENNReal.ofReal_mul hκpos.le).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hB).mpr hprod

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshModificationUniformNecessity
