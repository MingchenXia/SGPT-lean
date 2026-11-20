import SGPT.Foundations.Analysis.Pending.AnalyticModificationPreferredJacobianTest
import SGPT.Foundations.Analysis.Pending.AnalyticModificationJacobianMultiplierGerms
import SGPT.Foundations.Analysis.Pending.SNCPrincipalNumericalMultiplierSufficiency
import SGPT.Foundations.Analysis.Pending.FiniteGeneratorExponentialLelongBound
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold

set_option autoImplicit false

/-! # Raw whole-prime comparison gives an original analytic-target multiplier germ -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationNumericalMultiplierDescent

open FirstPass FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves
  FirstPass.NonKahlerLocus NormalCrossings InvertibleIdealQuotient
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section

private theorem psh_generatorLog_of_near_holomorphic {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) {p : ComplexModel n}
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    PlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hG)
  have hgen : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hpU, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hgen zero_lt_one

/-- The original raw numerical comparison and original source integral give
the actual analytic-target ideal membership after proper all-fiber descent. -/
theorem multiplierIdeal_mem_of_principalized_raw_prime_comparison
    {m s : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (x : X) (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y))
    (hE : IsSNCDivisor (m + 1) E) (hsupport : D.support = ⋃ H ∈ E, H)
    (hcomponents : ∀ y : Y, π y = x → ∀ i : Fin E.length, y ∈ E.get i →
      ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m ∧ (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) ∧
        y ∈ V.carrier ∧ (∀ z ∈ V.carrier, π z = x) ∧
        ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ E.get i ∩ O = V.carrier ∩ O)
    (G : Fin s → X → ℂ) (hG : ∀ i, HolomorphicAt (m + 1) (G i) x)
    (hgen : ∀ y : Y, π y = x → ∀ f : Y → ℂ, D.ideal.mem y f ↔
      IsInSpanAt (n := m + 1) (· ∈ range (fun i z => G i (π z))) y f)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {p q₀ q₁ : ℝ} (hp : 0 < p) (hq₁ : 0 < q₁) (hgap : q₁ < q₀)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : ∀ᶠ z in 𝓝 x, EReal.exp ((p : EReal) * v z) ≤
      C * ∑ i, ENNReal.ofReal (‖G i z‖ ^ 2))
    (horder : ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
      V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
      (∀ z ∈ V.carrier, π z = x) →
        (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
          ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => u (π w)) z)
    {F : X → ℂ} (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0)
    (hint : (multiplierIdeal (n := m + 1) q₀ u).mem x F) :
    (multiplierIdeal (n := m + 1) (q₁ / p) (generatorLog G)).mem x F := by
  classical
  have hq₀ : 0 < q₀ := hq₁.trans hgap
  let d := complexChartAt (n := m + 1) x
  let g : ComplexModel (m + 1) → ℂ := fun z => F (d.val.symm z)
  have hdx : d.val x ∈ d.val.target := d.val.map_source (mem_complexChartAt_source x)
  have hg : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ g z := by
    obtain ⟨_, O, hO, hpO, hgd, _⟩ := hint.2
    filter_upwards [hO.mem_nhds hpO] with z hz
    exact (hgd z hz).differentiableAt (hO.mem_nhds hz)
  have hgnon : ∃ᶠ z in 𝓝 (d.val x), g z ≠ 0 := by
    change ¬ ∀ᶠ z in 𝓝 (d.val x), ¬g z ≠ 0
    intro hzero
    have hround : ∀ᶠ z in 𝓝 x, F z = 0 := by
      filter_upwards [(d.val.continuousAt (mem_complexChartAt_source x)).eventually hzero,
        d.val.open_source.mem_nhds (mem_complexChartAt_source x)] with z hz hzs
      have h : F (d.val.symm (d.val z)) = 0 := not_ne_iff.mp hz
      simpa only [d.val.left_inv hzs] using h
    exact (hFnon.and_eventually hround).exists.elim fun _ h => h.1 h.2
  have huY := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu
  have hcompare : ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
      V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
      (∀ z ∈ V.carrier, π z = x) →
        (⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
          (generatorLog (fun i w => G i (π w))) z) ≤
          ENNReal.ofReal p * ⨅ z ∈ V.carrier,
            lelongNumber (n := m + 1) (fun w => u (π w)) z := by
    intro V hdim hreg hcenter
    have hpoint : ∀ z ∈ V.carrier, lelongNumber (n := m + 1)
        (generatorLog (fun i w => G i (π w))) z ≤
        ENNReal.ofReal p * lelongNumber (n := m + 1) (fun w => v (π w)) z := by
      intro z hz
      have ht : Tendsto π (𝓝 z) (𝓝 x) := by
        simpa only [hcenter z hz] using hπ.1.continuous.continuousAt.tendsto (x := z)
      exact FiniteGeneratorExponentialLelongBound.lelongNumber_generatorLog_le_scaled_of_exp_domination
        (fun i w => G i (π w)) hp hC (ht.eventually hdom)
    have hcoef : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
    have hwhole : (⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
        (generatorLog (fun i w => G i (π w))) z) ≤
        ENNReal.ofReal p * ⨅ z ∈ V.carrier,
          lelongNumber (n := m + 1) (fun w => v (π w)) z := by
      simp_rw [ENNReal.mul_iInf_of_ne hcoef ENNReal.ofReal_ne_top]
      exact iInf_mono fun z => iInf_mono fun hz => hpoint z hz
    apply hwhole.trans
    simpa only [mul_comm] using mul_le_mul_right (horder V hdim hreg hcenter) (ENNReal.ofReal p)
  have hsource :=
    (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
      hπ x hq₀ (hu d (d.val x) hdx) hg).mp hint.2
  have hGPnear (i : Fin s) : ∀ᶠ z in 𝓝 (d.val x),
      DifferentiableAt ℂ (fun z => G i (d.val.symm z)) z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source x) (hG i)
  have htargetQPsh : QuasiPlurisubharmonicAt
      (chartFunction (generatorLog G) d) (d.val x) := by
    have h := (psh_generatorLog_of_near_holomorphic
      (fun i z => G i (d.val.symm z)) hGPnear).quasiPlurisubharmonicAt
    convert h using 1
    funext z
    simp only [chartFunction, generatorLog_eq_log_sum]
  refine ⟨hint.1, ?_⟩
  apply (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x (div_pos hq₁ hp) htargetQPsh hg).mpr
  intro y hy
  let e := complexChartAt (n := m + 1) y
  let f := coordinateMap π e d
  let T : ComplexModel (m + 1) → ℂ := fun z => g (f z) * complexJacobian f z
  let K : Y → ℂ := fun z => T (e.val z)
  have hD := coordinateDomain_isOpen hπ.1 e d
  have hpD : e.val y ∈ coordinateDomain π e d := by
    apply mem_coordinateDomain (mem_complexChartAt_source y)
    rw [hy]
    exact mem_complexChartAt_source x
  have hcongr : (fun z => chartFunction u d (f z)) =ᶠ[𝓝 (e.val y)]
      chartFunction (fun z => u (π z)) e := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    change u (d.val.symm (d.val (π (e.val.symm z)))) = u (π (e.val.symm z))
    rw [d.val.left_inv hz.2]
  have hU : MultiplierIntegrableAt (chartFunction (fun z => u (π z)) e) q₀ T (e.val y) volume :=
    (hsource y hy).congr hcongr EventuallyEq.rfl
  have hTnear : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ T z := by
    obtain ⟨_, O, hO, hpO, hgd, _⟩ := hU
    filter_upwards [hO.mem_nhds hpO] with z hz
    exact (hgd z hz).differentiableAt (hO.mem_nhds hz)
  have hKhol : HolomorphicAt (m + 1) K y :=
    MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart
      (mem_complexChartAt_source y) hTnear
  have hTnon : ∃ᶠ z in 𝓝 (e.val y), T z ≠ 0 := by
    have h := AnalyticModificationPreferredJacobianTest.frequently_preferred_jacobian_test_ne_zero
      hπ y (g := g) (by simpa only [hy] using hg) (by simpa only [hy] using hgnon)
    simpa only [hy] using h
  have hKnon : ∃ᶠ z in 𝓝 y, K z ≠ 0 := by
    change ¬ ∀ᶠ z in 𝓝 y, ¬K z ≠ 0
    intro hzero
    have ht : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
      have h := (e.val.symm.continuousAt (e.val.map_source (mem_complexChartAt_source y))).tendsto
      simpa only [e.val.left_inv (mem_complexChartAt_source y)] using h
    have hzT : ∀ᶠ z in 𝓝 (e.val y), T z = 0 := by
      filter_upwards [ht.eventually hzero,
        e.val.open_target.mem_nhds (e.val.map_source (mem_complexChartAt_source y))] with z hz hzt
      have h : T (e.val (e.val.symm z)) = 0 := not_ne_iff.mp hz
      simpa only [e.val.right_inv hzt] using h
    exact (hTnon.and_eventually hzT).exists.elim fun _ h => h.1 h.2
  have hrep : (fun z => K (e.val.symm z)) =ᶠ[𝓝 (e.val y)] T := by
    filter_upwards [e.val.open_target.mem_nhds
      (e.val.map_source (mem_complexChartAt_source y))] with z hz
    exact congrArg T (e.val.right_inv hz)
  have hintK : (multiplierIdeal (n := m + 1) q₀ (fun z => u (π z))).mem y K :=
    ⟨hKhol, hU.congr EventuallyEq.rfl hrep.symm⟩
  have htarget := SNCPrincipalNumericalMultiplierSufficiency.multiplierIdeal_mem_of_whole_prime_bounds
    hπ.1 x y hy D E hE hsupport (hcomponents y hy) G hG (hgen y hy) huY
      hKhol hKnon hp hq₁ hgap hintK hcompare
  have hweight : chartFunction (generatorLog (fun i w => G i (π w))) e
      =ᶠ[𝓝 (e.val y)] (fun z => chartFunction (generatorLog G) d (f z)) := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    change generatorLog (fun i w => G i (π w)) (e.val.symm z) =
      generatorLog G (d.val.symm (d.val (π (e.val.symm z))))
    rw [d.val.left_inv hz.2]
    simp only [generatorLog_eq_log_sum]
  exact htarget.2.congr hweight hrep

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationNumericalMultiplierDescent
