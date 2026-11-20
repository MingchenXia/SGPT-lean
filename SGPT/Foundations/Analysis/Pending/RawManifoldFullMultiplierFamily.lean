import SGPT.Foundations.Analysis.Pending.RawMultiplierFullGeneratorExponentialDomination
import SGPT.Foundations.Analysis.Pending.FiniteGeneratorExponentialLelongBound
import SGPT.Foundations.Analysis.Pending.ManifoldAdaptedMultiplierGermTransport
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.Pending.NormalCrossings

set_option autoImplicit false

/-! # One full original multiplier family before all whole fiber readers

The genuine centered chart transports the complete weighted germ ideal,
actual exponential domination and strict reverse tests to the original point.
No local source is identified with a modification over the whole manifold.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u v

namespace SGPT.Foundations.Analysis.Pending.RawManifoldFullMultiplierFamily

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  NormalCrossings InvertibleIdealQuotient WeightedHolomorphicGermIdealIntegralClosure

noncomputable section


private theorem psh_generatorLog_of_near_holomorphic {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) {p : ComplexModel n}
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    PlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (Filter.eventually_all.mpr hG)
  have hgen : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hpU, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hgen zero_lt_one

/-- The complete original family is chosen before every future whole fiber
reader and every strict reverse test. -/
theorem exists_full_family_before_all_whole_fiber_bounds
    {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {v : X → EReal}
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) (x : X)
    {p : ℕ} (hp : 0 < p) :
    ∃ (s : ℕ) (G : Fin s → X → ℂ),
      (∀ i, HolomorphicAt n (G i) x) ∧
      (∀ F : X → ℂ, (multiplierIdeal (n := n) p v).mem x F ↔
        IsInSpanAt (n := n) (· ∈ range G) x F) ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        (∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * v z) ≤
          C * ∑ i, ENNReal.ofReal (‖G i z‖ ^ 2)) ∧
        (∀ (d : ℕ) (Y : Type v) [TopologicalSpace Y]
          [ChartedSpace (ComplexModel d) Y] (π : Y → X), Continuous π →
          ∀ E : Set Y, (∀ y ∈ E, π y = x) →
            (⨅ y ∈ E, lelongNumber (n := d) (generatorLog (fun i z => G i (π z))) y) ≤
              ENNReal.ofReal (p : ℝ) * ⨅ y ∈ E, lelongNumber (n := d) (fun z => v (π z)) y) ∧
        ∀ (c δ : ℝ), 0 < c → 0 < δ → 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) →
          ∀ F : X → ℂ,
            (multiplierIdeal (n := n) (c * (1 + δ) / p) (generatorLog G)).mem x F →
            (multiplierIdeal (n := n) c v).mem x F := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨Φ, hsrc, h0⟩ := NormalCrossings.exists_centred_coordinates (n := n) x
  let e := complexChartAt (n := n) x
  let T : ComplexModel n → X := fun z => e.val.symm (Φ.invFun z)
  let A : X → ComplexModel n := fun y => Φ.toFun (e.val y)
  have hzero : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun (0 : ComplexModel n) = e.val x := by
    change Φ.invFun 0 = (complexChartAt (n := n) x).val x
    rw [← h0, Φ.left_inv _ Φ.center_mem_source]
  have hT0 : T (0 : ComplexModel n) = x := by
    dsimp [T]
    rw [hinv0]
    exact e.val.left_inv (mem_complexChartAt_source x)
  have he : Tendsto e.val (𝓝 x) (𝓝 (e.val x)) :=
    (e.val.continuousAt (mem_complexChartAt_source x)).tendsto
  have hto : Tendsto Φ.toFun (𝓝 (e.val x)) (𝓝 (0 : ComplexModel n)) := by
    simpa only [h0] using (Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.tendsto
  have hA : Tendsto A (𝓝 x) (𝓝 (0 : ComplexModel n)) := hto.comp he
  have hTA : ∀ᶠ y in 𝓝 x, T (A y) = y := by
    filter_upwards [he.eventually (Φ.isOpen_source.mem_nhds Φ.center_mem_source),
      e.val.open_source.mem_nhds (mem_complexChartAt_source x)] with y hys hye
    dsimp [T, A]
    rw [Φ.left_inv (e.val y) hys, e.val.left_inv hye]
  have hAT : ∀ᶠ z in 𝓝 (0 : ComplexModel n), A (T z) = z := by
    filter_upwards [Φ.isOpen_target.mem_nhds hzero] with z hz
    have hi : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hz)
    dsimp [A, T]
    rw [e.val.right_inv hi, Φ.right_inv z hz]
  have hvP := hv e (e.val x) (e.val.map_source (mem_complexChartAt_source x))
  have hvT : QuasiPlurisubharmonicAt (fun z => v (T z)) 0 :=
    HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic Φ.isOpen_target
      (contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target)
      hzero (by simpa only [hinv0] using hvP)
  obtain ⟨s, g, hg, hspan, _, O, hO, h0O, hvO, hgO, C, hC, hdom, hreverse⟩ :=
    RawMultiplierFullGeneratorExponentialDomination.exists_full_family_with_exponential_domination
      hvT hp
  let G : Fin s → X → ℂ := fun i y => g i (A y)
  have hG (i : Fin s) : HolomorphicAt n (G i) x := by
    have hW : ∀ᶠ z in 𝓝 (e.val x),
        DifferentiableAt ℂ (fun w => g i (Φ.toFun w)) z := by
      filter_upwards [hto.eventually (hg i),
        Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z hgz hzs
      exact hgz.comp z (Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds hzs))
    exact MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart
      (mem_complexChartAt_source x) hW
  have hGa (i : Fin s) : (fun z => G i (T z)) =ᶠ[𝓝 (0 : ComplexModel n)] g i :=
    hAT.mono fun z hz => by dsimp [G]; rw [hz]
  have hfull (F : X → ℂ) : (multiplierIdeal (n := n) p v).mem x F ↔
      IsInSpanAt (n := n) (· ∈ range G) x F := by
    by_cases hF : HolomorphicAt n F x
    · have hFT : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => F (T z)) z :=
        ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
          x Φ h0 (fun _ : Fin 1 => F) F).mp
            (InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hF)).1.mono
              fun _ hz => hz.differentiableAt
      have hcov := ManifoldAdaptedMultiplierGermTransport.multiplierIdeal_mem_comp_adapted_iff
        x Φ h0 hv hF (p : ℝ)
      have hspancov := ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G F
      have hspancongr : IsInSpanAt (n := n) (· ∈ range fun i z => G i (T z)) 0 (fun z => F (T z)) ↔
          IsInSpanAt (n := n) (· ∈ range g) 0 (fun z => F (T z)) :=
        ⟨CoherentIdealColon.isInSpanAt_range_congr hGa EventuallyEq.rfl,
          CoherentIdealColon.isInSpanAt_range_congr (fun i => (hGa i).symm) EventuallyEq.rfl⟩
      have hring := EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span g hg hFT
      rw [hspan] at hring
      exact hcov.trans ((mem_weightedGermIdeal_iff hpr hvT hFT).symm.trans
        (hring.symm.trans (hspancongr.symm.trans hspancov.symm)))
    · constructor
      · intro hmem
        exact (hF hmem.1).elim
      · intro hmem
        exact (hF hmem.1).elim
  have hdomG : ∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * v z) ≤
      C * ∑ i, ENNReal.ofReal (‖G i z‖ ^ 2) := by
    filter_upwards [hA.eventually hdom, hTA] with z hz hround
    simpa only [hround, EReal.coe_natCast] using hz
  refine ⟨s, G, hG, hfull, C, hC, hdomG, ?_, ?_⟩
  · intro d Y _ _ π hπ E hcenter
    have hpoint : ∀ y ∈ E,
        lelongNumber (n := d) (generatorLog (fun i z => G i (π z))) y ≤
          ENNReal.ofReal (p : ℝ) * lelongNumber (n := d) (fun z => v (π z)) y := by
      intro y hy
      have ht : Tendsto π (𝓝 y) (𝓝 x) := by
        simpa only [hcenter y hy] using hπ.continuousAt.tendsto (x := y)
      exact FiniteGeneratorExponentialLelongBound.lelongNumber_generatorLog_le_scaled_of_exp_domination
        (fun i z => G i (π z)) hpr hC (ht.eventually hdomG)
    have hcoef : ENNReal.ofReal (p : ℝ) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hpr)
    simp_rw [ENNReal.mul_iInf_of_ne hcoef ENNReal.ofReal_ne_top]
    exact iInf_mono fun y => iInf_mono fun hy => hpoint y hy
  · intro c δ hc hδ hbound F hFmem
    have hF := hFmem.1
    have hGP (i : Fin s) : ∀ᶠ z in 𝓝 (e.val x),
        DifferentiableAt ℂ (fun z => G i (e.val.symm z)) z :=
      MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
        (mem_complexChartAt_source x) (hG i)
    have hpsh := (psh_generatorLog_of_near_holomorphic
      (fun i z => G i (e.val.symm z)) hGP).quasiPlurisubharmonicAt
    have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
      Φ (f := fun z => F (e.val.symm z)) (c := c * (1 + δ) / p) hpsh
    have hintGa : MultiplierIntegrableAt (generatorLog (fun i z => G i (T z)))
        (c * (1 + δ) / p) (fun z => F (T z)) 0 volume := by
      have hweq : (fun z => generatorLog (fun i z => G i (e.val.symm z)) (Φ.invFun z))
          =ᶠ[𝓝 (0 : ComplexModel n)] generatorLog (fun i z => G i (T z)) :=
        Eventually.of_forall fun z => by
          change generatorLog (fun i z => G i (e.val.symm z)) (Φ.invFun z) =
            generatorLog (fun i z => G i (T z)) z
          rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
      have hint : MultiplierIntegrableAt
          (fun z => generatorLog (fun i z => G i (e.val.symm z)) (Φ.invFun z))
          (c * (1 + δ) / p) (fun z => F (T z)) 0 volume := by
        simpa only [h0] using hcov.mpr hFmem.2
      exact hint.congr hweq EventuallyEq.rfl
    have hlog : (generatorLog (fun i z => G i (T z))) =ᶠ[𝓝 (0 : ComplexModel n)]
        generatorLog g := by
      filter_upwards [Filter.eventually_all.mpr hGa] with z hz
      rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
      rw [Finset.sum_congr rfl (fun i _ => congrArg (fun w : ℂ => ‖w‖ ^ 2) (hz i))]
    have hintg := hintGa.congr hlog EventuallyEq.rfl
    have hraw := hreverse c δ hc hδ hbound (fun z => F (T z)) hintg
    exact (ManifoldAdaptedMultiplierGermTransport.multiplierIdeal_mem_comp_adapted_iff
      x Φ h0 hv hF c).mpr hraw

end
end SGPT.Foundations.Analysis.Pending.RawManifoldFullMultiplierFamily
