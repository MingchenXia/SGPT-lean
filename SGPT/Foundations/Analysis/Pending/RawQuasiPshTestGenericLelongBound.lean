import SGPT.Foundations.Analysis.Pending.RawQuasiPshDivisorialSliceBound
import SGPT.Foundations.Analysis.Pending.SNCHolomorphicTestNecessity

set_option autoImplicit false

/-! # A raw weight and its actual original test supply local generic bounds

The original nonzero test supplies its own finite coordinate orders. The raw
quasi-PSH weight is never replaced by an assumed analytic presentation. Actual
slice growth and the finite integral force the last-coordinate reader bound,
including infinite-reader contradiction and additional zeros of the test.
Reference: Copy-4 domination lemma, slice/exponent proof; supplementary local
necessity toward the valuative test in Xia and Demailly's Analytic Methods.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshTestGenericLelongBound

open FirstPass FirstPass.NonKahlerLocus HolomorphicGermReducednessBridge

noncomputable section

private theorem threshold_of_integrability {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} (hu : QuasiPlurisubharmonicAt u 0)
    (a : Fin (m + 1) → ℕ) {F H : ComplexModel (m + 1) → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin (m + 1), z j ^ a j)
    {c : ℝ} (hint : MultiplierIntegrableAt u c F 0 volume)
    {R : ℝ} (hR : 0 < R) {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) < ⨅ q ∈ ball (0 : ComplexModel (m + 1)) R ∩
      {q | q (Fin.last m) = 0}, lelongNumber (n := m + 1) u q) :
    c * (γ : ℝ) < 2 * ((a (Fin.last m) : ℝ) + 1) := by
  classical
  obtain ⟨r, hr, _, C, hupper⟩ := RawQuasiPshDivisorialSliceBound.exists_slice_bound hu hR hγ
  let f : ComplexModel (m + 1) → ℂ := fun z =>
    H z * ∏ i : Fin m, z i.castSucc ^ a i.castSucc
  have htest : F =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      (fun z => z (Fin.last m) ^ a (Fin.last m) * f z) := by
    filter_upwards [heq] with z hz
    rw [hz, Fin.prod_univ_castSucc]
    dsimp only [f]
    ring
  obtain ⟨hc, U, hU, h0U, _, hL2⟩ := hint.congr EventuallyEq.rfl htest
  obtain ⟨V, hVsub, hV, h0V⟩ := _root_.mem_nhds_iff.mp hH
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      z ∈ (U ∩ V) ∩ ball 0 r :=
    ((show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ U from hU.mem_nhds h0U).and
      (show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ V from hV.mem_nhds h0V)).and
        (show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ ball 0 r from ball_mem_nhds _ hr)
  obtain ⟨y, hy, hyW⟩ :=
    ((SNCHolomorphicTestNecessity.frequently_last_zero_and_residual_and_other_coordinates_ne_zero
      hH hnot).and_eventually hnear).exists
  have hcontf : ContinuousAt f y := by
    apply (hVsub hyW.1.2).continuousAt.mul
    exact tendsto_finsetProd Finset.univ fun i _ =>
      (((EuclideanSpace.proj (𝕜 := ℂ) i.castSucc).continuous.continuousAt).pow (a i.castSucc))
  have hfy : f y ≠ 0 :=
    mul_ne_zero hy.2.1 (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hy.2.2 i))
  let W : Set (ComplexModel (m + 1)) := (U ∩ V) ∩ ball 0 r
  have hW : IsOpen W := (hU.inter hV).inter isOpen_ball
  have hWU : W ⊆ U := fun z hz => hz.1.1
  have hneg := DivisorialMultiplierOrder.neg_two_lt_of_lintegral_ne_top hy.1
    (hW.mem_nhds hyW) hc (fun z hz hz0 => hupper z hz.2 hz0) hcontf hfy
    (a (Fin.last m)) (hL2.mono hWU).2.ne
  nlinarith

/-- The original finite weighted integral supplies all finite coordinate orders
before every radius, and bounds its raw local hyperplane Lelong reader. -/
theorem exists_orders_and_generic_bound {m : ℕ} {u : ComplexModel (m + 1) → EReal}
    (hu : QuasiPlurisubharmonicAt u 0) {c : ℝ} {F : ComplexModel (m + 1) → ℂ}
    (hint : MultiplierIntegrableAt u c F 0 volume)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), F z ≠ 0) :
    ∃ (a : Fin (m + 1) → ℕ) (H : ComplexModel (m + 1) → ℂ)
      (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z),
      (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), H z ≠ 0) ∧
      F =ᶠ[𝓝 0] (fun z => H z * ∏ j : Fin (m + 1), z j ^ a j) ∧
      (∀ j : Fin (m + 1), ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
        (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) ∧
      ∀ R : ℝ, 0 < R →
        (⨅ q ∈ ball (0 : ComplexModel (m + 1)) R ∩ {q | q (Fin.last m) = 0},
          lelongNumber (n := m + 1) u q) ≤
          ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1) / c) := by
  have hintcopy := hint
  obtain ⟨hc, U, hU, h0U, hhol, _⟩ := hintcopy
  have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ F z := by
    filter_upwards [show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ U from hU.mem_nhds h0U]
      with z hz
    exact hhol.differentiableAt (hU.mem_nhds hz)
  obtain ⟨a, H, hH, hHnon, heq, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hne
  refine ⟨a, H, hH, hHnon, heq, hnot, fun R hR => ?_⟩
  by_contra hle
  have hlt : ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1) / c) <
      ⨅ q ∈ ball (0 : ComplexModel (m + 1)) R ∩ {q | q (Fin.last m) = 0},
        lelongNumber (n := m + 1) u q := lt_of_not_ge hle
  obtain ⟨γ, hγlower, hγupper⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hγ0 : (0 : ℝ≥0∞) < γ := bot_le.trans_lt hγlower
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ0
  have hγreal : 2 * ((a (Fin.last m) : ℝ) + 1) / c < (γ : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff hγr).mp (by
      simpa only [ENNReal.ofReal_coe_nnreal] using hγlower)
  have hthresh := threshold_of_integrability hu a hH (hnot (Fin.last m)) heq hint hR hγupper
  have hbad := (div_lt_iff₀ hc).mp hγreal
  nlinarith

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshTestGenericLelongBound
