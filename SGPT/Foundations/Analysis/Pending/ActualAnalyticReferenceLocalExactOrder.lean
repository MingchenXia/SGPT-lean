import SGPT.Foundations.Analysis.Pending.ActualSNCPrincipalizedIdealComparison
import SGPT.Foundations.Analysis.Pending.ActualLocalAnalyticReferenceIdeal
import SGPT.Foundations.Analysis.Pending.FiniteGermIdealPullbackGenerators
import SGPT.Foundations.Analysis.Pending.HironakaLocalPrincipalization

set_option autoImplicit false

/-! # Exact scalar-one comparison from original analytic data on a local domain

All ideal and principalization data are produced from the original reference.
Properness is used only over the actual local open base, never for its open
inclusion composite to the original compact manifold. No mass input is used.
-/

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticReferenceLocalExactOrder

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  NormalCrossings InvertibleIdealQuotient FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation BlowupTowers MarkedIdeals

noncomputable section

private theorem frequently_ne_zero_of_coordinate_zero_locus {n : ℕ}
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hzero : ∀ᶠ z in 𝓝 0, H z = 0 → ∃ j : Fin n, z j = 0) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0 := by
  classical
  obtain ⟨N, hdiv⟩ :=
    HolomorphicCoordinateFactorization.exists_coordinate_product_power_dvd_of_zero_locus hH hzero
  have hprod : (∏ j : Fin n, HolGerm.mk (fun z : ComplexModel n => z j)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ =>
      (HolomorphicCoordinatePrime.prime_coordinate_germ j).ne_zero
  have hnon : HolGerm.mk H hH ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdiv
    exact (pow_ne_zero N hprod) hdiv
  change ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n), ¬ H z ≠ 0
  intro h
  apply hnon
  have heq : H =ᶠ[𝓝 (0 : ComplexModel n)] (0 : ComplexModel n → ℂ) :=
    h.mono fun _ hz => not_ne_iff.mp hz
  exact (HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero

private theorem mul_sum_nonneg_real {ι : Type*} (S : Finset ι) (f : ι → EReal)
    {c : ℝ} (hc : 0 ≤ c) :
    (c : EReal) * (∑ i ∈ S, f i) = ∑ i ∈ S, (c : EReal) * f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

private theorem scaled_coordinate_sum_eq {n : ℕ} (a : Fin n → ℕ)
    {c : ℝ} (hc : 0 ≤ c) (z : ComplexModel n) :
    (c : EReal) * (∑ i, ((2 * (a i : ℝ) : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖z i‖)) =
      ∑ i, (((2 * c * (a i : ℝ)) / 2 : ℝ) : EReal) * logNormSq (z i) := by
  rw [mul_sum_nonneg_real Finset.univ _ hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [logNormSq, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.log_pow]
  change (c : EReal) * (((2 * (a i : ℝ) : ℝ) : EReal) * _) =
    (((2 * c * (a i : ℝ)) / 2 : ℝ) : EReal) * ((2 : ℝ) * _)
  simp only [← mul_assoc, ← EReal.coe_mul]
  congr 1
  congr 1
  ring

private theorem coordinate_comparison {m : ℕ}
    {u v : ComplexModel (m + 1) → EReal}
    (hu : QuasiPlurisubharmonicAt u 0)
    (a : Fin (m + 1) → ℝ≥0) {ρ : ComplexModel (m + 1) → ℝ}
    (hρ : BoundedRealGermAt ρ 0)
    (hv : v =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun z =>
      (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) + (ρ z : EReal))
    {R : ℝ} (hR : 0 < R)
    (hν : ∀ j z, z ∈ ball (0 : ComplexModel (m + 1)) R → z j = 0 →
      (a j : ℝ≥0∞) ≤ lelongNumber (n := m + 1) u z) :
    MoreSingularAt u v 0 := by
  obtain ⟨p, h, ⟨W, hW, h0W, hp⟩, hh, heq⟩ := hu
  have hpp : PlurisubharmonicOn p W := hp.plurisubharmonicOn hW
  obtain ⟨B, _, hB⟩ := hρ
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      (((z ∈ W ∧ u z = p z + (h z : EReal)) ∧ ContDiffAt ℝ ∞ h z) ∧
      (v z = (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) +
        (ρ z : EReal))) ∧ |ρ z| ≤ B := by
    filter_upwards [hW.mem_nhds h0W, heq, hh, hv, hB] with z hz he hh hv hb
    exact ⟨⟨⟨⟨hz, he⟩, hh⟩, hv⟩, hb⟩
  obtain ⟨R₀, hR₀, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hsub : closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) ⊆ ball 0 R₀ :=
    closedBall_subset_ball (by linarith)
  have hhcont : ContinuousOn h (closedBall (0 : ComplexModel (m + 1)) (R₀ / 2)) :=
    fun z hz => ((hball (hsub hz)).1.1.2.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ComplexModel (m + 1)) (R₀ / 2)).exists_bound_of_continuousOn hhcont
  let r : ℝ := min (R / 2) (R₀ / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r ≤ R := (min_le_left _ _).trans (by linarith)
  have hrR₀ : r ≤ R₀ / 4 := min_le_right _ _
  have hdouble : closedBall (0 : ComplexModel (m + 1)) (2 * r) ⊆
      closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) :=
    closedBall_subset_closedBall (by linarith)
  have hΩ : closedBall (0 : ComplexModel (m + 1)) (2 * r) ⊆ W :=
    fun z hz => (hball (hsub (hdouble hz))).1.1.1.1
  obtain ⟨K, _, hK⟩ := hpp.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall (0 : ComplexModel (m + 1)) (2 * r)) hΩ
  have hsmall : ball (0 : ComplexModel (m + 1)) r ⊆
      closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) :=
    fun z hz => ball_subset_closedBall (ball_subset_ball (by linarith) hz)
  have hpν : ∀ j z, z ∈ ball (0 : ComplexModel (m + 1)) r → z j = 0 →
      (a j : ℝ≥0∞) ≤ lelongNumber (n := m + 1) p z := by
    intro j z hz hzj
    have hzbig := hsub (hsmall hz)
    have hgerm : u =ᶠ[𝓝 z] fun w => p w + (h w : EReal) :=
      (show ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ComplexModel (m + 1)) R₀ from
        isOpen_ball.mem_nhds hzbig).mono fun w hw => (hball hw).1.1.1.2
    have heqν : lelongNumber (n := m + 1) u z = lelongNumber (n := m + 1) p z := by
      rw [LelongNumberComparison.lelongNumber_congr hgerm,
        LelongChartReaderInvariance.lelongNumber_add_continuous_eq
          (hball hzbig).1.1.2.continuousAt]
    rw [← heqν]
    exact hν j z (ball_subset_ball hrR hz) hzj
  obtain ⟨t, ht, htr, C, q, _, _, _, hbound⟩ :=
    ActualSNCLogarithmicResidual.exists_simultaneous_residual hpp hr hΩ hK a hpν
  refine ⟨C + M + B, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self ht)] with z hz
  have hzbig := hsub (hsmall (ball_subset_ball htr hz))
  have hhM : h z ≤ M := by
    have hm : |h z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z (hsmall (ball_subset_ball htr hz))
    exact (abs_le.mp hm).2
  have hρB : -B ≤ ρ z := (abs_le.mp (hball hzbig).2).1
  rw [(hball hzbig).1.1.1.2, (hball hzbig).1.2]
  calc
    p z + (h z : EReal) ≤
        ((∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) + (C : EReal)) +
          (M : EReal) := add_le_add (hbound z hz) (EReal.coe_le_coe_iff.mpr hhM)
    _ = (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) +
        ((C + M : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
    _ ≤ (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) +
        ((ρ z + (C + M + B) : ℝ) : EReal) :=
      add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
    _ = _ := by rw [EReal.coe_add, ← add_assoc]


private theorem local_comparison_of_snc_presented
    {n m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y]
    {θ ζ : ClosedRealOneOneForm n X} {ψ φ : X → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) (hφ : IsThetaPshPotential ζ.val φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) φ)
    (hI : IOrderOnManifold (n := n) ψ φ) {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel n) ∞ π)
    (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y)) (hE : IsSNCDivisor (m + 1) E)
    (hsupport : D.support = ⋃ H ∈ E, H) (y : Y)
    {s : ℕ} (G : Fin s → Y → ℂ) (hG : ∀ i, HolomorphicAt (m + 1) (G i) y)
    (hgen : ∀ F : Y → ℂ, D.ideal.mem y F ↔ IsInSpanAt (n := m + 1) (· ∈ Set.range G) y F)
    {c : ℝ} (hc : 0 < c) {b : Y → ℝ} (hb : BoundedRealGermAt b y)
    (hrep : (fun z => φ (π z)) =ᶠ[𝓝 y] fun z =>
      (c : EReal) * generatorLog G z + (b z : EReal)) :
    MoreSingularAt (fun z => ψ (π z)) (fun z => φ (π z)) y := by
  classical
  obtain ⟨U, hU, hyU, g, hg, _, hprincipal, S, Φ, hsrc, h0, _, _, _,
      d, K, hK, hK0, hfactor⟩ :=
    SNCDivisorLocalGenerator.exists_adapted_unit_monomial_generator D E hE hsupport y
  let e := complexChartAt (n := m + 1) y
  let T : ComplexModel (m + 1) → Y := fun z => e.val.symm (Φ.invFun z)
  have hfull : ∀ F : Y → ℂ,
      IsInSpanAt (n := m + 1) (· ∈ Set.range G) y F ↔
        IsInSpanAt (n := m + 1) (· = g) y F :=
    fun F => (hgen F).symm.trans (hprincipal y hyU F)
  have hfullT := ManifoldPrincipalSpanAdaptedTransport.full_principal_generation_comp_adapted
    y Φ hsrc h0 G g hfull
  have hGT (i : Fin s) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun w => G i (T w)) z := by
    have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      y Φ h0 G (G i)).mp (isInSpanAt_self ⟨i, rfl⟩ (hG i))
    exact h.1.mono fun _ hz => hz.differentiableAt
  have hgm : HolomorphicAt (m + 1) g y := holomorphicAt_of_mdifferentiableOn hU hg hyU
  have hgT : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun w => g (T w)) z := by
    have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      y Φ h0 (fun _ : Fin 1 => g) g).mp (isInSpanAt_self ⟨0, rfl⟩ hgm)
    exact h.1.mono fun _ hz => hz.differentiableAt
  have hKn : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), K z ≠ 0 :=
    hK.self_of_nhds.continuousAt.eventually_ne hK0
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), g (T z) = 0 → ∃ j, z j = 0 := by
    filter_upwards [hfactor, hKn] with z hfac hkn hz
    have hp : (∏ j : Fin (m + 1), z j ^ d j) = 0 :=
      (mul_eq_zero.mp (hfac.symm.trans hz)).resolve_left hkn
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
    refine ⟨j, ?_⟩
    by_contra hne
    exact (pow_ne_zero (d j) hne) hj
  obtain ⟨a, η, R, hR, hη, heq⟩ :=
    PrincipalGeneratorLogPointwiseNormalForm.exists_generatorLog_coordinate_normal_form
      (fun i z => G i (T z)) hGT hgT
      (frequently_ne_zero_of_coordinate_zero_locus hgT hzero)
      (PrincipalFiniteSpanLogNorm.ideal_span_eq_of_full_principal_generation
        (fun i z => G i (T z)) hGT hgT hfullT) hzero
  have h0t : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val y := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hT0 : T 0 = y := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_complexChartAt_source y)]
  have hTc : ContinuousAt T 0 :=
    (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt
  have hbT : BoundedRealGermAt (fun z => b (T z)) 0 := by
    apply BoundedRealGermAt.comp_continuousAt _ hTc
    rwa [hT0]
  have hrepT : (fun z => φ (π (T z))) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      fun z => (c : EReal) * generatorLog (fun i w => G i (T w)) z + (b (T z) : EReal) := by
    have h := hrep.comp_tendsto (show Tendsto T (𝓝 0) (𝓝 y) from by rw [← hT0]; exact hTc)
    exact h
  have hqu := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ
    hψ.1.quasiPlurisubharmonic
  have hqu0 : QuasiPlurisubharmonicAt
      (chartFunction (fun z => ψ (π z)) e) (Φ.invFun 0) := by
    rw [hinv0]
    exact hqu e _ (e.val.map_source (mem_complexChartAt_source y))
  have hu : QuasiPlurisubharmonicAt (fun z => ψ (π (T z))) 0 :=
    HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic Φ.isOpen_target
      (contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target) h0t hqu0
  obtain ⟨B, hB0, hbB⟩ := hbT
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      (z ∈ ball 0 R ∧ φ (π (T z)) =
        (c : EReal) * generatorLog (fun i w => G i (T w)) z + (b (T z) : EReal)) ∧
        |b (T z)| ≤ B := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR), hrepT, hbB] with z hz hr hb
    exact ⟨⟨hz, hr⟩, hb⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  let A : Fin (m + 1) → ℝ≥0 := fun j => ⟨2 * c * (a j : ℝ), by positivity⟩
  have hν : ∀ j z, z ∈ ball (0 : ComplexModel (m + 1)) r → z j = 0 →
      (A j : ℝ≥0∞) ≤ lelongNumber (n := m + 1) (fun w => ψ (π (T w))) z := by
    intro j z hz hzj
    have hzR := (hball hz).1.1
    have hBgerm : BoundedRealGermAt (fun w => b (T w)) z :=
      ⟨B, hB0, (show ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ComplexModel (m + 1)) r from
        isOpen_ball.mem_nhds hz).mono fun w hw => (hball hw).2⟩
    have hrν : lelongNumber (n := m + 1) (fun w => φ (π (T w))) z =
        ENNReal.ofReal c * lelongNumber (n := m + 1)
          (generatorLog (fun i w => G i (T w))) z := by
      have hgerm := (show ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ComplexModel (m + 1)) r from
        isOpen_ball.mem_nhds hz).mono fun w hw => (hball hw).1.2
      rw [LelongNumberComparison.lelongNumber_congr hgerm,
        CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq hBgerm,
        ActualLelongPositiveScaling.lelongNumber_smul_eq hc]
    have hgerm : generatorLog (fun i w => G i (T w)) =ᶠ[𝓝 z] fun w =>
        (∑ i, ((2 * (a i : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖w i‖)) +
          (η w : EReal) :=
      (show ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ComplexModel (m + 1)) R from
        isOpen_ball.mem_nhds hzR).mono fun w hw => heq w hw
    have hlo : ENNReal.ofReal (2 * (a j : ℝ)) ≤
        lelongNumber (n := m + 1) (generatorLog (fun i w => G i (T w))) z := by
      rw [LelongNumberComparison.lelongNumber_congr hgerm]
      rw [← SNCLogarithmicGenericCoordinateOrders.iInf_lelongNumber_coordinate_hyperplane_eq
        (fun i => 2 * (a i : ℝ)) (fun i => by positivity) j hR hη]
      exact iInf₂_le z ⟨hzR, hzj⟩
    have hAeq : (A j : ℝ≥0∞) = ENNReal.ofReal c * ENNReal.ofReal (2 * (a j : ℝ)) := by
      rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (A j : ℝ) = (A j : ℝ≥0∞)), ← ENNReal.ofReal_mul hc.le]
      change ENNReal.ofReal (2 * c * (a j : ℝ)) = _
      congr 1
      ring
    rw [hAeq]
    have hs : ENNReal.ofReal c * ENNReal.ofReal (2 * (a j : ℝ)) ≤
        ENNReal.ofReal c * lelongNumber (n := m + 1)
          (generatorLog (fun i w => G i (T w))) z := by gcongr
    exact hs.trans (hrν.symm.le.trans
      (IOrderDivisorialLelongForward.lelongNumber_comp_le_of_iOrder_analytic_reference
        hψ hφ hA hI (fun w => π (T w)) z))
  have hρ : BoundedRealGermAt (fun z => c * η z + b (T z)) 0 :=
    (boundedRealGermAt_of_continuousAt (continuousAt_const.mul (hη 0 (mem_ball_self hR)))).add ⟨B, hB0, hbB⟩
  have hv : (fun z => φ (π (T z))) =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun z =>
      (∑ i, (((A i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) +
        ((c * η z + b (T z) : ℝ) : EReal) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    rw [(hball hz).1.2, heq z (hball hz).1.1,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le) (EReal.coe_ne_top c),
      scaled_coordinate_sum_eq a hc.le z, add_assoc, ← EReal.coe_mul, ← EReal.coe_add]
    rfl
  obtain ⟨C, hC⟩ := coordinate_comparison hu A hρ hv hr hν
  refine ⟨C, ?_⟩
  let Q : Y → ComplexModel (m + 1) := fun z => Φ.toFun (e.val z)
  have hQc : ContinuousAt Q y :=
    (Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.comp
        (e.val.continuousAt (mem_complexChartAt_source y))
  have hQy : Q y = 0 := h0
  have hCt : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      ψ (π (T z)) ≤ φ (π (T z)) + (C : EReal) := hC
  have hCQ : ∀ᶠ z in 𝓝 y, ψ (π (T (Q z))) ≤ φ (π (T (Q z))) + (C : EReal) :=
    (show Tendsto Q (𝓝 y) (𝓝 0) from by rw [← hQy]; exact hQc).eventually hCt
  have hsrcQ : ∀ᶠ z in 𝓝 y, e.val z ∈ Φ.source :=
    (e.val.continuousAt (mem_complexChartAt_source y)).eventually
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  filter_upwards [hCQ, hsrcQ, e.val.open_source.mem_nhds (mem_complexChartAt_source y)]
    with z hz hzΦ hze
  have hTQ : T (Q z) = z := by
    dsimp only [T, Q]
    rw [Φ.left_inv _ hzΦ, e.val.left_inv hze]
  simpa only [hTQ] using hz


/-- Original all-level multiplier order compares exactly to the original
analytic reference, internally using local principalization and fiber descent. -/
theorem moreSingularAt_of_iOrder_analytic_reference
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] {θ ζ : ClosedRealOneOneForm (m + 1) X} {ψ φ : X → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) (hφ : IsThetaPshPotential ζ.val φ)
    (hA : HasManifoldAnalyticSingularityType (n := m + 1) φ)
    (hI : IOrderOnManifold (n := m + 1) ψ φ) (x : X) :
    MoreSingularAt ψ φ x := by
  classical
  obtain ⟨U, hxU, c, N, G, b, B, I, hc, hG, hbound, hformula, hgen, hcoh, _, hne⟩ :=
    ActualLocalAnalyticReferenceIdeal.exists_local_reference_ideal hφ.2 hA x
  let xU : U := ⟨x, hxU⟩
  obtain ⟨V, hxV, Y, T, hpb, hE, hsupp, _⟩ :=
    HironakaLocalPrincipalization.exists_tower_principalization_local
      (X := CMfd.of (n := m + 1) U) hcoh hne
      (K := {xU}) isCompact_singleton
  let xV : V := ⟨xU, hxV (mem_singleton xU)⟩
  let D := BlowupTowerTransforms.exceptionalDivisor T
  let E := (MarkedIdeal.geoTransformAlong
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → U)
      (⟨univ, [], I, 1⟩ : MarkedIdeal (m + 1) U)) T).E
  let j : V → X := fun z => z.val.val
  let τ : Y → X := fun y => j (T.proj y)
  let Gv : Fin N → V → ℂ := fun i z => G i z.val
  let Gy : Fin N → Y → ℂ := fun i y => Gv i (T.proj y)
  let bY : Y → ℝ := fun y => b (T.proj y).val
  have hj : ContMDiff 𝓘(ℂ, ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (m + 1)) ∞ j :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  have hτ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (m + 1)) ∞ τ := hj.comp T.contMDiff_proj
  have hGu (i : Fin N) (z : U) : HolomorphicAt (m + 1) (G i) z :=
    holomorphicAt_of_mdifferentiableOn isOpen_univ (hG i).mdifferentiableOn (mem_univ z)
  have hGv (i : Fin N) (z : V) : HolomorphicAt (m + 1) (Gv i) z :=
    (hGu i z.val).comp_contMDiff
      (Eventually.of_forall fun w => (contMDiff_subtype_val (U := V)).contMDiffAt)
  have hgenV (z : V) (F : V → ℂ) :
      (GermIdeal.pullback (m := m + 1) (Subtype.val : V → U) I).mem z F ↔
        IsInSpanAt (n := m + 1) (· ∈ Set.range Gv) z F :=
    FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun w => (contMDiff_subtype_val (U := V)).contMDiffAt)
      I G (fun i => hGu i z.val) (hgen z.val) F
  have hGy (i : Fin N) (y : Y) : HolomorphicAt (m + 1) (Gy i) y :=
    (hGv i (T.proj y)).comp_contMDiff
      (Eventually.of_forall fun w => T.contMDiff_proj.contMDiffAt)
  have hgenY (y : Y) (F : Y → ℂ) : D.ideal.mem y F ↔
      IsInSpanAt (n := m + 1) (· ∈ Set.range Gy) y F := by
    change (BlowupTowerTransforms.exceptionalDivisor T).ideal.mem y F ↔ _
    rw [← hpb]
    exact FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun w => T.contMDiff_proj.contMDiffAt)
      (GermIdeal.pullback (m := m + 1) (Subtype.val : V → U) I) Gv
      (fun i => hGv i (T.proj y)) (hgenV (T.proj y)) F
  have hformulaY (y : Y) : φ (τ y) = ((c : ℝ) : EReal) * generatorLog Gy y + (bY y : EReal) :=
    hformula (T.proj y).val
  have hbY (y : Y) : BoundedRealGermAt bY y := by
    refine ⟨max B 0, le_max_right _ _, Eventually.of_forall fun z => ?_⟩
    exact (hbound (T.proj z).val).trans (le_max_left _ _)
  have hlocal (y : T.proj ⁻¹' {xV}) : ∃ (C : ℝ) (O : Set Y),
      IsOpen O ∧ (y : Y) ∈ O ∧
        ∀ z ∈ O, ψ (τ z) ≤ φ (τ z) + (C : EReal) := by
    obtain ⟨C, hC⟩ := local_comparison_of_snc_presented hψ hφ hA hI hτ
      D E hE hsupp y Gy (fun i => hGy i y) (hgenY y)
      (show 0 < (c : ℝ) from by exact_mod_cast hc) (hbY y)
      (Eventually.of_forall hformulaY)
    obtain ⟨O, hOsub, hOopen, hyO⟩ := _root_.mem_nhds_iff.mp hC
    exact ⟨C, O, hOopen, hyO, fun z hz => hOsub hz⟩
  choose C O hO hyO hboundO using hlocal
  obtain ⟨t, W, hW, hxW, _, hcover⟩ :=
    ProperFiberFiniteNeighborhoodCover.exists_finite_fiber_cover_target_neighborhood
      (HironakaLocalPrincipalization.isProperMap_proj T)
      (HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence)
      xV O (fun y => ⟨hO y, hyO y⟩)
  have hWimage : IsOpen (j '' W : Set X) := by
    have hi : IsOpen ((Subtype.val : V → U) '' W) := V.isOpen.isOpenMap_subtype_val W hW
    have h : IsOpen ((Subtype.val : U → X) '' ((Subtype.val : V → U) '' W)) :=
      U.isOpen.isOpenMap_subtype_val _ hi
    have heq : (Subtype.val : U → X) '' ((Subtype.val : V → U) '' W) = j '' W := by
      rw [Set.image_image]
    exact heq ▸ h
  have hximage : x ∈ j '' W := ⟨xV, hxW, rfl⟩
  refine ⟨∑ y ∈ t, |C y|, ?_⟩
  filter_upwards [hWimage.mem_nhds hximage] with z hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨y, hyt, a, haO, hfa⟩ := mem_iUnion₂.mp (hcover hw)
  have hCy : C y ≤ ∑ v ∈ t, |C v| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun v _ => abs_nonneg (C v)) hyt)
  have h := hboundO y a haO
  change ψ (j (T.proj a)) ≤ φ (j (T.proj a)) + (C y : EReal) at h
  rw [hfa] at h
  exact h.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hCy))

end
end SGPT.Foundations.Analysis.Pending.ActualAnalyticReferenceLocalExactOrder
