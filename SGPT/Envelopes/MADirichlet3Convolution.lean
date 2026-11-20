import SGPT.Envelopes.MADirichlet3Energy
import SGPT.Envelopes.MADirichlet2Affine

/-!
# Convolution of a measure with the radial kernels

Toward FPT `prop:canonical-grid-energy-control` in the convolution variant of lane MA-DIR2
(blueprint `claude-ma-dir2:route`): instead of FPT's cube averages of a compactly supported
measure `α`, we use the convolutions `α ∗ ρⱼ` with TN's explicit radial kernels
`ρⱼ = explicitRadialKernel r hr j` (smooth, nonnegative, integral one, supported in the closed
ball of radius `r/(j+1)`).

* `le_integral_mul_explicitRadialKernel`: the **sub-mean value inequality** for these kernels:
  for `u` locally bounded plurisubharmonic on `Ω` and `B̄(z, 2r) ⊆ Ω`,
  `u(z) ≤ ∫ u(x) ρⱼ(x - z) dx` (TN's radial regularizations decrease to `u`).
* `convDensity α r hr j`, the density `x ↦ ∫ ρⱼ(x - t) dα(t)` of `α ∗ ρⱼ`: smooth
  (`contDiff_convDensity`), nonnegative, vanishing off `cthickening r K` if `α` is carried by `K`.
* `lintegral_convDensity_mul_le`: for `U ≤ 0` plurisubharmonic on `Ω ⊇ cthickening (2r) K`,
  `∫ (-U) (α ∗ ρⱼ) dV ≤ ∫ (-U) dα`. This replaces FPT's polydisc estimate
  `eq:canonical-grid-polydisc-average` for `p = 1`, with the constant `D_{n,1} = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff Convolution

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-- **Sub-mean value inequality for the explicit radial kernels**: if `u` is locally bounded
plurisubharmonic on `Ω` and `B̄(z, 2r) ⊆ Ω`, then `u(z) ≤ ∫ u(x) ρⱼ(x - z) dx`. -/
theorem le_integral_mul_explicitRadialKernel {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {r : ℝ} (hr : 0 < r)
    {z : ComplexModel n} (hz : closedBall z (2 * r) ⊆ Ω) (j : ℕ) :
    u z ≤ ∫ x, u x * explicitRadialKernel r hr j (x - z) := by
  set N : Set (ComplexModel n) := ball z r with hNdef
  set Kc : Set (ComplexModel n) := closedBall z (2 * r) with hKcdef
  have hNΩ : N ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hz)
  have hball : ∀ x ∈ N, closedBall x r ⊆ Kc := fun x hx =>
    closedBall_subset_closedBall' (by rw [mem_ball] at hx; linarith)
  obtain ⟨S, hSk⟩ := exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh hu hr
    isOpen_ball hNΩ (isCompact_closedBall z (2 * r)) hz hball
  have hpL : LocallyIntegrableOn u Ω volume := locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hpLevi := hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1
  set f : ℕ → ComplexModel n → ℝ := fun j =>
    translationPairing volume (Kc.indicator u) (S.kernel j) with hfdef
  have hfPsh : ∀ j, PlurisubharmonicOn (fun x => (f j x : EReal))
      ((⟨N, isOpen_ball⟩ : Opens (ComplexModel n)) : Set (ComplexModel n)) := fun j =>
    (discPshOn_translationPairing_indicator hpL hpLevi (S.kernel_hasCompactSupport j)
      (S.kernel_contDiff j) (S.kernel_nonneg j) (isCompact_closedBall _ _) hz
      (S.translated_tsupport j)).plurisubharmonicOn isOpen_ball
  have hpoint := tendsto_everywhere_of_ae_of_antitone_psh (U := ⟨N, isOpen_ball⟩)
    (hu.1.mono hNΩ) hfPsh (fun x hx => S.antitone_pairing x hx) S.ae_tendsto_pairing
  have hzN : z ∈ N := mem_ball_self hr
  have hle : u z ≤ f j z :=
    (S.antitone_pairing z hzN).le_of_tendsto (hpoint z hzN) j
  have heq : f j z = ∫ x, u x * explicitRadialKernel r hr j (x - z) := by
    simp only [hfdef, translationPairing, hSk]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : explicitRadialKernel r hr j (x - z) = 0
    · simp [hx]
    · have hxs : x - z ∈ closedBall (0 : ComplexModel n) (r / ((j : ℝ) + 1)) := by
        rw [← explicitRadialKernel_tsupport r hr j]
        exact subset_tsupport _ hx
      have hxz : x ∈ Kc := by
        rw [hKcdef, mem_closedBall, dist_eq_norm]
        rw [mem_closedBall, dist_zero_right] at hxs
        have h1 : r / ((j : ℝ) + 1) ≤ r := div_le_self hr.le (by linarith [j.cast_nonneg (α := ℝ)])
        linarith
      simp [indicator_of_mem hxz]
  rw [← heq]
  exact hle

/-- The density `x ↦ ∫ ρⱼ(x - t) dα(t)` of the convolution `α ∗ ρⱼ`. -/
def convDensity (α : Measure (ComplexModel n)) (r : ℝ) (hr : 0 < r) (j : ℕ)
    (x : ComplexModel n) : ℝ :=
  ∫ t, explicitRadialKernel r hr j (x - t) ∂α

theorem convDensity_eq_convolution (α : Measure (ComplexModel n)) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    convDensity α r hr j =
      (fun _ => (1 : ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, α] explicitRadialKernel r hr j := by
  funext x
  simp only [convDensity, convolution_def, ContinuousLinearMap.mul_apply', one_mul]

theorem contDiff_convDensity (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {r : ℝ}
    (hr : 0 < r) (j : ℕ) : ContDiff ℝ ∞ (convDensity α r hr j) := by
  rw [convDensity_eq_convolution]
  exact (explicitRadialKernel_hasCompactSupport r hr j).contDiff_convolution_right _
    (locallyIntegrable_const 1) (explicitRadialKernel_contDiff r hr j)

theorem convDensity_nonneg (α : Measure (ComplexModel n)) {r : ℝ} (hr : 0 < r) (j : ℕ)
    (x : ComplexModel n) : 0 ≤ convDensity α r hr j x :=
  integral_nonneg fun _ => explicitRadialKernel_nonneg r hr j _

theorem explicitRadialKernel_eq_zero_of_lt {r : ℝ} (hr : 0 < r) (j : ℕ) {y : ComplexModel n}
    (hy : r < ‖y‖) : explicitRadialKernel r hr j y = 0 := by
  by_contra h
  have hys : y ∈ closedBall (0 : ComplexModel n) (r / ((j : ℝ) + 1)) := by
    rw [← explicitRadialKernel_tsupport r hr j]
    exact subset_tsupport _ h
  rw [mem_closedBall, dist_zero_right] at hys
  have h1 : r / ((j : ℝ) + 1) ≤ r := div_le_self hr.le (by linarith [j.cast_nonneg (α := ℝ)])
  linarith

/-- If `α` is carried by `K`, the density of `α ∗ ρⱼ` vanishes off `cthickening r K`. -/
theorem convDensity_eq_zero_of_notMem (α : Measure (ComplexModel n)) {K : Set (ComplexModel n)}
    (hαK : α Kᶜ = 0) {r : ℝ} (hr : 0 < r) (j : ℕ) {x : ComplexModel n}
    (hx : x ∉ cthickening r K) : convDensity α r hr j x = 0 := by
  have hae : ∀ᵐ t ∂α, explicitRadialKernel r hr j (x - t) = 0 := by
    have hK : ∀ᵐ t ∂α, t ∈ K := measure_eq_zero_iff_ae_notMem.mp hαK |>.mono fun t ht => by
      simpa using ht
    filter_upwards [hK] with t ht
    refine explicitRadialKernel_eq_zero_of_lt hr j ?_
    by_contra hle
    push Not at hle
    exact hx (mem_cthickening_of_dist_le x t r K ht (by rwa [dist_eq_norm]))
  rw [convDensity, integral_eq_zero_of_ae hae]

theorem support_convDensity_subset (α : Measure (ComplexModel n)) {K : Set (ComplexModel n)}
    (hαK : α Kᶜ = 0) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    Function.support (convDensity α r hr j) ⊆ cthickening r K := fun x hx => by
  by_contra h
  exact hx (convDensity_eq_zero_of_notMem α hαK hr j h)

theorem exists_bound_explicitRadialKernel {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∃ C, ∀ y : ComplexModel n, ‖explicitRadialKernel r hr j y‖ ≤ C :=
  (explicitRadialKernel_contDiff r hr j).continuous.bounded_above_of_compact_support
    (explicitRadialKernel_hasCompactSupport r hr j)

theorem integrable_explicitRadialKernel_sub (α : Measure (ComplexModel n)) [IsFiniteMeasure α]
    {r : ℝ} (hr : 0 < r) (j : ℕ) (x : ComplexModel n) :
    Integrable (fun t => explicitRadialKernel r hr j (x - t)) α := by
  obtain ⟨C, hC⟩ := exists_bound_explicitRadialKernel (n := n) hr j
  exact Integrable.of_bound ((explicitRadialKernel_contDiff r hr j).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable C
    (Eventually.of_forall fun t => hC _)

/-- **Energy comparison for the convolution** (the role of FPT
`eq:canonical-grid-polydisc-average` for `p = 1`, here with constant `1`): if the finite measure
`α` is carried by `K`, `cthickening (2r) K ⊆ Ω` and `U ≤ 0` is locally bounded plurisubharmonic
on `Ω`, then `∫_Ω (-U) (α ∗ ρⱼ) dV ≤ ∫_Ω (-U) dα`. -/
theorem lintegral_convDensity_mul_le {Ω : Opens (ComplexModel n)} (α : Measure (ComplexModel n))
    [IsFiniteMeasure α] {K : Set (ComplexModel n)} (hαK : α Kᶜ = 0) {r : ℝ} (hr : 0 < r)
    (hKΩ : cthickening (2 * r) K ⊆ Ω) {U : ComplexModel n → ℝ} (hU : IsLocallyBoundedPshOn Ω U)
    (hU0 : ∀ z ∈ Ω, U z ≤ 0) (j : ℕ) :
    ∫⁻ x in (Ω : Set (ComplexModel n)),
        ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (-U x) ≤
      ∫⁻ t in (Ω : Set (ComplexModel n)), ENNReal.ofReal (-U t) ∂α := by
  set Ũ : ComplexModel n → ℝ := (Ω : Set (ComplexModel n)).indicator U with hŨdef
  have hŨm : Measurable Ũ := measurable_indicator_of_plurisubharmonicOn hU.1
  have hΩm : MeasurableSet (Ω : Set (ComplexModel n)) := Ω.isOpen.measurableSet
  set ρ := explicitRadialKernel (n := n) r hr j with hρdef
  have hρc : Continuous ρ := (explicitRadialKernel_contDiff r hr j).continuous
  have hpL : LocallyIntegrableOn U Ω volume := locallyIntegrableOn_of_plurisubharmonicOn_real hU.1
  -- rewrite both sides with the global function `Ũ`
  have hL : ∫⁻ x in (Ω : Set (ComplexModel n)),
        ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (-U x) ≤
      ∫⁻ x, ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (-Ũ x) := by
    rw [setLIntegral_congr_fun hΩm (g := fun x =>
      ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (-Ũ x))
      (fun x hx => by simp only [hŨdef, indicator_of_mem hx])]
    exact setLIntegral_le_lintegral _ _
  have hR : ∫⁻ t in (Ω : Set (ComplexModel n)), ENNReal.ofReal (-U t) ∂α =
      ∫⁻ t, ENNReal.ofReal (-Ũ t) ∂α := by
    rw [← lintegral_indicator hΩm]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ (Ω : Set (ComplexModel n))
    · simp [hŨdef, indicator_of_mem ht]
    · simp [hŨdef, indicator_of_notMem ht]
  refine hL.trans (le_of_le_of_eq ?_ hR.symm)
  -- Tonelli
  have hdens : ∀ x, ENNReal.ofReal (convDensity α r hr j x) = ∫⁻ t, ENNReal.ofReal (ρ (x - t)) ∂α :=
    fun x => ofReal_integral_eq_lintegral_ofReal (integrable_explicitRadialKernel_sub α hr j x)
      (Eventually.of_forall fun t => explicitRadialKernel_nonneg r hr j _)
  have hmeas : AEMeasurable (Function.uncurry fun (x t : ComplexModel n) =>
      ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (-Ũ x)) (volume.prod α) :=
    ((ENNReal.measurable_ofReal.comp (hρc.measurable.comp (measurable_fst.sub measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (hŨm.neg.comp measurable_fst))).aemeasurable
  calc ∫⁻ x, ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (-Ũ x)
      = ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (-Ũ x) ∂α := by
        refine lintegral_congr fun x => ?_
        rw [hdens, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (-Ũ x) ∂volume ∂α :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ t, ENNReal.ofReal (-Ũ t) ∂α := by
        refine lintegral_mono_ae ?_
        have hK : ∀ᵐ t ∂α, t ∈ K := measure_eq_zero_iff_ae_notMem.mp hαK |>.mono fun t ht => by
          simpa using ht
        filter_upwards [hK] with t ht
        have hball : closedBall t (2 * r) ⊆ Ω :=
          (closedBall_subset_cthickening ht _).trans hKΩ
        have htΩ : t ∈ (Ω : Set (ComplexModel n)) := hball (mem_closedBall_self (by linarith))
        have hsub : closedBall t r ⊆ Ω :=
          (closedBall_subset_closedBall (by linarith)).trans hball
        -- the integrand vanishes off `B̄(t, r)`
        have hzero : ∀ x, x ∉ closedBall t r → ρ (x - t) * -Ũ x = 0 := by
          intro x hx
          rw [mem_closedBall, dist_eq_norm, not_le] at hx
          have h0 : ρ (x - t) = 0 := explicitRadialKernel_eq_zero_of_lt hr j hx
          rw [h0, zero_mul]
        have hint : Integrable (fun x => ρ (x - t) * -Ũ x) := by
          refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hzero
          have hUi : IntegrableOn U (closedBall t r) :=
            (hpL.mono_set hsub).integrableOn_isCompact (isCompact_closedBall t r)
          have hŨi : IntegrableOn (fun x => -Ũ x) (closedBall t r) := by
            refine (hUi.neg).congr_fun (fun x hx => ?_) measurableSet_closedBall
            simp only [hŨdef, indicator_of_mem (hsub hx), Pi.neg_apply]
          obtain ⟨C, hC⟩ := exists_bound_explicitRadialKernel (n := n) hr j
          have hρt : Continuous fun x => ρ (x - t) := hρc.comp (continuous_id.sub continuous_const)
          exact hŨi.bdd_mul (f := fun x => ρ (x - t)) hρt.aestronglyMeasurable
            (Eventually.of_forall fun x => hC _)
        calc ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (-Ũ x)
            = ∫⁻ x, ENNReal.ofReal (ρ (x - t) * -Ũ x) := by
              refine lintegral_congr fun x => ?_
              rw [ENNReal.ofReal_mul (explicitRadialKernel_nonneg r hr j _)]
          _ = ENNReal.ofReal (∫ x, ρ (x - t) * -Ũ x) := by
              refine (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => ?_)).symm
              refine mul_nonneg (explicitRadialKernel_nonneg r hr j _) ?_
              by_cases hx : x ∈ (Ω : Set (ComplexModel n))
              · simp only [hŨdef, indicator_of_mem hx]; linarith [hU0 x hx]
              · simp [hŨdef, indicator_of_notMem hx]
          _ ≤ ENNReal.ofReal (-Ũ t) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have heq : ∫ x, ρ (x - t) * -Ũ x = -∫ x, U x * ρ (x - t) := by
                rw [← integral_neg]
                refine integral_congr_ae (Eventually.of_forall fun x => ?_)
                by_cases hx : x ∈ closedBall t r
                · show ρ (x - t) * -Ũ x = -(U x * ρ (x - t))
                  simp only [hŨdef, indicator_of_mem (hsub hx)]; ring
                · rw [mem_closedBall, dist_eq_norm, not_le] at hx
                  have h0 : ρ (x - t) = 0 := explicitRadialKernel_eq_zero_of_lt hr j hx
                  show ρ (x - t) * -Ũ x = -(U x * ρ (x - t))
                  rw [h0]
                  ring
              rw [heq, hŨdef, indicator_of_mem htΩ, neg_le_neg_iff]
              exact le_integral_mul_explicitRadialKernel hU hr hball j

/-- The radial kernels form an approximate identity at every point of continuity:
`∫ h(x) ρⱼ(x - t) dx → h(t)` for continuous `h`. -/
theorem tendsto_integral_mul_explicitRadialKernel {r : ℝ} (hr : 0 < r)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (t : ComplexModel n) :
    Tendsto (fun j : ℕ => ∫ x, h x * explicitRadialKernel r hr j (x - t)) atTop (𝓝 (h t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hηh⟩ := Metric.continuous_iff.mp hc t (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (r / η)
  refine ⟨N, fun j hj => ?_⟩
  set ρ := explicitRadialKernel (n := n) r hr j with hρdef
  have hρi : Integrable ρ := (explicitRadialKernel_contDiff r hr j).continuous.integrable_of_hasCompactSupport
    (explicitRadialKernel_hasCompactSupport r hr j)
  have hρ1 : ∫ y, ρ y = 1 := explicitRadialKernel_integral_one r hr j
  have hshift : ∫ x, h x * ρ (x - t) = ∫ y, h (t + y) * ρ y := by
    rw [← integral_add_left_eq_self (fun x => h x * ρ (x - t)) t]
    simp only [add_sub_cancel_left]
  have hrad : r / ((j : ℝ) + 1) < η := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη] at hN
    have : (N : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hρ0 : ∀ y, 0 ≤ ρ y := explicitRadialKernel_nonneg r hr j
  have hbound : ∀ y, ‖ρ y * (h (t + y) - h t)‖ ≤ ρ y * (ε / 2) := by
    intro y
    rw [norm_mul, Real.norm_eq_abs (ρ y), abs_of_nonneg (hρ0 y)]
    by_cases hy : ρ y = 0
    · rw [hy, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (hρ0 y)
      have hys : y ∈ closedBall (0 : ComplexModel n) (r / ((j : ℝ) + 1)) := by
        rw [← explicitRadialKernel_tsupport r hr j]
        exact subset_tsupport _ hy
      rw [mem_closedBall, dist_zero_right] at hys
      have := hηh (t + y) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
      rw [dist_eq_norm] at this
      exact this.le
  have hcont2 : Continuous fun y => h (t + y) - h t :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  obtain ⟨B, hB⟩ := (explicitRadialKernel_contDiff r hr j).continuous.bounded_above_of_compact_support
    (explicitRadialKernel_hasCompactSupport (n := n) r hr j)
  have hint2 : Integrable fun y => ρ y * (h (t + y) - h t) := by
    refine (hρi.mul_const (ε / 2)).mono' (hρi.aestronglyMeasurable.mul
      hcont2.aestronglyMeasurable) (Eventually.of_forall hbound)
  have heq : (∫ x, h x * ρ (x - t)) - h t = ∫ y, ρ y * (h (t + y) - h t) := by
    rw [hshift]
    have h1 : ∫ y, ρ y * (h (t + y) - h t) = (∫ y, h (t + y) * ρ y) - ∫ y, h t * ρ y := by
      rw [← integral_sub]
      · exact integral_congr_ae (Eventually.of_forall fun y => by ring)
      · refine (hint2.add (hρi.const_mul (h t))).congr (Eventually.of_forall fun y => ?_)
        simp only [Pi.add_apply]
        ring
      · exact hρi.const_mul _
    rw [h1, integral_const_mul, hρ1, mul_one]
  rw [Real.dist_eq, heq]
  calc |∫ y, ρ y * (h (t + y) - h t)| = ‖∫ y, ρ y * (h (t + y) - h t)‖ := rfl
    _ ≤ ∫ y, ρ y * (ε / 2) := norm_integral_le_of_norm_le (hρi.mul_const _)
        (Eventually.of_forall hbound)
    _ = ε / 2 := by rw [integral_mul_const, hρ1, one_mul]
    _ < ε := by linarith

/-- **Weak convergence of the convolutions** `α ∗ ρⱼ → α` (FPT
`prop:canonical-grid-energy-control`, "`μⱼ → μ` weakly", for the convolution variant): for every
continuous `h` with compact support, `∫ h (α ∗ ρⱼ) dV → ∫ h dα`. -/
theorem tendsto_integral_mul_convDensity (α : Measure (ComplexModel n)) [IsFiniteMeasure α]
    {r : ℝ} (hr : 0 < r) {h : ComplexModel n → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) :
    Tendsto (fun j : ℕ => ∫ x, h x * convDensity α r hr j x) atTop (𝓝 (∫ t, h t ∂α)) := by
  have hhi : Integrable h := hc.integrable_of_hasCompactSupport hcs
  obtain ⟨Bh, hBh⟩ := hc.bounded_above_of_compact_support hcs
  have hswap : ∀ j : ℕ, ∫ x, h x * convDensity α r hr j x =
      ∫ t, ∫ x, h x * explicitRadialKernel r hr j (x - t) ∂volume ∂α := by
    intro j
    obtain ⟨B, hB⟩ := exists_bound_explicitRadialKernel (n := n) hr j
    have hρc : Continuous (explicitRadialKernel (n := n) r hr j) :=
      (explicitRadialKernel_contDiff r hr j).continuous
    have hint : Integrable (Function.uncurry fun (x t : ComplexModel n) =>
        h x * explicitRadialKernel r hr j (x - t)) (volume.prod α) := by
      have hdom : Integrable (fun z : ComplexModel n × ComplexModel n => (B * ‖h z.1‖) * 1)
          (volume.prod α) := (hhi.norm.const_mul B).mul_prod (integrable_const 1)
      refine hdom.mono' ((hc.comp continuous_fst).mul (hρc.comp
        (continuous_fst.sub continuous_snd))).aestronglyMeasurable (Eventually.of_forall ?_)
      rintro ⟨x, t⟩
      show ‖h x * explicitRadialKernel r hr j (x - t)‖ ≤ B * ‖h x‖ * 1
      rw [norm_mul, mul_one, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    rw [← integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [convDensity]
    rw [← integral_const_mul]
  simp_rw [hswap]
  refine tendsto_integral_of_dominated_convergence (fun _ => Bh) (fun j => ?_)
    (integrable_const Bh) (fun j => Eventually.of_forall fun t => ?_)
    (Eventually.of_forall fun t => tendsto_integral_mul_explicitRadialKernel hr hc t)
  · -- measurability of the inner integrals: they are continuous in `t`
    have hρc : Continuous (explicitRadialKernel (n := n) r hr j) :=
      (explicitRadialKernel_contDiff r hr j).continuous
    have hcont : Continuous fun t => ∫ x, h x * explicitRadialKernel r hr j (x - t) := by
      have heq : (fun t => ∫ x, h x * explicitRadialKernel r hr j (x - t)) =
          fun t => ∫ y, h (t + y) * explicitRadialKernel r hr j y := by
        funext t
        rw [← integral_add_left_eq_self (fun x => h x * explicitRadialKernel r hr j (x - t)) t]
        simp only [add_sub_cancel_left]
      rw [heq]
      refine continuous_of_dominated (bound := fun y => Bh * ‖explicitRadialKernel r hr j y‖)
        (fun t => ((hc.comp (continuous_const.add continuous_id)).mul hρc).aestronglyMeasurable)
        (fun t => Eventually.of_forall fun y => ?_) ?_ (Eventually.of_forall fun y =>
          (hc.comp (continuous_id.add continuous_const)).mul continuous_const)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hBh _) (norm_nonneg _)
      · exact (hρc.integrable_of_hasCompactSupport
          (explicitRadialKernel_hasCompactSupport r hr j)).norm.const_mul Bh
    exact hcont.aestronglyMeasurable
  · -- the uniform bound
    have hρi : Integrable (explicitRadialKernel (n := n) r hr j) :=
      (explicitRadialKernel_contDiff r hr j).continuous.integrable_of_hasCompactSupport
        (explicitRadialKernel_hasCompactSupport r hr j)
    have hshift : ∫ x, h x * explicitRadialKernel r hr j (x - t) =
        ∫ y, h (t + y) * explicitRadialKernel r hr j y := by
      rw [← integral_add_left_eq_self (fun x => h x * explicitRadialKernel r hr j (x - t)) t]
      simp only [add_sub_cancel_left]
    rw [hshift]
    calc ‖∫ y, h (t + y) * explicitRadialKernel r hr j y‖
        ≤ ∫ y, Bh * explicitRadialKernel r hr j y :=
          norm_integral_le_of_norm_le (hρi.const_mul Bh) (Eventually.of_forall fun y => by
            rw [norm_mul, Real.norm_eq_abs (explicitRadialKernel r hr j y),
              abs_of_nonneg (explicitRadialKernel_nonneg r hr j y)]
            exact mul_le_mul_of_nonneg_right (hBh _) (explicitRadialKernel_nonneg r hr j y))
      _ = Bh := by rw [integral_const_mul, explicitRadialKernel_integral_one, mul_one]

end SGPT.Envelopes.MADirichlet
