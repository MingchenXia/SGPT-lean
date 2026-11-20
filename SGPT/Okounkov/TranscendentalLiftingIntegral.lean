import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.Foundations.Analysis.Pending.MeteredDivisorGlobalIdeal
import SGPT.Foundations.Analysis.Pending.MeteredDivisorScaling
import SGPT.Foundations.Analysis.Pending.DivisorMetric

/-!
# Integral models of metered effective `ℚ`-divisors

Source: blueprint node `tok:approx-pushforward` (chapter `claude-okounkov-transcendental`), the
step "put `D_k = D + k⁻¹ E`" of DRWNXZ Proposition 4.4: the pushforward theorem
(`TranscendentalRelGen.PushforwardAnalyticStatement`, DRWNXZ Lemma 2.8) is stated for
`c [D]` with `c ∈ ℚ_{>0}` and `D` an (integral) effective divisor with a smooth metric, while the
divisors produced on a blow-up (`D + k⁻¹ E`, `E` the exceptional `ℚ`-divisor of the Blanchard
forms) are metered effective `ℚ`-divisors (`MeteredEffectiveQDivisor`: locally
`ψ_E = ∑ aᵢ log |gᵢ|² + h`, `aᵢ ∈ ℚ_{≥0}`).

* `exists_integralModel`: on a compact complex manifold, for every metered effective
  `ℚ`-divisor `E` there are `q ∈ ℕ_{>0}` and an effective divisor `D` (an invertible ideal sheaf)
  such that `q E` (`MeteredDivisorScaling.smul`, weight `q ψ_E`, curvature `q Θ_E`) is a smooth
  metric of `D` (`DivisorMetric.IsDivisorMetric D (q E)`). So `E = q⁻¹ D` with its metric.
  The local generators are TN's uniform single-generator presentation
  (`MeteredDivisorSingleGenerator.exists_uniformDenominator`), and the Riemann-extension step
  `MeteredDivisorGlobalIdeal.isInSpanAt_iff_of_sameSingularityTypeAt` makes the local principal
  ideals glue (the same argument as TN's
  `exists_invertible_hasAnalyticSingularitiesOfType_of_presentation`,
  which keeps the ideal internal).
* `isThetaPshPotential_weight`: the weight of a metered effective `ℚ`-divisor on a compact
  manifold is a `Θ_E`-psh potential (`[E] = Θ_E + dd^c ψ_E ≥ 0`, and `ψ_E` is nowhere locally
  `-∞`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MeteredDivisorSingleGenerator
open SGPT.Foundations.Analysis.Pending.MeteredDivisorGlobalIdeal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `q ((1/q) L + h) = L + q h` in `EReal`, for `q > 0` and `h` real. -/
theorem ereal_mul_inv_mul_add {q : ℝ} (hq : 0 < q) (L : EReal) (h : ℝ) :
    (q : EReal) * (((1 / q : ℝ) : EReal) * L + (h : EReal)) = L + ((q * h : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hq.le) (EReal.coe_ne_top q),
    ← mul_assoc, ← EReal.coe_mul, mul_one_div_cancel hq.ne', EReal.coe_one, one_mul,
    ← EReal.coe_mul]

/-- **Integral model of a metered effective `ℚ`-divisor.** On a compact complex manifold, every
metered effective `ℚ`-divisor `E` is `q⁻¹` times a metered (integral) effective divisor: there
are `q > 0` and an effective divisor `D` such that `q E` is a smooth metric of `D`. -/
theorem exists_integralModel [CompactSpace M] (E : MeteredEffectiveQDivisor n M) :
    ∃ q : ℕ, 0 < q ∧ ∃ D : EffectiveDivisor n M,
      DivisorMetric.IsDivisorMetric D
        (MeteredDivisorScaling.smul (c := (q : ℚ)) (Nat.cast_nonneg q) E) := by
  classical
  obtain ⟨q, hqpos, hdata⟩ := exists_uniformDenominator E
  choose U hUopen hxU G hsm hGdiff hGne hhsmooth hweight using hdata
  set c : ℝ := 1 / (q : ℝ) with hc
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcont : ∀ x : M, ∀ z ∈ U x, ContinuousAt (hsm x) z := fun x z hz =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (hUopen x) (hhsmooth x) hz
  -- the germ ideal at a point does not depend on which local generator presents it
  have hagree : ∀ (x z : M), z ∈ U x → ∀ v : M → ℂ,
      IsInSpanAt (n := n) (· = G z) z v ↔ IsInSpanAt (n := n) (· = G x) z v := by
    intro x z hz v
    have hopen : IsOpen (U z ∩ U x) := (hUopen z).inter (hUopen x)
    have hmem : z ∈ U z ∩ U x := ⟨hxU z, hz⟩
    refine isInSpanAt_iff_of_sameSingularityTypeAt hopen
      ((hGdiff z).mono inter_subset_left) ((hGdiff x).mono inter_subset_right)
      (NowhereIdenticallyZeroOn.mono (hGne z) inter_subset_left)
      (NowhereIdenticallyZeroOn.mono (hGne x) inter_subset_right) hmem ?_ v
    refine sameSingularityTypeAt_of_weight_eq hcpos (hopen.mem_nhds hmem) ?_
      (hcont z z (hxU z)) (hcont x z hz)
    intro y hy
    rw [← hweight z y hy.1, ← hweight x y hy.2]
  let 𝔞 : GermIdeal n M := ⟨fun y v => IsInSpanAt (n := n) (· = G y) y v⟩
  have hinv : 𝔞.IsInvertible := fun x =>
    ⟨U x, hUopen x, hxU x, G x, hGdiff x, hGne x, fun y hy v => hagree x y hy v⟩
  refine ⟨q, hqpos, ⟨𝔞, hinv⟩, fun x => ?_⟩
  refine ⟨U x, hUopen x, hxU x, G x, hGdiff x, fun y hy f => hagree x y hy f,
    fun y => (q : ℝ) * hsm x y, fun e => contDiffOn_const.mul (hhsmooth x e), ?_⟩
  intro y hy
  rw [MeteredDivisorScaling.weight_smul, hweight x y hy, Rat.cast_natCast]
  exact ereal_mul_inv_mul_add hqR _ _

/-- The weight of a metered effective `ℚ`-divisor on a compact manifold is a `Θ_E`-psh
potential: `[E] = Θ_E + dd^c ψ_E ≥ 0` and `ψ_E` is not `-∞` on any nonempty open set. -/
theorem isThetaPshPotential_weight [CompactSpace M] (E : MeteredEffectiveQDivisor n M) :
    IsThetaPshPotential E.curvature.val E.weight := by
  refine ⟨MeteredDivisorPositivity.thetaPlurisubharmonic_weight E, ?_⟩
  obtain ⟨q, hq, D, hD⟩ := exists_integralModel E
  have h := (isThetaPshPotential_effectiveDivisorMetric D _ hD).2
  intro x V hV hxV
  obtain ⟨y, hyV, hy⟩ := h x V hV hxV
  refine ⟨y, hyV, fun hbot => hy ?_⟩
  rw [MeteredDivisorScaling.weight_smul, hbot]
  have hqR : (0 : EReal) < (((q : ℚ) : ℝ) : EReal) := by
    rw [Rat.cast_natCast]
    exact_mod_cast hq
  exact EReal.mul_bot_of_pos hqR

end SGPT.Okounkov.TranscendentalLifting
