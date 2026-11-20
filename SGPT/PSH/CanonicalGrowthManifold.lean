import SGPT.PSH.CanonicalAnalyticGrowthGerm
import SGPT.PSH.UniformRationalAnalyticCoefficient
import SGPT.PSH.OriginalAnalyticConventions
import SGPT.Foundations.Analysis.Pending.BoundedMultiplierGeneratorWeight
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient
import SGPT.Foundations.Analysis.Pending.EuclideanHolomorphicGermSpan
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

set_option autoImplicit false
noncomputable section

/-! # Canonical growth on the original manifold

Source: SGPT Chapter 1, `def:Iinfty`, normalized by the same positive rational
coefficient of `def:neatanasing`. The actual existing bounded weighted germ
object is reused, with exact original logarithmic-bound and chart dictionaries.
Pointwise finite generation is distinct from nearby uniform generation and
coherence.
-/

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient
open SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierIdeal
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original unnormalized infinity ideal, on genuine holomorphic germs. -/
abbrev inftyIdeal (u : M → EReal) : GermIdeal n M := boundedMultiplierIdeal u

omit [TopologicalSpace M] in
private theorem singleton_generatorLog (h : M → ℂ) (y : M) :
    generatorLog (fun _ : Fin 1 => h) y = logNormSq (h y) := by
  rw [generatorLog_eq_log_sum]
  simp [logNormSq]

/-- The exponential dictionary is valid at both extended-real endpoints. -/
theorem density_le_exp_of_original_log_bound {X : Type*}
    {u : X → EReal} {h : X → ℂ} {y : X} {D : ℝ}
    (hle : logNormSq (h y) ≤ u y + (D : EReal)) :
    multiplierDensity u 1 h y ≤ ENNReal.ofReal (Real.exp D) := by
  by_cases hh0 : h y = 0
  · simp [multiplierDensity, hh0]
  cases huy : u y with
  | bot =>
    have hbot : logNormSq (h y) = ⊥ := le_bot_iff.mp (by simpa [huy] using hle)
    exact False.elim (hh0 ((logNormSq_eq_bot_iff _).mp hbot))
  | top => simp [multiplierDensity, huy]
  | coe t =>
    have hr : Real.log (‖h y‖ ^ 2) ≤ t + D := by
      rw [logNormSq_of_ne_zero hh0, huy, ← EReal.coe_add] at hle
      exact EReal.coe_le_coe_iff.mp hle
    have hsq : 0 < ‖h y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh0)
    have hnorm : ‖h y‖ ^ 2 ≤ Real.exp (t + D) := by
      simpa only [Real.exp_log hsq] using Real.exp_le_exp.mpr hr
    have hreal : ‖h y‖ ^ 2 * Real.exp (-t) ≤ Real.exp D := by
      calc ‖h y‖ ^ 2 * Real.exp (-t) ≤ Real.exp (t + D) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    simpa only [multiplierDensity, huy, multiplierWeight_coe, one_mul,
      ← ENNReal.ofReal_mul (sq_nonneg (‖h y‖))] using ENNReal.ofReal_le_ofReal hreal

/-- Literal source membership `log |h|² ≤ u + C`, with no normalization. -/
theorem mem_inftyIdeal_iff_log_bound {u : M → EReal} {x : M} {h : M → ℂ} :
    (inftyIdeal (n := n) u).mem x h ↔
      HolomorphicAt n h x ∧ MoreSingularAt (fun y => logNormSq (h y)) u x := by
  constructor
  · intro hh
    obtain ⟨D, hD⟩ := BoundedMultiplierGeneratorWeight.exists_generatorLog_le_weight_add
      (h := fun _ : Fin 1 => h) (fun _ => hh)
    exact ⟨hh.1, D, hD.mono fun y hy => by simpa only [singleton_generatorLog] using hy⟩
  · rintro ⟨hh, D, hD⟩
    exact ⟨hh, Real.exp D, Real.exp_pos _,
      hD.mono fun _ hy => density_le_exp_of_original_log_bound hy⟩

/-- Zero is a genuine member, including at every pole. -/
theorem inftyIdeal_zero_mem (u : M → EReal) (x : M) :
    (inftyIdeal (n := n) u).mem x (fun _ => 0) := by
  refine ⟨holomorphicAt_const 0, 1, zero_lt_one, ?_⟩
  exact Eventually.of_forall fun y => by simp [multiplierDensity]

/-- Addition closes the original logarithmic growth condition. -/
theorem inftyIdeal_add_mem {u : M → EReal} {x : M} {h k : M → ℂ}
    (hh : (inftyIdeal (n := n) u).mem x h)
    (hk : (inftyIdeal (n := n) u).mem x k) :
    (inftyIdeal (n := n) u).mem x (fun y => h y + k y) := by
  let G : Fin 2 → M → ℂ := ![h, k]
  have hG : ∀ i, (boundedMultiplierIdeal (n := n) u).mem x (G i) := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨D, hD⟩ := BoundedMultiplierGeneratorWeight.exists_generatorLog_le_weight_add hG
  apply mem_inftyIdeal_iff_log_bound.mpr
  refine ⟨hh.1.add hk.1, D + Real.log 2, ?_⟩
  filter_upwards [hD] with y hy
  have hsq : generatorNormSq (fun _ : Fin 1 => fun z => h z + k z) y ≤
      2 * generatorNormSq G y := by
    simp only [generatorNormSq, Fin.sum_univ_one, Fin.sum_univ_two, G,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [norm_add_le (h y) (k y), norm_nonneg (h y), norm_nonneg (k y),
      norm_nonneg (h y + k y), sq_nonneg (‖h y‖ - ‖k y‖)]
  have hl := IdealWeightComparison.generatorLog_le_add_of_generatorNormSq_le
    (by norm_num : (0 : ℝ) < 2) hsq
  rw [singleton_generatorLog] at hl
  calc logNormSq (h y + k y) ≤ generatorLog G y + (Real.log 2 : EReal) := hl
    _ ≤ (u y + (D : EReal)) + (Real.log 2 : EReal) := add_le_add hy le_rfl
    _ = _ := by rw [EReal.coe_add, add_assoc]

/-- Multiplication by a holomorphic germ closes original infinity membership. -/
theorem inftyIdeal_mul_mem {u : M → EReal} {x : M} {a h : M → ℂ}
    (ha : HolomorphicAt n a x) (hh : (inftyIdeal (n := n) u).mem x h) :
    (inftyIdeal (n := n) u).mem x (fun y => a y * h y) := by
  obtain ⟨_, D, hD⟩ := mem_inftyIdeal_iff_log_bound.mp hh
  have hab : ∀ᶠ y in 𝓝 x, ‖a y‖ ≤ ‖a x‖ + 1 := by
    exact (ha.continuousAt.norm.eventually (gt_mem_nhds (by linarith : ‖a x‖ < ‖a x‖ + 1))).mono
      fun _ hy => hy.le
  let A : ℝ := (‖a x‖ + 1) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  apply mem_inftyIdeal_iff_log_bound.mpr
  refine ⟨ha.mul hh.1, D + Real.log A, ?_⟩
  filter_upwards [hD, hab] with y hy hay
  have hsq : generatorNormSq (fun _ : Fin 1 => fun z => a z * h z) y ≤
      A * generatorNormSq (fun _ : Fin 1 => h) y := by
    simp only [generatorNormSq, Fin.sum_univ_one, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hay 2) (sq_nonneg _)
  have hl := IdealWeightComparison.generatorLog_le_add_of_generatorNormSq_le hA hsq
  simp only [singleton_generatorLog] at hl
  calc logNormSq (a y * h y) ≤ logNormSq (h y) + (Real.log A : EReal) := hl
    _ ≤ (u y + (D : EReal)) + (Real.log A : EReal) := add_le_add hy le_rfl
    _ = _ := by rw [EReal.coe_add, add_assoc]

/-- Membership respects the actual holomorphic-germ equivalence relation. -/
theorem inftyIdeal_mem_congr {u : M → EReal} {x : M} {h k : M → ℂ}
    (heq : h =ᶠ[𝓝 x] k) :
    (inftyIdeal (n := n) u).mem x h ↔ (inftyIdeal (n := n) u).mem x k := by
  have transfer {f g : M → ℂ} (hfg : f =ᶠ[𝓝 x] g)
      (hf : (inftyIdeal (n := n) u).mem x f) : (inftyIdeal (n := n) u).mem x g := by
    obtain ⟨hf, D, hb⟩ := mem_inftyIdeal_iff_log_bound.mp hf
    apply mem_inftyIdeal_iff_log_bound.mpr
    refine ⟨hf.congr hfg, D, ?_⟩
    filter_upwards [hfg, hb] with y hy hby
    simpa only [← hy] using hby
  exact ⟨transfer heq, transfer heq.symm⟩

/-- The same genuine representative remains a member on a neighbourhood. -/
theorem inftyIdeal_mem_eventually {u : M → EReal} {x : M} {h : M → ℂ}
    (hh : (inftyIdeal (n := n) u).mem x h) :
    ∀ᶠ y in 𝓝 x, (inftyIdeal (n := n) u).mem y h := by
  obtain ⟨hh, K, hK, hb⟩ := hh
  filter_upwards [hh.eventually, hb.eventually_nhds] with y hy hby
  exact ⟨hy, K, hK, hby⟩

/-- The global growth germ object for the same positive rational coefficient. -/
def canonicalGrowthManifoldIdeal (c : ℚ) (u : M → EReal) : GermIdeal n M :=
  inftyIdeal (fun y => (((c : ℝ)⁻¹ : ℝ) : EReal) * u y)

private theorem moreSingularAt_pos_mul {X : Type*} [TopologicalSpace X]
    {f g : X → EReal} {x : X} {c : ℝ} (hc : 0 < c)
    (hfg : MoreSingularAt f g x) :
    MoreSingularAt (fun y => (c : EReal) * f y) (fun y => (c : EReal) * g y) x := by
  obtain ⟨D, hD⟩ := hfg
  refine ⟨c * D, ?_⟩
  filter_upwards [hD] with y hy
  have hl := mul_le_mul_of_nonneg_left hy (EReal.coe_nonneg.mpr hc.le)
  simpa only [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le)
    (EReal.coe_ne_top c), ← EReal.coe_mul] using hl

private theorem moreSingularAt_pos_mul_iff {X : Type*} [TopologicalSpace X]
    {f g : X → EReal} {x : X} {c : ℝ} (hc : 0 < c) :
    MoreSingularAt (fun y => (c : EReal) * f y) (fun y => (c : EReal) * g y) x ↔
      MoreSingularAt f g x := by
  constructor
  · intro hh
    have hi := moreSingularAt_pos_mul (inv_pos.mpr hc) hh
    simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne',
      EReal.coe_one, one_mul] using hi
  · exact moreSingularAt_pos_mul hc

/-- Exact source logarithmic membership with the original rational coefficient. -/
theorem mem_canonicalGrowthManifoldIdeal_iff_log_bound
    {c : ℚ} (hc : 0 < c) {u : M → EReal} {x : M} {h : M → ℂ} :
    (canonicalGrowthManifoldIdeal (n := n) c u).mem x h ↔
      HolomorphicAt n h x ∧
        MoreSingularAt (fun y => ((c : ℝ) : EReal) * logNormSq (h y)) u x := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  rw [canonicalGrowthManifoldIdeal, mem_inftyIdeal_iff_log_bound]
  apply and_congr_right
  intro _
  constructor
  · intro hh
    have hs := moreSingularAt_pos_mul hcR hh
    simpa only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hcR.ne',
      EReal.coe_one, one_mul] using hs
  · intro hh
    have hs := moreSingularAt_pos_mul (inv_pos.mpr hcR) hh
    simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hcR.ne',
      EReal.coe_one, one_mul] using hs

private theorem sum_norm_sq_le_sq_sum {N : ℕ} (G : Fin N → ℂ) :
    (∑ i, ‖G i‖ ^ 2) ≤ (∑ i, ‖G i‖) ^ 2 := by
  have h (s : Finset (Fin N)) : (∑ i ∈ s, ‖G i‖ ^ 2) ≤ (∑ i ∈ s, ‖G i‖) ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      nlinarith [norm_nonneg (G a), Finset.sum_nonneg (fun i (_ : i ∈ s) => norm_nonneg (G i))]
  simpa using h Finset.univ

/-- Logarithmic comparison is exactly an actual norm bound, including common zeros. -/
theorem moreSingularAt_singleLog_iff_norm_sum_bound {X : Type*} [TopologicalSpace X]
    {N : ℕ} {G : Fin N → X → ℂ} {h : X → ℂ} {x : X} :
    MoreSingularAt (fun y => logNormSq (h y)) (generatorLog G) x ↔
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ y in 𝓝 x, ‖h y‖ ≤ D * ∑ i, ‖G i y‖ := by
  classical
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨Real.sqrt (Real.exp K), Real.sqrt_nonneg _, ?_⟩
    filter_upwards [hK] with y hy
    have he := EReal.exp_monotone hy
    rw [logNormSq, ENNReal.exp_log, EReal.exp_add, generatorLog_eq_log_sum,
      ENNReal.exp_log, EReal.exp_coe] at he
    have hs : ‖h y‖ ^ 2 ≤ (∑ i, ‖G i y‖ ^ 2) * Real.exp K := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      simpa only [ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using he
    have hsum := sum_norm_sq_le_sq_sum (G · y)
    have hsum0 : 0 ≤ ∑ i, ‖G i y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsqrt := Real.sq_sqrt (Real.exp_pos K).le
    have hbound : ‖h y‖ ^ 2 ≤ (Real.sqrt (Real.exp K) * ∑ i, ‖G i y‖) ^ 2 := by
      rw [mul_pow, hsqrt]
      nlinarith [Real.exp_pos K]
    nlinarith [norm_nonneg (h y), Real.sqrt_nonneg (Real.exp K),
      mul_nonneg (Real.sqrt_nonneg (Real.exp K)) hsum0]
  · rintro ⟨D, hD, hb⟩
    let A : ℝ := D ^ 2 * (N : ℝ) + 1
    have hA : 0 < A := by dsimp [A]; positivity
    refine ⟨Real.log A, ?_⟩
    filter_upwards [hb] with y hy
    have hsum : (∑ i, ‖G i y‖) ^ 2 ≤ (N : ℝ) * generatorNormSq G y := by
      simpa [generatorNormSq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin N => (1 : ℝ)) (fun i => ‖G i y‖)
    have hsq : generatorNormSq (fun _ : Fin 1 => h) y ≤ A * generatorNormSq G y := by
      have he : generatorNormSq (fun _ : Fin 1 => h) y = ‖h y‖ ^ 2 := by
        simp [generatorNormSq]
      rw [he]
      have hpow := pow_le_pow_left₀ (norm_nonneg _) hy 2
      rw [mul_pow] at hpow
      have hm := mul_le_mul_of_nonneg_left hsum (sq_nonneg D)
      dsimp [A]
      nlinarith [generatorNormSq_nonneg G y]
    simpa only [singleton_generatorLog] using
      IdealWeightComparison.generatorLog_le_add_of_generatorNormSq_le hA hsq

/-- Every original presentation identifies the entire original growth stalk. -/
theorem mem_canonicalGrowthManifoldIdeal_iff_norm_bound {N : ℕ}
    {c : ℚ} (hc : 0 < c) {u : M → EReal} {G : Fin N → M → ℂ}
    {b : M → ℝ} {x : M} (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal))
    {h : M → ℂ} :
    (canonicalGrowthManifoldIdeal (n := n) c u).mem x h ↔
      HolomorphicAt n h x ∧
        ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ y in 𝓝 x, ‖h y‖ ≤ D * ∑ i, ‖G i y‖ := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨B, _, hB⟩ := hb
  have huG : MoreSingularAt u (fun y => ((c : ℝ) : EReal) * generatorLog G y) x := by
    refine ⟨B, ?_⟩
    filter_upwards [heq, hB] with y hy hby
    rw [hy]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp hby).2)
  have hGu : MoreSingularAt (fun y => ((c : ℝ) : EReal) * generatorLog G y) u x := by
    refine ⟨B, ?_⟩
    filter_upwards [heq, hB] with y hy hby
    rw [hy, add_assoc, ← EReal.coe_add]
    have h0 : (0 : EReal) ≤ ((b y + B : ℝ) : EReal) := by
      exact EReal.coe_nonneg.mpr (by linarith [(abs_le.mp hby).1])
    simpa only [add_zero] using add_le_add (le_refl (((c : ℝ) : EReal) * generatorLog G y)) h0
  rw [mem_canonicalGrowthManifoldIdeal_iff_log_bound hc]
  apply and_congr_right
  intro _
  rw [← moreSingularAt_singleLog_iff_norm_sum_bound]
  exact ⟨fun hh => (moreSingularAt_pos_mul_iff hcR).mp (hh.trans huG),
    fun hh => (moreSingularAt_pos_mul hcR hh).trans hGu⟩

/-- The original stalk and the actual recentered holomorphic-germ ideal agree. -/
theorem mem_canonicalGrowthManifoldIdeal_iff_recentered {N : ℕ}
    {c : ℚ} (hc : 0 < c) {u : M → EReal} {G : Fin N → M → ℂ}
    {b : M → ℝ} {x : M} (hG : ∀ i, HolomorphicAt n (G i) x)
    (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal))
    {h : M → ℂ} (hh : HolomorphicAt n h x) :
    (canonicalGrowthManifoldIdeal (n := n) c u).mem x h ↔
      HolGerm.mk (fun z => h (rechartSymm n x z))
        (differentiableAt_comp_rechartSymm hh) ∈
          canonicalGrowthGermIdeal (fun i z => G i (rechartSymm n x z)) := by
  obtain ⟨m, F, hF, hspan, hmem, hbound⟩ :=
    exists_finite_canonical_growth_germ_presentation
      (fun i z => G i (rechartSymm n x z))
      (fun i => differentiableAt_comp_rechartSymm (hG i))
  rw [hmem _ (differentiableAt_comp_rechartSymm hh),
    mem_canonicalGrowthManifoldIdeal_iff_norm_bound hc hb heq]
  constructor
  · rintro ⟨_, D, hD, hDb⟩
    exact ⟨D, hD, tendsto_rechartSymm x hDb⟩
  · rintro ⟨D, hD, hDb⟩
    refine ⟨hh, D, hD, ?_⟩
    filter_upwards [tendsto_rechart x hDb, eventually_rechartSymm_rechart (n := n) x]
      with y hy hxy
    change ‖h (rechartSymm n x (rechart n x y))‖ ≤
      D * ∑ i, ‖G i (rechartSymm n x (rechart n x y))‖ at hy
    simpa only [hxy] using hy

private theorem isInSpanAt_lifted_iff_recentered {s : ℕ}
    (F : Fin s → ComplexModel n → ℂ)
    (hF : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (F i) z)
    {x : M} {h : M → ℂ} (hh : HolomorphicAt n h x) :
    IsInSpanAt (n := n) (· ∈ range (fun i y => F i (rechart n x y))) x h ↔
      HolGerm.mk (fun z => h (rechartSymm n x z))
        (differentiableAt_comp_rechartSymm hh) ∈
          Ideal.span (range fun i => HolGerm.mk (F i) (hF i)) := by
  rw [← EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span]
  constructor
  · intro hm
    obtain ⟨_, a, ha, heq⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp hm
    apply CoherentIdealColon.isInSpanAt_range_iff.mpr
    refine ⟨(differentiableAt_comp_rechartSymm hh).mono fun _ hz => hz.mdifferentiableAt,
      fun i z => a i (rechartSymm n x z),
      fun i => (differentiableAt_comp_rechartSymm (ha i)).mono fun _ hz => hz.mdifferentiableAt,
      ?_⟩
    filter_upwards [tendsto_rechartSymm x heq, eventually_rechart_rechartSymm (n := n) x]
      with z hz hxz
    change h (rechartSymm n x z) = ∑ i,
      a i (rechartSymm n x z) * F i (rechart n x (rechartSymm n x z)) at hz
    simpa only [hxz] using hz
  · intro hm
    obtain ⟨_, a, ha, heq⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp hm
    apply CoherentIdealColon.isInSpanAt_range_iff.mpr
    refine ⟨hh, fun i y => a i (rechart n x y),
      fun i => holomorphicAt_comp_rechart ((ha i).mono fun _ hz => hz.differentiableAt), ?_⟩
    filter_upwards [tendsto_rechart x heq, eventually_rechartSymm_rechart (n := n) x]
      with y hy hxy
    change h (rechartSymm n x (rechart n x y)) = ∑ i,
      a i (rechart n x y) * F i (rechart n x y) at hy
    simpa only [hxy] using hy

/-- Finite generators are produced for the same original growth stalk. -/
theorem exists_original_canonical_growth_stalk_generators {N : ℕ}
    {c : ℚ} (hc : 0 < c) {u : M → EReal} {G : Fin N → M → ℂ}
    {b : M → ℝ} {x : M} (hG : ∀ i, HolomorphicAt n (G i) x)
    (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal)) :
    ∃ (m : ℕ) (F : Fin m → M → ℂ), (∀ j, HolomorphicAt n (F j) x) ∧
      ∀ h : M → ℂ, (canonicalGrowthManifoldIdeal (n := n) c u).mem x h ↔
        IsInSpanAt (n := n) (· ∈ range F) x h := by
  obtain ⟨m, F, hF, hspan, hmem, hbound⟩ :=
    exists_finite_canonical_growth_germ_presentation
      (fun i z => G i (rechartSymm n x z))
      (fun i => differentiableAt_comp_rechartSymm (hG i))
  refine ⟨m, fun j y => F j (rechart n x y),
    fun j => holomorphicAt_comp_rechart (hF j), ?_⟩
  intro h
  constructor
  · intro hm
    have hh : HolomorphicAt n h x := hm.1
    apply (isInSpanAt_lifted_iff_recentered F hF hh).mpr
    rw [hspan]
    exact (mem_canonicalGrowthManifoldIdeal_iff_recentered hc hG hb heq hh).mp hm
  · intro hm
    have hh : HolomorphicAt n h x := hm.1
    apply (mem_canonicalGrowthManifoldIdeal_iff_recentered hc hG hb heq hh).mpr
    rw [← hspan]
    exact (isInSpanAt_lifted_iff_recentered F hF hh).mp hm

namespace VariableComplexAtlas

/-- Compact original intrinsic analytic input supplies one coefficient and all
original growth stalks. Nearby uniform generation/coherence are not assumed. -/
theorem exists_original_canonical_growth_manifold_stalks [CompactSpace M]
    {u : M → EReal} (hu : (ofFixedModel n M).HasRationalAnalyticType u) :
    ∃ c : ℚ, 0 < c ∧ ∀ x : M, ∃ (m : ℕ) (F : Fin m → M → ℂ),
      (∀ j, HolomorphicAt n (F j) x) ∧
      ∀ h : M → ℂ, (canonicalGrowthManifoldIdeal (n := n) c u).mem x h ↔
        IsInSpanAt (n := n) (· ∈ range F) x h := by
  obtain ⟨c, m, N, G, b, C, U, hc, hcover, hp⟩ :=
    exists_uniform_rational_analytic_coefficient hu
  refine ⟨c, hc, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨hC, hU, _, hG, hb, heq⟩ := hp i
  have hGx (j : Fin (N i)) : HolomorphicAt n (G i j) x := by
    filter_upwards [hU.mem_nhds hxi] with y hy
    exact ((chartHolomorphicOn_iff_native hU).mp (hG j)).mdifferentiableAt (hU.mem_nhds hy)
  exact exists_original_canonical_growth_stalk_generators hc hGx
    ⟨C i, hC, Filter.eventually_of_mem (hU.mem_nhds hxi) fun y hy => hb y hy⟩
    (Filter.eventually_of_mem (hU.mem_nhds hxi) fun y hy => heq hy)

end VariableComplexAtlas

end SGPT.PSH
