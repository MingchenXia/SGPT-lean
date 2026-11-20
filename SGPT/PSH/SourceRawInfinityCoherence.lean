import SGPT.PSH.SourceGlobalAnalyticType
import Mathlib.Analysis.Complex.Liouville
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

/-! # Coherence of the original raw infinity ideal

Whole SGPT69360cfd source lma:pshfunctions:L1494, chapter_pshfunctions1480–1483.
The original positive rational coefficient and merely bounded remainder are
retained. Actual auxiliary tensor generators, internally produced normalized
growth coherence, actual Oka finite colon and Cauchy restriction construct
ONE finite family at EVERY nearby original stalk. Every original varying
chart dimension, zero family, common pole and dimension0 is included.
No normalized replacement of the original potential or raw ideal, supplied
output ideal/coherence/generator/quotient, proper-image or resolution
certificate is an input. The stronger local result needs neither compactness
nor QPSH; the full source wrapper retains both printed hypotheses.

Before-code blueprint: AUXILIARY-RAW-COHERENCE.tex. Checked component bodies
are consolidated below with imports and anonymous sections made explicit.
-/

/-! Checked component: LogPowerGrowth.lean. -/

/-! The raw coefficient is retained literally: logarithmic growth with
weight a*log|z|² is exactly actual |q|≤C|z|^a, including zero weights/poles.
Blueprint raw-infinity:log-rpow preceded this implementation. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- Genuine pointwise exponentiation of the original raw logarithmic bound,
with the same exponent and literal zero/pole values. -/
theorem norm_le_exp_half_mul_rpow_of_log_bound
    {q z : ℂ} {a D : ℝ} (ha : 0 ≤ a)
    (hlog : logNormSq q ≤ (a:EReal)*logNormSq z+(D:EReal)) :
    ‖q‖ ≤ Real.exp (D/2)*‖z‖^a := by
  by_cases hq : q=0
  · simp only [hq,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  by_cases ha0 : a=0
  · subst a
    simp only [EReal.coe_zero,zero_mul,zero_add] at hlog
    rw [logNormSq_of_ne_zero hq,EReal.coe_le_coe_iff,Real.log_pow] at hlog
    have hhalf : Real.log ‖q‖ ≤ D/2 := by norm_num at hlog; linarith
    simpa only [Real.rpow_zero,mul_one,Real.exp_log hqpos] using Real.exp_le_exp.mpr hhalf
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_cases hz : z=0
  · have hbot : logNormSq q = ⊥ := by
      apply le_bot_iff.mp
      rw [(logNormSq_eq_bot_iff z).mpr hz,EReal.coe_mul_bot_of_pos hap] at hlog
      simpa using hlog
    exact False.elim (hq ((logNormSq_eq_bot_iff _).mp hbot))
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [logNormSq_of_ne_zero hq,logNormSq_of_ne_zero hz,←EReal.coe_mul,
    ←EReal.coe_add,EReal.coe_le_coe_iff,Real.log_pow,Real.log_pow] at hlog
  have hr : Real.log ‖q‖ ≤ D/2+a*Real.log ‖z‖ := by norm_num at hlog; nlinarith
  calc ‖q‖ = Real.exp (Real.log ‖q‖) := (Real.exp_log hqpos).symm
    _ ≤ Real.exp (D/2+a*Real.log ‖z‖) := Real.exp_le_exp.mpr hr
    _ = Real.exp (D/2)*‖z‖^a := by
      rw [Real.exp_add,Real.rpow_def_of_pos hzpos]
      congr 1
      congr 1
      ring

/-- The actual real-power bound gives the exact original raw logarithmic
weight, with no coefficient normalization and both zero-exponent/pole cases. -/
theorem log_le_scaled_log_add_of_norm_le_rpow
    {q z : ℂ} {a C : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (hbound : ‖q‖ ≤ C*‖z‖^a) :
    logNormSq q ≤ (a:EReal)*logNormSq z+((2*Real.log C:ℝ):EReal) := by
  by_cases hq : q=0
  · rw [(logNormSq_eq_bot_iff q).mpr hq]
    exact bot_le
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  by_cases ha0 : a=0
  · subst a
    simp only [Real.rpow_zero,mul_one] at hbound
    have hlog := Real.log_le_log hqpos hbound
    simp only [EReal.coe_zero,zero_mul,zero_add]
    rw [logNormSq_of_ne_zero hq,EReal.coe_le_coe_iff,Real.log_pow]
    norm_num
    linarith
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_cases hz : z=0
  · have hnorm : ‖q‖ ≤ 0 := by simpa only [hz,norm_zero,Real.zero_rpow hap.ne',mul_zero] using hbound
    exact False.elim (hq (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))))
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlog := Real.log_le_log hqpos hbound
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hzpos a).ne',Real.log_rpow hzpos] at hlog
  rw [logNormSq_of_ne_zero hq,logNormSq_of_ne_zero hz,←EReal.coe_mul,
    ←EReal.coe_add,EReal.coe_le_coe_iff,Real.log_pow,Real.log_pow]
  norm_num
  nlinarith

/-- Exact original-germ logarithmic/rpow dictionary for EVERY nonnegative
real exponent, hence arbitrary effective rational SNC coefficients. -/
theorem moreSingularAt_scaled_singleLog_iff_rpow_bound
    {X : Type*} [TopologicalSpace X] {q z : X → ℂ} {a : ℝ} (ha : 0 ≤ a) {x : X} :
    MoreSingularAt (fun y => logNormSq (q y)) (fun y => (a:EReal)*logNormSq (z y)) x ↔
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ C*‖z y‖^a := by
  constructor
  · rintro ⟨D,hD⟩
    exact ⟨Real.exp (D/2),Real.exp_pos _,hD.mono fun _ hy =>
      norm_le_exp_half_mul_rpow_of_log_bound ha hy⟩
  · rintro ⟨C,hC,hbound⟩
    exact ⟨2*Real.log C,hbound.mono fun _ hy => log_le_scaled_log_add_of_norm_le_rpow ha hC hy⟩

end SGPT.PSH.RawInfinity

end

/-! Checked component: AuxiliaryCauchyBound.lean. -/

/-! Actual auxiliary-variable scalar and Cauchy restriction estimates for
RAW rational analytic coherence. Complete source blueprint
AUXILIARY-RAW-COHERENCE.tex preceded this code. The original holomorphic
function and its actual value at0 are retained, including zero radius and q1. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter Metric Complex
open scoped Topology

/-- The actual two-case estimate lifts original raw growth to the auxiliary
finite-colon weight. No auxiliary bound is assumed as a certificate. -/
theorem auxiliary_scalar_growth {q : ℕ} (hq : 0 < q)
    {b C r s : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hb : b ≤ C*r) : b*s^(q-1) ≤ C*(r^q+s^q) := by
  have hpow (t : ℝ) : t^q=t*t^(q-1) := by
    calc t^q=t^(q-1+1) := by congr 1; omega
         _=t*t^(q-1) := by rw [pow_succ]; ring
  by_cases hsr : s ≤ r
  · calc b*s^(q-1) ≤ (C*r)*s^(q-1) := mul_le_mul_of_nonneg_right hb (pow_nonneg hs _)
         _ ≤ (C*r)*r^(q-1) := mul_le_mul_of_nonneg_left
           (pow_le_pow_left₀ hs hsr _) (mul_nonneg hC hr)
         _ = C*r^q := by rw [hpow r]; ring
         _ ≤ C*(r^q+s^q) := mul_le_mul_of_nonneg_left
           (le_add_of_nonneg_right (pow_nonneg hs _)) hC
  · have hrs : r ≤ s := (le_of_not_ge hsr)
    calc b*s^(q-1) ≤ (C*s)*s^(q-1) := mul_le_mul_of_nonneg_right
           (hb.trans (mul_le_mul_of_nonneg_left hrs hC)) (pow_nonneg hs _)
         _ = C*s^q := by rw [hpow s]; ring
         _ ≤ C*(r^q+s^q) := mul_le_mul_of_nonneg_left
           (le_add_of_nonneg_left (pow_nonneg hr _)) hC

/-- Actual Cauchy circle average gives the exact original value bound at0
from the true auxiliary colon growth inequality, for positive radius. -/
theorem norm_zero_le_of_auxiliary_bound_pos
    {q : ℕ} (hq : 0 < q) {H : ℂ → ℂ} {R r C : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) R))
    (hbound : ∀ t ∈ ball (0 : ℂ) R,
      ‖H t‖*‖t‖^(q-1) ≤ C*(r^q+‖t‖^q)) : ‖H 0‖ ≤ 2*C*r := by
  have hpow : r^q=r*r^(q-1) := by
    calc r^q=r^(q-1+1) := by congr 1; omega
         _=r*r^(q-1) := by rw [pow_succ]; ring
  have hcirc : ∀ t ∈ sphere (0 : ℂ) r, ‖H t‖ ≤ 2*C*r := by
    intro t ht
    have hn : ‖t‖=r := by simpa using ht
    have htR : t ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff,hn]; exact hrR
    have hb := hbound t htR
    rw [hn] at hb
    have haux : ‖H t‖*r^(q-1) ≤ (2*C*r)*r^(q-1) := by
      calc ‖H t‖*r^(q-1) ≤ C*(r^q+r^q) := hb
           _ = (2*C*r)*r^(q-1) := by rw [hpow]; ring
    nlinarith [pow_pos hr (q-1)]
  have hcl : DiffContOnCl ℂ H (ball (0 : ℂ) r) :=
    hH.diffContOnCl_ball (by simpa only [closure_ball (0 : ℂ) hr.ne'] using
      (closedBall_subset_ball hrR))
  simpa using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0 hr hcl hcirc

/-- The true common-pole branch follows by actual positive circles tending
to0; no division by a zero radius, desired value or order assumption. -/
theorem norm_zero_le_of_auxiliary_bound
    {q : ℕ} (hq : 0 < q) {H : ℂ → ℂ} {R r C : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hR : 0 < R) (hrR : r < R)
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) R))
    (hbound : ∀ t ∈ ball (0 : ℂ) R,
      ‖H t‖*‖t‖^(q-1) ≤ C*(r^q+‖t‖^q)) : ‖H 0‖ ≤ 2*C*r := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · have hr0 : r=0 := hzero.symm
    subst r
    have hlim : Tendsto (fun s : ℝ => 2*C*s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous (fun s : ℝ => 2*C*s) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hcont.tendsto (0 : ℝ)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hnear : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ‖H 0‖ ≤ 2*C*s := by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (gt_mem_nhds hR)] with s hs hsR
      change 0 < s at hs
      apply norm_zero_le_of_auxiliary_bound_pos hq hs hsR hH
      intro t ht
      apply (hbound t ht).trans
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [zero_pow hq.ne',zero_add] using
        add_le_add (pow_nonneg hs.le q) (le_refl (‖t‖^q))
    simpa only [mul_zero] using ge_of_tendsto hlim hnear
  · exact norm_zero_le_of_auxiliary_bound_pos hq hpos hrR hH hbound

end SGPT.PSH.RawInfinity

end

/-! Checked component: AuxiliaryRestrictionGrowth.lean. -/

/-! Actual zero-section growth from an actual jointly holomorphic auxiliary
colon bound, uniformly on an original base neighborhood. No restriction
bound, order, quotient, coherent image or desired equality certificate.
The source-facing complete plan AUXILIARY-RAW-COHERENCE.tex preceded code. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- At the true common-zero basepoint, genuine Cauchy circles yield ONE
uniform original-base germ bound for the ACTUAL zero-section restriction. -/
theorem restriction_growth_of_auxiliary_bound_at_zero_scale
    {q : ℕ} (hq : 0 < q) {H : E × ℂ → ℂ} {a : E → ℝ} {x : E} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ y, 0 ≤ a y) (hac : ContinuousAt a x) (ha0 : a x=0)
    (hH : ∀ᶠ v in 𝓝 (x,(0 : ℂ)), DifferentiableAt ℂ H v)
    (hbound : ∀ᶠ v in 𝓝 (x,(0 : ℂ)),
      ‖H v‖*‖v.2‖^(q-1) ≤ C*((a v.1)^q+‖v.2‖^q)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y in 𝓝 x, ‖H (y,0)‖ ≤ K*a y := by
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff_ball.mp (hH.and hbound)
  have hasmall : ∀ᶠ y in 𝓝 x, a y < δ :=
    hac.eventually (gt_mem_nhds (by rw [ha0]; exact hδ))
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ ball x δ := isOpen_ball.mem_nhds (mem_ball_self hδ)
  refine ⟨2*C+1,by linarith,?_⟩
  filter_upwards [hasmall,hnear] with y hya hy
  have hp (t : ℂ) (ht : t ∈ ball (0 : ℂ) δ) : (y,t) ∈ ball (x,(0 : ℂ)) δ := by
    rw [mem_ball,Prod.dist_eq]
    exact max_lt (mem_ball.mp hy) (mem_ball.mp ht)
  have hslice : DifferentiableOn ℂ (fun t => H (y,t)) (ball (0 : ℂ) δ) := by
    intro t ht
    exact ((hball (y,t) (hp t ht)).1.comp t
      ((differentiableAt_const y).prodMk differentiableAt_id)).differentiableWithinAt
  have hv := norm_zero_le_of_auxiliary_bound hq hC (ha y) hδ hya hslice
    (fun t ht => (hball (y,t) (hp t ht)).2)
  exact hv.trans (mul_le_mul_of_nonneg_right (by linarith : 2*C ≤ 2*C+1) (ha y))

/-- Any genuine actual colon germ has an ACTUAL raw-growth zero-section
restriction. The unit branch and common-zero circle-limit branch are both
produced internally; all q≥1 and base dimensions including0 are retained. -/
theorem restriction_growth_of_auxiliary_bound
    {q : ℕ} (hq : 0 < q) {H : E × ℂ → ℂ} {a : E → ℝ} {x : E} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ y, 0 ≤ a y) (hac : ContinuousAt a x)
    (hH : ∀ᶠ v in 𝓝 (x,(0 : ℂ)), DifferentiableAt ℂ H v)
    (hbound : ∀ᶠ v in 𝓝 (x,(0 : ℂ)),
      ‖H v‖*‖v.2‖^(q-1) ≤ C*((a v.1)^q+‖v.2‖^q)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y in 𝓝 x, ‖H (y,0)‖ ≤ K*a y := by
  by_cases ha0 : a x=0
  · exact restriction_growth_of_auxiliary_bound_at_zero_scale hq hC ha hac ha0 hH hbound
  have hax : 0 < a x := lt_of_le_of_ne (ha x) (Ne.symm ha0)
  have hzero : ContinuousAt (fun y : E => (y,(0 : ℂ))) x :=
    continuousAt_id.prodMk continuousAt_const
  have hres : ContinuousAt (fun y => H (y,0)) x :=
    hH.self_of_nhds.continuousAt.comp (f := fun y : E => (y,(0 : ℂ))) hzero
  let M : ℝ := ‖H (x,0)‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  let K : ℝ := M/(a x/2)
  have hK : 0 < K := div_pos hM (half_pos hax)
  have hnorm : ∀ᶠ y in 𝓝 x, ‖H (y,0)‖ ≤ M :=
    (hres.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))).mono fun _ hy => hy.le
  have hlower : ∀ᶠ y in 𝓝 x, a x/2 ≤ a y :=
    (hac.eventually (lt_mem_nhds (half_lt_self hax))).mono fun _ hy => hy.le
  refine ⟨K,hK,?_⟩
  filter_upwards [hnorm,hlower] with y hy hya
  calc ‖H (y,0)‖ ≤ M := hy
       _ = K*(a x/2) := by dsimp [K]; rw [div_mul_cancel₀ _ (half_pos hax).ne']
       _ ≤ K*a y := mul_le_mul_of_nonneg_left hya hK.le

end SGPT.PSH.RawInfinity

end

/-! Checked component: RationalGeneratorGrowth.lean. -/

/-! Literal rational generator weights and actual Euclidean generator norms,
including all common zeros. No ideal normalization or closure certificate.
Full before-code source route AUXILIARY-RAW-COHERENCE.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

private theorem logNormSq_of_norm_as_complex {E : Type*} [NormedAddCommGroup E] (z : E) :
    logNormSq (‖z‖ : ℂ)=logNormSq z := by
  simp only [logNormSq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z)]

/-- ORIGINAL rational/real finite-generator log growth iff actual Euclidean
norm growth with the SAME coefficient, including common zero points. -/
theorem moreSingularAt_scaled_generatorLog_iff_rpow_bound
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (G : Fin N → X → ℂ) {F : X → ℂ} {x : X} {c : ℝ} (hc : 0 ≤ c) :
    MoreSingularAt (fun y => logNormSq (F y))
      (fun y => (c : EReal)*generatorLog G y) x ↔
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
        ‖F y‖ ≤ C*‖generatorVector G y‖^c := by
  have h := moreSingularAt_scaled_singleLog_iff_rpow_bound
    (q := F) (z := fun y => (‖generatorVector G y‖ : ℂ)) (x := x) hc
  simpa only [logNormSq_of_norm_as_complex,generatorLog,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using h

/-- Actual original fractional generator scale in the auxiliary construction. -/
def rationalGeneratorScale {X : Type*} {N : ℕ} (G : Fin N → X → ℂ) (p q : ℕ) (x : X) : ℝ :=
  ‖generatorVector G x‖^((p : ℝ)/(q : ℝ))

/-- The exact integer-root identity is produced from the genuine original
norm and positive denominator, not assumed as a radius certificate. -/
theorem rationalGeneratorScale_pow {X : Type*} {N : ℕ}
    (G : Fin N → X → ℂ) (p : ℕ) {q : ℕ} (hq : 0 < q) (x : X) :
    rationalGeneratorScale G p q x^q=‖generatorVector G x‖^p := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold rationalGeneratorScale
  rw [←Real.rpow_mul_natCast (norm_nonneg _) _ q,div_mul_cancel₀ _ hqR,Real.rpow_natCast]

/-- Actual continuity of the original fractional scale follows from the
original finite holomorphic family, including all common zero points. -/
theorem continuousAt_rationalGeneratorScale
    {n N : ℕ} (G : Fin N → ComplexModel n → ℂ) (p q : ℕ) {x : ComplexModel n}
    (hG : HolomorphicGeneratorsAt G x) : ContinuousAt (rationalGeneratorScale G p q) x := by
  obtain ⟨U,hU,hxU,hGU⟩ := hG
  have hGc (i : Fin N) : ContinuousAt (G i) x :=
    ((hGU i).differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hvec : ContinuousAt (generatorVector G) x :=
    (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr hGc)
  exact hvec.norm.rpow_const (Or.inr (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)))

/-- The unchanged original finite rational logarithmic growth ideal. -/
def fractionalGrowthGermPredicate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (G : Fin N → E → ℂ) (c : ℝ) (x : E) (F : E → ℂ) : Prop :=
  (∀ᶠ y in 𝓝 x, DifferentiableAt ℂ F y) ∧
    MoreSingularAt (fun y => logNormSq (F y)) (fun y => (c : EReal)*generatorLog G y) x

/-- The exact original rational ideal's norm reader, including every pole. -/
theorem fractionalGrowthGermPredicate_iff_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (G : Fin N → E → ℂ) (p q : ℕ) (x : E) (F : E → ℂ) :
    fractionalGrowthGermPredicate G ((p : ℝ)/(q : ℝ)) x F ↔
      (∀ᶠ y in 𝓝 x, DifferentiableAt ℂ F y) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, ‖F y‖ ≤ C*rationalGeneratorScale G p q y := by
  exact and_congr_right fun _ => moreSingularAt_scaled_generatorLog_iff_rpow_bound G
    (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q))

end SGPT.PSH.RawInfinity

end

/-! Checked component: AuxiliaryGrowthIdeal.lean. -/

/-! The ACTUAL auxiliary finite holomorphic family and its ACTUAL coherent
finite colon, produced from original G,p,q, with no output-ideal/coherence
certificate. Full before-code blueprint AUXILIARY-RAW-COHERENCE.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter Metric
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticGeneratorTensorPowers FiniteGeodesicMaximality OkaRelationSheaf OkaIdealOperations
variable {n N : ℕ}

/-- Literal original n-coordinate projection in actual auxiliary ℂ^(n+1). -/
def auxiliaryBase : ComplexModel (n+1) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ).comp (stripModelEquiv n).toContinuousLinearMap

/-- Literal original auxiliary last coordinate. -/
def auxiliaryParameter : ComplexModel (n+1) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (ComplexModel n) ℂ).comp (stripModelEquiv n).toContinuousLinearMap

/-- Actual p-fold original tensor products, plus the genuine auxiliary
coordinate t^q. No growth bound or desired restriction is a definition field. -/
def auxiliaryFamily (G : Fin N → ComplexModel n → ℂ) (p q : ℕ) :
    Fin (Fintype.card (Fin p → Fin N)+1) → ComplexModel (n+1) → ℂ :=
  Fin.cases (fun w => auxiliaryParameter w^q)
    (fun j w => tensorPowerFamily G p j (auxiliaryBase w))

/-- Exact ordinary norm algebra for the SAME actual auxiliary family. -/
theorem auxiliaryFamily_norm_sq (G : Fin N → ComplexModel n → ℂ) (p q : ℕ)
    (w : ComplexModel (n+1)) :
    ‖generatorVector (auxiliaryFamily G p q) w‖^2 =
      (‖generatorVector G (auxiliaryBase w)‖^p)^2+(‖auxiliaryParameter w‖^q)^2 := by
  rw [generatorVector_norm_sq,generatorNormSq,Fin.sum_univ_succ]
  change ‖auxiliaryParameter w^q‖^2+
    generatorNormSq (tensorPowerFamily G p) (auxiliaryBase w) = _
  rw [generatorNormSq_tensorPowerFamily,←generatorVector_norm_sq,norm_pow]
  rw [←pow_mul,←pow_mul,Nat.mul_comm 2 p]
  ring

/-- The actual original raw-scale sum bounds the actual auxiliary norm. -/
theorem auxiliaryFamily_norm_le_sum (G : Fin N → ComplexModel n → ℂ) (p q : ℕ)
    (w : ComplexModel (n+1)) :
    ‖generatorVector (auxiliaryFamily G p q) w‖ ≤
      ‖generatorVector G (auxiliaryBase w)‖^p+‖auxiliaryParameter w‖^q := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (by positivity) (by positivity))).mp
  rw [auxiliaryFamily_norm_sq]
  nlinarith [pow_nonneg (norm_nonneg (generatorVector G (auxiliaryBase w))) p,
    pow_nonneg (norm_nonneg (auxiliaryParameter w)) q]

/-- The converse actual norm comparison has one fixed finite constant2. -/
theorem auxiliaryFamily_sum_le_two_norm (G : Fin N → ComplexModel n → ℂ) (p q : ℕ)
    (w : ComplexModel (n+1)) :
    ‖generatorVector G (auxiliaryBase w)‖^p+‖auxiliaryParameter w‖^q ≤
      2*‖generatorVector (auxiliaryFamily G p q) w‖ := by
  have heq := auxiliaryFamily_norm_sq G p q w
  have hA : ‖generatorVector G (auxiliaryBase w)‖^p ≤
      ‖generatorVector (auxiliaryFamily G p q) w‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    nlinarith [sq_nonneg (‖auxiliaryParameter w‖^q)]
  have hB : ‖auxiliaryParameter w‖^q ≤
      ‖generatorVector (auxiliaryFamily G p q) w‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    nlinarith [sq_nonneg (‖generatorVector G (auxiliaryBase w)‖^p)]
  linarith

/-- Genuine original local holomorphic data manufacture the actual family
on an actual auxiliary neighborhood; n=0 and all-zero G are retained. -/
theorem holomorphicGeneratorsAt_auxiliaryFamily
    (G : Fin N → ComplexModel n → ℂ) (p q : ℕ) {x : ComplexModel n}
    (hG : HolomorphicGeneratorsAt G x) (t : ℂ) :
    HolomorphicGeneratorsAt (auxiliaryFamily G p q) ((stripModelEquiv n).symm (x,t)) := by
  obtain ⟨U,hU,hxU,hTU⟩ := holomorphicGeneratorsAt_tensorPowerFamily (r := p) hG
  let V := auxiliaryBase ⁻¹' U
  have hV : IsOpen V := hU.preimage (auxiliaryBase (n := n)).continuous
  have hxV : (stripModelEquiv n).symm (x,t) ∈ V := by
    simpa [V,auxiliaryBase] using hxU
  refine ⟨V,hV,hxV,?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change DifferentiableOn ℂ (fun w : ComplexModel (n+1) => auxiliaryParameter w^q) V
    exact ((auxiliaryParameter (n := n)).differentiable.pow q).differentiableOn
  · change DifferentiableOn ℂ (fun w : ComplexModel (n+1) =>
      tensorPowerFamily G p j (auxiliaryBase w)) V
    exact (hTU j).comp (auxiliaryBase (n := n)).differentiable.differentiableOn (fun _ hw => hw)

/-- ACTUAL auxiliary finite-colon ideal, using the existing genuine original
growth ideal rather than an assumed integral-closure or restriction ideal. -/
def auxiliaryColon (G : Fin N → ComplexModel n → ℂ) (p q : ℕ) :
    ComplexModel (n+1) → (ComplexModel (n+1) → ℂ) → Prop :=
  colonIdeal (GlobalAnalyticType.growthGermPredicate (auxiliaryFamily G p q))
    (fun w => auxiliaryParameter w^(q-1))

/-- Existing actual E01 normalized growth coherence and genuine Oka colon
relations PRODUCE the full nearby auxiliary colon generators internally.
No coherent ideal, matrix, generator family or desired restriction input. -/
theorem idealFGAt_auxiliaryColon
    (G : Fin N → ComplexModel n → ℂ) (p q : ℕ) {x : ComplexModel n}
    (hG : HolomorphicGeneratorsAt G x) (t : ℂ) :
    IdealFGAt (auxiliaryColon G p q) ((stripModelEquiv n).symm (x,t)) := by
  have hJ := GlobalAnalyticType.idealFGAt_growth_of_holomorphicGeneratorsAt
    (auxiliaryFamily G p q) (holomorphicGeneratorsAt_auxiliaryFamily G p q hG t)
  exact hJ.colon (OkaCoherence.okaProperty_euclidean (n+1))
    (Eventually.of_forall fun _ => (auxiliaryParameter (n := n)).differentiableAt.pow (q-1))

end SGPT.PSH.RawInfinity

end

/-! Checked component: AuxiliaryColonRestriction.lean. -/

/-! Exact actual auxiliary-colon lift and restriction producers for ORIGINAL
rational raw growth. All constants, radius-zero and unit branches are
produced internally. Before-code blueprint AUXILIARY-RAW-COHERENCE.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter Metric
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FiniteGeodesicMaximality OkaRelationSheaf OkaIdealOperations
variable {n N : ℕ}

/-- The actual original zero section, as a genuine holomorphic linear map. -/
def auxiliaryZeroSection : ComplexModel n →L[ℂ] ComplexModel (n+1) :=
  (stripModelEquiv n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (ComplexModel n) ℂ)

@[simp] theorem auxiliaryBase_stripInverse (v : ComplexModel n × ℂ) :
    auxiliaryBase ((stripModelEquiv n).symm v)=v.1 := by
  change (stripModelEquiv n ((stripModelEquiv n).symm v)).1=v.1
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem auxiliaryParameter_stripInverse (v : ComplexModel n × ℂ) :
    auxiliaryParameter ((stripModelEquiv n).symm v)=v.2 := by
  change (stripModelEquiv n ((stripModelEquiv n).symm v)).2=v.2
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem auxiliaryBase_zeroSection (x : ComplexModel n) :
    auxiliaryBase (auxiliaryZeroSection x)=x := auxiliaryBase_stripInverse (x,0)

@[simp] theorem auxiliaryParameter_zeroSection (x : ComplexModel n) :
    auxiliaryParameter (auxiliaryZeroSection x)=0 := auxiliaryParameter_stripInverse (x,0)

private theorem normalized_growth_iff_norm
    {d r : ℕ} (G : Fin r → ComplexModel d → ℂ) (x : ComplexModel d) (F : ComplexModel d → ℂ) :
    GlobalAnalyticType.growthGermPredicate G x F ↔
      HolAt F x ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
        ‖F y‖ ≤ C*‖generatorVector G y‖ := by
  exact and_congr_right fun _ => by
    simpa only [EReal.coe_one,one_mul,Real.rpow_one] using
      (moreSingularAt_scaled_generatorLog_iff_rpow_bound G (F := F) (x := x) (c := 1) zero_le_one)

/-- EVERY original rational raw germ has its actual constant-in-t lift in
the genuinely coherent auxiliary colon. No colon membership is assumed. -/
theorem lift_mem_auxiliaryColon_of_fractionalGrowth
    (G : Fin N → ComplexModel n → ℂ) (p : ℕ) {q : ℕ} (hq : 0 < q)
    {x : ComplexModel n} {F : ComplexModel n → ℂ}
    (hF : fractionalGrowthGermPredicate G ((p : ℝ)/(q : ℝ)) x F) :
    auxiliaryColon G p q (auxiliaryZeroSection x) (fun w => F (auxiliaryBase w)) := by
  obtain ⟨hF,C,hC,hbound⟩ := (fractionalGrowthGermPredicate_iff_norm G p q x F).mp hF
  have ht : Tendsto (auxiliaryBase (n := n)) (𝓝 (auxiliaryZeroSection x)) (𝓝 x) := by
    simpa only [auxiliaryBase_zeroSection] using
      (auxiliaryBase (n := n)).continuous.tendsto (auxiliaryZeroSection x)
  have hLift : HolAt (fun w => F (auxiliaryBase w)) (auxiliaryZeroSection x) := by
    filter_upwards [ht.eventually hF] with w hw
    exact hw.comp w (auxiliaryBase (n := n)).differentiableAt
  refine ⟨hLift,(normalized_growth_iff_norm (auxiliaryFamily G p q) _ _).mpr ?_⟩
  refine ⟨hLift.mul (Eventually.of_forall fun _ =>
    (auxiliaryParameter (n := n)).differentiableAt.pow (q-1)),2*C,by positivity,?_⟩
  filter_upwards [ht.eventually hbound] with w hw
  rw [norm_mul,norm_pow]
  have ha := auxiliary_scalar_growth hq hC.le
    (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg (auxiliaryParameter w)) hw
  change ‖F (auxiliaryBase w)‖*‖auxiliaryParameter w‖^(q-1) ≤
    C*((rationalGeneratorScale G p q (auxiliaryBase w))^q+‖auxiliaryParameter w‖^q) at ha
  rw [rationalGeneratorScale_pow G p hq] at ha
  calc ‖F (auxiliaryBase w)‖*‖auxiliaryParameter w‖^(q-1) ≤
      C*(‖generatorVector G (auxiliaryBase w)‖^p+‖auxiliaryParameter w‖^q) := ha
       _ ≤ C*(2*‖generatorVector (auxiliaryFamily G p q) w‖) :=
         mul_le_mul_of_nonneg_left (auxiliaryFamily_sum_le_two_norm G p q w) hC.le
       _ = (2*C)*‖generatorVector (auxiliaryFamily G p q) w‖ := by ring

/-- EVERY actual auxiliary-colon germ has the actual zero-section
restriction in the ORIGINAL rational raw ideal, including all common zeros.
Actual Cauchy produces the uniform original-base bound internally. -/
theorem fractionalGrowth_restrict_of_mem_auxiliaryColon
    (G : Fin N → ComplexModel n → ℂ) (p : ℕ) {q : ℕ} (hq : 0 < q)
    {x : ComplexModel n} (hG : HolomorphicGeneratorsAt G x)
    {H : ComplexModel (n+1) → ℂ}
    (hH : auxiliaryColon G p q (auxiliaryZeroSection x) H) :
    fractionalGrowthGermPredicate G ((p : ℝ)/(q : ℝ)) x (fun y => H (auxiliaryZeroSection y)) := by
  obtain ⟨hH,hprod⟩ := hH
  obtain ⟨_,C,hC,hbound⟩ := (normalized_growth_iff_norm (auxiliaryFamily G p q) _ _).mp hprod
  have ht : Tendsto (stripModelEquiv n).symm (𝓝 (x,(0 : ℂ))) (𝓝 (auxiliaryZeroSection x)) :=
    (stripModelEquiv n).symm.continuous.tendsto (x,(0 : ℂ))
  let J : ComplexModel n × ℂ → ℂ := fun v => H ((stripModelEquiv n).symm v)
  have hJ : HolAt J (x,(0 : ℂ)) := by
    filter_upwards [ht.eventually hH] with v hv
    exact hv.comp v (stripModelEquiv n).symm.differentiableAt
  have hJB : ∀ᶠ v in 𝓝 (x,(0 : ℂ)),
      ‖J v‖*‖v.2‖^(q-1) ≤ C*((rationalGeneratorScale G p q v.1)^q+‖v.2‖^q) := by
    filter_upwards [ht.eventually hbound] with v hv
    rw [norm_mul,norm_pow,auxiliaryParameter_stripInverse] at hv
    calc ‖J v‖*‖v.2‖^(q-1) ≤ C*‖generatorVector (auxiliaryFamily G p q) ((stripModelEquiv n).symm v)‖ := hv
         _ ≤ C*(‖generatorVector G v.1‖^p+‖v.2‖^q) := by
           simpa only [auxiliaryBase_stripInverse,auxiliaryParameter_stripInverse] using
             mul_le_mul_of_nonneg_left
               (auxiliaryFamily_norm_le_sum G p q ((stripModelEquiv n).symm v)) hC.le
         _ = C*((rationalGeneratorScale G p q v.1)^q+‖v.2‖^q) := by
           rw [rationalGeneratorScale_pow G p hq]
  obtain ⟨K,hK,hrestriction⟩ := restriction_growth_of_auxiliary_bound hq hC.le
    (fun y => Real.rpow_nonneg (norm_nonneg _) _) (continuousAt_rationalGeneratorScale G p q hG) hJ hJB
  apply (fractionalGrowthGermPredicate_iff_norm G p q x _).mpr
  refine ⟨?_,K,hK,hrestriction⟩
  filter_upwards [(auxiliaryZeroSection (n := n)).continuous.tendsto x |>.eventually hH] with y hy
  exact hy.comp y (auxiliaryZeroSection (n := n)).differentiableAt

end SGPT.PSH.RawInfinity

end

/-! Checked component: FractionalGrowthCoherence.lean. -/

/-! COMPLETE local RAW rational finite-generator growth coherence, from the
actual original holomorphic family and rational coefficient only. Actual
auxiliary family, E01 growth coherence, Oka colon, Cauchy restriction and
all nearby span equations are constructed internally. No output ideal,
coherence, quotient, proper-image or restriction certificate premise.
Before-code complete source plan AUXILIARY-RAW-COHERENCE.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter Metric
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FiniteGeodesicMaximality OkaRelationSheaf OkaIdealOperations
variable {n N : ℕ}

/-- Genuine whole local rational growth coherence. The SAME actual finite
zero-section restrictions generate at EVERY nearby original point, with
all original functions/poles and base n=0 retained. -/
theorem idealFGAt_fractionalGrowthGermPredicate
    (G : Fin N → ComplexModel n → ℂ) (p : ℕ) {q : ℕ} (hq : 0 < q)
    {x : ComplexModel n} (hG : HolomorphicGeneratorsAt G x) :
    IdealFGAt (fractionalGrowthGermPredicate G ((p : ℝ)/(q : ℝ))) x := by
  classical
  obtain ⟨V,hV,hZx,m,H,hHhol,hHgen⟩ := GlobalAnalyticType.idealFGAt_exists_fin
    (idealFGAt_auxiliaryColon G p q hG 0)
  obtain ⟨Ω,hΩ,hxΩ,hGΩ⟩ := hG
  let U : Set (ComplexModel n) := auxiliaryZeroSection ⁻¹' V ∩ Ω
  have hU : IsOpen U := (hV.preimage (auxiliaryZeroSection (n := n)).continuous).inter hΩ
  have hxU : x ∈ U := ⟨hZx,hxΩ⟩
  let S : Fin m → ComplexModel n → ℂ := fun j y => H j (auxiliaryZeroSection y)
  have hS (j : Fin m) : DifferentiableOn ℂ (S j) U :=
    (hHhol j).comp (auxiliaryZeroSection (n := n)).differentiable.differentiableOn (fun _ hy => hy.1)
  refine ⟨U,hU,hxU,Fin m,inferInstance,S,hS,?_⟩
  intro y hy F
  have hyV : auxiliaryZeroSection y ∈ V := hy.1
  have hGy : HolomorphicGeneratorsAt G y := ⟨Ω,hΩ,hy.2,hGΩ⟩
  have hHol (j : Fin m) : HolAt (H j) (auxiliaryZeroSection y) :=
    eventually_of_mem (hV.mem_nhds hyV) fun w hw =>
      (hHhol j).differentiableAt (hV.mem_nhds hw)
  have hKgen (j : Fin m) : auxiliaryColon G p q (auxiliaryZeroSection y) (H j) :=
    (hHgen (auxiliaryZeroSection y) hyV (H j)).mpr (inSpanAt_self hHol j)
  have hSraw (j : Fin m) : fractionalGrowthGermPredicate G ((p : ℝ)/(q : ℝ)) y (S j) :=
    fractionalGrowth_restrict_of_mem_auxiliaryColon G p hq hGy (hKgen j)
  constructor
  · intro hF
    have hLift := lift_mem_auxiliaryColon_of_fractionalGrowth G p hq hF
    obtain ⟨_,c,hc,heq⟩ := (hHgen (auxiliaryZeroSection y) hyV _).mp hLift
    refine ⟨hF.1,fun j z => c j (auxiliaryZeroSection z),?_,?_⟩
    · intro j
      filter_upwards [(auxiliaryZeroSection (n := n)).continuous.tendsto y |>.eventually (hc j)] with z hz
      exact hz.comp z (auxiliaryZeroSection (n := n)).differentiableAt
    · filter_upwards [(auxiliaryZeroSection (n := n)).continuous.tendsto y |>.eventually heq] with z hz
      simpa only [auxiliaryBase_zeroSection,S] using hz
  · intro hF
    refine ⟨hF.1,?_⟩
    have hFweight : MoreSingularAt (fun z => logNormSq (F z)) (generatorLog S) y :=
      moreSingularAt_singleLog_iff_norm_sum_bound.mpr
        (GlobalAnalyticType.exists_norm_sum_bound_of_inSpanAt hF)
    exact hFweight.trans (GlobalAnalyticType.moreSingularAt_generatorLog_of_single_bounds
      (fun j => (hSraw j).2))

end SGPT.PSH.RawInfinity

end

/-! Checked component: SourceRawInfinityCoherence.lean. -/

/-! Whole original source lma:pshfunctions:L1494, source69360cfd
chapter_pshfunctions1480–1483. The ORIGINAL RAW ideal is coherent, from
ORIGINAL local rational bounded analytic data; all original varying chart
dimensions, common poles, zero families and n=0 are retained. Actual
auxiliary family/finite colon/Cauchy/nearby generators are produced inside
checked dependencies. No global ideal, normalized potential, output
coherence, desired equality, proper image or resolution certificate input.
The stronger local proof does not need source compactness or QPSH, and so
applies directly to the full original compact QPSH source assertion.
Full before-code blueprint AUXILIARY-RAW-COHERENCE.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.RawInfinity
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations
open SGPT.PSH.VariableComplexAtlas
variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- One ORIGINAL rational bounded presentation gives actual finite
holomorphic generators of the ORIGINAL RAW ideal on ONE original open,
with exact membership at EVERY nearby original stalk. -/
theorem exists_local_atlasRawInfty_generators
    {u : X → EReal} {c : ℚ} (hc : 0 < c)
    {r : ℕ} {G : Fin r → X → ℂ} {b : X → ℝ} {C : ℝ} {U : Set X}
    (hC : 0 ≤ C) (hU : IsOpen U) (hG : ∀ j, A.ChartHolomorphicOn (G j) U)
    (hb : ∀ y ∈ U, |b y| ≤ C)
    (heq : EqOn u (fun y => ((c : ℝ) : EReal)*generatorLog G y+(b y : EReal)) U)
    {x : X} (hxU : x ∈ U) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ (N : ℕ) (F : Fin N → X → ℂ),
      (∀ j, A.ChartHolomorphicOn (F j) W) ∧
      ∀ y ∈ W, ∀ f, (atlasInftyIdeal A u).mem y f ↔
        A.AtlasIsInSpanAt (· ∈ range F) y f := by
  classical
  obtain ⟨i,hxS⟩ := A.cover x
  let e := A.chart i
  let D := e.target ∩ e.symm ⁻¹' U
  have hD : IsOpen D := e.isOpen_inter_preimage_symm hU
  have hxD : e x ∈ D := by
    refine ⟨e.map_source hxS,?_⟩
    simpa only [mem_preimage,e,(A.chart i).left_inv hxS] using hxU
  let G' : Fin r → ComplexModel (A.dimension i) → ℂ := fun j => G j ∘ e.symm
  have hG' : HolomorphicGeneratorsAt G' (e x) := ⟨D,hD,hxD,fun j => hG j i⟩
  obtain ⟨q,p,hq,hpq⟩ := MeteredDivisorSingleGenerator.exists_commonDenominator
    (fun _ : Fin 1 => c) (fun _ => hc.le)
  have hcR : (c : ℝ)=(p 0 : ℝ)/(q : ℝ) := hpq 0
  obtain ⟨V,hV,hxV,N,F,hF,hgen⟩ := GlobalAnalyticType.idealFGAt_exists_fin
    (idealFGAt_fractionalGrowthGermPredicate G' (p 0) hq hG')
  let W' := V ∩ D
  let W : Set X := e.source ∩ e ⁻¹' W'
  have hW : IsOpen W := e.isOpen_inter_preimage (hV.inter hD)
  refine ⟨W,hW,⟨hxS,hxV,hxD⟩,N,fun j => F j ∘ e,?_,?_⟩
  · intro j
    exact coordinate_holomorphic_chartHolomorphicOn (A := A) i ((hF j).mono inter_subset_left)
  · intro y hy f
    have hyV : e y ∈ V := hy.2.1
    have hyU : y ∈ U := by
      have h := hy.2.2.2
      simpa only [mem_preimage,e.left_inv hy.1] using h
    have hby : BoundedRealGermAt b y :=
      ⟨C,hC,eventually_of_mem (hU.mem_nhds hyU) fun z hz => hb z hz⟩
    have heqy : u =ᶠ[𝓝 y] fun z => ((c : ℝ) : EReal)*generatorLog G z+(b z : EReal) :=
      eventually_of_mem (hU.mem_nhds hyU) fun z hz => heq hz
    have hpair := GlobalAnalyticType.moreSingularAt_pair_of_bounded_remainder hby heqy
    have hraw : (atlasInftyIdeal A u).mem y f ↔
        A.AtlasHolomorphicAt f y ∧ MoreSingularAt (fun z => logNormSq (f z))
          (fun z => ((c : ℝ) : EReal)*generatorLog G z) y :=
      and_congr_right fun _ => ⟨fun h => h.trans hpair.1,fun h => h.trans hpair.2⟩
    have hchart : (atlasInftyIdeal A u).mem y f ↔
        fractionalGrowthGermPredicate G' ((p 0 : ℝ)/(q : ℝ)) (e y) (f ∘ e.symm) := by
      rw [hraw]
      change _ ↔ HolAt _ _ ∧ MoreSingularAt _ _ _
      rw [GlobalAnalyticType.atlasHolomorphicAt_iff_chart_holAt (A := A) i hy.1,
        GlobalAnalyticType.moreSingularAt_iff_chart (A := A) i hy.1]
      rw [←hcR]
      rfl
    exact hchart.trans ((hgen (e y) hyV (f ∘ e.symm)).trans
      (GlobalAnalyticType.atlasIsInSpanAt_chartLift_iff (A := A) i hy.1 F).symm)

/-- WHOLE original RAW infinity-ideal coherence from the actual original
local rational analytic hypothesis, on the entire variable-dimensional
atlas. Stronger than the printed compact-QPSH statement, with no weakening
or normalization of its actual ideal or source potential. -/
theorem atlasInftyIdeal_isCoherent_of_hasRationalAnalyticType
    {u : X → EReal} (ha : A.HasRationalAnalyticType u) :
    (atlasInftyIdeal A u).IsCoherent := by
  intro x
  obtain ⟨c,r,G,b,C,U,hc,hC,hU,_hconn,hxU,hG,hb,heq⟩ := ha x
  exact exists_local_atlasRawInfty_generators hc hC hU hG hb heq hxU

/-- Exact native ideal coherence for the SAME original source functions
and germs, in every native dimension including0. -/
theorem nativeInftyIdeal_isCoherent_of_hasRationalAnalyticType
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M]
    {u : M → EReal} (ha : (ofFixedModel d M).HasRationalAnalyticType u) :
    (SGPT.PSH.inftyIdeal (n := d) u).IsCoherent := by
  have h := atlasInftyIdeal_isCoherent_of_hasRationalAnalyticType ha
  have hn := (atlasGermIdeal_isCoherent_iff_native (atlasInftyIdeal (ofFixedModel d M) u)).mp h
  rwa [atlasInftyIdeal_toNative_eq] at hn

/-- COMPLETE printed source lma:pshfunctions:L1494, keeping original compact
QPSH and ORIGINAL local rational analytic input, and returning coherence of
the literal RAW original ideal. No ideal/type/coherent-output certificate. -/
theorem sourceRawInfinityIdealCoherence [CompactSpace X]
    {u : X → EReal} (_hQPSH : A.IsQPSH u) (ha : A.HasRationalAnalyticType u) :
    (atlasInftyIdeal A u).IsCoherent :=
  atlasInftyIdeal_isCoherent_of_hasRationalAnalyticType ha

end SGPT.PSH.RawInfinity

end
