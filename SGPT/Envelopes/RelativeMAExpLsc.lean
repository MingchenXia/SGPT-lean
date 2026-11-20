import SGPT.Envelopes.RelativeMALsc
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Lower semicontinuity of exponential integrals against non-pluripolar measures

For nonpositive `θ`-psh potentials `w_j → v` in `L¹` and a finite measure `ν`
charging no pluripolar set,
`∫ e^{λ v} dν ≤ lim ∫ e^{λ w_j} dν` whenever the right-hand limit exists
(Xia, *Foundations of pluripotential theory*,
`cor:exponential-psh-measure-continuity`, lower semicontinuous half).

The potentials may be unbounded. We truncate: `max(w_j, -N)` is `(θ + A ω)`-psh
for a constant `A` with `θ + A ω ≥ 0`, uniformly bounded, and still converges in
`L¹`; `e^{λ max(a,-N)} ≤ e^{λ a} + e^{-λ N}`, so the bounded case
(`RelativeMALsc`) gives the claim up to `e^{-λ N} ν(X)`, and `N → ∞`.

Integrands use the real value `Real.exp (λ * (u x).toReal)`; at the pole set of
`u` (a pluripolar set, hence `ν`-null) this differs from `e^{λ u} = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

/-- The real exponential weight `e^{λ u}` (with value `1` on the pole set). -/
def expWeight {X : Type*} (lam : ℝ) (u : X → EReal) (x : X) : ℝ := Real.exp (lam * (u x).toReal)

theorem convexOn_exp_mul (lam : ℝ) : ConvexOn ℝ univ (fun t : ℝ => Real.exp (lam * t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := convexOn_exp.2 (mem_univ (lam * x)) (mem_univ (lam * y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  convert h using 2
  ring

theorem coe_max_real (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_max

theorem canonicalERealAbsDiff_max_le (a b : EReal) (c : ℝ) :
    canonicalERealAbsDiff (max a c) (max b c) ≤ canonicalERealAbsDiff a b := by
  induction a using EReal.rec with
  | bot =>
    induction b using EReal.rec with
    | bot => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | coe b => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | top => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  | coe a =>
    induction b using EReal.rec with
    | bot => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | coe b =>
      rw [← coe_max_real, ← coe_max_real, canonicalERealAbsDiff_coe, canonicalERealAbsDiff_coe]
      exact ENNReal.ofReal_le_ofReal (abs_max_sub_max_le_abs a b c)
    | top => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  | top =>
    induction b using EReal.rec with
    | bot => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | coe b => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | top => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] in
theorem measurable_expWeight {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (lam : ℝ) : Measurable (expWeight lam u) :=
  Real.continuous_exp.measurable.comp (measurable_const.mul
    (measurable_ereal_toReal.comp hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem expWeight_nonneg (lam : ℝ) (u : M → EReal) (x : M) : 0 ≤ expWeight lam u x :=
  (Real.exp_pos _).le

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem expWeight_le_one {lam : ℝ} (hlam : 0 ≤ lam) {u : M → EReal} (hu : ∀ x, u x ≤ 0)
    (x : M) : expWeight lam u x ≤ 1 := by
  unfold expWeight
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hlam (EReal.toReal_nonpos (hu x))

omit [CompactSpace M] in
theorem integrable_expWeight {ν : Measure M} [IsFiniteMeasure ν] {lam : ℝ} (hlam : 0 ≤ lam)
    {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : IsThetaPshPotential θ u)
    (hu0 : ∀ x, u x ≤ 0) : Integrable (expWeight lam u) ν :=
  Integrable.of_bound (measurable_expWeight hu lam).aestronglyMeasurable 1
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (expWeight_nonneg _ _ _)]
      exact expWeight_le_one hlam hu0 x)

omit [CompactSpace M] [BorelSpace M] in
/-- The pole set of a `θ`-psh potential is null for a measure charging no pluripolar set. -/
theorem ae_ne_bot_of_doesNotCharge {ν : Measure M}
    (hν : DoesNotChargeManifoldPluripolar (n := n) ν) {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) : ∀ᵐ x ∂ν, u x ≠ ⊥ := by
  apply ae_iff.mpr
  simpa only [ne_eq, not_not] using hν _ (quasiPsh_poles_manifoldLocallyPluripolar hu.quasiPshPotential)

variable [ConnectedSpace M]

/-- **Lower semicontinuity of `∫ e^{λ u} dν`** along `L¹` convergence of nonpositive
`θ`-psh potentials, for a finite measure charging no pluripolar set. -/
theorem integral_expWeight_le_of_tendsto (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {ν : Measure M} [IsFiniteMeasure ν]
    (hν : DoesNotChargeManifoldPluripolar (n := n) ν) {lam : ℝ} (hlam : 0 < lam)
    {w : ℕ → M → EReal} {v : M → EReal} (hw : ∀ j, IsThetaPshPotential θ.val (w j))
    (hv : IsThetaPshPotential θ.val v) (hw0 : ∀ j x, w j x ≤ 0) (hv0 : ∀ x, v x ≤ 0)
    (hlim : ManifoldL1LocallyTendsto (n := n) w atTop v)
    {L : ℝ} (hL : Tendsto (fun j => ∫ x, expWeight lam (w j) x ∂ν) atTop (𝓝 L)) :
    ∫ x, expWeight lam v x ∂ν ≤ L := by
  obtain ⟨A, hA, hθA⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega θ
  set θ' : ClosedRealOneOneForm n M := θ + A • omega.form with hθ'
  have hsemi : (A • omega.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive hA.le
  have hw' : ∀ j, IsThetaPshPotential θ'.val (w j) := fun j =>
    LocalPotentials.isThetaPshPotential_add_of_semipositive (hw j) hsemi
  have hv' : IsThetaPshPotential θ'.val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv hsemi
  have hconst : ∀ c : ℝ, IsThetaPshPotential θ'.val (fun _ => (c : EReal)) := by
    intro c
    have h := ((LocalPotentials.isThetaPshPotential_zero_iff θ').mpr hθA).add_const c
    simpa only [zero_add] using h
  let vol : Measure M := IntegrationCurrent.kahlerVolume omega
  have hvol : IsSmoothPositiveVolume (n := n) vol :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  have hglob : Tendsto (fun j => globalL1EDistance vol (w j) v) atTop (𝓝 0) :=
    (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hvol
      (fun j => (hw j).1.quasiPlurisubharmonic) hv.1.quasiPlurisubharmonic).mp hlim
  have hpole : ∀ᵐ x ∂ν, v x ≠ ⊥ := ae_ne_bot_of_doesNotCharge hν hv
  have hmassν : (ν univ).toReal = ν.real univ := rfl
  -- the estimate for every truncation level
  have hstep : ∀ N : ℕ, ∫ x, expWeight lam v x ∂ν ≤
      L + Real.exp (-(lam * N)) * ν.real univ := by
    intro N
    let c : ℝ := -(N : ℝ)
    let q : ℕ → M → ℝ := fun j x => (max (w j x) (c : EReal)).toReal
    let p : M → ℝ := fun x => (max (v x) (c : EReal)).toReal
    have hmaxfin : ∀ (a : EReal), a ≤ 0 → ((max a (c : EReal)).toReal : EReal) = max a c := by
      intro a ha
      refine EReal.coe_toReal ?_ ?_
      · exact ne_top_of_le_ne_top EReal.zero_ne_top (max_le ha
          (EReal.coe_nonpos.mpr (by simp only [c]; exact neg_nonpos.mpr (Nat.cast_nonneg N))))
      · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (le_max_right _ _)
    have hqe : ∀ j, (fun x => (q j x : EReal)) = fun x => max (w j x) (c : EReal) := fun j =>
      funext fun x => hmaxfin (w j x) (hw0 j x)
    have hpe : (fun x => (p x : EReal)) = fun x => max (v x) (c : EReal) :=
      funext fun x => hmaxfin (v x) (hv0 x)
    have hc0 : c ≤ 0 := by simp only [c]; exact neg_nonpos.mpr (Nat.cast_nonneg N)
    have hbound : ∀ (a : EReal), a ≤ 0 → |(max a (c : EReal)).toReal| ≤ N := by
      intro a ha
      have h1 : (c : EReal) ≤ max a c := le_max_right _ _
      have h2 : max a (c : EReal) ≤ 0 := max_le ha (EReal.coe_nonpos.mpr hc0)
      rw [← hmaxfin a ha] at h1 h2
      rw [abs_le]
      constructor
      · have := EReal.coe_le_coe_iff.mp h1
        simp only [c] at this
        linarith
      · have := EReal.coe_le_coe_iff.mp (h2.trans_eq EReal.coe_zero.symm)
        linarith [Nat.cast_nonneg (α := ℝ) N]
    have hq : ∀ j, IsThetaPshPotential θ'.val (fun x => (q j x : EReal)) := fun j => by
      rw [hqe j]; exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max (hw' j) (hconst c)
    have hp : IsThetaPshPotential θ'.val (fun x => (p x : EReal)) := by
      rw [hpe]; exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hv' (hconst c)
    have hqlim : ManifoldL1LocallyTendsto (n := n) (fun j x => (q j x : EReal)) atTop
        (fun x => (p x : EReal)) := by
      refine (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hvol
        (fun j => (hq j).1.quasiPlurisubharmonic) hp.1.quasiPlurisubharmonic).mpr ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglob
        (fun _ => zero_le) (fun j => ?_)
      unfold globalL1EDistance
      rw [hqe j, hpe]
      exact lintegral_mono fun x => canonicalERealAbsDiff_max_le _ _ _
    -- a convergent subsequence of the truncated integrals
    let J : ℕ → ℝ := fun j => ∫ x, Real.exp (lam * q j x) ∂ν
    have hJmem : ∀ j, J j ∈ Icc (0 : ℝ) (ν.real univ) := by
      intro j
      have hqm := measurable_of_isThetaPshPotential_coe (hq j)
      have hI : Integrable (fun x => Real.exp (lam * q j x)) ν :=
        integrable_comp_of_bound (F := fun t => Real.exp (lam * t))
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))
          (fun a b hab => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hlam.le)) hqm
          (B := N) (ae_of_all _ fun x => hbound _ (hw0 j x))
      refine ⟨integral_nonneg fun x => (Real.exp_pos _).le, ?_⟩
      calc J j ≤ ∫ _x, (1 : ℝ) ∂ν := by
            apply integral_mono hI (integrable_const _)
            intro x
            simp only
            rw [Real.exp_le_one_iff]
            refine mul_nonpos_of_nonneg_of_nonpos hlam.le ?_
            have h2 : max (w j x) (c : EReal) ≤ 0 := max_le (hw0 j x) (EReal.coe_nonpos.mpr hc0)
            exact EReal.toReal_nonpos h2
        _ = ν.real univ := by simp
    obtain ⟨LN, -, φ, hφ, hφlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 (ν.real univ)) hJmem
    have hφL1 : ManifoldL1LocallyTendsto (n := n) (fun k x => (q (φ k) x : EReal)) atTop
        (fun x => (p x : EReal)) := fun e K hK hKe => (hqlim e K hK hKe).comp hφ.tendsto_atTop
    have hA := integral_comp_le_of_tendsto omega θ' hν
      (F := fun t => Real.exp (lam * t))
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      (fun a b hab => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hlam.le))
      (convexOn_exp_mul lam)
      (fun k => hq (φ k)) hp (B := N) (fun k x => hbound _ (hw0 (φ k) x))
      (fun x => hbound _ (hv0 x)) hφL1 hφlim
    -- compare the truncated and untruncated integrals
    have hcmp : ∀ j x, Real.exp (lam * q j x) ≤ expWeight lam (w j) x + Real.exp (-(lam * N)) := by
      intro j x
      unfold expWeight
      simp only [q]
      by_cases hb : w j x = ⊥
      · rw [hb, max_eq_right bot_le, EReal.toReal_coe, EReal.toReal_bot, mul_zero, Real.exp_zero]
        have : lam * c = -(lam * N) := by simp only [c]; ring
        rw [this]
        linarith [Real.exp_pos (-(lam * N))]
      · have hfin : ((w j x).toReal : EReal) = w j x :=
          EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (hw0 j x)) hb
        rw [show max (w j x) (c : EReal) = ((max (w j x).toReal c : ℝ) : EReal) by
          rw [coe_max_real, hfin], EReal.toReal_coe]
        rcases le_total (w j x).toReal c with h | h
        · rw [max_eq_right h]
          have : lam * c = -(lam * N) := by simp only [c]; ring
          rw [this]
          linarith [Real.exp_pos (lam * (w j x).toReal)]
        · rw [max_eq_left h]
          linarith [Real.exp_pos (-(lam * N))]
    have hJle : ∀ k, J (φ k) ≤ ∫ x, expWeight lam (w (φ k)) x ∂ν +
        Real.exp (-(lam * N)) * ν.real univ := by
      intro k
      have hqm := measurable_of_isThetaPshPotential_coe (hq (φ k))
      have hI : Integrable (fun x => Real.exp (lam * q (φ k) x)) ν :=
        integrable_comp_of_bound (F := fun t => Real.exp (lam * t))
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))
          (fun a b hab => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hlam.le)) hqm
          (B := N) (ae_of_all _ fun x => hbound _ (hw0 (φ k) x))
      have hIw := integrable_expWeight (ν := ν) hlam.le (hw (φ k)) (hw0 (φ k))
      calc J (φ k) ≤ ∫ x, (expWeight lam (w (φ k)) x + Real.exp (-(lam * N))) ∂ν :=
            integral_mono hI (hIw.add (integrable_const _)) (fun x => hcmp (φ k) x)
        _ = _ := by rw [integral_add hIw (integrable_const _)]; simp [mul_comm]
    have hLN : LN ≤ L + Real.exp (-(lam * N)) * ν.real univ :=
      le_of_tendsto_of_tendsto' hφlim ((hL.comp hφ.tendsto_atTop).add_const _) hJle
    have hvle : ∫ x, expWeight lam v x ∂ν ≤ ∫ x, Real.exp (lam * p x) ∂ν := by
      have hpm := measurable_of_isThetaPshPotential_coe hp
      have hI : Integrable (fun x => Real.exp (lam * p x)) ν :=
        integrable_comp_of_bound (F := fun t => Real.exp (lam * t))
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))
          (fun a b hab => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hlam.le)) hpm
          (B := N) (ae_of_all _ fun x => hbound _ (hv0 x))
      apply integral_mono_ae (integrable_expWeight hlam.le hv hv0) hI
      filter_upwards [hpole] with x hx
      unfold expWeight
      simp only [p]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hlam.le
      have hfin : ((v x).toReal : EReal) = v x :=
        EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (hv0 x)) hx
      rw [show max (v x) (c : EReal) = ((max (v x).toReal c : ℝ) : EReal) by
          rw [coe_max_real, hfin], EReal.toReal_coe]
      exact le_max_left _ _
    linarith
  -- let the truncation level tend to infinity
  have hlimN : Tendsto (fun N : ℕ => L + Real.exp (-(lam * N)) * ν.real univ) atTop
      (𝓝 (L + 0 * ν.real univ)) := by
    refine tendsto_const_nhds.add (Tendsto.mul_const _ ?_)
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop hlam
  rw [zero_mul, add_zero] at hlimN
  exact ge_of_tendsto' hlimN hstep

end SGPT.Envelopes.RelativeMA
