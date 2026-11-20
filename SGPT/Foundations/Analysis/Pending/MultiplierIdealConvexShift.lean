import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.RestrictionOhsawaTakegoshi
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Shifting the level of a multiplier ideal across a convex combination (route F, step F-b P3)

Source: Copy-4, `sec:trace-approx` as adapted on route F
(`scratch/tn23-envelopes-qea-plan-0117.md` §5.2, F-b step 3; blueprint `pc:f-ideal-shift`):

> `(1-t) V_ε + t w_ε ≤ V_θ`.  Let `f ∈ 𝓘((q+1) V_ε)_x`.  Then `e^{-q V_θ} ≤ e^{-q(1-t)V_ε} e^{-qt w_ε}`, and Hölder's
> inequality with `r = (q+1)/(q(1-t))`, `r' = (q+1)/(1+qt)` bounds `∫|f|² e^{-q V_θ}` by
> `(∫|f|² e^{-(q+1)V_ε})^{1/r} (∫|f|² e^{-r' q t w_ε})^{1/r'}`.  Choosing `t` so small that `r' q t N < 2`, `N` a uniform
> bound for the Lelong numbers, Skoda's theorem makes `e^{-r' q t w_ε}` integrable, so `f ∈ 𝓘(q V_θ)_x`.

## Main results

* `exp_rpow`, `multiplierWeight_rpow`, `multiplierWeight_le_mul` — extended-real exponent arithmetic
  (`e^{-qφ} ≤ e^{-q(1-t)v} e^{-qtw}` from `(1-t)v + tw ≤ φ`, all `⊥` cases included).
* `setLIntegral_multiplierDensity_le` — **the Hölder step** on any set and any measure.
* `HasUniformLelongBound θ₂` — a `Prop` (NOT an interface, no `sorry`): one bound `N` for the Lelong numbers of all
  `θ₂`-psh potentials at all points.
* `exists_multiplierIdeal_le_of_convexComb_le_of_hasUniformLelongBound` — **P3 given the uniform bound**: for
  `q > 0` there is `t₀ > 0` such that for `0 < t ≤ t₀`, `v, φ` quasi-psh, `w` a `θ₂`-psh potential and
  `(1-t)v + tw ≤ φ` everywhere, `𝓘((q+1)v) ⊆ 𝓘(qφ)`.  Skoda (`SkodaIntegrability`) at exponent
  `c = r' q t ≤ (q+1) q t`.

What is NOT here: the uniform Lelong bound itself (`HasUniformLelongBound` for every closed real `(1,1)`-form on a
compact manifold of positive dimension); it is the remaining input of P3.

Sorry-free.
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealConvexShift

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus

noncomputable section

/-! ### Extended-real exponent arithmetic -/

section ExpArith

/-- `(e^x)^r = e^{rx}` for `r > 0`, every extended real `x`. -/
theorem exp_rpow (x : EReal) {r : ℝ} (hr : 0 < r) :
    EReal.exp x ^ r = EReal.exp ((r : EReal) * x) := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hr, EReal.exp_bot, ENNReal.zero_rpow_of_pos hr]
  | top => rw [EReal.coe_mul_top_of_pos hr, EReal.exp_top, ENNReal.top_rpow_of_pos hr]
  | coe a =>
      rw [← EReal.coe_mul, EReal.exp_coe, EReal.exp_coe,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hr.le, ← Real.exp_mul, mul_comm]

/-- `(e^{-ca})^r = e^{-(rc)a}`. -/
theorem multiplierWeight_rpow (c : ℝ) (a : EReal) {r : ℝ} (hr : 0 < r) :
    multiplierWeight c a ^ r = multiplierWeight (r * c) a := by
  rw [multiplierWeight, multiplierWeight, exp_rpow _ hr, EReal.coe_mul, mul_neg, mul_assoc]

/-- `e^{-qφ} ≤ e^{-q(1-t)v} e^{-qtw}` from `(1-t)v + tw ≤ φ`. -/
theorem multiplierWeight_le_mul {q t : ℝ} (hq : 0 < q) (ht0 : 0 < t) (ht1 : t < 1)
    {v w φ : EReal} (hv : v ≠ ⊤) (hw : w ≠ ⊤)
    (h : ((1 - t : ℝ) : EReal) * v + (t : EReal) * w ≤ φ) :
    multiplierWeight q φ ≤ multiplierWeight (q * (1 - t)) v * multiplierWeight (q * t) w := by
  unfold multiplierWeight
  rw [← EReal.exp_add]
  apply EReal.exp_monotone
  have hq' : (0 : EReal) ≤ (q : EReal) := EReal.coe_nonneg.mpr hq.le
  have h1 : (q : EReal) * (((1 - t : ℝ) : EReal) * v + (t : EReal) * w) ≤ (q : EReal) * φ :=
    mul_le_mul_of_nonneg_left h hq'
  have hdist : (q : EReal) * (((1 - t : ℝ) : EReal) * v + (t : EReal) * w) =
      ((q * (1 - t) : ℝ) : EReal) * v + ((q * t : ℝ) : EReal) * w := by
    rw [EReal.left_distrib_of_nonneg_of_ne_top hq' (EReal.coe_ne_top q), EReal.coe_mul,
      EReal.coe_mul, mul_assoc, mul_assoc]
  rw [hdist] at h1
  have hx : ((q * (1 - t) : ℝ) : EReal) * v ≠ ⊤ := by
    intro htop
    rcases EReal.mul_eq_top _ _ |>.mp htop with h | h | h | h
    · exact EReal.coe_ne_bot _ h.1
    · exact absurd h.1 (not_lt.mpr (EReal.coe_nonneg.mpr (by positivity)))
    · exact EReal.coe_ne_top _ h.1
    · exact hv h.2
  have hy : ((q * t : ℝ) : EReal) * w ≠ ⊤ := by
    intro htop
    rcases EReal.mul_eq_top _ _ |>.mp htop with h | h | h | h
    · exact EReal.coe_ne_bot _ h.1
    · exact absurd h.1 (not_lt.mpr (EReal.coe_nonneg.mpr (by positivity)))
    · exact EReal.coe_ne_top _ h.1
    · exact hw h.2
  rw [← sub_eq_add_neg, ← EReal.neg_add (Or.inr hy) (Or.inl hx)]
  exact EReal.neg_le_neg_iff.mpr h1

end ExpArith

/-! ### The Hölder step -/

section Holder

variable {E : Type*} [MeasurableSpace E]

/-- **Hölder for the multiplier densities.**  On `U`, if `(1-t)v + tw ≤ φ`, then with
`r = (q+1)/(q(1-t))`, `r' = (q+1)/(1+qt)`:
`∫_U |g|² e^{-qφ} ≤ (∫_U |g|² e^{-(q+1)v})^{1/r} (∫_U |g|² e^{-r' q t w})^{1/r'}`. -/
theorem setLIntegral_multiplierDensity_le (μ : Measure E) (U : Set E) {q t : ℝ} (hq : 0 < q)
    (ht0 : 0 < t) (ht1 : t < 1) {g : E → ℂ} {v w φ : E → EReal}
    (hvt : ∀ y ∈ U, v y ≠ ⊤) (hwt : ∀ y ∈ U, w y ≠ ⊤)
    (hle : ∀ y ∈ U, ((1 - t : ℝ) : EReal) * v y + (t : EReal) * w y ≤ φ y)
    (hgm : AEMeasurable (fun y => ENNReal.ofReal (‖g y‖ ^ 2)) (μ.restrict U))
    (hvm : AEMeasurable (fun y => multiplierWeight (q * (1 - t)) (v y)) (μ.restrict U))
    (hwm : AEMeasurable (fun y => multiplierWeight (q * t) (w y)) (μ.restrict U))
    (hU : MeasurableSet U) :
    ∫⁻ y in U, multiplierDensity φ q g y ∂μ ≤
      (∫⁻ y in U, multiplierDensity v (q + 1) g y ∂μ) ^ (1 / ((q + 1) / (q * (1 - t)))) *
      (∫⁻ y in U, multiplierDensity w ((q + 1) / (1 + q * t) * (q * t)) g y ∂μ) ^
        (1 / ((q + 1) / (1 + q * t))) := by
  set r : ℝ := (q + 1) / (q * (1 - t)) with hr
  set r' : ℝ := (q + 1) / (1 + q * t) with hr'
  have h1t : 0 < 1 - t := by linarith
  have hqt : 0 < q * (1 - t) := mul_pos hq h1t
  have hrpos : 0 < r := div_pos (by linarith) hqt
  have hr'pos : 0 < r' := div_pos (by linarith) (by nlinarith)
  have hsum : 1 / r + 1 / r' = 1 := by
    rw [hr, hr', one_div_div, one_div_div, ← add_div]
    rw [div_eq_one_iff_eq (by linarith)]
    ring
  have hconj : r.HolderConjugate r' := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [hr, one_lt_div hqt]; nlinarith
    · simpa only [one_div] using hsum
  set a : E → ℝ≥0∞ := fun y => ENNReal.ofReal (‖g y‖ ^ 2) with ha
  set F : E → ℝ≥0∞ := fun y => a y ^ (1 / r) * multiplierWeight (q * (1 - t)) (v y) with hF
  set G : E → ℝ≥0∞ := fun y => a y ^ (1 / r') * multiplierWeight (q * t) (w y) with hG
  have hFm : AEMeasurable F (μ.restrict U) :=
    (hgm.pow_const _).mul hvm
  have hGm : AEMeasurable G (μ.restrict U) :=
    (hgm.pow_const _).mul hwm
  have hFr : ∀ y, F y ^ r = multiplierDensity v (q + 1) g y := by
    intro y
    rw [hF, ENNReal.mul_rpow_of_nonneg _ _ hrpos.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hrpos.ne', ENNReal.rpow_one, multiplierWeight_rpow _ _ hrpos]
    congr 2
    rw [hr]; field_simp
  have hGr : ∀ y, G y ^ r' = multiplierDensity w ((q + 1) / (1 + q * t) * (q * t)) g y := by
    intro y
    rw [hG, ENNReal.mul_rpow_of_nonneg _ _ hr'pos.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hr'pos.ne', ENNReal.rpow_one, multiplierWeight_rpow _ _ hr'pos]
    rfl
  have hpt : ∀ y ∈ U, multiplierDensity φ q g y ≤ (F * G) y := by
    intro y hy
    have hw := multiplierWeight_le_mul hq ht0 ht1 (hvt y hy) (hwt y hy) (hle y hy)
    simp only [Pi.mul_apply, hF, hG, multiplierDensity]
    by_cases ha0 : a y = 0
    · rw [show ENNReal.ofReal (‖g y‖ ^ 2) = a y from rfl, ha0, zero_mul]
      exact bot_le
    have hatop : a y ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsplit : a y = a y ^ (1 / r) * a y ^ (1 / r') := by
      rw [← ENNReal.rpow_add _ _ ha0 hatop, hsum, ENNReal.rpow_one]
    calc ENNReal.ofReal (‖g y‖ ^ 2) * multiplierWeight q (φ y)
        = a y ^ (1 / r) * a y ^ (1 / r') * multiplierWeight q (φ y) := by
          rw [← hsplit]
      _ ≤ a y ^ (1 / r) * a y ^ (1 / r') *
            (multiplierWeight (q * (1 - t)) (v y) * multiplierWeight (q * t) (w y)) :=
          by gcongr
      _ = a y ^ (1 / r) * multiplierWeight (q * (1 - t)) (v y) *
            (a y ^ (1 / r') * multiplierWeight (q * t) (w y)) := by ring
  calc ∫⁻ y in U, multiplierDensity φ q g y ∂μ
      ≤ ∫⁻ y in U, (F * G) y ∂μ := setLIntegral_mono' hU hpt
    _ ≤ (∫⁻ y in U, F y ^ r ∂μ) ^ (1 / r) * (∫⁻ y in U, G y ^ r' ∂μ) ^ (1 / r') :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ hconj hFm hGm
    _ = _ := by simp only [hFr, hGr]; rfl

end Holder

/-! ### P3 given a uniform Lelong bound -/

section Manifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **One bound for the Lelong numbers of all `θ₂`-psh potentials at all points.**  A `Prop`, the
hypothesis of the theorem below (not an interface). -/
def HasUniformLelongBound (θ₂ : ClosedRealOneOneForm n X) : Prop :=
  ∃ N : ℝ, ∀ w : X → EReal, IsThetaPshPotential θ₂.val w → ∀ x : X,
    lelongNumber (n := n) w x ≤ ENNReal.ofReal N

/-- The weight `e^{-cP}` of an upper semicontinuous `P` is a.e. measurable on an open set. -/
theorem aemeasurable_multiplierWeight_of_upperSemicontinuousOn {m : ℕ}
    {μ : Measure (ComplexModel m)} {P : ComplexModel m → EReal} {Ω : Set (ComplexModel m)}
    (hΩ : IsOpen Ω) (hP : UpperSemicontinuousOn P Ω) {c : ℝ} (hc : c ≠ 0) :
    AEMeasurable (fun y => multiplierWeight c (P y)) (μ.restrict Ω) := by
  have hPmeas : AEMeasurable P (μ.restrict Ω) :=
    ChartWeightedL2.aemeasurable_restrict_of_upperSemicontinuousOn hP hΩ
  have hcmul : AEMeasurable (fun y => (c : EReal) * P y) (μ.restrict Ω) :=
    (continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hPmeas
  have hneg : AEMeasurable (fun y => -((c : EReal) * P y)) (μ.restrict Ω) :=
    continuous_neg.measurable.comp_aemeasurable' hcmul
  simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg

/-- **Route F, F-b step 3 (P3), given a uniform Lelong bound.**  For `q > 0` there is `t₀ > 0` such
that for `0 < t ≤ t₀`, quasi-psh `v, φ`, a `θ₂`-psh potential `w` and `(1-t)v + tw ≤ φ`,
`𝓘((q+1)v) ⊆ 𝓘(qφ)`.  Hölder with `r = (q+1)/(q(1-t))`, `r' = (q+1)/(1+qt)`, and Skoda for `w` at
the exponent `c = r' q t ≤ (q+1) q t`, which satisfies `c N < 2` for `t ≤ 1/((q+1) q (N+1))`. -/
theorem exists_multiplierIdeal_le_of_convexComb_le_of_hasUniformLelongBound
    (θ₂ : ClosedRealOneOneForm n X) (hN : HasUniformLelongBound θ₂) {q : ℝ} (hq : 0 < q) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ {v w φ : X → EReal},
      ManifoldQuasiPlurisubharmonic (n := n) v → IsThetaPshPotential θ₂.val w →
      ManifoldQuasiPlurisubharmonic (n := n) φ →
      (∀ x, ((1 - t : ℝ) : EReal) * v x + (t : EReal) * w x ≤ φ x) →
      (multiplierIdeal (n := n) (q + 1) v).Le (multiplierIdeal (n := n) q φ) := by
  classical
  obtain ⟨N, hN⟩ := hN
  set N' : ℝ := max N 0 with hN'def
  have hN'0 : 0 ≤ N' := le_max_right _ _
  have hden : 0 < (q + 1) * q * (N' + 1) := by positivity
  refine ⟨min (1 / 2) (1 / ((q + 1) * q * (N' + 1))), lt_min (by norm_num) (by positivity), ?_⟩
  intro t ht0 htt₀ v w φ hv hw hφ hconv x g hg
  have ht1 : t < 1 := lt_of_le_of_lt (htt₀.trans (min_le_left _ _)) (by norm_num)
  set c : ℝ := (q + 1) / (1 + q * t) * (q * t) with hcdef
  have hc : 0 < c := by positivity
  have hcle : c ≤ (q + 1) * q * t := by
    have h1 : (q + 1) / (1 + q * t) ≤ q + 1 :=
      div_le_self (by positivity) (by nlinarith)
    calc c ≤ (q + 1) * (q * t) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (q + 1) * q * t := by ring
  have hcN : c * N' < 2 := by
    have htle : t ≤ 1 / ((q + 1) * q * (N' + 1)) := htt₀.trans (min_le_right _ _)
    calc c * N' ≤ (q + 1) * q * t * N' := mul_le_mul_of_nonneg_right hcle hN'0
      _ ≤ (q + 1) * q * (1 / ((q + 1) * q * (N' + 1))) * N' := by gcongr
      _ = N' / (N' + 1) := by field_simp
      _ < 2 := by
          rw [div_lt_iff₀ (by linarith)]
          linarith
  -- Skoda for `w` at `x` with exponent `c`
  have hν : lelongNumber (n := n) w x < ENNReal.ofReal (2 / c) := by
    refine lt_of_le_of_lt ((hN w hw x).trans (ENNReal.ofReal_le_ofReal (le_max_left N 0))) ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ hc]
    linarith [mul_comm c N']
  obtain ⟨-, -, U₂, hU₂o, hxU₂, -, hW₂⟩ :=
    SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hw.1 hc hν
  obtain ⟨hgx, -, U₁, hU₁o, hxU₁, hgd, hW₁⟩ := hg
  refine ⟨hgx, hq, ?_⟩
  set e := complexChartAt (n := n) x with he
  set G : ComplexModel n → ℂ := fun z => g (e.val.symm z) with hGdef
  have hxt : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  -- a ball on which `G` is bounded
  have hGc : ContinuousAt G (e.val x) :=
    (hgd.differentiableAt (hU₁o.mem_nhds hxU₁)).continuousAt
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball (e.val x) ρ, ‖G z‖ < ‖G (e.val x)‖ + 1 := by
    have h := (continuous_norm.continuousAt.comp hGc).eventually
      (Iio_mem_nhds (lt_add_one ‖G (e.val x)‖))
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp h
    exact ⟨ρ, hρ, fun z hz => hsub hz⟩
  set B : ℝ := ‖G (e.val x)‖ + 1 with hB
  set U : Set (ComplexModel n) := U₁ ∩ U₂ ∩ e.val.target ∩ ball (e.val x) ρ with hUdef
  have hUo : IsOpen U :=
    ((hU₁o.inter hU₂o).inter e.val.open_target).inter isOpen_ball
  have hxU : e.val x ∈ U := ⟨⟨⟨hxU₁, hxU₂⟩, hxt⟩, mem_ball_self hρ⟩
  have hUU₁ : U ⊆ U₁ := fun y hy => hy.1.1.1
  have hUU₂ : U ⊆ U₂ := fun y hy => hy.1.1.2
  have hUt : U ⊆ e.val.target := fun y hy => hy.1.2
  have hGU : ContinuousOn G U := hgd.continuousOn.mono hUU₁
  have husc : ∀ {u : X → EReal}, ManifoldQuasiPlurisubharmonic (n := n) u →
      UpperSemicontinuousOn (chartFunction u e) U := fun hu =>
    (QuasiPlurisubharmonicOn.upperSemicontinuousOn (hu e)).mono hUt
  refine ⟨U, hUo, hxU, hgd.mono hUU₁, ?_, ?_⟩
  · exact RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn hUo
      (husc hφ) hGU hq.ne'
  -- the Hölder bound
  have hgm : AEMeasurable (fun y => ENNReal.ofReal (‖G y‖ ^ 2)) (volume.restrict U) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((continuous_norm.comp_continuousOn hGU).pow 2)).aemeasurable hUo.measurableSet
  have hH := setLIntegral_multiplierDensity_le volume U hq ht0 ht1 (g := G)
    (v := chartFunction v e) (w := chartFunction w e) (φ := chartFunction φ e)
    (fun y _ => hv.ne_top _) (fun y _ => hw.1.quasiPlurisubharmonic.ne_top _)
    (fun y _ => hconv _) hgm
    (aemeasurable_multiplierWeight_of_upperSemicontinuousOn hUo (husc hv)
      (mul_pos hq (by linarith)).ne')
    (aemeasurable_multiplierWeight_of_upperSemicontinuousOn hUo
      (husc hw.1.quasiPlurisubharmonic) (mul_pos hq ht0).ne')
    hUo.measurableSet
  refine lt_of_le_of_lt hH (ENNReal.mul_lt_top ?_ ?_)
  · refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    exact (lt_of_le_of_lt (lintegral_mono_set hUU₁) hW₁.2).ne
  · refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    have hpt : ∀ y ∈ U, multiplierDensity (chartFunction w e) c G y ≤
        ENNReal.ofReal (B ^ 2) * multiplierDensity (chartFunction w e) c (fun _ => (1 : ℂ)) y := by
      intro y hy
      simp only [multiplierDensity, norm_one, one_pow, ENNReal.ofReal_one, one_mul]
      gcongr
      exact (hball y hy.2).le
    refine (lt_of_le_of_lt (setLIntegral_mono' hUo.measurableSet hpt) ?_).ne
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (lintegral_mono_set hUU₂) hW₂.2)

end Manifold

end

end SGPT.Foundations.Analysis.Pending.MultiplierIdealConvexShift
