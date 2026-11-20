import SGPT.Okounkov.TranscendentalWNVolumeGlobalDeformation

/-!
# The identification of the partial Legendre transform (package WN-VF2)

Blueprint node `tok-wn-vf:legendre-bounds` (chapter `claude-tok-wn-vf`, sub-lemmas in
`claude-tok-wn-vf2`); WN21 Proposition 4.5.

Let `w` be the base potential on `X × ℙ¹` (`exists_basePotential`) and
`u(x, τ) = w(x, [τ : 1]) + b log (1 + |τ|²)` (`affineTwist`), WN21's envelope `u` on `X × ℂ*`.
For `t ≥ 0` put `v_t = V_{θ - tη} + t g` (`twistEnvelope`, `g = log |s_Z|²_h`).

* `partialLegendre_eq_bot_of_le`: `û_λ ≡ -∞` for `λ ∉ [0, b]` (`u ≤ b log (1 + |τ|²)`).
* `twistEnvelope_le_partialLegendre`: `v_t ≤ û_λ` for `λ ∈ [0, b]`, `t = max (c - λ) 0`: the
  competitor `v_t ∘ π_X μ + λ log N₀ + (b - λ) log N₁ - c log |s_ℰ|²` lies below `V_θ̃` off `ℰ`
  (`tok-wn-vf:competitor`, generalized to the weight `λ log N₀ + (b - λ) log N₁`).
* `partialLegendre_le_twistEnvelope_add`: `û_λ ≤ v_t + C`: at `|τ|² = e^g` the obstacle gives
  `û_λ ≤ (c - λ) g + C` off `Z`, and `û_λ - t g` extends across `Z` below `V_{θ - tη} + C`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Toric

/-! ### `û_λ ≡ -∞` off `[0, b]` -/

section Bot

variable {Y : Type*}

theorem log_one_add_exp_le_of_nonpos {s : ℝ} (hs : s ≤ 0) : Real.log (1 + Real.exp s) ≤ Real.log 2 :=
  Real.log_le_log (by positivity) (by linarith [Real.exp_le_one_iff.mpr hs])

theorem log_one_add_exp_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    Real.log (1 + Real.exp s) ≤ Real.log 2 + s := by
  have h1 : 1 + Real.exp s ≤ 2 * Real.exp s := by linarith [Real.one_le_exp hs]
  calc Real.log (1 + Real.exp s) ≤ Real.log (2 * Real.exp s) :=
        Real.log_le_log (by positivity) h1
    _ = Real.log 2 + s := by rw [Real.log_mul (by norm_num) (Real.exp_pos s).ne', Real.log_exp]

theorem norm_exp_half_sq (s : ℝ) : ‖Complex.exp ((s : ℂ) / 2)‖ ^ 2 = Real.exp s := by
  rw [norm_exp_half]
  simp only [Complex.ofReal_re]
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- **`û_λ ≡ -∞` for `λ ∉ [0, b]`** (WN21 §4, after Proposition 4.2): if
`u(x, τ) ≤ b log (1 + |τ|²)` on `ℂ*` with `b ≥ 0`. -/
theorem partialLegendre_eq_bot_of_le {u : Y → ℂ → EReal} {b : ℝ} (hb : 0 ≤ b)
    (hu : ∀ x τ, τ ≠ 0 → u x τ ≤ ((b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal)) {lam : ℝ}
    (hlam : lam ∉ Icc 0 b) (x : Y) : partialLegendre u lam x = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  -- the value at `τ = e^{s/2}` is at most `b log (1 + e^s) - λ s`
  have hval : ∀ s : ℝ, partialLegendre u lam x ≤
      ((b * Real.log (1 + Real.exp s) - lam * s : ℝ) : EReal) := by
    intro s
    have hτ : Complex.exp ((s : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
    refine (iInf_le _ ⟨Complex.exp ((s : ℂ) / 2), hτ⟩).trans ?_
    have h1 := hu x _ hτ
    rw [norm_exp_half_sq] at h1
    simp only
    rw [logNormSq_exp_half, sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, EReal.coe_add]
    exact add_le_add h1 le_rfl
  rcases not_and_or.mp hlam with h | h
  · -- `λ < 0`: let `s → -∞`
    push Not at h
    set s := min 0 ((y - b * Real.log 2 - 1) / (-lam)) with hs
    have hs0 : s ≤ 0 := min_le_left _ _
    have hs1 : s ≤ (y - b * Real.log 2 - 1) / (-lam) := min_le_right _ _
    refine (hval s).trans_lt (EReal.coe_lt_coe_iff.mpr ?_)
    have h2 := mul_le_mul_of_nonneg_left (log_one_add_exp_le_of_nonpos hs0) hb
    have h3 : (-lam) * s ≤ y - b * Real.log 2 - 1 := by
      rw [le_div_iff₀ (by linarith)] at hs1; linarith
    nlinarith
  · -- `λ > b`: let `s → +∞`
    push Not at h
    set s := max 0 ((b * Real.log 2 - y + 1) / (lam - b)) with hs
    have hs0 : 0 ≤ s := le_max_left _ _
    have hs1 : (b * Real.log 2 - y + 1) / (lam - b) ≤ s := le_max_right _ _
    refine (hval s).trans_lt (EReal.coe_lt_coe_iff.mpr ?_)
    have h2 := mul_le_mul_of_nonneg_left (log_one_add_exp_le_of_nonneg hs0) hb
    have h3 : b * Real.log 2 - y + 1 ≤ (lam - b) * s := by
      rw [div_le_iff₀ (by linarith)] at hs1; linarith
    nlinarith

end Bot

/-! ### The envelopes `v_t` -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- `v_t = V_{θ - tη} + t g` (WN21 §4: `v_t = P_θ(t g)`, `tok-wn:envelopes` (b)). -/
def twistEnvelope (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (t : ℝ) (x : F.carrier) : EReal :=
  thetaPshSupremum (θ - t • E.curvature).val x + (t : EReal) * E.weight x

/-- The level `t = max (c - λ) 0`. -/
def legendreLevel (c lam : ℝ) : ℝ := max (c - lam) 0

theorem legendreLevel_nonneg (c lam : ℝ) : 0 ≤ legendreLevel c lam := le_max_right _ _

theorem ereal_coe_mul_nonpos {t : ℝ} (ht : 0 ≤ t) {g : EReal} (hg : g ≤ 0) :
    (t : EReal) * g ≤ 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  induction g using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht]; exact bot_le
  | top => exact absurd hg (by simp)
  | coe g =>
    rw [← EReal.coe_mul]; exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le
      (EReal.coe_nonpos.mp hg))

theorem twistEnvelope_le_zero {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE0 : ∀ x, E.weight x ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) (x : F.carrier) : twistEnvelope F θ E t x ≤ 0 := by
  have h1 := thetaPshSupremum_le_zero (θ - t • E.curvature).val x
  have h2 := ereal_coe_mul_nonpos ht (hE0 x)
  simpa [twistEnvelope] using add_le_add h1 h2

theorem twistEnvelope_zero (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) :
    twistEnvelope F θ E 0 = thetaPshSupremum θ.val := by
  funext x; simp [twistEnvelope]

/-- `v_t` is `θ`-psh: `V_{θ - tη}` is `(θ - tη)`-psh and `t g` is `tη`-psh. -/
theorem isThetaPshPotential_twistEnvelope {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE0 : ∀ x, E.weight x ≤ 0)
    (hEs : E.support = F.flag (1 : Fin (m + 2))) {t : ℝ} (ht : 0 ≤ t)
    (hV : IsThetaPshPotential (θ - t • E.curvature).val (thetaPshSupremum (θ - t • E.curvature).val)) :
    IsThetaPshPotential θ.val (twistEnvelope F θ E t) := by
  rcases ht.eq_or_lt with rfl | ht'
  · rw [twistEnvelope_zero]; simpa using hV
  refine ⟨?_, ?_⟩
  · have h2 := GlobalMultilinearExpansion.thetaPlurisubharmonic_smul ht'
      (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E)
    have h3 := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul one_pos one_pos hV.1 h2
    simp only [one_smul, EReal.coe_one, one_mul] at h3
    rwa [sub_add_cancel] at h3
  · intro x O hO hxO
    have hnot : ¬ O ⊆ E.support := fun hsub => by
      have := interior_maximal hsub hO
      rw [hEs, interior_firstFlag F] at this
      exact this hxO
    obtain ⟨x', hx'O, hx'Z⟩ := not_subset.mp hnot
    have hZc : IsOpen E.supportᶜ := (ResidualNef.isComplexAnalyticSubset_support E).isClosed.isOpen_compl
    obtain ⟨y, hy, hyfin⟩ := hV.2 x' (O ∩ E.supportᶜ) (hO.inter hZc) ⟨hx'O, hx'Z⟩
    refine ⟨y, hy.1, fun hbot => ?_⟩
    have hwy : E.weight y ≠ ⊥ := hy.2
    have hwy' : E.weight y = ((E.weight y).toReal : EReal) :=
      (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (hE0 y)) hwy).symm
    rw [twistEnvelope, hwy', ← EReal.coe_mul, EReal.add_eq_bot_iff] at hbot
    rcases hbot with h | h
    · exact hyfin h
    · exact EReal.coe_ne_bot _ h


/-! ### Real inequalities for the competitor -/

theorem log_le_log_add {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : Real.log a ≤ Real.log (b + a) :=
  Real.log_le_log ha (by linarith)

/-- The competitor bound, interior weights (`0 < λ < b`). -/
theorem real_competitor_bound {f lam b c t G N0 N1 : ℝ} (hc : 0 < c) (hcb : c ≤ b)
    (hlam0 : 0 ≤ lam) (hlamb : lam ≤ b) (ht : t = max (c - lam) 0) (hf0 : f ≤ 0) (hG0 : 0 ≤ G)
    (hN0 : 0 < N0) (hN1 : 0 < N1) (hN0le : N0 ≤ 1) (hN1le : N1 ≤ 1)
    (hft : 0 < t → 0 < G ∧ f ≤ t * Real.log G) :
    f + lam * Real.log N0 + (b - lam) * Real.log N1 ≤ c * Real.log (G * N1 + N0) := by
  have ha0 : Real.log N0 ≤ 0 := Real.log_nonpos hN0.le hN0le
  have ha1 : Real.log N1 ≤ 0 := Real.log_nonpos hN1.le hN1le
  by_cases hl : c ≤ lam
  · have h1 : lam * Real.log N0 ≤ c * Real.log N0 := mul_le_mul_of_nonpos_right hl ha0
    have h2 : Real.log N0 ≤ Real.log (G * N1 + N0) := log_le_log_add hN0 (by positivity)
    have h3 : (b - lam) * Real.log N1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) ha1
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  push Not at hl
  have htpos : 0 < t := by rw [ht]; exact lt_max_of_lt_left (by linarith)
  obtain ⟨hG, hf⟩ := hft htpos
  have ht' : t = c - lam := by rw [ht]; exact max_eq_left (by linarith)
  rw [ht'] at hf
  have h1 : (b - lam) * Real.log N1 ≤ (c - lam) * Real.log N1 :=
    mul_le_mul_of_nonpos_right (by linarith) ha1
  set s := lam / c with hs
  have hs0 : 0 ≤ s := div_nonneg hlam0 hc.le
  have hs1 : s ≤ 1 := (div_le_one hc).mpr hl.le
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (mem_Ioi.mpr (mul_pos hG hN1))
    (mem_Ioi.mpr hN0) (sub_nonneg.mpr hs1) hs0 (by ring)
  simp only [smul_eq_mul] at hconc
  have hmono : Real.log ((1 - s) * (G * N1) + s * N0) ≤ Real.log (G * N1 + N0) := by
    apply Real.log_le_log
    · have : 0 < (1 - s) * (G * N1) + s * N0 ∨ True := Or.inr trivial
      rcases hs1.eq_or_lt with h | h
      · rw [h]; simp [hN0]
      · have : 0 < 1 - s := by linarith
        positivity
    · nlinarith [mul_pos hG hN1]
  have hlogGN : Real.log (G * N1) = Real.log G + Real.log N1 :=
    Real.log_mul hG.ne' hN1.ne'
  have hcs : c * s = lam := by rw [hs]; field_simp
  have key : (c - lam) * Real.log (G * N1) + lam * Real.log N0 ≤
      c * Real.log (G * N1 + N0) := by
    have := mul_le_mul_of_nonneg_left (hconc.trans hmono) hc.le
    have e : c * ((1 - s) * Real.log (G * N1) + s * Real.log N0) =
        (c - lam) * Real.log (G * N1) + lam * Real.log N0 := by
      rw [← hcs]; ring
    linarith
  rw [hlogGN] at key
  nlinarith

/-- The competitor bound at `λ = 0` (weight `b log N₁`). -/
theorem real_competitor_bound_zero {f b c G N0 N1 : ℝ} (hc : 0 < c) (hcb : c ≤ b)
    (hN0 : 0 ≤ N0) (hN1 : 0 < N1) (hN1le : N1 ≤ 1) (hG : 0 < G)
    (hf : f ≤ c * Real.log G) :
    f + b * Real.log N1 ≤ c * Real.log (G * N1 + N0) := by
  have ha1 : Real.log N1 ≤ 0 := Real.log_nonpos hN1.le hN1le
  have h1 : b * Real.log N1 ≤ c * Real.log N1 := mul_le_mul_of_nonpos_right hcb ha1
  have h2 : Real.log (G * N1) ≤ Real.log (G * N1 + N0) :=
    Real.log_le_log (mul_pos hG hN1) (by linarith)
  have hlogGN : Real.log (G * N1) = Real.log G + Real.log N1 := Real.log_mul hG.ne' hN1.ne'
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

/-- The competitor bound at `λ = b` (weight `b log N₀`). -/
theorem real_competitor_bound_top {f b c G N0 N1 : ℝ} (hc : 0 < c) (hcb : c ≤ b)
    (hN0 : 0 < N0) (hN0le : N0 ≤ 1) (hN1 : 0 ≤ N1) (hG : 0 ≤ G) (hf : f ≤ 0) :
    f + b * Real.log N0 ≤ c * Real.log (G * N1 + N0) := by
  have ha0 : Real.log N0 ≤ 0 := Real.log_nonpos hN0.le hN0le
  have h1 : b * Real.log N0 ≤ c * Real.log N0 := mul_le_mul_of_nonpos_right hcb ha0
  have h2 : Real.log N0 ≤ Real.log (G * N1 + N0) := log_le_log_add hN0 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

/-! ### Values of `v_t` and of the weights -/

/-- A finite value of `v_t` is `≤ 0`, and `≤ t log e^g` when `t > 0`. -/
theorem twistEnvelope_eq_coe {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE0 : ∀ x, E.weight x ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) {x : F.carrier} (hx : twistEnvelope F θ E t x ≠ ⊥) :
    ∃ f : ℝ, twistEnvelope F θ E t x = f ∧ f ≤ 0 ∧
      (0 < t → 0 < (EReal.exp (E.weight x)).toReal ∧
        f ≤ t * Real.log (EReal.exp (E.weight x)).toReal) := by
  have hle := twistEnvelope_le_zero F (θ := θ) hE0 ht x
  have hne : twistEnvelope F θ E t x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top hle
  refine ⟨(twistEnvelope F θ E t x).toReal, (EReal.coe_toReal hne hx).symm,
    EReal.toReal_nonpos hle, fun htpos => ?_⟩
  -- `x ∉ Z`: otherwise `t g = -∞`
  have hw : E.weight x ≠ ⊥ := by
    intro hbot
    apply hx
    rw [twistEnvelope, hbot, EReal.coe_mul_bot_of_pos htpos, EReal.add_bot]
  have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
  set g := (E.weight x).toReal with hg
  have hgw : E.weight x = (g : EReal) := (EReal.coe_toReal hwt hw).symm
  have hexp : (EReal.exp (E.weight x)).toReal = Real.exp g := by
    rw [hgw, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos g).le]
  rw [hexp, Real.log_exp]
  refine ⟨Real.exp_pos g, ?_⟩
  have hV : thetaPshSupremum (θ - t • E.curvature).val x ≠ ⊥ := by
    intro hbot; apply hx; rw [twistEnvelope, hbot, EReal.bot_add]
  have hV0 := thetaPshSupremum_le_zero (θ - t • E.curvature).val x
  have hVt : thetaPshSupremum (θ - t • E.curvature).val x ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top hV0
  have hdef : twistEnvelope F θ E t x =
      (((thetaPshSupremum (θ - t • E.curvature).val x).toReal + t * g : ℝ) : EReal) := by
    rw [twistEnvelope, hgw, ← EReal.coe_mul, ← EReal.coe_toReal hVt hV, EReal.coe_add,
      EReal.toReal_coe]
  rw [hdef, EReal.toReal_coe]
  linarith [EReal.toReal_nonpos hV0]

theorem projectiveWeight_affinePoint (τ : ℂ) :
    projectiveWeight 0 (affinePoint τ) = ‖τ‖ ^ 2 / (‖τ‖ ^ 2 + 1) ∧
      projectiveWeight 1 (affinePoint τ) = 1 / (‖τ‖ ^ 2 + 1) := by
  unfold affinePoint
  rw [projectiveWeight_chart_symm, projectiveWeight_chart_symm]
  simp [projectiveAffineLift]

theorem affinePoint_ne_projectiveZero {τ : ℂ} (hτ : τ ≠ 0) : affinePoint τ ≠ projectiveZero := by
  rw [affinePoint_eq]
  intro h
  exact hτ (OnePoint.coe_injective (projectiveLineHomeomorph.injective h))

theorem projectiveLogWeight_affinePoint {τ : ℂ} (hτ : τ ≠ 0) :
    projectiveLogWeight 0 (affinePoint τ) =
        ((logNormSq τ - Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal) ∧
      projectiveLogWeight 1 (affinePoint τ) = ((-Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal) := by
  obtain ⟨h0, h1⟩ := projectiveWeight_affinePoint τ
  have hn : 0 < ‖τ‖ ^ 2 := by positivity
  have hd : 0 < ‖τ‖ ^ 2 + 1 := by positivity
  constructor
  · rw [projectiveLogWeight_eq_coe (by rw [h0]; positivity), h0, Real.log_div hn.ne' hd.ne',
      logNormSq, add_comm (‖τ‖ ^ 2) 1]
  · rw [projectiveLogWeight_eq_coe (by rw [h1]; positivity), h1, one_div, Real.log_inv,
      add_comm (‖τ‖ ^ 2) 1]

/-! ### The competitor bound -/

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **Competitors lie below the base potential.**  If `φ ∈ PSH(X, θ)`, `ℓ ∈ PSH(ℙ¹, ω_FS)` and
`φ + b ℓ ≤ c log W` off `Z × {0}` (finite somewhere), then `φ + b ℓ ≤ w` off `Z × {0}`. -/
theorem le_basePotential_of_competitor {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hb : 0 < b) {w : F.carrier × ProjectiveLine → EReal}
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    {φ : F.carrier → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    {ℓ : ProjectiveLine → EReal}
    (hℓ : ThetaPlurisubharmonic projectiveNativeFSClosedForm.val ℓ)
    (hbound : ∀ q ∉ deformationCentre F, φ q.1 + (b : EReal) * ℓ q.2 ≤
      ((c * Real.log (baseExceptionalWeight F E q) : ℝ) : EReal))
    (hne : ∃ q ∉ deformationCentre F, φ q.1 + (b : EReal) * ℓ q.2 ≠ ⊥) :
    ∀ q ∉ deformationCentre F, φ q.1 + (b : EReal) * ℓ q.2 ≤ w q := by
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  set Θt := deformationForm F hμ.contMDiff θ b c Eℰ with hΘt
  obtain ⟨hA, hAi⟩ := isComplexAnalyticSubset_support_exceptional F hEℰ
  have hoff := thetaPshOff_deformationCompetitor F hμ hφ hℓ hb c Eℰ
  have hle0 : ∀ z ∉ Eℰ.support, deformationCompetitor F μ φ ℓ b c Eℰ z ≤ 0 := by
    intro z hz
    rw [hEℰ.support_eq] at hz
    exact deformationCompetitor_le_zero F hE hEℰ hz (hbound _ hz)
  have hne' : ∃ z ∉ Eℰ.support, deformationCompetitor F μ φ ℓ b c Eℰ z ≠ ⊥ := by
    obtain ⟨q, hq, hqne⟩ := hne
    obtain ⟨z, hz, rfl⟩ := exists_preimage_of_notMem_centre F hμ hq
    refine ⟨z, hEℰ.support_eq ▸ hz, fun hbot => ?_⟩
    unfold deformationCompetitor at hbot
    rw [EReal.add_eq_bot_iff] at hbot
    rcases hbot with h | h
    · exact hqne h
    · exact EReal.coe_ne_bot _ h
  have hcomp := le_thetaPshSupremum_of_thetaPshOff Θt hA hAi hoff hle0 hne'
  intro q hq
  obtain ⟨z, hz, rfl⟩ := exists_preimage_of_notMem_centre F hμ hq
  have h1 := hcomp z (hEℰ.support_eq ▸ hz)
  rw [hwμ z hz]
  have h2 := add_le_add h1 (le_refl ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
  unfold deformationCompetitor at h2
  have h3 : ∀ (A : EReal) (t : ℝ), A + ((-t : ℝ) : EReal) + (t : EReal) = A := fun A t => by
    simpa using MeteredDivisorPositivity.add_coe_add_neg_coe A (-t)
  rwa [h3] at h2

theorem notMem_centre_affinePoint (x : F.carrier) {τ : ℂ} (hτ : τ ≠ 0) :
    (x, affinePoint τ) ∉ deformationCentre F := fun h =>
  affinePoint_ne_projectiveZero hτ ((mem_deformationCentre_iff F).mp h).2

theorem ereal_add_mul_bot {A : EReal} {b : ℝ} (hb : 0 < b) : A + (b : EReal) * ⊥ = ⊥ := by
  rw [EReal.coe_mul_bot_of_pos hb, EReal.add_bot]

/-- **The lower bound** `v_t ≤ û_λ` (`tok-wn-vf:legendre-bounds`; WN21 Proposition 4.5, second
half), `λ ∈ [0, b]`, `t = max (c - λ) 0`. -/
theorem twistEnvelope_le_partialLegendre {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c) (hcb : c < b) {w : F.carrier × ProjectiveLine → EReal}
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    {lam : ℝ} (hlam : lam ∈ Icc 0 b)
    (hV : IsThetaPshPotential (θ - legendreLevel c lam • E.curvature).val
      (thetaPshSupremum (θ - legendreLevel c lam • E.curvature).val)) (x : F.carrier) :
    twistEnvelope F θ E (legendreLevel c lam) x ≤ partialLegendre (affineTwist w b) lam x := by
  have hb : 0 < b := hc.trans hcb
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  set t := legendreLevel c lam with htdef
  set φ := twistEnvelope F θ E t with hφdef
  have hφ : IsThetaPshPotential θ.val φ :=
    isThetaPshPotential_twistEnvelope F hE0 hEs (legendreLevel_nonneg _ _) hV
  obtain ⟨x₀, -, hx₀⟩ := hφ.2 x univ isOpen_univ (mem_univ x)
  have hq₀ : (x₀, affinePoint 1) ∉ deformationCentre F := notMem_centre_affinePoint F x₀ one_ne_zero
  have hW : ∀ q : F.carrier × ProjectiveLine,
      baseExceptionalWeight F E q =
        (EReal.exp (E.weight q.1)).toReal * projectiveWeight 1 q.2 + projectiveWeight 0 q.2 :=
    baseExceptionalWeight_eq F E
  -- the core inequality, from a competitor weight `ℓ` with `b ℓ([τ:1]) = λ log |τ|² - b log (1+|τ|²)`
  have hcore : ∀ ℓ : ProjectiveLine → EReal,
      ThetaPlurisubharmonic projectiveNativeFSClosedForm.val ℓ →
      (∀ q ∉ deformationCentre F, φ q.1 + (b : EReal) * ℓ q.2 ≤
        ((c * Real.log (baseExceptionalWeight F E q) : ℝ) : EReal)) →
      (∀ τ : ℂ, τ ≠ 0 → (b : EReal) * ℓ (affinePoint τ) =
        ((lam * logNormSq τ - b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal)) →
      ∀ τ : ℂ, τ ≠ 0 → φ x + ((lam * logNormSq τ - b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal) ≤
        w (x, affinePoint τ) := by
    intro ℓ hℓ hbound hval τ hτ
    have hne : ∃ q ∉ deformationCentre F, φ q.1 + (b : EReal) * ℓ q.2 ≠ ⊥ := by
      refine ⟨_, hq₀, ?_⟩
      rw [hval 1 one_ne_zero, Ne, EReal.add_eq_bot_iff, not_or]
      exact ⟨hx₀, EReal.coe_ne_bot _⟩
    have h := le_basePotential_of_competitor F hE hμ hEℰ hb hwμ hφ.1 hℓ hbound hne
      _ (notMem_centre_affinePoint F x hτ)
    rwa [hval τ hτ] at h
  -- the values of `log Nᵢ`
  have hlog : ∀ (i : Fin 2) (p : ProjectiveLine), projectiveWeight i p ≠ 0 →
      projectiveLogWeight i p = ((Real.log (projectiveWeight i p) : ℝ) : EReal) := fun i p hp =>
    projectiveLogWeight_eq_coe (lt_of_le_of_ne (projectiveWeight_nonneg i p) (Ne.symm hp))
  have hlogbot : ∀ (i : Fin 2) (p : ProjectiveLine), projectiveWeight i p = 0 →
      projectiveLogWeight i p = ⊥ := fun i p hp => by
    rw [projectiveLogWeight, hp, ENNReal.ofReal_zero, ENNReal.log_zero]
  have hG0 : ∀ y : F.carrier, 0 ≤ (EReal.exp (E.weight y)).toReal := fun _ => ENNReal.toReal_nonneg
  -- reduction to the core inequality
  have hfinal : (∀ τ : ℂ, τ ≠ 0 → φ x + ((lam * logNormSq τ - b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) :
      EReal) ≤ w (x, affinePoint τ)) → φ x ≤ partialLegendre (affineTwist w b) lam x := by
    intro hτ
    refine le_iInf fun τ => ?_
    have h := hτ τ τ.2
    have h2 := add_le_add h (le_refl ((b * Real.log (1 + ‖(τ : ℂ)‖ ^ 2) - lam * logNormSq τ : ℝ) :
      EReal))
    have e1 : φ x + ((lam * logNormSq τ - b * Real.log (1 + ‖(τ : ℂ)‖ ^ 2) : ℝ) : EReal) +
        ((b * Real.log (1 + ‖(τ : ℂ)‖ ^ 2) - lam * logNormSq τ : ℝ) : EReal) = φ x := by
      have := MeteredDivisorPositivity.add_coe_add_neg_coe (φ x)
        (lam * logNormSq τ - b * Real.log (1 + ‖(τ : ℂ)‖ ^ 2))
      rwa [neg_sub] at this
    have e2 : w (x, affinePoint τ) + ((b * Real.log (1 + ‖(τ : ℂ)‖ ^ 2) - lam * logNormSq τ : ℝ) :
        EReal) = affineTwist w b x τ - ((lam * logNormSq τ : ℝ) : EReal) := by
      simp only [affineTwist, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg, add_assoc]
    rw [e1, e2] at h2
    exact h2
  apply hfinal
  rcases hlam.1.eq_or_lt with h0 | h0
  · -- `λ = 0`: the weight `b log N₁`, `t = c`
    subst h0
    have ht : t = c := by rw [htdef, legendreLevel, sub_zero]; exact max_eq_left hc.le
    refine hcore (projectiveLogWeight 1) (thetaPlurisubharmonic_projectiveLogWeight 1) ?_ ?_
    · intro q hq
      by_cases hφq : φ q.1 = ⊥
      · rw [hφq, EReal.bot_add]; exact bot_le
      by_cases hN1 : projectiveWeight 1 q.2 = 0
      · rw [hlogbot 1 _ hN1, ereal_add_mul_bot hb]; exact bot_le
      obtain ⟨f, hf, -, hft⟩ := twistEnvelope_eq_coe F hE0 (legendreLevel_nonneg c 0) hφq
      obtain ⟨hGpos, hfG⟩ := hft (by rw [← htdef, ht]; exact hc)
      rw [← htdef, ht] at hfG
      rw [show φ q.1 = (f : EReal) from hf, hlog 1 _ hN1, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff, hW]
      exact real_competitor_bound_zero hc hcb.le (projectiveWeight_nonneg 0 _)
        (lt_of_le_of_ne (projectiveWeight_nonneg 1 _) (Ne.symm hN1)) (projectiveWeight_le_one 1 _)
        hGpos hfG
    · intro τ hτ
      rw [(projectiveLogWeight_affinePoint hτ).2, ← EReal.coe_mul]
      congr 1; ring
  rcases hlam.2.eq_or_lt with h1 | h1
  · -- `λ = b`: the weight `b log N₀`, `t = 0`
    subst h1
    refine hcore (projectiveLogWeight 0) (thetaPlurisubharmonic_projectiveLogWeight 0) ?_ ?_
    · intro q hq
      by_cases hφq : φ q.1 = ⊥
      · rw [hφq, EReal.bot_add]; exact bot_le
      by_cases hN0 : projectiveWeight 0 q.2 = 0
      · rw [hlogbot 0 _ hN0, ereal_add_mul_bot hb]; exact bot_le
      obtain ⟨f, hf, hf0, -⟩ := twistEnvelope_eq_coe F hE0 (legendreLevel_nonneg c lam) hφq
      rw [show φ q.1 = (f : EReal) from hf, hlog 0 _ hN0, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff, hW]
      exact real_competitor_bound_top hc hcb.le
        (lt_of_le_of_ne (projectiveWeight_nonneg 0 _) (Ne.symm hN0)) (projectiveWeight_le_one 0 _)
        (projectiveWeight_nonneg 1 _) (hG0 _) hf0
    · intro τ hτ
      rw [(projectiveLogWeight_affinePoint hτ).1, ← EReal.coe_mul]
      congr 1; ring
  -- `0 < λ < b`: the weight `(λ / b) log N₀ + (1 - λ / b) log N₁`
  set s := lam / b with hs
  have hs0 : 0 < s := div_pos h0 hb
  have hs1 : 0 < 1 - s := by rw [hs, sub_pos, div_lt_one hb]; exact h1
  set ℓ : ProjectiveLine → EReal := fun p => (s : EReal) * projectiveLogWeight 0 p +
    ((1 - s : ℝ) : EReal) * projectiveLogWeight 1 p with hℓdef
  have hℓ : ThetaPlurisubharmonic projectiveNativeFSClosedForm.val ℓ := by
    have h := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul hs0 hs1
      (thetaPlurisubharmonic_projectiveLogWeight 0) (thetaPlurisubharmonic_projectiveLogWeight 1)
    rwa [← add_smul, add_sub_cancel, one_smul] at h
  have hbs : b * s = lam := by rw [hs]; field_simp
  refine hcore ℓ hℓ ?_ ?_
  · intro q hq
    by_cases hφq : φ q.1 = ⊥
    · rw [hφq, EReal.bot_add]; exact bot_le
    by_cases hN0 : projectiveWeight 0 q.2 = 0
    · rw [hℓdef]; simp only
      rw [hlogbot 0 _ hN0, EReal.coe_mul_bot_of_pos hs0, EReal.bot_add, ereal_add_mul_bot hb]
      exact bot_le
    by_cases hN1 : projectiveWeight 1 q.2 = 0
    · rw [hℓdef]; simp only
      rw [hlogbot 1 _ hN1, EReal.coe_mul_bot_of_pos hs1, EReal.add_bot, ereal_add_mul_bot hb]
      exact bot_le
    obtain ⟨f, hf, hf0, hft⟩ := twistEnvelope_eq_coe F hE0 (legendreLevel_nonneg c lam) hφq
    rw [hℓdef]; simp only
    rw [show φ q.1 = (f : EReal) from hf, hlog 0 _ hN0, hlog 1 _ hN1, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff, hW]
    have key := real_competitor_bound (f := f) (lam := lam) (b := b) (t := t) hc hcb.le h0.le
      h1.le rfl hf0 (hG0 _) (lt_of_le_of_ne (projectiveWeight_nonneg 0 _) (Ne.symm hN0))
      (lt_of_le_of_ne (projectiveWeight_nonneg 1 _) (Ne.symm hN1)) (projectiveWeight_le_one 0 _)
      (projectiveWeight_le_one 1 _) hft
    have e : f + b * (s * Real.log (projectiveWeight 0 q.2) +
        (1 - s) * Real.log (projectiveWeight 1 q.2)) =
        f + lam * Real.log (projectiveWeight 0 q.2) +
          (b - lam) * Real.log (projectiveWeight 1 q.2) := by
      rw [← hbs]; ring
    rw [e]; exact key
  · intro τ hτ
    rw [hℓdef]; simp only
    rw [(projectiveLogWeight_affinePoint hτ).1, (projectiveLogWeight_affinePoint hτ).2,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul]
    congr 1
    rw [← hbs]; ring


theorem ereal_add_coe_add_coe_add_coe (A : EReal) {a b c : ℝ} (h : a + b + c = 0) :
    A + (a : EReal) + (b : EReal) + (c : EReal) = A := by
  induction A using EReal.rec with
  | bot => simp
  | top => rw [EReal.top_add_coe, EReal.top_add_coe, EReal.top_add_coe]
  | coe A =>
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
    congr 1; linarith

theorem log_baseExceptionalWeight_affine_exp {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (x : F.carrier) {g : ℝ} (hg : E.weight x = (g : EReal)) :
    Real.log (baseExceptionalWeight F E (x, affinePoint (Complex.exp ((g : ℂ) / 2)))) ≤
      Real.log 2 + g := by
  obtain ⟨h0, h1⟩ := projectiveWeight_affinePoint (Complex.exp ((g : ℂ) / 2))
  rw [norm_exp_half_sq] at h0 h1
  have hexp : (EReal.exp (E.weight x)).toReal = Real.exp g := by
    rw [hg, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos g).le]
  have hW : baseExceptionalWeight F E (x, affinePoint (Complex.exp ((g : ℂ) / 2))) =
      2 * Real.exp g / (Real.exp g + 1) := by
    rw [baseExceptionalWeight_eq]
    simp only
    rw [hexp, h0, h1]
    field_simp
    ring
  have hd : 0 < Real.exp g + 1 := by positivity
  rw [hW]
  calc Real.log (2 * Real.exp g / (Real.exp g + 1)) ≤ Real.log (2 * Real.exp g) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hd]
        nlinarith [Real.exp_pos g]
    _ = Real.log 2 + g := by rw [Real.log_mul (by norm_num) (Real.exp_pos g).ne', Real.log_exp]

/-- **The upper bound** `û_λ ≤ v_t + C` (`tok-wn-vf:legendre-bounds`; WN21 Proposition 4.5, first
half, without Lelong numbers): at `|τ|² = e^g` the obstacle gives `û_λ ≤ (c - λ) g + C` off `Z`,
and `û_λ - t g` extends across `Z` below `V_{θ - tη} + C`. -/
theorem partialLegendre_le_twistEnvelope_add {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c) (hcb : c < b) {w : F.carrier × ProjectiveLine → EReal}
    (hw : IsThetaPshPotential (productLineForm θ b).val w)
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    (hrot : ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ∀ q, w (lineRotation a q) = w q)
    {lam : ℝ} (hlam : lam ∈ Icc 0 b)
    (hV : IsThetaPshPotential (θ - legendreLevel c lam • E.curvature).val
      (thetaPshSupremum (θ - legendreLevel c lam • E.curvature).val)) :
    ∃ C : ℝ, ∀ x, partialLegendre (affineTwist w b) lam x ≤
      twistEnvelope F θ E (legendreLevel c lam) x + (C : EReal) := by
  have hb : 0 < b := hc.trans hcb
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  set t := legendreLevel c lam with htdef
  set φ := twistEnvelope F θ E t with hφdef
  have hφ : IsThetaPshPotential θ.val φ :=
    isThetaPshPotential_twistEnvelope F hE0 hEs (legendreLevel_nonneg _ _) hV
  set U := partialLegendre (affineTwist w b) lam with hUdef
  have hU : ThetaPlurisubharmonic θ.val U :=
    thetaPlurisubharmonic_partialLegendre (isPullbackThetaPshPunctured_affineTwist hw.1)
      (isCircleInvariant_affineTwist b hrot) lam
  have hlow : ∀ x, φ x ≤ U x := fun x =>
    twistEnvelope_le_partialLegendre F hE hE0 hμ hEℰ hc hcb hwμ hlam hV x
  have hUpot : IsThetaPshPotential θ.val U := by
    refine ⟨hU, fun x O hO hxO => ?_⟩
    obtain ⟨y, hy, hyne⟩ := hφ.2 x O hO hxO
    exact ⟨y, hy, fun h => hyne (le_bot_iff.mp (h ▸ hlow y))⟩
  have hwle : ∀ x (τ : ℂ), τ ≠ 0 → w (x, affinePoint τ) ≤
      ((c * Real.log (baseExceptionalWeight F E (x, affinePoint τ)) : ℝ) : EReal) :=
    fun x τ hτ => basePotential_le F hE hμ hEℰ hwμ (notMem_centre_affinePoint F x hτ)
  -- the value of `û_λ` at `τ`
  have hUτ : ∀ x (τ : ℂ) (hτ : τ ≠ 0), U x ≤
      ((c * Real.log (baseExceptionalWeight F E (x, affinePoint τ)) +
        b * Real.log (1 + ‖τ‖ ^ 2) - lam * logNormSq τ : ℝ) : EReal) := by
    intro x τ hτ
    refine (iInf_le _ (⟨τ, hτ⟩ : puncturedPlane)).trans ?_
    simp only [affineTwist]
    rw [sub_eq_add_neg, sub_eq_add_neg, EReal.coe_add, EReal.coe_add, EReal.coe_neg]
    exact add_le_add (add_le_add (hwle x τ hτ) le_rfl) le_rfl
  rcases le_or_gt lam c with hl | hl
  · -- `λ ≤ c`: `t = c - λ`
    have ht : t = c - lam := by rw [htdef, legendreLevel]; exact max_eq_left (by linarith)
    set C₀ := (b + c) * Real.log 2 with hC₀
    have hoffZ : ∀ x ∉ E.support, U x ≤ ((t * (E.weight x).toReal + C₀ : ℝ) : EReal) := by
      intro x hx
      have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
      set g := (E.weight x).toReal with hgdef
      have hg : E.weight x = (g : EReal) := (EReal.coe_toReal hwt hx).symm
      have hg0 : g ≤ 0 := EReal.toReal_nonpos (hE0 x)
      have hτ : Complex.exp ((g : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
      refine (hUτ x _ hτ).trans (EReal.coe_le_coe_iff.mpr ?_)
      rw [norm_exp_half_sq, logNormSq_exp_half, ht]
      have h1 := log_baseExceptionalWeight_affine_exp F (E := E) x hg
      have h2 := log_one_add_exp_le_of_nonpos hg0
      have h3 := mul_le_mul_of_nonneg_left h1 hc.le
      have h4 := mul_le_mul_of_nonneg_left h2 hb.le
      nlinarith
    have hψ : IsThetaPshPotential θ.val (fun x => U x - (C₀ : EReal)) := hUpot.sub_const C₀
    have hoff := SGPT.Siu.thetaPshOff_sub_smul_weight hψ.1 E t
    have hZ : IsComplexAnalyticSubset (n := m + 1) E.support :=
      ResidualNef.isComplexAnalyticSubset_support E
    have hZi : interior E.support = ∅ := by rw [hEs]; exact interior_firstFlag F
    have hle0 : ∀ x ∉ E.support,
        U x - (C₀ : EReal) + ((-(t * (E.weight x).toReal) : ℝ) : EReal) ≤ 0 := by
      intro x hx
      have h := add_le_add (add_le_add (hoffZ x hx) (le_refl ((-C₀ : ℝ) : EReal)))
        (le_refl ((-(t * (E.weight x).toReal) : ℝ) : EReal))
      rw [sub_eq_add_neg, ← EReal.coe_neg]
      refine h.trans (le_of_eq ?_)
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_zero]
      congr 1; ring
    have hne : ∃ x ∉ E.support, U x - (C₀ : EReal) + ((-(t * (E.weight x).toReal) : ℝ) : EReal) ≠ ⊥ := by
      have hnot : ¬ (univ : Set F.carrier) ⊆ E.support := fun h => by
        have := interior_maximal h isOpen_univ
        rw [hZi] at this
        exact this (mem_univ (Classical.arbitrary F.carrier))
      obtain ⟨x₁, -, hx₁⟩ := not_subset.mp hnot
      obtain ⟨y, hy, hyne⟩ := hφ.2 x₁ E.supportᶜ hZ.isClosed.isOpen_compl hx₁
      refine ⟨y, hy, fun hbot => ?_⟩
      rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.add_eq_bot_iff, EReal.add_eq_bot_iff] at hbot
      rcases hbot with (h | h) | h
      · exact hyne (le_bot_iff.mp (h ▸ hlow y))
      · exact EReal.coe_ne_bot _ h
      · exact EReal.coe_ne_bot _ h
    have hcomp := le_thetaPshSupremum_of_thetaPshOff (θ - t • E.curvature) hZ hZi hoff hle0 hne
    refine ⟨C₀, ?_⟩
    have hoffZ' : ∀ x ∉ E.support, U x ≤ φ x + (C₀ : EReal) := by
      intro x hx
      have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
      have hg : E.weight x = ((E.weight x).toReal : EReal) := (EReal.coe_toReal hwt hx).symm
      have h := add_le_add (hcomp x hx) (le_refl ((t * (E.weight x).toReal + C₀ : ℝ) : EReal))
      rw [sub_eq_add_neg, ← EReal.coe_neg, ereal_add_coe_add_coe_add_coe _ (by ring)] at h
      refine h.trans (le_of_eq ?_)
      rw [hφdef, twistEnvelope, hg, ← EReal.coe_mul, EReal.coe_add, add_assoc, EReal.toReal_coe]
    exact le_of_le_off_analytic hZ hZi (hφ.add_const C₀).1 hU hoffZ'
  · -- `λ > c`: `t = 0` and `û_λ ≤ b log 2`
    have ht : t = 0 := by rw [htdef, legendreLevel]; exact max_eq_right (by linarith)
    refine ⟨b * Real.log 2, ?_⟩
    have hbd : ∀ x, U x ≤ ((b * Real.log 2 : ℝ) : EReal) := by
      intro x
      refine (hUτ x 1 one_ne_zero).trans (EReal.coe_le_coe_iff.mpr ?_)
      have hW1 := baseExceptionalWeight_le_one F E hE0 (x, affinePoint 1)
      have hWpos := baseExceptionalWeight_pos F hE (notMem_centre_affinePoint F x one_ne_zero)
      have hlogW := Real.log_nonpos hWpos.le hW1
      simp only [norm_one, one_pow, logNormSq, Real.log_one, mul_zero, sub_zero]
      norm_num
      nlinarith
    have hpot : IsThetaPshPotential θ.val (fun x => U x - ((b * Real.log 2 : ℝ) : EReal)) :=
      hUpot.sub_const _
    have hle := le_thetaPshSupremum hpot (fun x => by
      have := hbd x
      simpa using EReal.sub_nonpos.mpr this)
    intro x
    have h := add_le_add (hle x) (le_refl ((b * Real.log 2 : ℝ) : EReal))
    rw [ereal_sub_add_cancel] at h
    rw [hφdef, ht, twistEnvelope_zero]
    exact h

end Deformation

end SGPT.Okounkov.TranscendentalWN
