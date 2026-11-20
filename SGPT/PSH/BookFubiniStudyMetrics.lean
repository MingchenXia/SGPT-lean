import SGPT.PSH.BookPSHMetrics
import SGPT.Bergman.SourceBergmanNorms
import SGPT.Bergman.SourceTensorDictionary
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

/-!
# Fubini–Study and generalized Fubini–Study metrics (`def:ArcFSmetric`, `def:gFSmetric`)

Source: chapter *Plurisubharmonic functions*, section *Plurisubharmonic metrics on line bundles*.

* Change of reference: every psh metric `h = h₀ e^{-φ}` is also `h₁ e^{-(φ - log(h₀/h₁))}` with
  `φ - log(h₀/h₁) ∈ PSH(X, c₁(L,h₁))` for ANY Hermitian metric `h₁`
  (`IsPSHMetricWith.changeReference`): the book's bijection between `PSH(X, c₁(L,h₀))` and
  `PSH(L)` (`isPSHMetric_iff_exists_potential`).
* `def:ArcFSmetric` (`IsFubiniStudyMetric`): for a holomorphic Hermitian line bundle `L` (the
  project's `HermitianHolomorphicLineBundle`, whose tensor powers `L^m` and holomorphic sections
  `H⁰(X, L^m)` are those of the Bergman chapter), a psh metric `h` with `m > 0`, sections
  `s₁, …, s_N ∈ H⁰(X, L^m)` and `λᵢ ∈ ℚ` such that for every local nowhere vanishing holomorphic
  section `s` of `L`, `|s|²_h = minᵢ |s^{⊗m}/(e^{λᵢ/2} sᵢ)|^{2/m}`.
* `def:gFSmetric` (`IsGeneralizedFubiniStudyMetric`): the smallest set of metrics containing
  `FS(L)` and closed under `ℚ`-convex combinations `h₁^t ⊗ h₂^{1-t}` and minima; it is contained in
  `PSH(L)` (`IsGeneralizedFubiniStudyMetric.isPSHMetric`), so it is the smallest such subset of
  `PSH(L)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff ENNReal TensorProduct InnerProductSpace

namespace SGPT.PSH.LineBundleMetric

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

section Reference

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

theorem logRatio_eq_vector (h h' : HermitianMetric (n := n) L) {x : X} {v : L x} (hv : v ≠ 0) :
    logRatio h h' x = Real.log ((h.form x).normSq v / (h'.form x).normSq v) := by
  rw [logRatio, normSq_ratio_eq (finrank_fiber x) (h.form x) (h'.form x)
    (frame_ne_zero (mem_frameDomain x)) hv]

/-- Change of the reference metric in the presentation `h = h₀ e^{-φ}`. -/
theorem twistedForm_changeReference (h₀ h₁ : HermitianMetric (n := n) L) (φ : X → EReal) :
    twistedForm h₀ φ = twistedForm h₁ (fun x => φ x - (logRatio h₀ h₁ x : EReal)) := by
  classical
  funext x v
  by_cases hv : v = 0
  · simp [twistedForm, hv]
  · simp only [twistedForm, hv, if_false]
    have h0 := (h₀.form x).normSq_pos hv
    have h1 := (h₁.form x).normSq_pos hv
    have hexp : -(φ x - (logRatio h₀ h₁ x : EReal)) = -φ x + (logRatio h₀ h₁ x : EReal) := by
      induction φ x using EReal.rec with
      | bot => simp
      | top => simp
      | coe a =>
        rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
        congr 1
        ring
    rw [hexp, EReal.exp_add, EReal.exp_coe, logRatio_eq_vector h₀ h₁ hv,
      Real.exp_log (div_pos h0 h1), mul_comm (EReal.exp (-φ x)), ← mul_assoc,
      ← ENNReal.ofReal_mul h1.le, mul_div_cancel₀ _ h1.ne']

/-- Every psh metric has a presentation over ANY reference Hermitian metric. -/
theorem IsPSHMetricWith.changeReference {q : (x : X) → L x → ℝ≥0∞}
    {h₀ : HermitianMetric (n := n) L} {φ : X → EReal} (hq : IsPSHMetricWith q h₀ φ)
    (h₁ : HermitianMetric (n := n) L) :
    IsPSHMetricWith q h₁ (fun x => φ x - (logRatio h₀ h₁ x : EReal)) := by
  refine ⟨?_, fun x v => by rw [hq.eq_twisted, twistedForm_changeReference h₀ h₁]⟩
  exact PositiveClasses.thetaPshPotential_sub_smooth (chartSmooth_logRatio h₀ h₁)
    (fun e z hz => firstChernForm_coeff_eq_add h₀ h₁ e hz) hq.thetaPsh

/-- Once a reference Hermitian metric `h₁` is fixed, the psh metrics are exactly the
`h₁ e^{-φ}` with `φ ∈ PSH(X, c₁(L,h₁))` (and `φ` is unique, `twistedForm_injective`). -/
theorem isPSHMetric_iff_exists_potential (h₁ : HermitianMetric (n := n) L)
    (q : (x : X) → L x → ℝ≥0∞) :
    IsPSHMetric (n := n) L q ↔ ∃ φ : X → EReal, IsPSHMetricWith q h₁ φ := by
  constructor
  · rintro ⟨-, h₀, φ, hq⟩
    exact ⟨_, hq.changeReference h₁⟩
  · rintro ⟨φ, hq⟩
    exact IsPSHMetric.of_with hq

/-- Minimum of two psh metrics: `min(h₀ e^{-φ₁}, h₀ e^{-φ₂}) = h₀ e^{-max(φ₁, φ₂)}`. -/
theorem twistedForm_min (h₀ : HermitianMetric (n := n) L) (φ₁ φ₂ : X → EReal) :
    (fun x v => min (twistedForm h₀ φ₁ x v) (twistedForm h₀ φ₂ x v)) =
      twistedForm h₀ (fun x => max (φ₁ x) (φ₂ x)) := by
  classical
  funext x v
  by_cases hv : v = 0
  · simp [twistedForm, hv]
  · simp only [twistedForm, hv, if_false]
    rcases le_total (φ₁ x) (φ₂ x) with h | h
    · rw [max_eq_right h]
      exact min_eq_right (mul_le_mul_of_nonneg_left
        (EReal.exp_monotone (EReal.neg_le_neg_iff.mpr h)) zero_le)
    · rw [max_eq_left h]
      exact min_eq_left (mul_le_mul_of_nonneg_left
        (EReal.exp_monotone (EReal.neg_le_neg_iff.mpr h)) zero_le)

/-- `ℚ`-convex combination of two psh metrics on the same line bundle:
`(h₀ e^{-φ₁})^t (h₀ e^{-φ₂})^{1-t} = h₀ e^{-(tφ₁ + (1-t)φ₂)}`, for `0 < t < 1` and potentials
that never take the value `+∞`. -/
theorem twistedForm_convex (h₀ : HermitianMetric (n := n) L) {φ₁ φ₂ : X → EReal}
    (h₁ : ∀ x, φ₁ x ≠ ⊤) (h₂ : ∀ x, φ₂ x ≠ ⊤) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (fun x v => twistedForm h₀ φ₁ x v ^ t * twistedForm h₀ φ₂ x v ^ (1 - t)) =
      twistedForm h₀ (Pending.ThetaPshConvexCombination.convexComb t φ₁ φ₂) := by
  classical
  have ht1' : 0 < 1 - t := by linarith
  funext x v
  by_cases hv : v = 0
  · simp [twistedForm, hv, ENNReal.zero_rpow_of_pos ht0, ENNReal.zero_rpow_of_pos ht1']
  · simp only [twistedForm, hv, if_false, Pending.ThetaPshConvexCombination.convexComb]
    set a := ENNReal.ofReal ((h₀.form x).normSq v)
    have ha0 : a ≠ 0 := by simpa [a] using (h₀.form x).normSq_pos hv
    have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
    have he₁ : EReal.exp (-φ₁ x) ≠ 0 := by
      rw [ne_eq, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff]; exact h₁ x
    have he₂ : EReal.exp (-φ₂ x) ≠ 0 := by
      rw [ne_eq, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff]; exact h₂ x
    by_cases hb₁ : φ₁ x = ⊥
    · -- a pole of `φ₁` is a pole of the combination
      have hbot : (t : EReal) * φ₁ x + ((1 - t : ℝ) : EReal) * φ₂ x = ⊥ := by
        rw [hb₁, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
      have htop : EReal.exp (-φ₁ x) = ⊤ := by rw [hb₁, EReal.neg_bot, EReal.exp_top]
      rw [hbot, htop, EReal.neg_bot, EReal.exp_top, ENNReal.mul_top ha0,
        ENNReal.top_rpow_of_pos ht0,
        ENNReal.top_mul ((ENNReal.rpow_eq_zero_iff_of_pos ht1').not.mpr (mul_ne_zero ha0 he₂))]
    · by_cases hb₂ : φ₂ x = ⊥
      · have hbot : (t : EReal) * φ₁ x + ((1 - t : ℝ) : EReal) * φ₂ x = ⊥ := by
          rw [hb₂, EReal.coe_mul_bot_of_pos ht1', EReal.add_bot]
        have htop : EReal.exp (-φ₂ x) = ⊤ := by rw [hb₂, EReal.neg_bot, EReal.exp_top]
        rw [hbot, htop, EReal.neg_bot, EReal.exp_top, ENNReal.mul_top ha0,
          ENNReal.top_rpow_of_pos ht1',
          ENNReal.mul_top ((ENNReal.rpow_eq_zero_iff_of_pos ht0).not.mpr (mul_ne_zero ha0 he₁))]
      · obtain ⟨b₁, hb₁'⟩ : ∃ b : ℝ, φ₁ x = b := ⟨(φ₁ x).toReal,
          (EReal.coe_toReal (h₁ x) hb₁).symm⟩
        obtain ⟨b₂, hb₂'⟩ : ∃ b : ℝ, φ₂ x = b := ⟨(φ₂ x).toReal,
          (EReal.coe_toReal (h₂ x) hb₂).symm⟩
        have hpow : a ^ t * a ^ (1 - t) = a := by
          rw [← ENNReal.rpow_add _ _ ha0 hat, add_sub_cancel, ENNReal.rpow_one]
        rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ _ ht1'.le]
        rw [hb₁', hb₂', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_neg,
          ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe, EReal.exp_coe, EReal.exp_coe,
          ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
          ← Real.exp_mul, ← Real.exp_mul]
        calc a ^ t * ENNReal.ofReal (Real.exp (-b₁ * t)) *
              (a ^ (1 - t) * ENNReal.ofReal (Real.exp (-b₂ * (1 - t))))
            = (a ^ t * a ^ (1 - t)) * (ENNReal.ofReal (Real.exp (-b₁ * t)) *
                ENNReal.ofReal (Real.exp (-b₂ * (1 - t)))) := by ring
          _ = a * ENNReal.ofReal (Real.exp (-(t * b₁ + (1 - t) * b₂))) := by
            rw [hpow, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 3
            ring

end Reference

section FubiniStudy

open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The tensor power `v ↦ v^{⊗(k+1)} ∈ (L^{k+1})_x` of a fibre vector. -/
def powVec (L : HermitianHolomorphicLineBundle.{u,v} n M) {x : M} :
    (k : ℕ) → L.Fiber x → (positivePower L k).Fiber x
  | 0, w => w
  | k + 1, w => (powVec L k w : (positivePower L k).Fiber x) ⊗ₜ[ℂ] w

/-- The value `|s^{⊗m}/(e^{λ/2} σ)|^{2/m}` (`m = k + 1`) of one Fubini–Study term at a fibre
vector `w = s(x)`: the ratio of two vectors of the line `(L^m)_x`, written through the
coefficient `c` of `σ = c w^{⊗m}`; it is `∞` where `σ(x) = 0`. -/
def fsTerm (L : HermitianHolomorphicLineBundle.{u,v} n M) (k : ℕ) {x : M} (σ : (positivePower L k).Fiber x)
    (lam : ℚ) (w : L.Fiber x) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-(lam : ℝ))) /
      ENNReal.ofReal (‖⟪powVec L k w, σ⟫_ℂ / ((‖powVec L k w‖ : ℂ) ^ 2)‖ ^ 2)) ^
    ((1 : ℝ) / (k + 1))

/-- `def:ArcFSmetric`. A Fubini–Study metric on `L`: a psh metric `h` for which there are `m > 0`
(here `m = k + 1`), finitely many sections `s₁, …, s_N ∈ H⁰(X, L^m)` and `λᵢ ∈ ℚ` such that for
every local nowhere vanishing holomorphic section `s` of `L`,
`|s|²_h = minᵢ |s^{⊗m}/(e^{λᵢ/2} sᵢ)|^{2/m}`. -/
def IsFubiniStudyMetric (L : HermitianHolomorphicLineBundle.{u,v} n M)
    (q : (x : M) → L.Fiber x → ℝ≥0∞) : Prop :=
  IsPSHMetric (n := n) L.Fiber q ∧
    ∃ (k N : ℕ) (_ : 0 < N) (s : Fin N → SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n)
        (positivePower L k).Fiber) (lam : Fin N → ℚ),
      ∀ (σ : (x : M) → L.Fiber x) (U : Set M), IsOpen U →
        IsHolomorphicSectionOn (n := n) L.Fiber σ U → (∀ x ∈ U, σ x ≠ 0) →
          ∀ x ∈ U, q x (σ x) = ⨅ i, fsTerm L k (s i x) (lam i) (σ x)

/-- `FS(L)`. -/
def fubiniStudyMetrics (L : HermitianHolomorphicLineBundle.{u,v} n M) :
    Set ((x : M) → L.Fiber x → ℝ≥0∞) :=
  {q | IsFubiniStudyMetric L q}

/-- `def:gFSmetric`. Generalized Fubini–Study metrics: the smallest set containing `FS(L)` and
closed under `ℚ`-convex combinations `h₁^t ⊗ h₂^{1-t}` (`t ∈ (0,1) ∩ ℚ`) and minima. -/
inductive IsGeneralizedFubiniStudyMetric (L : HermitianHolomorphicLineBundle.{u,v} n M) :
    ((x : M) → L.Fiber x → ℝ≥0∞) → Prop
  | fs {q} : IsFubiniStudyMetric L q → IsGeneralizedFubiniStudyMetric L q
  | convex {q₁ q₂} (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1) :
      IsGeneralizedFubiniStudyMetric L q₁ → IsGeneralizedFubiniStudyMetric L q₂ →
        IsGeneralizedFubiniStudyMetric L (fun x w => q₁ x w ^ (t : ℝ) * q₂ x w ^ (1 - (t : ℝ)))
  | min {q₁ q₂} : IsGeneralizedFubiniStudyMetric L q₁ → IsGeneralizedFubiniStudyMetric L q₂ →
      IsGeneralizedFubiniStudyMetric L (fun x w => min (q₁ x w) (q₂ x w))

/-- Generalized Fubini–Study metrics are psh metrics, so `def:gFSmetric` describes the smallest
subset of `PSH(L)` with the stated properties. -/
theorem IsGeneralizedFubiniStudyMetric.isPSHMetric {L : HermitianHolomorphicLineBundle.{u,v} n M}
    {q : (x : M) → L.Fiber x → ℝ≥0∞} (hq : IsGeneralizedFubiniStudyMetric L q) :
    IsPSHMetric (n := n) L.Fiber q := by
  induction hq with
  | fs h => exact h.1
  | @convex q₁ q₂ t ht0 ht1 _ _ ih₁ ih₂ =>
    obtain ⟨-, h₀, φ₁, hq₁⟩ := ih₁
    obtain ⟨φ₂, hq₂⟩ := (isPSHMetric_iff_exists_potential h₀ q₂).mp ih₂
    have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
    have ht1' : (t : ℝ) < 1 := by exact_mod_cast ht1
    refine IsPSHMetric.of_with (h₀ := h₀)
      (φ := Pending.ThetaPshConvexCombination.convexComb t φ₁ φ₂) ⟨?_, ?_⟩
    · exact Pending.ThetaPshConvexCombination.isThetaPshPotential_convexComb hq₁.thetaPsh
        hq₂.thetaPsh ht0' ht1'
    · intro x w
      have := congrFun (congrFun (twistedForm_convex h₀
        (fun y => hq₁.thetaPsh.1.quasiPlurisubharmonic.ne_top y)
        (fun y => hq₂.thetaPsh.1.quasiPlurisubharmonic.ne_top y) ht0' ht1') x) w
      rw [← this, hq₁.eq_twisted, hq₂.eq_twisted]
  | @min q₁ q₂ _ _ ih₁ ih₂ =>
    obtain ⟨-, h₀, φ₁, hq₁⟩ := ih₁
    obtain ⟨φ₂, hq₂⟩ := (isPSHMetric_iff_exists_potential h₀ q₂).mp ih₂
    refine IsPSHMetric.of_with (h₀ := h₀) (φ := fun x => max (φ₁ x) (φ₂ x)) ⟨?_, ?_⟩
    · exact Pending.IsThetaPshPotential.max hq₁.thetaPsh hq₂.thetaPsh
    · intro x w
      have := congrFun (congrFun (twistedForm_min h₀ φ₁ φ₂) x) w
      rw [← this, hq₁.eq_twisted, hq₂.eq_twisted]

end FubiniStudy

end SGPT.PSH.LineBundleMetric
