import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization

/-!
# Concavity of the singularity envelope `P_θ[·]`

Source `prop:Pconc` (chapter *Envelopes*), in the form used by `ex:RWN`: for
`t ∈ (0, 1)` and obstacles with `t φ₁ + (1 - t) φ₀ ≤ ψ`,

`t P_θ[φ₁] + (1 - t) P_θ[φ₀] ≤ P_θ[ψ]`,

for the singularity envelope `P_θ[φ] = usc sup {u ∈ PSH(X, θ) : u ≤ 0, u ⪯ φ}` of the
`SGPT.Foundations.Analysis` API (`singularityEnvelope`) on a complex manifold (second countable by
definition).

Proof: by Choquet's lemma and running maxima, `P_θ[φ]` is the usc regularization of an increasing
sequence of competitors `r_k`, hence equals `sup_k r_k` almost everywhere in every chart. For each
`k`, `t r¹_k + (1-t) r⁰_k` is a competitor for `ψ`, so `t sup_k r¹_k + (1 - t) sup_k r⁰_k ≤ P_θ[ψ]`
pointwise; thus the inequality holds almost everywhere in charts, hence everywhere, both sides
being `θ`-psh.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.Misc2EnvelopeConcave

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-- `c ≤ y` from `c - ε ≤ y` for every `ε > 0`. -/
theorem coe_le_of_forall_sub_le {c : ℝ} {y : EReal}
    (h : ∀ ε : ℝ, 0 < ε → (((c - ε : ℝ)) : EReal) ≤ y) : (c : EReal) ≤ y := by
  by_contra hlt
  rw [not_le] at hlt
  induction y using EReal.rec with
  | bot => exact (not_le.mpr (EReal.bot_lt_coe (c - 1))) (h 1 one_pos)
  | top => exact (not_lt.mpr le_top) hlt
  | coe r =>
    have hr : r < c := EReal.coe_lt_coe_iff.mp hlt
    have := EReal.coe_le_coe_iff.mp (h ((c - r) / 2) (by linarith))
    linarith

/-- For increasing nonpositive sequences, a bound on every convex combination
`t aₖ + (1 - t) bₖ` bounds the convex combination of the suprema. -/
theorem convexComb_iSup_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {a b : ℕ → EReal}
    (ha : Monotone a) (hb : Monotone b) (ha0 : ∀ k, a k ≤ 0) (hb0 : ∀ k, b k ≤ 0) {c : EReal}
    (h : ∀ k, (t : EReal) * a k + ((1 - t : ℝ) : EReal) * b k ≤ c) :
    (t : EReal) * (⨆ k, a k) + ((1 - t : ℝ) : EReal) * (⨆ k, b k) ≤ c := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hA0 : (⨆ k, a k) ≤ 0 := iSup_le ha0
  have hB0 : (⨆ k, b k) ≤ 0 := iSup_le hb0
  induction hA : (⨆ k, a k) using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]; exact bot_le
  | top => exact absurd (hA ▸ hA0) (not_le.mpr EReal.zero_lt_top)
  | coe A =>
  induction hB : (⨆ k, b k) using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos h1t, EReal.add_bot]; exact bot_le
  | top => exact absurd (hB ▸ hB0) (not_le.mpr EReal.zero_lt_top)
  | coe B =>
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  refine coe_le_of_forall_sub_le fun ε hε => ?_
  obtain ⟨k₁, hk₁⟩ := lt_iSup_iff.mp
    (show ((A - ε : ℝ) : EReal) < ⨆ k, a k from hA ▸ EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨k₀, hk₀⟩ := lt_iSup_iff.mp
    (show ((B - ε : ℝ) : EReal) < ⨆ k, b k from hB ▸ EReal.coe_lt_coe_iff.mpr (by linarith))
  set k := max k₁ k₀
  have hak : ((A - ε : ℝ) : EReal) < a k := hk₁.trans_le (ha (le_max_left _ _))
  have hbk : ((B - ε : ℝ) : EReal) < b k := hk₀.trans_le (hb (le_max_right _ _))
  have haR : a k = ((a k).toReal : EReal) :=
    (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (ha0 k))
      (ne_bot_of_gt hak)).symm
  have hbR : b k = ((b k).toReal : EReal) :=
    (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (hb0 k))
      (ne_bot_of_gt hbk)).symm
  have hk := h k
  rw [haR, hbR, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hk
  rw [haR, EReal.coe_lt_coe_iff] at hak
  rw [hbR, EReal.coe_lt_coe_iff] at hbk
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hk
  nlinarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A finite maximum of competitors of `P_θ[φ]` is a competitor. -/
theorem max_mem_singularityCompetitors {θ : SmoothRealForm n M 2} {φ u v : M → EReal}
    (hu : u ∈ singularityCompetitors θ φ) (hv : v ∈ singularityCompetitors θ φ) :
    (fun x => max (u x) (v x)) ∈ singularityCompetitors θ φ := by
  obtain ⟨⟨hupsh, hu0⟩, C, hC⟩ := hu
  obtain ⟨⟨hvpsh, hv0⟩, C', hC'⟩ := hv
  refine ⟨⟨IsThetaPshPotential.max hupsh hvpsh, fun x => max_le (hu0 x) (hv0 x)⟩,
    max C C', fun x hx => max_le ?_ ?_⟩
  · exact (hC x hx).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  · exact (hC' x hx).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))

/-- **`P_θ[φ]` is the regularization of an increasing sequence of competitors** (Choquet). -/
theorem exists_monotone_competitors (θ : SmoothRealForm n M 2) {φ : M → EReal}
    (hne : (singularityCompetitors θ φ).Nonempty) :
    ∃ r : ℕ → M → EReal, (∀ k, r k ∈ singularityCompetitors θ φ) ∧ Monotone r ∧
      uscRegularization (⨆ k, r k) = singularityEnvelope θ φ := by
  obtain ⟨s, hs, heq⟩ := exists_seq_uscRegularization_iSup_eq hne
  refine ⟨runningMax s, fun k => ?_, runningMax_monotone s, ?_⟩
  · induction k with
    | zero => exact hs 0
    | succ m ih => exact max_mem_singularityCompetitors ih (hs (m + 1))
  · have hsup : (⨆ k, runningMax s k) = ⨆ k, s k := by
      funext x
      rw [iSup_apply, iSup_apply]
      exact iSup_runningMax s x
    rw [hsup, heq]
    rfl

/-- **Concavity of `P_θ[·]`** (`prop:Pconc`, the form used in `ex:RWN`): if `t ∈ (0, 1)` and
`t φ₁ + (1 - t) φ₀ ≤ ψ` pointwise, then `t P_θ[φ₁] + (1 - t) P_θ[φ₀] ≤ P_θ[ψ]`, provided the
competitor families of `φ₀, φ₁` are nonempty and the three envelopes are `θ`-psh. -/
theorem convexComb_singularityEnvelope_le (θ : ClosedRealOneOneForm n M) {φ₀ φ₁ ψ : M → EReal}
    (h₀ : (singularityCompetitors θ.val φ₀).Nonempty)
    (h₁ : (singularityCompetitors θ.val φ₁).Nonempty)
    (hP₀ : IsThetaPshPotential θ.val (singularityEnvelope θ.val φ₀))
    (hP₁ : IsThetaPshPotential θ.val (singularityEnvelope θ.val φ₁))
    (hPψ : IsThetaPshPotential θ.val (singularityEnvelope θ.val ψ))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hle : convexComb t φ₁ φ₀ ≤ ψ) :
    convexComb t (singularityEnvelope θ.val φ₁) (singularityEnvelope θ.val φ₀) ≤
      singularityEnvelope θ.val ψ := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  obtain ⟨r₁, hr₁, hm₁, heq₁⟩ := exists_monotone_competitors θ.val h₁
  obtain ⟨r₀, hr₀, hm₀, heq₀⟩ := exists_monotone_competitors θ.val h₀
  -- each convex combination of competitors is a competitor for `ψ`
  have hcomb : ∀ k, convexComb t (r₁ k) (r₀ k) ≤ singularityEnvelope θ.val ψ := by
    intro k
    obtain ⟨⟨hpsh₁, h0₁⟩, C₁, hC₁⟩ := hr₁ k
    obtain ⟨⟨hpsh₀, h0₀⟩, C₀, hC₀⟩ := hr₀ k
    refine le_singularityEnvelope (isThetaPshPotential_convexComb hpsh₁ hpsh₀ ht0 ht1)
      (fun x => ?_) ⟨t * C₁ + (1 - t) * C₀, fun x _ => ?_⟩
    · rw [convexComb_apply]
      have h1 : (t : EReal) * r₁ k x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ht0.le) (h0₁ x)
      have h2 : ((1 - t : ℝ) : EReal) * r₀ k x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr h1t.le) (h0₀ x)
      simpa using add_le_add h1 h2
    · rw [convexComb_apply]
      have hdist : ∀ (s : ℝ), 0 ≤ s → ∀ (y : EReal) (C : ℝ),
          (s : EReal) * (y + (C : EReal)) = (s : EReal) * y + ((s * C : ℝ) : EReal) := by
        intro s hs y C
        rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hs)
          (EReal.coe_ne_top s), EReal.coe_mul]
      calc (t : EReal) * r₁ k x + ((1 - t : ℝ) : EReal) * r₀ k x
          ≤ (t : EReal) * (φ₁ x + (C₁ : EReal)) + ((1 - t : ℝ) : EReal) * (φ₀ x + (C₀ : EReal)) :=
            add_le_add (mul_le_mul_of_nonneg_left (hC₁ x (mem_univ x))
              (EReal.coe_nonneg.mpr ht0.le))
              (mul_le_mul_of_nonneg_left (hC₀ x (mem_univ x)) (EReal.coe_nonneg.mpr h1t.le))
        _ = ((t : EReal) * φ₁ x + ((1 - t : ℝ) : EReal) * φ₀ x) +
              (((t * C₁ : ℝ) : EReal) + (((1 - t) * C₀ : ℝ) : EReal)) := by
            rw [hdist t ht0.le, hdist (1 - t) h1t.le, add_add_add_comm]
        _ ≤ ψ x + ((t * C₁ + (1 - t) * C₀ : ℝ) : EReal) := by
            rw [EReal.coe_add]
            exact add_le_add (hle x) le_rfl
  have hL := isThetaPshPotential_convexComb hP₁ hP₀ ht0 ht1
  refine RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hL.1 hPψ.1
    fun e => ?_
  have hae₁ := RooftopEnvelopeAeObstacle.ae_chartFunction_iSup_eq_of_le_const (theta := θ)
    (B := 0) (fun k => (hr₁ k).1.1) (fun k x => by simpa using (hr₁ k).1.2 x) hm₁ heq₁ e
  have hae₀ := RooftopEnvelopeAeObstacle.ae_chartFunction_iSup_eq_of_le_const (theta := θ)
    (B := 0) (fun k => (hr₀ k).1.1) (fun k x => by simpa using (hr₀ k).1.2 x) hm₀ heq₀ e
  filter_upwards [hae₁, hae₀] with z hz₁ hz₀
  rw [convexComb_apply]
  have e₁ : singularityEnvelope θ.val φ₁ (e.val.symm z) = ⨆ k, r₁ k (e.val.symm z) := hz₁.symm
  have e₀ : singularityEnvelope θ.val φ₀ (e.val.symm z) = ⨆ k, r₀ k (e.val.symm z) := hz₀.symm
  rw [e₁, e₀]
  exact convexComb_iSup_le ht0 ht1 (fun i j hij => hm₁ hij _) (fun i j hij => hm₀ hij _)
    (fun k => (hr₁ k).1.2 _) (fun k => (hr₀ k).1.2 _)
    (fun k => by simpa only [convexComb_apply] using hcomb k (e.val.symm z))

end SGPT.PSH.Misc2EnvelopeConcave
