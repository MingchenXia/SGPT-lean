import SGPT.TestCurve.KFiltPotential

/-!
# The obstacle and the test curve of a filtration (abstract metered section ring)

Source `ex:RWN` (chapter *Test curves*). Blueprint `claude-k-filt`, node `claude-k-filt:obstacle`.
For a filtration `𝓕` of a metered graded section ring (`SectionMetric`), with `θ = c₁(L, h)`:

`Γ^𝓕_τ = P_θ[usc sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ]`,  `τ < τ(𝓕)`.

This file ports the projective proofs (`SGPT.LineBundle.SectionFiltration`, lanes MISC2 and RWN) to
the abstract interface:

* `GradedFiltration.testCurvePotential_anti`: `τ ↦ Γ^𝓕_τ` is decreasing;
* `GradedFiltration.obstacle_isThetaPshPotential`, `testCurvePotential_isThetaPshPotential`:
  `θ`-psh for `τ < τ(𝓕)`;
* `GradedFiltration.rawObstacle_concave` (`eq:GammaFconctemp1`), **`obstacle_concave`** and
  **`testCurvePotential_concave`** (with `prop:Pconc`,
  `SGPT.PSH.Misc2EnvelopeConcave.convexComb_singularityEnvelope_le`);
* **`GradedFiltration.obstacle_iGood`**: the obstacle is `𝓘`-good (`prop:Igoodsup` applied to
  the normalized section potentials, `𝓘`-good by `ex:analyIgood`);
* `GradedFiltration.normalizedLog_singularityLE_obstacle`: every `s ∈ 𝓕^{kτ}_k` has
  `k⁻¹ log |s|²_{h^k} ≤ obstacle + C`; `testCurvePotential_eq_of_le_neg_bound`: `Γ^𝓕_τ` does
  not depend on `τ ≤ -C`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open Filter Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.RWN SGPT.LineBundle
open scoped Topology

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
variable {S : ℕ → Type} [∀ k, AddCommGroup (S k)] [∀ k, Module ℂ (S k)]
  {mul : ∀ k k' : ℕ, S k → S k' → S (k + k')}

namespace GradedFiltration

variable (F : GradedFiltration mul) (D : SectionMetric n X S mul)

/-- `k⁻¹ Γ^{𝓕,k}_τ`. -/
def normalizedPotential (k : ℕ) (τ : ℝ) (x : X) : EReal :=
  F.sectionPotential D k τ x / ((k : ℝ) : EReal)

/-- The unregularized supremum `sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ`. -/
def rawObstacle (τ : ℝ) (x : X) : EReal :=
  ⨆ (k : ℕ) (_ : 0 < k), F.normalizedPotential D k τ x

/-- The obstacle `usc sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ` of source `ex:RWN`. -/
def obstacle (τ : ℝ) : X → EReal :=
  uscRegularization (F.rawObstacle D τ)

/-- Source `ex:RWN`: `Γ^𝓕_τ = P_θ[usc sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ]`, `θ = c₁(L, h)`. -/
def testCurvePotential (τ : ℝ) : X → EReal :=
  singularityEnvelope D.θ.val (F.obstacle D τ)

theorem normalizedPotential_le_zero (k : ℕ) (τ : ℝ) (x : X) :
    F.normalizedPotential D k τ x ≤ 0 := by
  unfold normalizedPotential
  calc F.sectionPotential D k τ x / ((k : ℝ) : EReal) ≤ 0 / ((k : ℝ) : EReal) :=
        EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr (Nat.cast_nonneg k))
          (F.sectionPotential_le_zero D k τ x)
    _ = 0 := EReal.zero_div

theorem rawObstacle_le_zero (τ : ℝ) (x : X) : F.rawObstacle D τ x ≤ 0 :=
  iSup₂_le fun k _ => F.normalizedPotential_le_zero D k τ x


variable [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)]

/-- `τ ↦ Γ^{𝓕,k}_τ` is decreasing. -/
theorem sectionPotential_anti (k : ℕ) {τ τ' : ℝ} (h : τ ≤ τ') (x : X) :
    F.sectionPotential D k τ' x ≤ F.sectionPotential D k τ x := by
  rw [F.sectionPotential_eq_raw D k τ', F.sectionPotential_eq_raw D k τ]
  refine iSup_le fun s => le_iSup_of_le
    ⟨s.1, F.piece_anti (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)) k s.2.1, s.2.2⟩ le_rfl

theorem normalizedPotential_anti (k : ℕ) {τ τ' : ℝ} (h : τ ≤ τ') (x : X) :
    F.normalizedPotential D k τ' x ≤ F.normalizedPotential D k τ x :=
  EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr (Nat.cast_nonneg k))
    (F.sectionPotential_anti D k h x)

theorem rawObstacle_anti {τ τ' : ℝ} (h : τ ≤ τ') (x : X) :
    F.rawObstacle D τ' x ≤ F.rawObstacle D τ x :=
  iSup₂_mono fun k _ => F.normalizedPotential_anti D k h x

theorem obstacle_anti {τ τ' : ℝ} (h : τ ≤ τ') : F.obstacle D τ' ≤ F.obstacle D τ :=
  uscRegularization_mono fun x => F.rawObstacle_anti D h x

/-- Source `ex:RWN`: `τ ↦ Γ^𝓕_τ` is decreasing. -/
theorem testCurvePotential_anti {τ τ' : ℝ} (h : τ ≤ τ') :
    F.testCurvePotential D τ' ≤ F.testCurvePotential D τ := by
  refine singularityEnvelope_mono ⟨0, fun x _ => ?_⟩
  rw [EReal.coe_zero, add_zero]
  exact F.obstacle_anti D h x

/-- `Γ^{𝓕,lk}_τ ≥ l Γ^{𝓕,k}_τ`. -/
theorem coe_mul_le_sectionPotential_mul (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (τ : ℝ)
    (x : X) (α : ℝ) (hα : F.sectionPotential D k τ x = α) :
    (((l : ℝ) * α : ℝ) : EReal) ≤ F.sectionPotential D (l * k) τ x := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have h := EReal.superadditive_iterate (a := fun j => F.sectionPotential D j τ x)
    (fun m j _ _ => F.sectionPotential_add_le D m j τ x) hk hα hk l'
  have hidx : l' * k + k = (l' + 1) * k := by ring
  rw [hidx, hα, ← EReal.coe_add] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  push_cast
  ring

/-- `k⁻¹Γ^{𝓕,k}_τ ≤ (lk)⁻¹Γ^{𝓕,lk}_τ`. -/
theorem normalizedPotential_le_mul (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (τ : ℝ)
    (x : X) :
    F.normalizedPotential D k τ x ≤ F.normalizedPotential D (l * k) τ x := by
  unfold normalizedPotential
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  by_cases hbot : F.sectionPotential D k τ x = ⊥
  · rw [hbot, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _)]
    exact bot_le
  · have htop : F.sectionPotential D k τ x ≠ ⊤ :=
      ne_top_of_le_ne_top EReal.zero_ne_top (F.sectionPotential_le_zero D k τ x)
    have hα : F.sectionPotential D k τ x = ((F.sectionPotential D k τ x).toReal : EReal) :=
      (EReal.coe_toReal htop hbot).symm
    have h := F.coe_mul_le_sectionPotential_mul D k l hk hl τ x _ hα
    have hlk : (0 : ℝ) ≤ ((l * k : ℕ) : ℝ) := Nat.cast_nonneg _
    calc F.sectionPotential D k τ x / ((k : ℝ) : EReal)
        = ((((l : ℝ) * (F.sectionPotential D k τ x).toReal : ℝ) : EReal)) /
            (((l * k : ℕ) : ℝ) : EReal) := by
          rw [hα, ← EReal.coe_div, ← EReal.coe_div, EReal.toReal_coe]
          congr 1
          push_cast
          field_simp
      _ ≤ _ := EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hlk) h

/-- **The inequality `eq:GammaFconctemp1` for rational weights.** For `0 < p < q`, sections of
degrees `k₀, k₁` at levels `τ₀, τ₁` with finite values `α₀, α₁` at `x` give
`sup_k k⁻¹Γ^{𝓕,k}_{wτ₁+(1-w)τ₀}(x) ≥ (1-w) α₀/k₀ + w α₁/k₁`, `w = p/q`. -/
theorem le_rawObstacle_of_rat (k₀ k₁ : ℕ) (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (τ₀ τ₁ : ℝ) (x : X) (α₀ α₁ : ℝ)
    (h₀ : F.sectionPotential D k₀ τ₀ x = α₀) (h₁ : F.sectionPotential D k₁ τ₁ x = α₁) :
    (((1 - (p : ℝ) / q) * (α₀ / k₀) + (p : ℝ) / q * (α₁ / k₁) : ℝ) : EReal) ≤
      F.rawObstacle D ((p : ℝ) / q * τ₁ + (1 - (p : ℝ) / q) * τ₀) x := by
  have hA : 0 < k₁ * (q - p) := Nat.mul_pos hk₁ (by omega)
  have hB : 0 < k₀ * p := Nat.mul_pos hk₀ hp
  have hle0 := F.coe_mul_le_sectionPotential_mul D k₀ (k₁ * (q - p)) hk₀ hA τ₀ x α₀ h₀
  have hle1 := F.coe_mul_le_sectionPotential_mul D k₁ (k₀ * p) hk₁ hB τ₁ x α₁ h₁
  have hKpos : 0 < k₁ * (q - p) * k₀ + k₀ * p * k₁ := by positivity
  have hj := F.sectionPotential_add_le_mix D (k₁ * (q - p) * k₀) (k₀ * p * k₁) hKpos τ₀ τ₁ x
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hpq)
  have hk₀R : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  have hk₁R : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hsub : ((q - p : ℕ) : ℝ) = (q : ℝ) - p := Nat.cast_sub hpq.le
  have hqne : (q : ℝ) ≠ 0 := hq0.ne'
  have hk₀ne : (k₀ : ℝ) ≠ 0 := hk₀R.ne'
  have hk₁ne : (k₁ : ℝ) ≠ 0 := hk₁R.ne'
  have hqp : (0 : ℝ) < (q : ℝ) - p := by
    have : (p : ℝ) < q := by exact_mod_cast hpq
    linarith
  have hτ : ((((k₁ * (q - p) * k₀ : ℕ) : ℝ) * τ₀ + ((k₀ * p * k₁ : ℕ) : ℝ) * τ₁) /
      (((k₁ * (q - p) * k₀ : ℕ) : ℝ) + ((k₀ * p * k₁ : ℕ) : ℝ))) =
      (p : ℝ) / q * τ₁ + (1 - (p : ℝ) / q) * τ₀ := by
    push_cast
    rw [hsub]
    field_simp
    ring
  rw [hτ] at hj
  have hK : ((k₁ * (q - p) * k₀ + k₀ * p * k₁ : ℕ) : ℝ) = (k₀ : ℝ) * k₁ * q := by
    push_cast
    rw [hsub]
    ring
  refine le_trans ?_ (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential D k
    ((p : ℝ) / q * τ₁ + (1 - (p : ℝ) / q) * τ₀) x) _ hKpos)
  unfold normalizedPotential
  have hsum : ((((k₁ * (q - p) : ℕ) : ℝ) * α₀ + ((k₀ * p : ℕ) : ℝ) * α₁ : ℝ) : EReal) ≤
      F.sectionPotential D (k₁ * (q - p) * k₀ + k₀ * p * k₁)
        ((p : ℝ) / q * τ₁ + (1 - (p : ℝ) / q) * τ₀) x := by
    rw [EReal.coe_add]
    exact (add_le_add hle0 hle1).trans hj
  refine le_trans (le_of_eq ?_) (EReal.div_le_div_right_of_nonneg
    (EReal.coe_nonneg.mpr (Nat.cast_nonneg _)) hsum)
  rw [← EReal.coe_div]
  congr 1
  rw [hK]
  push_cast
  rw [hsub]
  field_simp

/-- Real version of `x ≤ y` from `x - ε ≤ y` for all `ε > 0`. -/
private theorem coe_le_of_forall_sub_le {c : ℝ} {y : EReal}
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

omit [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)] in
/-- From `r < sup_{k>0} k⁻¹Γ^{𝓕,k}_τ(x)` extract a degree with a finite value above `r`. -/
private theorem exists_degree_of_lt_rawObstacle {τ : ℝ} {x : X} {r : ℝ}
    (h : (r : EReal) < F.rawObstacle D τ x) :
    ∃ k : ℕ, 0 < k ∧ ∃ α : ℝ, F.sectionPotential D k τ x = α ∧ r < α / k := by
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp h
  obtain ⟨hk0, hkr⟩ := lt_iSup_iff.mp hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  unfold normalizedPotential at hkr
  have hbot : F.sectionPotential D k τ x ≠ ⊥ := by
    intro hb
    rw [hb, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _)] at hkr
    exact not_lt_bot hkr
  have htop : F.sectionPotential D k τ x ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (F.sectionPotential_le_zero D k τ x)
  refine ⟨k, hk0, (F.sectionPotential D k τ x).toReal, (EReal.coe_toReal htop hbot).symm, ?_⟩
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_div] at hkr
  exact EReal.coe_lt_coe_iff.mp hkr

/-- **Source `ex:RWN`, `eq:GammaFconctemp1`**: for `τ₀ < τ₁` and `t ∈ (0, 1)`,
`sup_k k⁻¹Γ^{𝓕,k}_{tτ₁+(1-t)τ₀} ≥ t sup_k k⁻¹Γ^{𝓕,k}_{τ₁} + (1-t) sup_k k⁻¹Γ^{𝓕,k}_{τ₀}`
pointwise. -/
theorem rawObstacle_concave {τ₀ τ₁ : ℝ} (hτ : τ₀ < τ₁) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x : X) :
    ThetaPshConvexCombination.convexComb t (F.rawObstacle D τ₁) (F.rawObstacle D τ₀) x ≤
      F.rawObstacle D (t * τ₁ + (1 - t) * τ₀) x := by
  rw [ThetaPshConvexCombination.convexComb_apply]
  have h1t : (0 : ℝ) < 1 - t := by linarith
  induction h1 : F.rawObstacle D τ₁ x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]; exact bot_le
  | top => exact absurd (h1 ▸ F.rawObstacle_le_zero D τ₁ x) (not_le.mpr EReal.zero_lt_top)
  | coe r₁ =>
  induction h0 : F.rawObstacle D τ₀ x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos h1t, EReal.add_bot]; exact bot_le
  | top => exact absurd (h0 ▸ F.rawObstacle_le_zero D τ₀ x) (not_le.mpr EReal.zero_lt_top)
  | coe r₀ =>
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  refine coe_le_of_forall_sub_le fun ε hε => ?_
  set δ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨k₁, hk₁, α₁, hα₁, hr₁⟩ := F.exists_degree_of_lt_rawObstacle D
    (r := r₁ - δ) (by rw [h1]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨k₀, hk₀, α₀, hα₀, hr₀⟩ := F.exists_degree_of_lt_rawObstacle D
    (r := r₀ - δ) (by rw [h0]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
  set a₀ : ℝ := α₀ / k₀
  set a₁ : ℝ := α₁ / k₁
  set η : ℝ := δ / (|a₁ - a₀| + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨w, hw1, hw2⟩ := exists_rat_btwn (lt_min ht1 (lt_add_of_pos_right t hη0))
  have hwt : t < w := hw1
  have hw1' : (w : ℝ) < 1 := lt_of_lt_of_le hw2 (min_le_left _ _)
  have hwη : (w : ℝ) < t + η := lt_of_lt_of_le hw2 (min_le_right _ _)
  have hw0 : (0 : ℝ) < w := ht0.trans hwt
  have hnum : 0 < w.num := Rat.num_pos.mpr (by exact_mod_cast hw0)
  set p : ℕ := w.num.toNat with hp
  set q : ℕ := w.den with hq
  have hpZ : (p : ℤ) = w.num := Int.toNat_of_nonneg hnum.le
  have hwpq : (w : ℝ) = (p : ℝ) / q := by
    rw [Rat.cast_def, ← hpZ]
    push_cast
    rfl
  have hp0 : 0 < p := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast w.den_pos
  have hpq : p < q := by
    have : (p : ℝ) / q < 1 := hwpq ▸ hw1'
    rw [div_lt_one hqpos] at this
    exact_mod_cast this
  have hrat := F.le_rawObstacle_of_rat D k₀ k₁ hk₀ hk₁ p q hp0 hpq τ₀ τ₁ x α₀ α₁ hα₀ hα₁
  rw [← hwpq] at hrat
  -- monotonicity in the level
  have hlevel : t * τ₁ + (1 - t) * τ₀ ≤ (w : ℝ) * τ₁ + (1 - (w : ℝ)) * τ₀ := by
    nlinarith
  have hanti := F.rawObstacle_anti D hlevel x
  refine le_trans ?_ (hrat.trans hanti)
  rw [EReal.coe_le_coe_iff]
  -- real arithmetic
  have herr : |((1 - (w : ℝ)) * a₀ + (w : ℝ) * a₁) - ((1 - t) * a₀ + t * a₁)| ≤ δ := by
    have heq : ((1 - (w : ℝ)) * a₀ + (w : ℝ) * a₁) - ((1 - t) * a₀ + t * a₁) =
        ((w : ℝ) - t) * (a₁ - a₀) := by ring
    rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hwt)]
    have h1 : ((w : ℝ) - t) ≤ η := by linarith
    calc ((w : ℝ) - t) * |a₁ - a₀| ≤ η * |a₁ - a₀| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ η * (|a₁ - a₀| + 1) := mul_le_mul_of_nonneg_left (by linarith) hη0.le
      _ = δ := by rw [hη]; field_simp
  have hlow := neg_abs_le (((1 - (w : ℝ)) * a₀ + (w : ℝ) * a₁) - ((1 - t) * a₀ + t * a₁))
  have hr₀' : r₀ - δ < a₀ := hr₀
  have hr₁' : r₁ - δ < a₁ := hr₁
  nlinarith

omit [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)] in
include D in
/-- For `τ < τ(𝓕)` there is a degree `m > 0` such that `(lm) τ ≤ τ_{lm}(𝓕)` for all `l > 0`. -/
theorem exists_degree_jump_of_lt_slope {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    ∃ m : ℕ, 0 < m ∧ ∀ l : ℕ, 0 < l → ((((l * m : ℕ) : ℝ) * τ : ℝ) : EReal) ≤ F.jump (l * m) := by
  obtain ⟨m, hm⟩ := lt_iSup_iff.mp hτ
  obtain ⟨hm0, hmτ⟩ := lt_iSup_iff.mp hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hbot : F.jump m ≠ ⊥ := by
    intro hb
    rw [hb, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr hmR) (EReal.coe_ne_top _)] at hmτ
    exact not_lt_bot hmτ
  have htop : F.jump m ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (F.jump_le_bound hm0)
  set β := (F.jump m).toReal
  have hβ : F.jump m = β := (EReal.coe_toReal htop hbot).symm
  have hτβ : τ < β / m := by
    rw [hβ, ← EReal.coe_div] at hmτ
    exact EReal.coe_lt_coe_iff.mp hmτ
  have hmτβ : (m : ℝ) * τ ≤ β := by
    rw [lt_div_iff₀ hmR] at hτβ
    linarith
  refine ⟨m, hm0, fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have h := EReal.superadditive_iterate (a := F.jump)
    (fun i j _ _ => F.jump_add_le D.mul_ne_zero i j) hm0 hβ hm0 l'
  have hidx : l' * m + m = (l' + 1) * m := by ring
  rw [hidx, hβ, ← EReal.coe_add] at h
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) h
  push_cast
  have : (0 : ℝ) ≤ l' := Nat.cast_nonneg l'
  nlinarith

/-- For `τ < τ(𝓕)`: the normalized potentials along the degrees `(j+1)! m` form an increasing
sequence of `θ`-psh functions whose supremum is `sup_{k>0} k⁻¹Γ^{𝓕,k}_τ`. -/
theorem exists_increasing_sequence {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    ∃ g : ℕ → X → EReal,
      (∀ j, IsThetaPshPotential D.θ.val (g j)) ∧
      (∀ j x, g j x ≤ ((0 : ℝ) : EReal)) ∧ Monotone g ∧ (⨆ j, g j) = F.rawObstacle D τ := by
  obtain ⟨m, hm0, hjump⟩ := F.exists_degree_jump_of_lt_slope D hτ
  let kseq : ℕ → ℕ := fun j => (j + 1).factorial * m
  have hkpos : ∀ j, 0 < kseq j := fun j => Nat.mul_pos (Nat.factorial_pos _) hm0
  refine ⟨fun j => F.normalizedPotential D (kseq j) τ, fun j => ?_, fun j x => ?_, ?_, ?_⟩
  · have hkR : (0 : ℝ) < kseq j := by exact_mod_cast hkpos j
    have hpsh := F.isThetaPshPotential_sectionPotential D (hkpos j) (τ := τ)
      (hjump _ (Nat.factorial_pos _))
    have h := RestrictedApproximantComparison.isThetaPshPotential_smul hpsh (inv_pos.mpr hkR)
    simp only [smul_smul, inv_mul_cancel₀ hkR.ne', one_smul] at h
    convert h using 1
    funext x
    change F.sectionPotential D (kseq j) τ x / (((kseq j : ℕ) : ℝ) : EReal) = _
    rw [div_eq_mul_inv, mul_comm, ← EReal.coe_inv]
  · rw [EReal.coe_zero]
    exact F.normalizedPotential_le_zero D _ τ x
  · refine monotone_nat_of_le_succ fun j x => ?_
    have hidx : kseq (j + 1) = (j + 2) * kseq j := by
      simp only [kseq, Nat.factorial_succ (j + 1)]
      ring
    change F.normalizedPotential D (kseq j) τ x ≤ F.normalizedPotential D (kseq (j + 1)) τ x
    rw [hidx]
    exact F.normalizedPotential_le_mul D _ _ (hkpos j) (by omega) τ x
  · funext x
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun j => le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential D k τ x)
        (kseq j) (hkpos j)
    · refine iSup₂_le fun k hk => ?_
      obtain ⟨c, hc⟩ := Nat.dvd_factorial hk (Nat.le_succ k)
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h, mul_zero] at hc
          exact absurd hc (Nat.factorial_pos _).ne'
        · exact h
      have hidx : kseq k = (c * m) * k := by
        simp only [kseq, hc]
        ring
      refine le_trans ?_ (le_iSup (fun j => F.normalizedPotential D (kseq j) τ x) k)
      rw [hidx]
      exact F.normalizedPotential_le_mul D k (c * m) hk (Nat.mul_pos hc0 hm0) τ x

/-- **Source `ex:RWN`**: for `τ < τ(𝓕)` the obstacle `usc sup_k k⁻¹Γ^{𝓕,k}_τ` is in
`PSH(X, θ)`. -/
theorem obstacle_isThetaPshPotential {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    IsThetaPshPotential D.θ.val (F.obstacle D τ) := by
  obtain ⟨g, hg, hg0, -, hsup⟩ := F.exists_increasing_sequence D hτ
  have h := SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup hg hg0
  have hfun : (fun x => ⨆ j, g j x) = F.rawObstacle D τ := by
    rw [← hsup]
    funext x
    rw [iSup_apply]
  rw [hfun] at h
  exact h

/-- For `τ < τ(𝓕)`, the obstacle equals the unregularized supremum almost everywhere in every
holomorphic chart. -/
theorem ae_rawObstacle_eq_obstacle {τ : ℝ} (hτ : (τ : EReal) < F.slope)
    (e : ComplexChart n (X)) :
    ∀ᵐ z ∂((MeasureTheory.volume : Measure (ComplexModel n)).restrict e.val.target),
      F.rawObstacle D τ (e.val.symm z) = F.obstacle D τ (e.val.symm z) := by
  obtain ⟨g, hg, hg0, hmono, hsup⟩ := F.exists_increasing_sequence D hτ
  have heq : uscRegularization (⨆ j, g j) = F.obstacle D τ := by
    rw [hsup]
    rfl
  have hae := RooftopEnvelopeAeObstacle.ae_chartFunction_iSup_eq_of_le_const
    (theta := D.θ) hg hg0 hmono heq e
  filter_upwards [hae] with z hz
  have h1 : F.rawObstacle D τ (e.val.symm z) = ⨆ j, chartFunction (g j) e z := by
    rw [← hsup, iSup_apply]
    rfl
  rw [h1, hz]
  rfl

/-- **Source `ex:RWN`, concavity of the obstacle**: for `τ₀ < τ₁ < τ(𝓕)` and `t ∈ (0, 1)`,
`usc sup_k k⁻¹Γ^{𝓕,k}_{tτ₁+(1-t)τ₀} ≥ t · usc sup_k k⁻¹Γ^{𝓕,k}_{τ₁} +
(1-t) · usc sup_k k⁻¹Γ^{𝓕,k}_{τ₀}`. -/
theorem obstacle_concave {τ₀ τ₁ : ℝ} (hτ : τ₀ < τ₁) (hτ₁ : (τ₁ : EReal) < F.slope) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t (F.obstacle D τ₁) (F.obstacle D τ₀) ≤
      F.obstacle D (t * τ₁ + (1 - t) * τ₀) := by
  have hτ₀ : (τ₀ : EReal) < F.slope := lt_trans (EReal.coe_lt_coe_iff.mpr hτ) hτ₁
  have hτt : ((t * τ₁ + (1 - t) * τ₀ : ℝ) : EReal) < F.slope :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by nlinarith)) hτ₁
  have hL := ThetaPshConvexCombination.isThetaPshPotential_convexComb
    (F.obstacle_isThetaPshPotential D hτ₁) (F.obstacle_isThetaPshPotential D hτ₀) ht0 ht1
  have hR := F.obstacle_isThetaPshPotential D hτt
  refine RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hL.1 hR.1
    fun e => ?_
  filter_upwards [F.ae_rawObstacle_eq_obstacle D hτ₁ e, F.ae_rawObstacle_eq_obstacle D hτ₀ e]
    with z h₁ h₀
  rw [ThetaPshConvexCombination.convexComb_apply, ← h₁, ← h₀,
    ← ThetaPshConvexCombination.convexComb_apply]
  exact (F.rawObstacle_concave D hτ ht0 ht1 _).trans (le_uscRegularization _ _)

/-- **Source `ex:RWN`**: `Γ^𝓕_τ ∈ PSH(X, θ)` for `τ < τ(𝓕)`. -/
theorem testCurvePotential_isThetaPshPotential [Nonempty X] {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) :
    IsThetaPshPotential D.θ.val (F.testCurvePotential D τ) := by
  exact Pending.singularityEnvelope_isThetaPshPotential D.θ.val
    D.θ.property.1 D.θ.property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) _
    (F.obstacle_isThetaPshPotential D hτ)

omit [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)] in
theorem obstacle_le_zero (τ : ℝ) : F.obstacle D τ ≤ 0 :=
  uscRegularization_le upperSemicontinuous_const fun x => F.rawObstacle_le_zero D τ x

/-- For `τ < τ(𝓕)` the obstacle is a competitor of its own envelope. -/
theorem obstacle_mem_singularityCompetitors {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    F.obstacle D τ ∈ singularityCompetitors D.θ.val (F.obstacle D τ) := by
  refine ⟨⟨F.obstacle_isThetaPshPotential D hτ, F.obstacle_le_zero D τ⟩, 0, fun x _ => ?_⟩
  rw [EReal.coe_zero, add_zero]

/-- **Source `ex:RWN`, concavity of the test curve**: for `τ₀ < τ₁ < τ(𝓕)` and `t ∈ (0, 1)`,
`Γ^𝓕_{tτ₁+(1-t)τ₀} ≥ t Γ^𝓕_{τ₁} + (1-t) Γ^𝓕_{τ₀}` (concavity of the obstacle and of
`P_θ[·]`). -/
theorem testCurvePotential_concave [Nonempty X] {τ₀ τ₁ : ℝ}
    (hτ : τ₀ < τ₁) (hτ₁ : (τ₁ : EReal) < F.slope) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t (F.testCurvePotential D τ₁)
        (F.testCurvePotential D τ₀) ≤
      F.testCurvePotential D (t * τ₁ + (1 - t) * τ₀) := by
  have hτ₀ : (τ₀ : EReal) < F.slope := lt_trans (EReal.coe_lt_coe_iff.mpr hτ) hτ₁
  have hτt : ((t * τ₁ + (1 - t) * τ₀ : ℝ) : EReal) < F.slope :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by nlinarith)) hτ₁
  exact SGPT.PSH.Misc2EnvelopeConcave.convexComb_singularityEnvelope_le D.θ
    ⟨_, F.obstacle_mem_singularityCompetitors D hτ₀⟩
    ⟨_, F.obstacle_mem_singularityCompetitors D hτ₁⟩
    (F.testCurvePotential_isThetaPshPotential D hτ₀)
    (F.testCurvePotential_isThetaPshPotential D hτ₁)
    (F.testCurvePotential_isThetaPshPotential D hτt) ht0 ht1
    (F.obstacle_concave D hτ hτ₁ ht0 ht1)

/-! ### The normalized section potentials and the obstacle -/

/-- The normalized section potential `k⁻¹ log |s|²_{h^k}`. -/
def _root_.SGPT.TestCurve.KFilt.SectionMetric.normalizedLog (k : ℕ) (s : S k) : X → EReal :=
  fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * D.logNormSq k s x

/-- The index set of the normalized section potentials entering the obstacle at `τ`:
`k > 0` and `0 ≠ s ∈ 𝓕^{kτ}_k` with `|s|²_{h^k} ≤ 1`. -/
def ObstacleIndex (τ : ℝ) : Type :=
  {p : Σ k : ℕ, S k // 0 < p.1 ∧ p.2 ∈ F.normalizedSections D p.1 τ ∧ p.2 ≠ 0}

/-- The normalized section potential `k⁻¹ log |s|²_{h^k}` of an index `(k, s)`. -/
def obstacleFamily (τ : ℝ) (i : F.ObstacleIndex D τ) : X → EReal :=
  D.normalizedLog i.1.1 i.1.2

/-- `k⁻¹ Γ^{𝓕,k}_τ = sup_{s} k⁻¹ log |s|²_{h^k}` over normalized `s ∈ 𝓕^{kτ}_k`. -/
theorem normalizedPotential_eq_iSup (k : ℕ) (hk : 0 < k) (τ : ℝ) (x : X) :
    F.normalizedPotential D k τ x =
      ⨆ s : F.normalizedSections D k τ, ((((k : ℝ)⁻¹ : ℝ) : EReal) * D.logNormSq k s.1 x) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold normalizedPotential
  rw [F.sectionPotential_eq_raw D k τ]
  change (⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x) / ((k : ℝ) : EReal) = _
  rw [EReal.iSup_div_coe _ hkR]
  simp only [EReal.div_coe_eq_inv_mul]

/-- **The raw obstacle is the supremum of the normalized section potentials**. -/
theorem obstacleFamily_iSup (τ : ℝ) (x : X) :
    (⨆ i : F.ObstacleIndex D τ, F.obstacleFamily D τ i x) = F.rawObstacle D τ x := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    obtain ⟨⟨k, s⟩, hk, hs, -⟩ := i
    refine le_trans ?_ (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential D k τ x) k hk)
    rw [F.normalizedPotential_eq_iSup D k hk τ x]
    exact le_iSup (fun s : F.normalizedSections D k τ => ((((k : ℝ)⁻¹ : ℝ) : EReal) *
      D.logNormSq k s.1 x)) ⟨s, hs⟩
  · refine iSup₂_le fun k hk => ?_
    rw [F.normalizedPotential_eq_iSup D k hk τ x]
    refine iSup_le fun s => ?_
    by_cases hs0 : s.1 = 0
    · rw [hs0, D.logNormSq_zero,
        EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (by exact_mod_cast hk)))]
      exact bot_le
    · exact le_iSup (fun i : F.ObstacleIndex D τ => F.obstacleFamily D τ i x)
        ⟨⟨k, s.1⟩, hk, s.2, hs0⟩

/-- Each normalized section potential lies below the raw obstacle. -/
theorem obstacleFamily_le_rawObstacle (τ : ℝ) (i : F.ObstacleIndex D τ) (x : X) :
    F.obstacleFamily D τ i x ≤ F.rawObstacle D τ x := by
  rw [← F.obstacleFamily_iSup D τ x]
  exact le_iSup (fun j : F.ObstacleIndex D τ => F.obstacleFamily D τ j x) i

omit [∀ k, FiniteDimensional ℂ (S k)] in
/-- The index set is nonempty as soon as `𝓕^{kτ}_k ≠ 0` for some `k > 0`. -/
theorem obstacleIndex_nonempty {τ : ℝ} {k : ℕ} (hk : 0 < k)
    (hne : F.piece ((k : ℝ) * τ) k ≠ ⊥) : Nonempty (F.ObstacleIndex D τ) := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, -, hc0, hcle⟩ := D.exists_normalized k s hs0
  exact ⟨⟨⟨k, c • s⟩, hk, ⟨Submodule.smul_mem _ c hs, hcle⟩, hc0⟩⟩

/-- For `τ < τ(𝓕)` the index set is nonempty. -/
theorem obstacleIndex_nonempty_of_lt_slope {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    Nonempty (F.ObstacleIndex D τ) := by
  obtain ⟨m, hm, hjump⟩ := F.exists_degree_jump_of_lt_slope D hτ
  have h1 := hjump 1 one_pos
  simp only [one_mul] at h1
  exact F.obstacleIndex_nonempty D hm ((F.piece_ne_bot_iff _).mpr h1)

section IGood

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- **Source `ex:RWN`: the obstacle is `𝓘`-good.** If `𝓕^{kτ}_k ≠ 0` for some `k > 0`, then
`usc sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ` is `𝓘`-good (`def:Igoodpot`), by `prop:Igoodsup` applied
to the normalized section potentials (each `𝓘`-good by `ex:analyIgood`). -/
theorem obstacle_iGood (omega : KahlerBackground n X) {τ : ℝ}
    (hne : Nonempty (F.ObstacleIndex D τ)) : IGood (n := n) (F.obstacle D τ) := by
  have hpshN : ∀ i : F.ObstacleIndex D τ,
      IsThetaPshPotential D.θ.val (F.obstacleFamily D τ i) := fun i =>
    D.isThetaPsh_normalized i.2.1 i.2.2.2
  have hpsh : ∀ i : F.ObstacleIndex D τ,
      (ofFixedModel n X).IsThetaPSH (nativeClosedFormToAtlas D.θ) (F.obstacleFamily D τ i) := by
    intro i
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [sourceNativeAtlasForm_roundTrip]
    exact hpshN i
  have hgood : ∀ i : F.ObstacleIndex D τ, sourceIGood (n := n) (F.obstacleFamily D τ i) := by
    intro i
    apply (sourceIGood_iff_native _).mpr
    have hA := SGPT.Okounkov.TranscendentalCore.hasManifoldAnalyticSingularityType_nonneg_rat_smul
      (D.analyticType i.1.1 i.1.2 i.2.2.2) (r := ((i.1.1 : ℚ))⁻¹) (by positivity)
    have hcast : ((((i.1.1 : ℚ))⁻¹ : ℚ) : ℝ) = (i.1.1 : ℝ)⁻¹ := by push_cast; ring
    rw [hcast] at hA
    exact AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type omega
      (hpshN i).quasiPshPotential hA
  have hbdd : LocallyUniformlyBoundedAbove (range (F.obstacleFamily D τ)) univ := by
    intro x _
    refine ⟨univ, Filter.univ_mem, 0, ?_⟩
    rintro _ ⟨i, rfl⟩ y -
    exact (F.obstacleFamily_le_rawObstacle D τ i y).trans (F.rawObstacle_le_zero D τ y)
  have h := sourceIGood_uscSup omega (F.obstacleFamily D τ) hpsh hgood hbdd
  have heq : (⨆ i, F.obstacleFamily D τ i) = F.rawObstacle D τ := by
    funext x
    rw [iSup_apply]
    exact F.obstacleFamily_iSup D τ x
  rw [heq] at h
  exact (sourceIGood_iff_native _).mp h

/-- For `τ < τ(𝓕)` the obstacle `usc sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` is `𝓘`-good. -/
theorem obstacle_iGood_of_lt_slope (omega : KahlerBackground n X) {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) : IGood (n := n) (F.obstacle D τ) :=
  F.obstacle_iGood D omega (F.obstacleIndex_nonempty_of_lt_slope D hτ)

end IGood

/-! ### Sections and the obstacle -/

/-- Every section `s ∈ 𝓕^{kτ}_k`, `k > 0`, satisfies `k⁻¹ log |s|²_{h^k} ≤ obstacle + C`. -/
theorem normalizedLog_singularityLE_obstacle {k : ℕ} (hk : 0 < k) {τ : ℝ} {s : S k}
    (hs : s ∈ F.piece ((k : ℝ) * τ) k) :
    SGPT.PSH.SingularityLE (D.normalizedLog k s) (F.obstacle D τ) := by
  by_cases hs0 : s = 0
  · refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => ?_⟩
    change (((k : ℝ)⁻¹ : ℝ) : EReal) * D.logNormSq k s x ≤ _
    rw [hs0, D.logNormSq_zero,
      EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (by exact_mod_cast hk)))]
    exact bot_le
  obtain ⟨c, hc, hc0, hcle⟩ := D.exists_normalized k s hs0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    ⟨-((k : ℝ)⁻¹ * Real.log (Complex.normSq c)), fun x => ?_⟩
  have hmem : c • s ∈ F.normalizedSections D k τ := ⟨Submodule.smul_mem _ c hs, hcle⟩
  have hle : (((k : ℝ)⁻¹ : ℝ) : EReal) * D.logNormSq k (c • s) x ≤ F.obstacle D τ x := by
    refine le_trans ?_ (le_uscRegularization _ x)
    refine le_trans ?_ (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential D k τ x) k hk)
    rw [F.normalizedPotential_eq_iSup D k hk τ x]
    exact le_iSup (fun s : F.normalizedSections D k τ => ((((k : ℝ)⁻¹ : ℝ) : EReal) *
      D.logNormSq k s.1 x)) ⟨_, hmem⟩
  rw [D.logNormSq_smul k hc s x] at hle
  change (((k : ℝ)⁻¹ : ℝ) : EReal) * D.logNormSq k s x ≤ _
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  have hO0 : F.obstacle D τ x ≤ 0 := F.obstacle_le_zero D τ x
  generalize D.logNormSq k s x = A at hle ⊢
  generalize F.obstacle D τ x = O at hle hO0 ⊢
  generalize Real.log (Complex.normSq c) = l at hle ⊢
  induction A using EReal.rec with
  | bot =>
    rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr hk')]
    exact bot_le
  | top =>
    rw [EReal.coe_add_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr hk')] at hle
    exact absurd (top_le_iff.mp (hle.trans hO0)) EReal.zero_ne_top
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_mul] at hle
    induction O using EReal.rec with
    | bot => exact absurd (le_bot_iff.mp hle) (EReal.coe_ne_bot _)
    | top => exact absurd hO0 (by simp)
    | coe o =>
      have hle' : (k : ℝ)⁻¹ * (l + r) ≤ o := EReal.coe_le_coe_iff.mp hle
      rw [← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by nlinarith)

omit [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)] in
/-- For `τ ≤ -C` (`C` the constant of `eq:Flinearlybdd`) and `k > 0`: `𝓕^{kτ}_k = S k`. -/
theorem piece_eq_top_of_le_neg_bound {τ : ℝ} (hτ : τ ≤ -(F.bound : ℝ)) {k : ℕ} (hk : 0 < k) :
    F.piece ((k : ℝ) * τ) k = ⊤ := by
  apply F.piece_eq_top_of_le hk
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

omit [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)] in
/-- For `τ, τ' ≤ -C`: `Γ^𝓕_τ = Γ^𝓕_{τ'}`. -/
theorem testCurvePotential_eq_of_le_neg_bound {τ τ' : ℝ} (hτ : τ ≤ -(F.bound : ℝ))
    (hτ' : τ' ≤ -(F.bound : ℝ)) : F.testCurvePotential D τ = F.testCurvePotential D τ' := by
  have hsec : ∀ k : ℕ, 0 < k → F.normalizedSections D k τ = F.normalizedSections D k τ' := by
    intro k hk
    ext s
    simp only [normalizedSections, Set.mem_ofPred_eq, F.piece_eq_top_of_le_neg_bound hτ hk,
      F.piece_eq_top_of_le_neg_bound hτ' hk, Submodule.mem_top, true_and]
  have hraw : F.rawObstacle D τ = F.rawObstacle D τ' := by
    funext x
    unfold rawObstacle
    refine iSup_congr fun k => iSup_congr fun hk => ?_
    unfold normalizedPotential sectionPotential
    rw [hsec k hk]
  unfold testCurvePotential obstacle
  rw [hraw]

end GradedFiltration

end SGPT.TestCurve.KFilt
