import SGPT.LineBundle.Misc2SectionPotentialContinuity
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.PSH.Misc2EnvelopeConcave

/-!
# The obstacle of the test curve of a filtration and its concavity

Source `ex:RWN` (chapter *Test curves*). For a filtration `𝓕` of `R(X, L)` and a smooth metric
`h` on `L`, `θ = c₁(L, h)`, the book defines

`Γ^𝓕_τ = P_θ[usc sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ]`,  `τ < τ(𝓕)`,

claims that `τ ↦ Γ^𝓕_τ` is decreasing, and proves its concavity by showing that the obstacle
`τ ↦ usc sup_k k⁻¹ Γ^{𝓕,k}_τ` is concave on `(-∞, τ(𝓕))` (then `prop:Pconc`).

This file proves:

* `SectionFiltration.obstacle_isThetaPshPotential`: for `τ < τ(𝓕)` the obstacle is `θ`-psh;
* `SectionFiltration.ae_rawObstacle_eq_obstacle`: it agrees with the unregularized supremum
  almost everywhere in every chart (the supremum is the increasing limit along the degrees
  `(j+1)! m`, by superadditivity);
* `SectionFiltration.rawObstacle_concave`: the book's inequality `eq:GammaFconctemp1` for the
  unregularized suprema, `sup_k k⁻¹Γ^{𝓕,k}_{tτ₁+(1-t)τ₀} ≥ t sup_k k⁻¹Γ^{𝓕,k}_{τ₁} +
  (1-t) sup_k k⁻¹Γ^{𝓕,k}_{τ₀}` (products of powers of sections for rational `t`, then
  monotonicity of the filtration);
* **`SectionFiltration.obstacle_concave`**: the obstacle is concave on `(-∞, τ(𝓕))` (the claim
  proved in the book's text; the comparison of `θ`-psh functions almost everywhere in charts
  replaces `prop:pshfuncdetdense` and `prop:supsupstardiff`);
* `SectionFiltration.testCurvePotential`, `testCurvePotential_anti`,
  `testCurvePotential_isThetaPshPotential`: `Γ^𝓕_τ` itself, decreasing in `τ`, in
  `PSH(X, θ)` for `τ < τ(𝓕)`;
* **`SectionFiltration.testCurvePotential_concave`**: `τ ↦ Γ^𝓕_τ` is concave on
  `(-∞, τ(𝓕))` (obstacle concavity and the concavity of `P_θ[·]`,
  `SGPT.PSH.Misc2EnvelopeConcave.convexComb_singularityEnvelope_le`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance misc2ObstTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance misc2ObstCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance misc2ObstManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

namespace SectionFiltration

variable {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]
variable (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)

/-- `k⁻¹ Γ^{𝓕,k}_τ`. -/
def normalizedPotential (k : ℕ) (τ : ℝ) (x : SchemeComplexPoint f) : EReal :=
  F.sectionPotential H k τ x / ((k : ℝ) : EReal)

/-- The unregularized supremum `sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ`. -/
def rawObstacle (τ : ℝ) (x : SchemeComplexPoint f) : EReal :=
  ⨆ (k : ℕ) (_ : 0 < k), F.normalizedPotential H k τ x

/-- The obstacle `usc sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ` of source `ex:RWN`. -/
def obstacle (τ : ℝ) : SchemeComplexPoint f → EReal :=
  uscRegularization (F.rawObstacle H τ)

/-- Source `ex:RWN`: `Γ^𝓕_τ = P_θ[usc sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ]`, `θ = c₁(L, h)`. -/
def testCurvePotential (τ : ℝ) : SchemeComplexPoint f → EReal :=
  letI := E.isSeparated
  letI := E.quasiCompact
  singularityEnvelope (H.curvature a).val (F.obstacle H τ)

omit [IsIntegral X] in
theorem normalizedPotential_le_zero (k : ℕ) (τ : ℝ) (x : SchemeComplexPoint f) :
    F.normalizedPotential H k τ x ≤ 0 := by
  unfold normalizedPotential
  calc F.sectionPotential H k τ x / ((k : ℝ) : EReal) ≤ 0 / ((k : ℝ) : EReal) :=
        EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr (Nat.cast_nonneg k))
          (F.sectionPotential_le_zero H k τ x)
    _ = 0 := EReal.zero_div

omit [IsIntegral X] in
theorem rawObstacle_le_zero (τ : ℝ) (x : SchemeComplexPoint f) : F.rawObstacle H τ x ≤ 0 :=
  iSup₂_le fun k _ => F.normalizedPotential_le_zero H k τ x

/-- `τ ↦ Γ^{𝓕,k}_τ` is decreasing. -/
theorem sectionPotential_anti (k : ℕ) {τ τ' : ℝ} (h : τ ≤ τ') (x : SchemeComplexPoint f) :
    F.sectionPotential H k τ' x ≤ F.sectionPotential H k τ x := by
  rw [F.sectionPotential_eq_raw H k τ', F.sectionPotential_eq_raw H k τ]
  refine iSup_le fun s => le_iSup_of_le
    ⟨s.1, F.piece_anti (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)) k s.2.1, s.2.2⟩ le_rfl

theorem normalizedPotential_anti (k : ℕ) {τ τ' : ℝ} (h : τ ≤ τ') (x : SchemeComplexPoint f) :
    F.normalizedPotential H k τ' x ≤ F.normalizedPotential H k τ x :=
  EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr (Nat.cast_nonneg k))
    (F.sectionPotential_anti H k h x)

theorem rawObstacle_anti {τ τ' : ℝ} (h : τ ≤ τ') (x : SchemeComplexPoint f) :
    F.rawObstacle H τ' x ≤ F.rawObstacle H τ x :=
  iSup₂_mono fun k _ => F.normalizedPotential_anti H k h x

theorem obstacle_anti {τ τ' : ℝ} (h : τ ≤ τ') : F.obstacle H τ' ≤ F.obstacle H τ :=
  uscRegularization_mono fun x => F.rawObstacle_anti H h x

/-- Source `ex:RWN`: `τ ↦ Γ^𝓕_τ` is decreasing. -/
theorem testCurvePotential_anti {τ τ' : ℝ} (h : τ ≤ τ') :
    F.testCurvePotential H τ' ≤ F.testCurvePotential H τ := by
  let := E.isSeparated
  let := E.quasiCompact
  refine singularityEnvelope_mono ⟨0, fun x _ => ?_⟩
  rw [EReal.coe_zero, add_zero]
  exact F.obstacle_anti H h x

/-- Superadditivity across levels: `Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_{τ'} ≤ Γ^{𝓕,k+k'}_{(kτ+k'τ')/(k+k')}`
(products of sections). -/
theorem sectionPotential_add_le_mix (k k' : ℕ) (hkk : 0 < k + k') (τ τ' : ℝ)
    (x : SchemeComplexPoint f) :
    F.sectionPotential H k τ x + F.sectionPotential H k' τ' x ≤
      F.sectionPotential H (k + k') (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) x := by
  rw [F.sectionPotential_eq_raw H k τ, F.sectionPotential_eq_raw H k' τ',
    F.sectionPotential_eq_raw H (k + k')]
  refine EReal.add_le_of_forall_lt fun u hu v hv => ?_
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hu
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hv
  have hmem : SectionSpace.mul f a k k' s.1 t.1 ∈
      F.normalizedSections H (k + k') (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) := by
    refine ⟨?_, fun p => ?_⟩
    · have h := F.mul_mem _ _ k k' s.1 t.1 s.2.1 t.2.1
      have hne : ((k : ℝ) + k') ≠ 0 := by
        have : (0 : ℝ) < ((k + k' : ℕ) : ℝ) := by exact_mod_cast hkk
        push_cast at this
        exact this.ne'
      have he : ((k + k' : ℕ) : ℝ) * (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) =
          (k : ℝ) * τ + (k' : ℝ) * τ' := by
        push_cast
        field_simp
      rw [he]
      exact h
    · rw [SectionSpace.mul_apply]
      erw [H.sectionNormSq_mul a k k' s.1 t.1 p]
      exact mul_le_one₀ (s.2.2 p) (H.sectionNormSq_nonneg a k' t.1 p) (t.2.2 p)
  calc u + v ≤ H.sectionLogNormSq a k s.1 x + H.sectionLogNormSq a k' t.1 x :=
        add_le_add hs.le ht.le
    _ = H.sectionLogNormSq a (k + k') (SectionSpace.mul f a k k' s.1 t.1) x :=
        (congrFun (H.sectionLogNormSq_mul a k k' s.1 t.1) x).symm
    _ ≤ ⨆ r : F.normalizedSections H (k + k') (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')),
          H.sectionLogNormSq a (k + k') r.1 x :=
        le_iSup (fun r : F.normalizedSections H (k + k')
          (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) =>
            H.sectionLogNormSq a (k + k') r.1 x) ⟨SectionSpace.mul f a k k' s.1 t.1, hmem⟩

/-- `Γ^{𝓕,lk}_τ ≥ l Γ^{𝓕,k}_τ`. -/
theorem coe_mul_le_sectionPotential_mul (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (τ : ℝ)
    (x : SchemeComplexPoint f) (α : ℝ) (hα : F.sectionPotential H k τ x = α) :
    (((l : ℝ) * α : ℝ) : EReal) ≤ F.sectionPotential H (l * k) τ x := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have h := EReal.superadditive_iterate (a := fun j => F.sectionPotential H j τ x)
    (fun m j _ _ => F.sectionPotential_add_le H m j τ x) hk hα hk l'
  have hidx : l' * k + k = (l' + 1) * k := by ring
  rw [hidx, hα, ← EReal.coe_add] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  push_cast
  ring

/-- `k⁻¹Γ^{𝓕,k}_τ ≤ (lk)⁻¹Γ^{𝓕,lk}_τ`. -/
theorem normalizedPotential_le_mul (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (τ : ℝ)
    (x : SchemeComplexPoint f) :
    F.normalizedPotential H k τ x ≤ F.normalizedPotential H (l * k) τ x := by
  unfold normalizedPotential
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  by_cases hbot : F.sectionPotential H k τ x = ⊥
  · rw [hbot, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _)]
    exact bot_le
  · have htop : F.sectionPotential H k τ x ≠ ⊤ :=
      ne_top_of_le_ne_top EReal.zero_ne_top (F.sectionPotential_le_zero H k τ x)
    have hα : F.sectionPotential H k τ x = ((F.sectionPotential H k τ x).toReal : EReal) :=
      (EReal.coe_toReal htop hbot).symm
    have h := F.coe_mul_le_sectionPotential_mul H k l hk hl τ x _ hα
    have hlk : (0 : ℝ) ≤ ((l * k : ℕ) : ℝ) := Nat.cast_nonneg _
    calc F.sectionPotential H k τ x / ((k : ℝ) : EReal)
        = ((((l : ℝ) * (F.sectionPotential H k τ x).toReal : ℝ) : EReal)) /
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
    (hp : 0 < p) (hpq : p < q) (τ₀ τ₁ : ℝ) (x : SchemeComplexPoint f) (α₀ α₁ : ℝ)
    (h₀ : F.sectionPotential H k₀ τ₀ x = α₀) (h₁ : F.sectionPotential H k₁ τ₁ x = α₁) :
    (((1 - (p : ℝ) / q) * (α₀ / k₀) + (p : ℝ) / q * (α₁ / k₁) : ℝ) : EReal) ≤
      F.rawObstacle H ((p : ℝ) / q * τ₁ + (1 - (p : ℝ) / q) * τ₀) x := by
  have hA : 0 < k₁ * (q - p) := Nat.mul_pos hk₁ (by omega)
  have hB : 0 < k₀ * p := Nat.mul_pos hk₀ hp
  have hle0 := F.coe_mul_le_sectionPotential_mul H k₀ (k₁ * (q - p)) hk₀ hA τ₀ x α₀ h₀
  have hle1 := F.coe_mul_le_sectionPotential_mul H k₁ (k₀ * p) hk₁ hB τ₁ x α₁ h₁
  have hKpos : 0 < k₁ * (q - p) * k₀ + k₀ * p * k₁ := by positivity
  have hj := F.sectionPotential_add_le_mix H (k₁ * (q - p) * k₀) (k₀ * p * k₁) hKpos τ₀ τ₁ x
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
  refine le_trans ?_ (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential H k
    ((p : ℝ) / q * τ₁ + (1 - (p : ℝ) / q) * τ₀) x) _ hKpos)
  unfold normalizedPotential
  have hsum : ((((k₁ * (q - p) : ℕ) : ℝ) * α₀ + ((k₀ * p : ℕ) : ℝ) * α₁ : ℝ) : EReal) ≤
      F.sectionPotential H (k₁ * (q - p) * k₀ + k₀ * p * k₁)
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

omit [IsIntegral X] in
/-- From `r < sup_{k>0} k⁻¹Γ^{𝓕,k}_τ(x)` extract a degree with a finite value above `r`. -/
private theorem exists_degree_of_lt_rawObstacle {τ : ℝ} {x : SchemeComplexPoint f} {r : ℝ}
    (h : (r : EReal) < F.rawObstacle H τ x) :
    ∃ k : ℕ, 0 < k ∧ ∃ α : ℝ, F.sectionPotential H k τ x = α ∧ r < α / k := by
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp h
  obtain ⟨hk0, hkr⟩ := lt_iSup_iff.mp hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  unfold normalizedPotential at hkr
  have hbot : F.sectionPotential H k τ x ≠ ⊥ := by
    intro hb
    rw [hb, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _)] at hkr
    exact not_lt_bot hkr
  have htop : F.sectionPotential H k τ x ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (F.sectionPotential_le_zero H k τ x)
  refine ⟨k, hk0, (F.sectionPotential H k τ x).toReal, (EReal.coe_toReal htop hbot).symm, ?_⟩
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_div] at hkr
  exact EReal.coe_lt_coe_iff.mp hkr

/-- **Source `ex:RWN`, `eq:GammaFconctemp1`**: for `τ₀ < τ₁` and `t ∈ (0, 1)`,
`sup_k k⁻¹Γ^{𝓕,k}_{tτ₁+(1-t)τ₀} ≥ t sup_k k⁻¹Γ^{𝓕,k}_{τ₁} + (1-t) sup_k k⁻¹Γ^{𝓕,k}_{τ₀}`
pointwise. -/
theorem rawObstacle_concave {τ₀ τ₁ : ℝ} (hτ : τ₀ < τ₁) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x : SchemeComplexPoint f) :
    ThetaPshConvexCombination.convexComb t (F.rawObstacle H τ₁) (F.rawObstacle H τ₀) x ≤
      F.rawObstacle H (t * τ₁ + (1 - t) * τ₀) x := by
  rw [ThetaPshConvexCombination.convexComb_apply]
  have h1t : (0 : ℝ) < 1 - t := by linarith
  induction h1 : F.rawObstacle H τ₁ x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]; exact bot_le
  | top => exact absurd (h1 ▸ F.rawObstacle_le_zero H τ₁ x) (not_le.mpr EReal.zero_lt_top)
  | coe r₁ =>
  induction h0 : F.rawObstacle H τ₀ x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos h1t, EReal.add_bot]; exact bot_le
  | top => exact absurd (h0 ▸ F.rawObstacle_le_zero H τ₀ x) (not_le.mpr EReal.zero_lt_top)
  | coe r₀ =>
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  refine coe_le_of_forall_sub_le fun ε hε => ?_
  set δ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨k₁, hk₁, α₁, hα₁, hr₁⟩ := F.exists_degree_of_lt_rawObstacle H
    (r := r₁ - δ) (by rw [h1]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨k₀, hk₀, α₀, hα₀, hr₀⟩ := F.exists_degree_of_lt_rawObstacle H
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
  have hrat := F.le_rawObstacle_of_rat H k₀ k₁ hk₀ hk₁ p q hp0 hpq τ₀ τ₁ x α₀ α₁ hα₀ hα₁
  rw [← hwpq] at hrat
  -- monotonicity in the level
  have hlevel : t * τ₁ + (1 - t) * τ₀ ≤ (w : ℝ) * τ₁ + (1 - (w : ℝ)) * τ₀ := by
    nlinarith
  have hanti := F.rawObstacle_anti H hlevel x
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
    (fun i j _ _ => F.jump_add_le i j) hm0 hβ hm0 l'
  have hidx : l' * m + m = (l' + 1) * m := by ring
  rw [hidx, hβ, ← EReal.coe_add] at h
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) h
  push_cast
  have : (0 : ℝ) ≤ l' := Nat.cast_nonneg l'
  nlinarith

/-- For `τ < τ(𝓕)`: the normalized potentials along the degrees `(j+1)! m` form an increasing
sequence of `θ`-psh functions whose supremum is `sup_{k>0} k⁻¹Γ^{𝓕,k}_τ`. -/
theorem exists_increasing_sequence {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    ∃ g : ℕ → SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        ∀ j, IsThetaPshPotential (H.curvature a).val (g j)) ∧
      (∀ j x, g j x ≤ ((0 : ℝ) : EReal)) ∧ Monotone g ∧ (⨆ j, g j) = F.rawObstacle H τ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨m, hm0, hjump⟩ := F.exists_degree_jump_of_lt_slope hτ
  let kseq : ℕ → ℕ := fun j => (j + 1).factorial * m
  have hkpos : ∀ j, 0 < kseq j := fun j => Nat.mul_pos (Nat.factorial_pos _) hm0
  refine ⟨fun j => F.normalizedPotential H (kseq j) τ, fun j => ?_, fun j x => ?_, ?_, ?_⟩
  · have hkR : (0 : ℝ) < kseq j := by exact_mod_cast hkpos j
    have hpsh := F.isThetaPshPotential_sectionPotential H (k := kseq j) (τ := τ)
      (hjump _ (Nat.factorial_pos _))
    have h := RestrictedApproximantComparison.isThetaPshPotential_smul hpsh (inv_pos.mpr hkR)
    simp only [smul_smul, inv_mul_cancel₀ hkR.ne', one_smul] at h
    convert h using 1
    funext x
    change F.sectionPotential H (kseq j) τ x / (((kseq j : ℕ) : ℝ) : EReal) = _
    rw [div_eq_mul_inv, mul_comm, ← EReal.coe_inv]
  · rw [EReal.coe_zero]
    exact F.normalizedPotential_le_zero H _ τ x
  · refine monotone_nat_of_le_succ fun j x => ?_
    have hidx : kseq (j + 1) = (j + 2) * kseq j := by
      simp only [kseq, Nat.factorial_succ (j + 1)]
      ring
    change F.normalizedPotential H (kseq j) τ x ≤ F.normalizedPotential H (kseq (j + 1)) τ x
    rw [hidx]
    exact F.normalizedPotential_le_mul H _ _ (hkpos j) (by omega) τ x
  · funext x
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun j => le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential H k τ x)
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
      refine le_trans ?_ (le_iSup (fun j => F.normalizedPotential H (kseq j) τ x) k)
      rw [hidx]
      exact F.normalizedPotential_le_mul H k (c * m) hk (Nat.mul_pos hc0 hm0) τ x

/-- **Source `ex:RWN`**: for `τ < τ(𝓕)` the obstacle `usc sup_k k⁻¹Γ^{𝓕,k}_τ` is in
`PSH(X, θ)`. -/
theorem obstacle_isThetaPshPotential {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential (H.curvature a).val (F.obstacle H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨g, hg, hg0, -, hsup⟩ := F.exists_increasing_sequence H hτ
  have h := SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup hg hg0
  have hfun : (fun x => ⨆ j, g j x) = F.rawObstacle H τ := by
    rw [← hsup]
    funext x
    rw [iSup_apply]
  rw [hfun] at h
  exact h

/-- For `τ < τ(𝓕)`, the obstacle equals the unregularized supremum almost everywhere in every
holomorphic chart. -/
theorem ae_rawObstacle_eq_obstacle {τ : ℝ} (hτ : (τ : EReal) < F.slope)
    (e : ComplexChart n (SchemeComplexPoint f)) :
    ∀ᵐ z ∂((MeasureTheory.volume : Measure (ComplexModel n)).restrict e.val.target),
      F.rawObstacle H τ (e.val.symm z) = F.obstacle H τ (e.val.symm z) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨g, hg, hg0, hmono, hsup⟩ := F.exists_increasing_sequence H hτ
  have heq : uscRegularization (⨆ j, g j) = F.obstacle H τ := by
    rw [hsup]
    rfl
  have hae := RooftopEnvelopeAeObstacle.ae_chartFunction_iSup_eq_of_le_const
    (theta := H.curvature a) hg hg0 hmono heq e
  filter_upwards [hae] with z hz
  have h1 : F.rawObstacle H τ (e.val.symm z) = ⨆ j, chartFunction (g j) e z := by
    rw [← hsup, iSup_apply]
    rfl
  rw [h1, hz]
  rfl

/-- **Source `ex:RWN`, concavity of the obstacle**: for `τ₀ < τ₁ < τ(𝓕)` and `t ∈ (0, 1)`,
`usc sup_k k⁻¹Γ^{𝓕,k}_{tτ₁+(1-t)τ₀} ≥ t · usc sup_k k⁻¹Γ^{𝓕,k}_{τ₁} +
(1-t) · usc sup_k k⁻¹Γ^{𝓕,k}_{τ₀}`. -/
theorem obstacle_concave {τ₀ τ₁ : ℝ} (hτ : τ₀ < τ₁) (hτ₁ : (τ₁ : EReal) < F.slope) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t (F.obstacle H τ₁) (F.obstacle H τ₀) ≤
      F.obstacle H (t * τ₁ + (1 - t) * τ₀) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hτ₀ : (τ₀ : EReal) < F.slope := lt_trans (EReal.coe_lt_coe_iff.mpr hτ) hτ₁
  have hτt : ((t * τ₁ + (1 - t) * τ₀ : ℝ) : EReal) < F.slope :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by nlinarith)) hτ₁
  have hL := ThetaPshConvexCombination.isThetaPshPotential_convexComb
    (F.obstacle_isThetaPshPotential H hτ₁) (F.obstacle_isThetaPshPotential H hτ₀) ht0 ht1
  have hR := F.obstacle_isThetaPshPotential H hτt
  refine RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hL.1 hR.1
    fun e => ?_
  filter_upwards [F.ae_rawObstacle_eq_obstacle H hτ₁ e, F.ae_rawObstacle_eq_obstacle H hτ₀ e]
    with z h₁ h₀
  rw [ThetaPshConvexCombination.convexComb_apply, ← h₁, ← h₀,
    ← ThetaPshConvexCombination.convexComb_apply]
  exact (F.rawObstacle_concave H hτ ht0 ht1 _).trans (le_uscRegularization _ _)

/-- **Source `ex:RWN`**: `Γ^𝓕_τ ∈ PSH(X, θ)` for `τ < τ(𝓕)`. -/
theorem testCurvePotential_isThetaPshPotential [Nonempty (SchemeComplexPoint f)] {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential (H.curvature a).val (F.testCurvePotential H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact Pending.singularityEnvelope_isThetaPshPotential (H.curvature a).val
    (H.curvature a).property.1 (H.curvature a).property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) _
    (F.obstacle_isThetaPshPotential H hτ)

omit [IsIntegral X] in
theorem obstacle_le_zero (τ : ℝ) : F.obstacle H τ ≤ 0 :=
  uscRegularization_le upperSemicontinuous_const fun x => F.rawObstacle_le_zero H τ x

/-- For `τ < τ(𝓕)` the obstacle is a competitor of its own envelope. -/
theorem obstacle_mem_singularityCompetitors {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    F.obstacle H τ ∈ singularityCompetitors (H.curvature a).val (F.obstacle H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  refine ⟨⟨F.obstacle_isThetaPshPotential H hτ, F.obstacle_le_zero H τ⟩, 0, fun x _ => ?_⟩
  rw [EReal.coe_zero, add_zero]

/-- **Source `ex:RWN`, concavity of the test curve**: for `τ₀ < τ₁ < τ(𝓕)` and `t ∈ (0, 1)`,
`Γ^𝓕_{tτ₁+(1-t)τ₀} ≥ t Γ^𝓕_{τ₁} + (1-t) Γ^𝓕_{τ₀}` (concavity of the obstacle and of
`P_θ[·]`). -/
theorem testCurvePotential_concave [Nonempty (SchemeComplexPoint f)] {τ₀ τ₁ : ℝ}
    (hτ : τ₀ < τ₁) (hτ₁ : (τ₁ : EReal) < F.slope) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t (F.testCurvePotential H τ₁)
        (F.testCurvePotential H τ₀) ≤
      F.testCurvePotential H (t * τ₁ + (1 - t) * τ₀) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hτ₀ : (τ₀ : EReal) < F.slope := lt_trans (EReal.coe_lt_coe_iff.mpr hτ) hτ₁
  have hτt : ((t * τ₁ + (1 - t) * τ₀ : ℝ) : EReal) < F.slope :=
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by nlinarith)) hτ₁
  exact SGPT.PSH.Misc2EnvelopeConcave.convexComb_singularityEnvelope_le (H.curvature a)
    ⟨_, F.obstacle_mem_singularityCompetitors H hτ₀⟩
    ⟨_, F.obstacle_mem_singularityCompetitors H hτ₁⟩
    (F.testCurvePotential_isThetaPshPotential H hτ₀)
    (F.testCurvePotential_isThetaPshPotential H hτ₁)
    (F.testCurvePotential_isThetaPshPotential H hτt) ht0 ht1
    (F.obstacle_concave H hτ hτ₁ ht0 ht1)

end SectionFiltration

end SGPT.LineBundle
