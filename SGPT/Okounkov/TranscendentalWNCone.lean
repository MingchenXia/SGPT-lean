import SGPT.Okounkov.TranscendentalWNStatement
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound

/-!
# Openness of the cone of classes whose Kähler locus meets `Y₁`

Blueprint node `tok-wn:cone`, part (a) (chapter `claude-tok-wn`; Matsumura 2013,
Proposition 4.10, as cited by Collins--Tosatti before their Corollary 5.3): if `ξ` is big and
its Kähler locus `X \ E_nK(ξ)` meets `Y₁`, then so does `ξ + s{γ}` for every closed real smooth
`(1,1)`-form `γ` and all sufficiently small `|s|`.

Proof: let `T = θ + dd^c φ ≥ κ` be a Kähler current in `ξ` with Lelong number `0` at a point
`y ∈ Y₁`. If `A κ ± γ ≥ 0`, then for `|s| ≤ 1/(2A)` the form `κ/2 + sγ` is semipositive, so
`(θ + sγ) + dd^c φ ≥ κ/2` is a Kähler current in `ξ + s{γ}` with the same potential `φ`, hence
with Lelong number `0` at `y`.

## Main results

* `kahlerCurrentAddSmul`: the perturbed Kähler current `T + sγ`, with the same potential and
  lower bound `κ/2`;
* `exists_pos_isSemipositive_half_add_smul`: `κ/2 + sγ ≥ 0` for `|s| ≤ s₀`;
* `exists_isBigClass_add_smul_meeting` (**`tok-wn:cone` (a)** for any subset `Z`) and its
  flag form `isBigMeetingFirstDivisor_add_smul`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

section Perturbation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A Kähler current perturbed by a small smooth form.** If `T = θ + dd^c φ ≥ κ` is a Kähler
current in `α` and `κ/2 + sγ` is semipositive, then `(θ + sγ) + dd^c φ ≥ κ/2` is a Kähler
current in `α + s{γ}` with the same potential `φ`. -/
def kahlerCurrentAddSmul {α : RealBottChern n M} (T : KahlerCurrent α)
    (γ : ClosedRealOneOneForm n M) (s : ℝ)
    (hs : (((1 / 2 : ℝ)) • T.lowerBound.form + s • γ).val.IsSemipositive) :
    KahlerCurrent (α + s • RealBottChern.ofRepresentative γ) where
  representative := T.representative + s • γ
  represents := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
      T.represents]
  potential := T.potential
  lowerBound := KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) T.lowerBound
  strictlyPsh := by
    have hform : T.representative + s • γ -
        (KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) T.lowerBound).form =
        (T.representative - T.lowerBound.form) +
          (((1 / 2 : ℝ)) • T.lowerBound.form + s • γ) := by
      rw [KahlerBackground.smul_form]
      module
    rw [hform]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hs

@[simp] theorem kahlerCurrentAddSmul_potential {α : RealBottChern n M} (T : KahlerCurrent α)
    (γ : ClosedRealOneOneForm n M) (s : ℝ)
    (hs : (((1 / 2 : ℝ)) • T.lowerBound.form + s • γ).val.IsSemipositive) :
    (kahlerCurrentAddSmul T γ s hs).potential = T.potential :=
  rfl

/-- On a compact manifold, `κ/2 + sγ` is semipositive for all sufficiently small `|s|`. -/
theorem exists_pos_isSemipositive_half_add_smul [CompactSpace M] (κ : KahlerBackground n M)
    (γ : ClosedRealOneOneForm n M) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, |s| ≤ s₀ →
      (((1 / 2 : ℝ)) • κ.form + s • γ).val.IsSemipositive := by
  obtain ⟨A₁, hA₁, h₁⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ γ
  obtain ⟨A₂, hA₂, h₂⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-γ)
  have hκ := κ.isSemipositive
  refine ⟨1 / (2 * (A₁ + A₂)), by positivity, fun s hs => ?_⟩
  intro e z hz v
  have e₁ := h₁ e z hz v
  have e₂ := h₂ e z hz v
  have e₀ := hκ e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at e₁ e₂ ⊢
  set a := κ.form.val.coeff e z ![v, Complex.I • v] with ha
  set g := γ.val.coeff e z ![v, Complex.I • v] with hg
  have hsum : 0 < A₁ + A₂ := add_pos hA₁ hA₂
  have hsA : |s| * (2 * (A₁ + A₂)) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hs
    exact hs
  rcases le_or_gt 0 s with hs0 | hs0
  · rw [abs_of_nonneg hs0] at hsA
    nlinarith [mul_nonneg hs0 e₁, mul_nonneg hs0 e₀, mul_nonneg hA₂.le e₀]
  · rw [abs_of_neg hs0] at hsA
    nlinarith [mul_nonneg (neg_nonneg.mpr hs0.le) e₂, mul_nonneg (neg_nonneg.mpr hs0.le) e₀,
      mul_nonneg hA₁.le e₀]

/-- **`tok-wn:cone` (a)**, for an arbitrary subset `Z` of a compact complex manifold: if the
Kähler locus `X \ E_nK(ξ)` of `ξ` meets `Z`, then for every closed real smooth `(1,1)`-form
`γ` there is `s₀ > 0` such that, for `|s| ≤ s₀`, the class `ξ + s{γ}` is big and its Kähler
locus meets `Z` (witnessed by the same point). -/
theorem exists_isBigClass_add_smul_meeting [CompactSpace M] {ξ : RealBottChern n M}
    {Z : Set M} (hZ : ∃ y ∈ Z, y ∉ nonKahlerLocus ξ) (γ : ClosedRealOneOneForm n M) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, |s| ≤ s₀ →
      IsBigClass (ξ + s • RealBottChern.ofRepresentative γ) ∧
        ∃ y ∈ Z, y ∉ nonKahlerLocus (ξ + s • RealBottChern.ofRepresentative γ) := by
  obtain ⟨y, hy, hyK⟩ := hZ
  have hex : ∃ T : KahlerCurrent ξ, ¬ 0 < lelongNumber (n := n) T.potential y := by
    by_contra hcon
    exact hyK fun T => by_contra fun h => hcon ⟨T, h⟩
  obtain ⟨T, hT⟩ := hex
  obtain ⟨s₀, hs₀, hsemi⟩ := exists_pos_isSemipositive_half_add_smul T.lowerBound γ
  refine ⟨s₀, hs₀, fun s hs => ?_⟩
  let T' := kahlerCurrentAddSmul T γ s (hsemi s hs)
  refine ⟨⟨T'⟩, y, hy, ?_⟩
  intro hall
  exact hT (hall T')

end Perturbation

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn:cone` (a)** (Matsumura 2013, Proposition 4.10): if `ξ` is big and its Kähler locus
meets `Y₁`, then for every closed real smooth `(1,1)`-form `γ` there is `s₀ > 0` such that
`ξ + s{γ}` is big with Kähler locus meeting `Y₁` for all `|s| ≤ s₀`. -/
theorem isBigMeetingFirstDivisor_add_smul {ξ : RealBottChern (m + 1) F.carrier}
    (hξ : IsBigMeetingFirstDivisor F ξ) (γ : ClosedRealOneOneForm (m + 1) F.carrier) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, |s| ≤ s₀ →
      IsBigMeetingFirstDivisor F (ξ + s • RealBottChern.ofRepresentative γ) := by
  obtain ⟨s₀, hs₀, h⟩ := exists_isBigClass_add_smul_meeting hξ.2 γ
  exact ⟨s₀, hs₀, fun s hs => ⟨(SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr (h s hs).1,
    (h s hs).2⟩⟩

end SGPT.Okounkov.TranscendentalWN
