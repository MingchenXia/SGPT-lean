import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound

set_option autoImplicit false

/-! # Actual uniform upper bounds for the singular Perron strip, retaining poles -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPerronUpperBound

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual nonnegative endpoint chords give the entire Perron strip the same actual endpoint upper bound. -/
theorem finiteGeodesic_le_const_of_endpoints_le
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {B : ℝ} (hB₀ : ∀ x, u₀ x ≤ (B : EReal)) (hB₁ : ∀ x, u₁ x ≤ (B : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    finiteGeodesic θ u₀ u₁ t x ≤ (B : EReal) := by
  calc
    finiteGeodesic θ u₀ u₁ t x ≤ eRealChord (u₀ x) (u₁ x) t :=
      finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
    _ ≤ eRealChord (B : EReal) (B : EReal) t :=
      eRealChord_mono (hB₀ x) (hB₁ x) ht.1.le ht.2.le
    _ = (B : EReal) := by
      simp only [eRealChord, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

/-- Actual compact theta-PSH endpoints internally produce one real upper bound for all actual interior Perron slices, including empty manifolds. -/
theorem exists_finiteGeodesic_uniform_upper_bound
    [CompactSpace M] {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) :
    ∃ B : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, finiteGeodesic θ u₀ u₁ t x ≤ (B : EReal) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let : IsEmpty M := hM
    exact ⟨0, fun _ _ x => isEmptyElim x⟩
  · let : Nonempty M := hM
    obtain ⟨B₀, hB₀⟩ := hu₀.exists_global_upper_bound
    obtain ⟨B₁, hB₁⟩ := hu₁.exists_global_upper_bound
    refine ⟨max B₀ B₁, fun _ ht x => ?_⟩
    exact finiteGeodesic_le_const_of_endpoints_le hu₀ hu₁
      (fun y => (hB₀ y).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
      (fun y => (hB₁ y).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))) ht x

end

end SGPT.Foundations.Analysis.Pending.SingularPerronUpperBound
