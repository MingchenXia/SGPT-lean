import SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCompactTesting
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

set_option autoImplicit false

/-! # Pullback on natural smaller biholomorphic domains

Both mathematical statements and entire proofs preceded this file.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalSubdomainCurrentPullback

open FirstPass BedfordTaylor LocalProductCurrents LocalBedfordTaylorLocality
  LocalCurrentPullback LocalCurrentPullbackDdc RelativeSupportWeightedCurrentPullback
  RelativeSupportWeightedCompactTesting

variable {n q : ℕ} {A A' B B' V : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

/-- The actual smaller biholomorphism internally determines the pullback restriction. -/
theorem pullback_on_subdomains (h : IsBiholomorphicPair A B τ σ)
    (h' : IsBiholomorphicPair A' B' τ σ) (hA'A : A' ≤ A) (hB'B : B' ≤ B)
    {T : LocalProductCurrent n B q} (hT : IsPositive T) :
    pullback h' (isPositive_restrict hT hB'B) = restrict hA'A (pullback h hT) := by
  have heq : preOpen h B' = A' := by
    ext x
    constructor
    · intro hx
      have hh := h'.mapsTo_inv hx.2
      rwa [h.left_inv x hx.1] at hh
    · intro hx
      exact ⟨hA'A hx, h'.mapsTo hx⟩
  subst A'
  exact pullback_restrict h hT hB'B

/-- An original larger test internally reads the actual smaller pullback. -/
theorem exists_weighted_test_on_subdomains (h : IsBiholomorphicPair A B τ σ)
    (h' : IsBiholomorphicPair A' B' τ σ) (hA'A : A' ≤ A) (hB'B : B' ≤ B)
    {T : LocalProductCurrent n B q} (hT : IsPositive T) (hAV : A ≤ V)
    (χ : ComplexModel n → ℝ) (hχ : ContDiffOn ℝ ∞ χ V)
    (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A') (φ : 𝓓(V, ℝ)) :
    ∃ ψ : 𝓓(A', ℝ), (∀ x, ψ x = φ x * χ x) ∧ ∀ γ : formSpan n q,
      weightedExtendedPullback h hT hAV χ hχ.continuousOn
        (fun _ hx => hA'A (hsupp hx)) γ φ =
      pullback h' (isPositive_restrict hT hB'B) γ ψ := by
  obtain ⟨η, hη, hread⟩ := exists_weighted_test h hT hAV χ hχ
    (fun _ hx => hA'A (hsupp hx)) φ
  have hfunc : (η : ComplexModel n → ℝ) = fun x => φ x * χ x := funext hη
  let ψ : 𝓓(A', ℝ) :=
    { toFun := η
      contDiff' := η.contDiff
      hasCompactSupport' := η.hasCompactSupport
      tsupport_subset' := fun x hx => by
        rw [hfunc] at hx
        exact hsupp
          ⟨tsupport_mul_subset_right hx, φ.tsupport_subset (tsupport_mul_subset_left hx)⟩ }
  have hext : extTest hA'A ψ = η := by
    ext x
    rw [extTest_apply]
    rfl
  refine ⟨ψ, hη, ?_⟩
  intro γ
  rw [pullback_on_subdomains h h' hA'A hB'B hT,
    LocalBedfordTaylorLocality.restrict_apply, hext]
  exact hread γ

end SGPT.Foundations.Analysis.Pending.NaturalSubdomainCurrentPullback
