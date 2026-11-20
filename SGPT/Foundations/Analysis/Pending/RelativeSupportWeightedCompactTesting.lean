import SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCurrentPullback

set_option autoImplicit false

/-! # Actual compact testing on the smaller relative support

The mathematical statement and complete proof preceded this source.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCompactTesting

open FirstPass LocalProductCurrents LocalCurrentPullback BedfordTaylor
  RelativeSupportWeightedCurrentPullback

variable {n q : ℕ} {A B V : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

/-- Every larger-domain compact test internally gives the actual weighted overlap test. -/
theorem exists_weighted_test (h : IsBiholomorphicPair A B τ σ)
    {T : LocalProductCurrent n B q} (hT : IsPositive T) (hAV : A ≤ V)
    (χ : ComplexModel n → ℝ) (hχ : ContDiffOn ℝ ∞ χ V)
    (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A) (φ : 𝓓(V, ℝ)) :
    ∃ ψ : 𝓓(A, ℝ), (∀ x, ψ x = φ x * χ x) ∧ ∀ γ : formSpan n q,
      weightedExtendedPullback h hT hAV χ hχ.continuousOn hsupp γ φ =
        pullback h hT γ ψ := by
  let ψ : 𝓓(A, ℝ) :=
    { toFun := fun x => φ x * χ x
      contDiff' := contDiff_mul_of_tsupport_subset V.isOpen φ.contDiff
        φ.tsupport_subset hχ
      hasCompactSupport' := φ.hasCompactSupport.mul_right
      tsupport_subset' := fun x hx => hsupp
        ⟨tsupport_mul_subset_right hx, φ.tsupport_subset (tsupport_mul_subset_left hx)⟩ }
  refine ⟨ψ, fun _ => rfl, ?_⟩
  intro γ
  change regularDistribution (pbMeasure σ hT)
    (fun x => χ x * pbDensity A τ σ hT γ x)
    (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ.continuousOn hsupp γ) φ = _
  rw [regularDistribution_apply, pullback_apply_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change φ x * (χ x * pbDensity A τ σ hT γ x) =
      (φ x * χ x) * pbDensity A τ σ hT γ x
    ring

end SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCompactTesting
