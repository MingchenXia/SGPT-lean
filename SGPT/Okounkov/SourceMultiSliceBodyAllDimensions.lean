import SGPT.Okounkov.SourceMultiSliceOriginalAnalytic

/-! Literal original source-body algebra in all dimensions, retaining the
genuine zero-source construction rather than substituting an abstract carrier. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set Filter
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody

/-- The actual zero-source body, with its original approximation and
perturbation intersections, has the full original zero-dimensional carrier. -/
theorem sourceBody_zero_eq_univ (F : OriginalFlagGeometry.{u} 0)
    (θ : ClosedRealOneOneForm 0 F.carrier) {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩ = Set.univ := by
  change ZeroSource.generalBody F θ φ hφ = Set.univ
  rw [ZeroSource.generalBody_eq_partial, ZeroSource.partialOkounkovBody_eq_univ F hφ]

/-- Actual ideal-order monotonicity of the original source body in all n,
including the literal genuine zero-source branch. -/
theorem sourceBody_mono_of_iOrder {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {φ ψ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (hI : IOrderOnManifold (n := n) φ ψ) :
    SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩ ⊆
      SourceTestCurveAllDimensions.generalBody F θ ⟨ψ,hψ⟩ := by
  cases n with
  | zero =>
      simpa only [sourceBody_zero_eq_univ] using
        (Set.Subset.refl (Set.univ : Set (Fin 0 → ℝ)))
  | succ n => exact Valuative.generalPartialBody_mono_of_iOrder hφ hψ hI

/-- The exact same original Kähler-QEA stages give the original source body
intersection, including the genuine zero-dimensional source construction. -/
theorem sourceBody_eq_iInter_kahlerQEA {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U) :
    SourceTestCurveAllDimensions.generalBody F θ
      ⟨φ,isThetaPshPotential_of_isKahlerCurrentPotential hK⟩ =
      ⋂ j, SourceTestCurveAllDimensions.generalBody F θ ⟨U j,(hU.2 j).1.1⟩ := by
  cases n with
  | zero => simp only [sourceBody_zero_eq_univ, iInter_univ]
  | succ n =>
      change generalPartialBody F θ φ = ⋂ j, generalPartialBody F θ (U j)
      rw [generalPartialBody_eq_kahlerPartialBody hK, kahlerPartialBody_eq_iInter hU]
      apply iInter_congr
      intro j
      exact ((generalPartialBody_eq_analyticPartialBody (hU.2 j).1 (hU.2 j).2).trans
        (TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody (hU.2 j).1 (hU.2 j).2)).symm

/-- The same original potential's genuine positive Kähler perturbations
recover its original source body in every dimension and reference form. -/
theorem sourceBody_eq_iInter_general_add_kahler {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (omegaRef : KahlerBackground n F.carrier) :
    SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩ = ⋂ j : ℕ,
      SourceTestCurveAllDimensions.generalBody F (θ + ((j : ℝ) + 1)⁻¹ • omegaRef.form)
        ⟨φ,isThetaPshPotential_of_isKahlerCurrentPotential
          (isKahlerCurrentPotential_add_smul hφ omegaRef (by positivity))⟩ := by
  cases n with
  | zero => simp only [sourceBody_zero_eq_univ, iInter_univ]
  | succ n => exact SourceSlice.generalPartialBody_eq_iInter_general_add_kahler F hφ omegaRef
end SGPT.Okounkov.SourceMultiSlice
