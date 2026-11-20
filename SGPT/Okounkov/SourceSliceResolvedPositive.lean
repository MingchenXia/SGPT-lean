import SGPT.Okounkov.SourceSliceResolvedAnalytic

/-! Exact Kähler perturbation removes the Kähler hypothesis from the
actual resolved analytic slice, retaining the original potential/divisor. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Matrix
open scoped Pointwise Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.PartialBody
open SGPT.PSH
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalSlice SGPT.Okounkov.TranscendentalWN

/-- The actual zero-coordinate preimage commutes with every intersection. -/
theorem firstCoordinateSlice_iInter {m : ℕ} {ι : Sort*}
    (B : ι → Set (Fin (m + 1) → ℝ)) (t : ℝ) :
    firstCoordinateSlice (⋂ i, B i) t = ⋂ i, firstCoordinateSlice (B i) t := by
  ext y
  simp only [firstCoordinateSlice, mem_ofPred_eq, mem_iInter]

/-- The same current's general body is the intersection of the general
bodies of its actual positive Kähler perturbations, for any original Kähler form. -/
theorem generalPartialBody_eq_iInter_general_add_kahler
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (ω : KahlerBackground (m + 1) F.carrier) :
    generalPartialBody F θ φ = ⋂ j : ℕ,
      generalPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • ω.form) φ := by
  rw [generalPartialBody_eq_of_kahler hφ ω]
  congr 1
  funext j
  exact (generalPartialBody_eq_kahlerPartialBody
    (isKahlerCurrentPotential_add_smul hφ ω (by positivity))).symm

/-- Actual resolved positive analytic current: no Kähler hypothesis on this
original current or its modification pullback is needed. -/
theorem slice_zero_of_actual_positive_resolved_decomposition
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ b : F.carrier → EReal}
    (hφA : φ ∈ globalAnalyticCurrents θ)
    (D : MeteredEffectiveQDivisor (m + 2) F.carrier)
    (hb : IsThetaPshPotential (θ - D.curvature).val b)
    (hbounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal))
    (heq : ∀ y, φ y = D.weight y + b y)
    (hnd : LocallyNondegenerate (fun y : F.tail.carrier => φ y.val)) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ)
        (fun y : F.tail.carrier => φ y.val) := by
  have hφr : IsThetaPshPotential (firstFlagRestriction F θ).val
      (fun y : F.tail.carrier => φ y.val) :=
    TranscendentalVolId.isThetaPshPotential_restrict
      (F := F) hφA.1.1 hnd (singularityLE_refl _)
  rw [generalPartialBody_eq_iInter_general_add_kahler F hφA.1 F.omega,
    firstCoordinateSlice_iInter,
    generalPartialBody_eq_iInter_general_add_kahler F.tail hφr
      (restrictedKahlerForm F.omega)]
  congr 1
  funext j
  have he : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  have hK := isKahlerCurrentPotential_add_smul hφA.1 F.omega he
  have hA : φ ∈ globalAnalyticCurrents (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) :=
    ⟨isThetaPshPotential_of_isKahlerCurrentPotential hK, hφA.2⟩
  have hbe := isKahlerCurrentPotential_add_smul hb F.omega he
  have hb' : IsThetaPshPotential
      (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form - D.curvature).val b := by
    have hform : θ + ((j : ℝ) + 1)⁻¹ • F.omega.form - D.curvature =
        (θ - D.curvature) + ((j : ℝ) + 1)⁻¹ • F.omega.form := by module
    rw [hform]
    exact isThetaPshPotential_of_isKahlerCurrentPotential hbe
  have h := slice_zero_of_actual_resolved_decomposition F hA hK D hb' hbounded heq hnd
  simpa only [Valuative.firstFlagRestriction_add_smul, restrictedKahlerForm_form] using h
end SGPT.Okounkov.SourceSlice
