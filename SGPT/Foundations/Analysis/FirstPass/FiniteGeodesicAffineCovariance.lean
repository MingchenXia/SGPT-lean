import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesics
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicAffineTranslation

set_option autoImplicit false

/-!
# Affine covariance of Perron finite geodesics

Vertical translation by `A t + B` gives a bijection between the two Perron
competitor families.  The proof uses the least-USC-majorant characterization
of the Perron envelope, avoiding a separate extended-real `sSup` translation
API.
-/

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Affine translation sends every Perron competitor to the correspondingly
translated endpoint problem. -/
theorem affineTranslatedCurve_mem_finiteGeodesicCompetitors
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal}
    (hcurve : curve ∈ finiteGeodesicCompetitors θ u₀ u₁) (A B : ℝ) :
    affineTranslatedCurve curve A B ∈
      finiteGeodesicCompetitors θ
        (fun x => u₀ x + (B : EReal))
        (fun x => u₁ x + ((A + B : ℝ) : EReal)) := by
  rcases hcurve with ⟨v₀, v₁, hv₀, hv₁, hv₀u₀, hv₁u₁, hcurve⟩
  refine ⟨fun x => v₀ x + (B : EReal),
    fun x => v₁ x + ((A + B : ℝ) : EReal),
    hv₀.add_const B, hv₁.add_const (A + B), ?_, ?_,
    hcurve.affineTranslated A B⟩
  · intro x
    exact (EReal.addLECancellable_coe B).add_le_add_iff_right.mpr (hv₀u₀ x)
  · intro x
    exact (EReal.addLECancellable_coe (A + B)).add_le_add_iff_right.mpr
      (hv₁u₁ x)

/-- Affine translation is a bijection of the original and translated Perron
competitor families. -/
theorem affineTranslatedCurve_mem_finiteGeodesicCompetitors_iff
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (A B : ℝ) :
    affineTranslatedCurve curve A B ∈
        finiteGeodesicCompetitors θ
          (fun x => u₀ x + (B : EReal))
          (fun x => u₁ x + ((A + B : ℝ) : EReal)) ↔
      curve ∈ finiteGeodesicCompetitors θ u₀ u₁ := by
  constructor
  · intro hcurve
    have hinv := affineTranslatedCurve_mem_finiteGeodesicCompetitors
      hcurve (-A) (-B)
    have h₀ : (fun x => (u₀ x + (B : EReal)) + ((-B : ℝ) : EReal)) = u₀ := by
      funext x
      rw [add_assoc, ← EReal.coe_add]
      simp
    have h₁ : (fun x =>
        (u₁ x + ((A + B : ℝ) : EReal)) +
          (((-A) + (-B) : ℝ) : EReal)) = u₁ := by
      funext x
      rw [add_assoc, ← EReal.coe_add]
      have hsum : (A + B) + ((-A) + (-B)) = 0 := by ring
      rw [hsum, EReal.coe_zero, add_zero]
    rw [affineTranslatedCurve_inverse, h₀, h₁] at hinv
    exact hinv
  · exact fun hcurve =>
      affineTranslatedCurve_mem_finiteGeodesicCompetitors hcurve A B

/-- The Perron finite geodesic is equivariant under affine translation of
its endpoint data. -/
theorem finiteGeodesic_affineCovariance
    (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal) (A B t : ℝ) :
    finiteGeodesic θ
        (fun x => u₀ x + (B : EReal))
        (fun x => u₁ x + ((A + B : ℝ) : EReal)) t =
      fun x => finiteGeodesic θ u₀ u₁ t x +
        ((A * t + B : ℝ) : EReal) := by
  apply le_antisymm
  · apply (finiteGeodesic_le_iff
      (upperSemicontinuous_add_coe_const
        (upperSemicontinuous_finiteGeodesic θ u₀ u₁ t) (A * t + B))).2
    intro curve hcurve x
    have hinv : affineTranslatedCurve curve (-A) (-B) ∈
        finiteGeodesicCompetitors θ u₀ u₁ := by
      apply (affineTranslatedCurve_mem_finiteGeodesicCompetitors_iff
        (θ := θ) (u₀ := u₀) (u₁ := u₁)
        (curve := affineTranslatedCurve curve (-A) (-B)) A B).mp
      simpa using hcurve
    have hs := competitor_slice_le_finiteGeodesic hinv t x
    have hadd :=
      (EReal.addLECancellable_coe (A * t + B)).add_le_add_iff_right.mpr hs
    have hadd' :
        affineTranslatedCurve
            (affineTranslatedCurve curve (-A) (-B)) A B t x ≤
          finiteGeodesic θ u₀ u₁ t x + ((A * t + B : ℝ) : EReal) := by
      simpa only [affineTranslatedCurve_apply] using hadd
    rw [affineTranslatedCurve_inverse_left] at hadd'
    exact hadd'
  · have hminus : UpperSemicontinuous (fun x =>
        finiteGeodesic θ
            (fun y => u₀ y + (B : EReal))
            (fun y => u₁ y + ((A + B : ℝ) : EReal)) t x +
          ((-(A * t + B) : ℝ) : EReal)) :=
      upperSemicontinuous_add_coe_const
        (upperSemicontinuous_finiteGeodesic θ
          (fun y => u₀ y + (B : EReal))
          (fun y => u₁ y + ((A + B : ℝ) : EReal)) t)
        (-(A * t + B))
    have hbase : finiteGeodesic θ u₀ u₁ t ≤ fun x =>
        finiteGeodesic θ
            (fun y => u₀ y + (B : EReal))
            (fun y => u₁ y + ((A + B : ℝ) : EReal)) t x +
          ((-(A * t + B) : ℝ) : EReal) := by
      apply (finiteGeodesic_le_iff hminus).2
      intro curve hcurve x
      have htranslated :=
        affineTranslatedCurve_mem_finiteGeodesicCompetitors hcurve A B
      have hs := competitor_slice_le_finiteGeodesic htranslated t x
      have hneg : (-A) * t + (-B) = -(A * t + B) := by ring
      have hadd :=
        (EReal.addLECancellable_coe ((-A) * t + (-B))).add_le_add_iff_right.mpr hs
      have hadd' :
          affineTranslatedCurve (affineTranslatedCurve curve A B) (-A) (-B)
              t x ≤
            finiteGeodesic θ
                (fun y => u₀ y + (B : EReal))
                (fun y => u₁ y + ((A + B : ℝ) : EReal)) t x +
              ((-(A * t + B) : ℝ) : EReal) := by
        simpa only [affineTranslatedCurve_apply, hneg] using hadd
      rw [affineTranslatedCurve_inverse] at hadd'
      exact hadd'
    intro x
    have hadd :=
      (EReal.addLECancellable_coe (A * t + B)).add_le_add_iff_right.mpr
        (hbase x)
    simpa [add_assoc, ← EReal.coe_add] using hadd

end

end SGPT.Foundations.Analysis.FirstPass
