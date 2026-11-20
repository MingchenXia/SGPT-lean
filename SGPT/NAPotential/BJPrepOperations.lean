import SGPT.NAPotential.BJPrepDivisorialTransform
import SGPT.PSH.SourceNATranslation

/-!
# Translation of non-Archimedean metrics on divisorial values

One of the operations in `thm:NApotential:L1352` (`chapter_NApotential.tex`): translation
`Γ ↦ Γ + c` of `PSH^NA(X, θ)` (`def:NApotential:L341`) corresponds to `φ ↦ φ + c` on
`PSH(L^An)`.  On the divisorial values in Lelong-number form (`naDivisorialTransform`) this is
`(Γ + c)^An(t ord_E) = Γ^An(t ord_E) + c`.  (Together with `naDivisorialTransform_decreasingInf`
for the infimum; the remaining operations and the passage to `X^An` are open.)
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJPrep

universe u

open Set
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem ereal_add_neg_add (x : EReal) (c : ℝ) :
    x + ((-c : ℝ) : EReal) + (c : EReal) = x := by
  rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

/-- Translating a test curve by `c` translates its divisorial transform by `c`. -/
theorem curveDivisorialTransform_translate [MeasurableSpace M] [CompactSpace M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (C : SourceTestCurve θ) (c : ℝ)
    (p : PrimePresentation n M) (t : ℝ) :
    curveDivisorialTransform (C.translate c).toSourceTestCurvePredata p t =
      curveDivisorialTransform C.toSourceTestCurvePredata p t + (c : EReal) := by
  have hmax : (C.translate c).max = C.max + c := C.translate_max c
  -- slice Lelong numbers of the translate
  have hslice : ∀ (τ : ℝ) (h : τ < (C.translate c).max),
      presentationReader ((C.translate c).potential ⟨τ, h⟩) p =
        presentationReader (C.potential ⟨τ - c, by rw [hmax] at h; show τ - c < C.max; linarith⟩) p := by
    intro τ h
    rfl
  apply le_antisymm
  · refine iSup₂_le fun τ h => ?_
    have h' : τ - c < C.max := by rw [hmax] at h; linarith
    rw [hslice τ h]
    have hle := le_curveDivisorialTransform C.toSourceTestCurvePredata p t h'
    rw [curveDivisorialTransform_term C.toSourceTestCurvePredata p t h'] at hle
    have hx := coe_sliceLelong C.toSourceTestCurvePredata p h'
    rw [← hx, EReal.coe_ennreal_ofReal, max_eq_left (sliceLelong_nonneg _ p _),
      ← EReal.coe_mul, ← EReal.coe_sub]
    calc (((τ - t * sliceLelong C.toSourceTestCurvePredata p (τ - c)) : ℝ) : EReal)
        = ((τ - c - t * sliceLelong C.toSourceTestCurvePredata p (τ - c) : ℝ) : EReal) +
            (c : EReal) := by rw [← EReal.coe_add]; ring_nf
      _ ≤ curveDivisorialTransform C.toSourceTestCurvePredata p t + (c : EReal) :=
          add_le_add_left hle _
  · have hA : curveDivisorialTransform C.toSourceTestCurvePredata p t ≤
        curveDivisorialTransform (C.translate c).toSourceTestCurvePredata p t +
          ((-c : ℝ) : EReal) := by
      refine iSup₂_le fun σ h => ?_
      have h' : σ + c < (C.translate c).max := by rw [hmax]; linarith
      have hle := le_curveDivisorialTransform (C.translate c).toSourceTestCurvePredata p t h'
      have heq : presentationReader ((C.translate c).potential ⟨σ + c, h'⟩) p =
          presentationReader (C.potential ⟨σ, h⟩) p := by
        rw [hslice (σ + c) h']
        congr 3
        ring
      rw [heq] at hle
      have hx := coe_sliceLelong C.toSourceTestCurvePredata p h
      rw [← hx, EReal.coe_ennreal_ofReal, max_eq_left (sliceLelong_nonneg _ p _),
        ← EReal.coe_mul, ← EReal.coe_sub] at hle ⊢
      calc (((σ - t * sliceLelong C.toSourceTestCurvePredata p σ) : ℝ) : EReal)
          = ((σ + c - t * sliceLelong C.toSourceTestCurvePredata p σ : ℝ) : EReal) +
              ((-c : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
        _ ≤ _ := add_le_add_left hle _
    calc curveDivisorialTransform C.toSourceTestCurvePredata p t + (c : EReal)
        ≤ curveDivisorialTransform (C.translate c).toSourceTestCurvePredata p t +
            ((-c : ℝ) : EReal) + (c : EReal) := add_le_add_left hA _
      _ = _ := ereal_add_neg_add _ c

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- **Translation on `X^Div`** (the translation clause of `thm:NApotential:L1352`, divisorial
values in Lelong-number form): `(Γ + c)^An(t ord_E) = Γ^An(t ord_E) + c`. -/
theorem naDivisorialTransform_translate (Γ : SourceNAPotential θ) (c : ℝ)
    (ω : SourceKahlerForm n M) (p : PrimePresentation n M) (t : ℝ) :
    naDivisorialTransform (Γ.translate c) ω p t = naDivisorialTransform Γ ω p t + (c : EReal) :=
  curveDivisorialTransform_translate (Γ.component ω).val c p t

end SGPT.NAPotential.BJPrep
