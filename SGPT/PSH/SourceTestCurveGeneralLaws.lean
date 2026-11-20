import SGPT.PSH.SourceTestCurveGeneralProjection
import SGPT.PSH.SourceTestCurveOriginalTranslation

/-! # Original general-supremum translation and cross-background comparison

The genuine least-upper-bound property gives original parameter translation.
Existing finite Kähler domination manufactures a common full background.
Actual intrinsic projection equivalences and the accepted entire-curve
projection identity give a least-upper-bound property across backgrounds.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [BorelSpace M] [ConnectedSpace M] in
/-- Original parameter translation preserves the full cross-background intrinsic order. -/
theorem SourceTestCurvePOrder.translate {Γ : SourceTestCurve θ} {Δ : SourceTestCurve σ}
    (h : SourceTestCurvePOrder Γ Δ) (C : ℝ) :
    SourceTestCurvePOrder (Γ.translate C) (Δ.translate C) := by
  have hc : (Γ.translate C).max ≤ (Δ.translate C).max := by
    simp only [SourceTestCurve.translate_max]
    linarith [h.cutoff_le]
  refine ⟨hc, ?_⟩
  intro r hr
  have hr' : r - C < Γ.max := by
    rw [SourceTestCurve.translate_max] at hr
    linarith
  simpa only [SourceTestCurve.translate_potential] using h.slice_le (r - C) hr'

omit [BorelSpace M] [ConnectedSpace M] in
/-- An actual original cutoff bound manufactures the translated cutoff bound. -/
theorem sourceTestCurveTranslatedFamily_bddAbove {I : Type*}
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) (C : ℝ) :
    BddAbove (range fun i => ((Γ i).translate C).max) := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B + C, ?_⟩
  rintro _ ⟨i, rfl⟩
  change ((Γ i).translate C).max ≤ B + C
  rw [SourceTestCurve.translate_max]
  have hi := hB (mem_range_self i)
  linarith

/-- The entire actual arbitrary-family supremum commutes with the book's translation. -/
theorem SourceTestCurve.generalSup_translate {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) (C : ℝ) :
    SourceTestCurve.generalSup omega (fun i => (Γ i).translate C)
        (sourceTestCurveTranslatedFamily_bddAbove Γ hb C) =
      (SourceTestCurve.generalSup omega Γ hb).translate C := by
  let T := SourceTestCurve.generalSup omega (fun i => (Γ i).translate C)
    (sourceTestCurveTranslatedFamily_bddAbove Γ hb C)
  apply SourceTestCurvePOrder.antisymm omega
  · exact SourceTestCurve.generalSup_le omega (fun i => (Γ i).translate C)
      (sourceTestCurveTranslatedFamily_bddAbove Γ hb C) _
      (fun i => (SourceTestCurve.le_generalSup omega Γ hb i).translate C)
  · have h : SourceTestCurvePOrder (SourceTestCurve.generalSup omega Γ hb)
        (T.translate (-C)) := by
      apply SourceTestCurve.generalSup_le omega Γ hb
      intro i
      have hi := (SourceTestCurve.le_generalSup omega (fun i => (Γ i).translate C)
        (sourceTestCurveTranslatedFamily_bddAbove Γ hb C) i).translate (-C)
      simpa only [SourceTestCurve.translate_translate, add_neg_cancel,
        SourceTestCurve.translate_zero] using hi
    have h' := h.translate C
    simpa only [SourceTestCurve.translate_translate, neg_add_cancel,
      SourceTestCurve.translate_zero] using h'

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Existing finite Kähler domination manufactures a common full atlas background. -/
theorem sourceTestCurve_exists_common_semipositive_background
    (omega : KahlerBackground n M)
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    ∃ η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M),
      (atlasClosedFormToNative η).val.IsSemipositive ∧
      (atlasClosedFormToNative ζ).val.IsSemipositive ∧ θ.add η = σ.add ζ := by
  obtain ⟨A, _, hA⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
    (fun b : Bool => if b then -atlasClosedFormToNative θ else -atlasClosedFormToNative σ)
  let η := nativeClosedFormToAtlas (-atlasClosedFormToNative θ + A • omega.form)
  let ζ := nativeClosedFormToAtlas (-atlasClosedFormToNative σ + A • omega.form)
  refine ⟨η, ζ, ?_, ?_, ?_⟩
  · simpa [η, sourceNativeAtlasForm_roundTrip] using hA true
  · simpa [ζ, sourceNativeAtlasForm_roundTrip] using hA false
  · apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
    simp only [sourceNativeClosedForm_add, η, ζ, sourceNativeAtlasForm_roundTrip]
    abel

/-- Every actual semipositive projection retains the original intrinsic global P class. -/
theorem SourceTestCurve.semipositiveProjection_equivalent (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : SourceTestCurve θ) :
    SourceTestCurvePOrder Γ (Γ.semipositiveProjection omega η hη) ∧
      SourceTestCurvePOrder (Γ.semipositiveProjection omega η hη) Γ := by
  have he (r : ℝ) (hr : r < Γ.max) :
      SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n) (Γ.potential ⟨r, hr⟩)
        (sourceSingularityEnvelope (θ.add η) (Γ.potential ⟨r, hr⟩)) := by
    have h := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
      (atlasClosedFormToNative (θ.add η))
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp
        (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH ⟨r, hr⟩)))
    simpa only [← sourceSingularityEnvelope_eq_native] using h
  exact ⟨⟨le_rfl, fun r hr => (he r hr).1⟩, ⟨le_rfl, fun r hr => (he r hr).2⟩⟩

omit [BorelSpace M] [ConnectedSpace M] in
/-- Full background equality changes neither the target cutoff nor its strict slices. -/
theorem sourceTestCurvePOrder_cast_right_iff
    {τ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (h : σ = τ) :
    SourceTestCurvePOrder Γ (Δ.castBackground h) ↔ SourceTestCurvePOrder Γ Δ := by
  cases h
  rfl

/-- The actual general supremum has its genuine LUB property even against another background. -/
theorem SourceTestCurve.generalSup_le_cross_background {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) (Ξ : SourceTestCurve σ)
    (hΞ : ∀ i, SourceTestCurvePOrder (Γ i) Ξ) :
    SourceTestCurvePOrder (SourceTestCurve.generalSup omega Γ hb) Ξ := by
  obtain ⟨η, ζ, hη, hζ, hforms⟩ :=
    sourceTestCurve_exists_common_semipositive_background omega θ σ
  have hX := Ξ.semipositiveProjection_equivalent omega ζ hζ
  have hInputs (i : I) : SourceTestCurvePOrder
      ((Γ i).semipositiveProjection omega η hη)
      ((Ξ.semipositiveProjection omega ζ hζ).castBackground hforms.symm) := by
    apply (sourceTestCurvePOrder_cast_right_iff _ _ hforms.symm).mpr
    exact (((Γ i).semipositiveProjection_equivalent omega η hη).2.trans omega
      (hΞ i)).trans omega hX.1
  have h := SourceTestCurve.generalSup_le omega
    (fun i => (Γ i).semipositiveProjection omega η hη)
    (sourceTestCurveSemipositiveProjectedFamily_bddAbove omega η hη Γ hb)
    ((Ξ.semipositiveProjection omega ζ hζ).castBackground hforms.symm) hInputs
  rw [← source_test_curve_generalSup_semipositive_projection_compatible omega η hη Γ hb] at h
  have h' := (sourceTestCurvePOrder_cast_right_iff _ _ hforms.symm).mp h
  exact ((SourceTestCurve.generalSup omega Γ hb).semipositiveProjection_equivalent
    omega η hη).1.trans omega (h'.trans omega hX.2)

/-- Original pointwise intrinsic comparison gives full cross-background supremum comparison. -/
theorem SourceTestCurve.generalSup_mono_cross_background {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ) (Δ : I → SourceTestCurve σ)
    (hbΓ : BddAbove (range fun i => (Γ i).max))
    (hbΔ : BddAbove (range fun i => (Δ i).max))
    (h : ∀ i, SourceTestCurvePOrder (Γ i) (Δ i)) :
    SourceTestCurvePOrder (SourceTestCurve.generalSup omega Γ hbΓ)
      (SourceTestCurve.generalSup omega Δ hbΔ) :=
  SourceTestCurve.generalSup_le_cross_background omega Γ hbΓ _
    (fun i => (h i).trans omega (SourceTestCurve.le_generalSup omega Δ hbΔ i))

/-- BOTH whole original prop:supGammiotherprop clauses, on the actual entire curves. -/
theorem source_test_curve_generalSup_laws_whole {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ) (Δ : I → SourceTestCurve σ)
    (hbΓ : BddAbove (range fun i => (Γ i).max))
    (hbΔ : BddAbove (range fun i => (Δ i).max)) (C : ℝ) :
    (SourceTestCurve.generalSup omega (fun i => (Γ i).translate C)
        (sourceTestCurveTranslatedFamily_bddAbove Γ hbΓ C) =
      (SourceTestCurve.generalSup omega Γ hbΓ).translate C) ∧
    ((∀ i, SourceTestCurvePOrder (Γ i) (Δ i)) →
      SourceTestCurvePOrder (SourceTestCurve.generalSup omega Γ hbΓ)
        (SourceTestCurve.generalSup omega Δ hbΔ)) :=
  ⟨SourceTestCurve.generalSup_translate omega Γ hbΓ C,
    SourceTestCurve.generalSup_mono_cross_background omega Γ Δ hbΓ hbΔ⟩

end SGPT.PSH.VariableComplexAtlas
