import SGPT.PSH.SourceNATranslation

/-! # Full semipositive change of the original non-Archimedean background

Actual components at eta + omega are obtained from the existing realized
component producer. Equality of entire backgrounds transports them to the
required target, and original compatibility is proved before constructing
the new inverse-system element. No target compatibility certificate, positive
NA-volume premise or strict positivity of eta is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {α β θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual sum eta + omega is genuinely Kähler, even for eta = 0. -/
def sourceNAAugmentedKahlerBackground
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (omega : KahlerBackground n M) : KahlerBackground n M where
  form := atlasClosedFormToNative η + omega.form
  isKahler := by
    simpa only [one_smul] using
      Pending.NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive
        omega hη (t := 1) zero_lt_one

/-- The exact entire background equality, including the original atlas form. -/
theorem sourceNAAugmentedBackground_eq
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (omega : KahlerBackground n M) :
    sourceTestCurveEnlargedBackground (sourceNAAugmentedKahlerBackground η hη omega) θ =
      sourceTestCurveEnlargedBackground omega (θ.add η) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceTestCurveEnlargedBackground_native, sourceNativeClosedForm_add,
    sourceNAAugmentedKahlerBackground, add_assoc]

/-- The same entire equality at the original geometric component index. -/
theorem sourceNAAugmentedComponentBackground_eq
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (ω : SourceKahlerForm n M) :
    sourceTestCurveEnlargedBackground
        (sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative ω)) θ =
      sourceNAComponentBackground (θ.add η) ω :=
  sourceNAAugmentedBackground_eq θ η hη (sourceKahlerFormRepresentative ω)

/-- The physical difference after augmentation is precisely the old difference. -/
theorem sourceNAAugmentedKahlerBackground_mono
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    {omega omega' : KahlerBackground n M}
    (h : (omega'.form - omega.form).val.IsSemipositive) :
    ((sourceNAAugmentedKahlerBackground η hη omega').form -
      (sourceNAAugmentedKahlerBackground η hη omega).form).val.IsSemipositive := by
  have heq : (atlasClosedFormToNative η + omega'.form) -
      (atlasClosedFormToNative η + omega.form) = omega'.form - omega.form := by abel
  change ((atlasClosedFormToNative η + omega'.form) -
    (atlasClosedFormToNative η + omega.form)).val.IsSemipositive
  rw [heq]
  exact h

variable [MeasurableSpace M] [CompactSpace M]

/-- Equality transport of the same genuine positive I-model curve. -/
def SourcePositiveIModelTestCurve.castBackground
    (G : SourcePositiveIModelTestCurve α) (h : α = β) :
    SourcePositiveIModelTestCurve β := h ▸ G

/-- Its underlying object is the existing literal curve equality transport. -/
theorem SourcePositiveIModelTestCurve.castBackground_val
    (G : SourcePositiveIModelTestCurve α) (h : α = β) :
    (G.castBackground h).val = G.val.castBackground h := by
  cases h
  rfl

/-- Equality transport retains the exact original finite real cutoff. -/
theorem SourcePositiveIModelTestCurve.castBackground_max
    (G : SourcePositiveIModelTestCurve α) (h : α = β) :
    (G.castBackground h).val.max = G.val.max := by
  cases h
  rfl

/-- Equality transport retains every actual open slice function and all poles. -/
theorem SourcePositiveIModelTestCurve.castBackground_potential
    (G : SourcePositiveIModelTestCurve α) (h : α = β) (r : ℝ)
    (hr : r < G.val.max) (hs : r < (G.castBackground h).val.max) :
    (G.castBackground h).val.potential ⟨r, hs⟩ = G.val.potential ⟨r, hr⟩ := by
  cases h
  rfl

/-- Reindexing the original real parameter commutes with background equality. -/
theorem SourcePositiveIModelTestCurve.castBackground_translate
    (G : SourcePositiveIModelTestCurve α) (h : α = β) (C : ℝ) :
    (G.translate C).castBackground h = (G.castBackground h).translate C := by
  cases h
  rfl

variable [BorelSpace M] [ConnectedSpace M]

/-- The actual original component at eta + omega in its entire target background. -/
def SourceNAPotential.reindexedComponent (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (ω : SourceKahlerForm n M) : SourcePositiveIModelTestCurve
      (sourceNAComponentBackground (θ.add η) ω) :=
  (Γ.realizedComponent (sourceNAAugmentedKahlerBackground η hη
    (sourceKahlerFormRepresentative ω))).castBackground
      (sourceNAAugmentedComponentBackground_eq θ η hη ω)

/-- All reindexed components retain the same original common cutoff. -/
theorem SourceNAPotential.reindexedComponent_max (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (ω : SourceKahlerForm n M) :
    (Γ.reindexedComponent η hη ω).val.max = sourceNAPotentialCutoff omega Γ := by
  rw [SourceNAPotential.reindexedComponent, SourcePositiveIModelTestCurve.castBackground_max]
  exact Γ.realizedComponent_max_eq_cutoff omega _

/-- The reindexed component reader is the SAME actual original realized slice. -/
theorem SourceNAPotential.reindexedComponent_potential
    (Γ : SourceNAPotential θ) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (ω : SourceKahlerForm n M)
    (r : ℝ)
    (hr : r < (Γ.realizedComponent (sourceNAAugmentedKahlerBackground η hη
      (sourceKahlerFormRepresentative ω))).val.max)
    (hs : r < (Γ.reindexedComponent η hη ω).val.max) :
    (Γ.reindexedComponent η hη ω).val.potential ⟨r, hs⟩ =
      (Γ.realizedComponent (sourceNAAugmentedKahlerBackground η hη
        (sourceKahlerFormRepresentative ω))).val.potential ⟨r, hr⟩ :=
  SourcePositiveIModelTestCurve.castBackground_potential _ _ r hr hs

/-- Every original inverse-system compatibility is manufactured from the
existing full realized-component compatibility, rather than assumed. -/
theorem SourceNAPotential.reindexedComponent_compatible
    (Γ : SourceNAPotential θ) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (ω ζ : SourceKahlerForm n M) (h : sourceKahlerFormLE ω ζ) :
    sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
      (sourceNAComponentBackground_difference (θ.add η) h)
      (Γ.reindexedComponent η hη ω) = Γ.reindexedComponent η hη ζ := by
  let omega := sourceKahlerFormRepresentative ζ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · rw [sourceIModelTestCurveTransition_max,
      Γ.reindexedComponent_max omega η hη ω, Γ.reindexedComponent_max omega η hη ζ]
  · intro r hr hs
    have hw : r < (Γ.reindexedComponent η hη ω).val.max := by
      simpa only [sourceIModelTestCurveTransition_max] using hr
    have hw' : r < (Γ.realizedComponent (sourceNAAugmentedKahlerBackground η hη
        (sourceKahlerFormRepresentative ω))).val.max := by
      simpa only [SourceNAPotential.reindexedComponent,
        SourcePositiveIModelTestCurve.castBackground_max] using hw
    have hz' : r < (Γ.realizedComponent (sourceNAAugmentedKahlerBackground η hη
        (sourceKahlerFormRepresentative ζ))).val.max := by
      simpa only [SourceNAPotential.reindexedComponent,
        SourcePositiveIModelTestCurve.castBackground_max] using hs
    rw [sourceIModelTestCurveTransition_potential _ _ _ r hw hr,
      Γ.reindexedComponent_potential η hη ω r hw' hw,
      Γ.reindexedComponent_potential η hη ζ r hz' hs]
    have hp := Γ.realizedComponent_potential_transition
      (sourceNAAugmentedKahlerBackground_mono η hη h) r hw' hz'
    have he := congrArg (fun background ↦ sourceIEnvelope background
        ((Γ.realizedComponent (sourceNAAugmentedKahlerBackground η hη
          (sourceKahlerFormRepresentative ω))).val.potential ⟨r, hw'⟩))
      (sourceNAAugmentedComponentBackground_eq θ η hη ζ)
    exact (hp.trans he).symm

/-- Whole original semipositive NA-to-NA background change. -/
def SourceNAPotential.backgroundChange (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) : SourceNAPotential (θ.add η) where
  component ω := Γ.reindexedComponent η hη ω
  compatible ω ζ h := Γ.reindexedComponent_compatible η hη ω ζ h

/-- The entire component prescription of the original background-change map. -/
theorem SourceNAPotential.backgroundChange_component (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (ω : SourceKahlerForm n M) :
    (Γ.backgroundChange η hη).component ω = Γ.reindexedComponent η hη ω := rfl

/-- Every component determines the full original output metric uniquely. -/
theorem SourceNAPotential.backgroundChange_unique (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Δ : SourceNAPotential (θ.add η))
    (h : ∀ ω : SourceKahlerForm n M, Δ.component ω = Γ.reindexedComponent η hη ω) :
    Δ = Γ.backgroundChange η hη := SourceNAPotential.ext h

/-- Full background change leaves the original common cutoff unchanged. -/
theorem sourceNAPotentialCutoff_backgroundChange (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    sourceNAPotentialCutoff omega (Γ.backgroundChange η hη) =
      sourceNAPotentialCutoff omega Γ :=
  Γ.reindexedComponent_max omega η hη _

/-- The actual positive inclusion, read in ANY literal smooth Kähler background. -/
theorem sourcePositiveTestCurveToNA_realizedComponent_potential
    (G : SourcePositiveIModelTestCurve θ) (omega : KahlerBackground n M) (r : ℝ)
    (hr : r < G.val.max)
    (hs : r < ((sourcePositiveTestCurveToNA G).realizedComponent omega).val.max) :
    ((sourcePositiveTestCurveToNA G).realizedComponent omega).val.potential ⟨r, hs⟩ =
      sourceIEnvelope (sourceTestCurveEnlargedBackground omega θ) (G.val.potential ⟨r, hr⟩) := by
  have hi : r < ((sourcePositiveTestCurveToNA G).component
      (sourceKahlerFormOfBackground omega)).val.max := by
    rw [sourcePositiveTestCurveToNA_max]
    exact hr
  rw [(sourcePositiveTestCurveToNA G).realizedComponent_potential omega r hi hs,
    sourcePositiveTestCurveToNA_potential G _ r hr hi,
    sourceIEnvelope_geometricallyEq (sourceNAComponentBackground_geometricallyEq omega)]

/-- The full original NA background change extends the canonical positive-curve
transition, rather than merely defining a disconnected operation on systems. -/
theorem sourcePositiveTestCurveToNA_backgroundChange (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (sourcePositiveTestCurveToNA G).backgroundChange η hη =
      sourcePositiveTestCurveToNA (sourceIModelTestCurveTransition omega
        (show (atlasClosedFormToNative (θ.add η) - atlasClosedFormToNative θ).val.IsSemipositive by
          simpa only [sourceNativeClosedForm_add, add_sub_cancel_left] using hη) G) := by
  have hd : (atlasClosedFormToNative (θ.add η) - atlasClosedFormToNative θ).val.IsSemipositive := by
    simpa only [sourceNativeClosedForm_add, add_sub_cancel_left] using hη
  let D := sourceIModelTestCurveTransition omega hd G
  apply SourceNAPotential.ext
  intro ω
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · change ((sourcePositiveTestCurveToNA G).reindexedComponent η hη ω).val.max =
      ((sourcePositiveTestCurveToNA D).component ω).val.max
    rw [(sourcePositiveTestCurveToNA G).reindexedComponent_max omega η hη ω,
      sourcePositiveTestCurveToNA_cutoff, sourcePositiveTestCurveToNA_max]
    exact (sourceIModelTestCurveTransition_max omega hd G).symm
  · intro r hr hs
    change r < ((sourcePositiveTestCurveToNA G).reindexedComponent η hη ω).val.max at hr
    change r < ((sourcePositiveTestCurveToNA D).component ω).val.max at hs
    have hrG : r < G.val.max := by
      rwa [(sourcePositiveTestCurveToNA G).reindexedComponent_max omega η hη ω,
        sourcePositiveTestCurveToNA_cutoff] at hr
    have hrB : r < ((sourcePositiveTestCurveToNA G).realizedComponent
        (sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative ω))).val.max := by
      rw [(sourcePositiveTestCurveToNA G).realizedComponent_max_eq_cutoff omega,
        sourcePositiveTestCurveToNA_cutoff]
      exact hrG
    have hrD : r < D.val.max := by
      rw [sourceIModelTestCurveTransition_max]
      exact hrG
    change ((sourcePositiveTestCurveToNA G).reindexedComponent η hη ω).val.potential ⟨r, hr⟩ =
      ((sourcePositiveTestCurveToNA D).component ω).val.potential ⟨r, hs⟩
    rw [(sourcePositiveTestCurveToNA G).reindexedComponent_potential η hη ω r hrB hr,
      sourcePositiveTestCurveToNA_realizedComponent_potential G _ r hrG hrB,
      sourcePositiveTestCurveToNA_potential D ω r hrD hs,
      sourceIModelTestCurveTransition_potential omega hd G r hrG hrD,
      sourceNAAugmentedComponentBackground_eq]
    exact sourceIEnvelope_eq_of_equivalent
      (sourceIEquivalent_iEnvelope (sourceThetaPSH_of_semipositive_difference hd (G.val.thetaPSH ⟨r, hrG⟩)))

/-- Whole original full NA-to-NA projection/translation proposition,
for arbitrary semipositive eta and with no positive NA-volume premise. -/
theorem SourceNAPotential.backgroundChange_translate (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (C : ℝ) :
    (Γ.translate C).backgroundChange η hη = (Γ.backgroundChange η hη).translate C := by
  apply SourceNAPotential.ext
  intro ω
  change ((Γ.translate C).realizedComponent
      (sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative ω))).castBackground _ =
    ((Γ.realizedComponent
      (sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative ω))).castBackground _).translate C
  rw [Γ.translate_realizedComponent C]
  exact SourcePositiveIModelTestCurve.castBackground_translate _ _ C

end SGPT.PSH.VariableComplexAtlas
