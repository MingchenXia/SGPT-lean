import SGPT.PSH.SourceNonArchimedeanVolume
import SGPT.PSH.SourceTestCurveOriginalTranslation

/-! # Translation of genuine original non-Archimedean metrics

The actual compatible system is constructed from translated positive I-model
test curves. Every transition and every component limit is preserved literally;
no positivity of the infimum defining the non-Archimedean volume is assumed.
See `source-na-translation.tex` for the complete mathematical route.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α β θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Translation reindexes the same genuine I-model slices and retains the
same positive model base; it supplies an actual member of the original union. -/
def SourcePositiveIModelTestCurve.translate (G : SourcePositiveIModelTestCurve α)
    (C : ℝ) : SourcePositiveIModelTestCurve α := by
  refine ⟨G.val.translate C, ?_⟩
  obtain ⟨φ, hφ, hb, hI⟩ := G.property
  refine ⟨φ, hφ, (G.val.shift_based_iff hφ (-C)).mpr hb, ?_⟩
  intro r
  exact hI ⟨r.val + -C, by
    have hr := r.property
    change r.val < G.val.max - -C at hr
    change r.val + -C < G.val.max
    linarith⟩

omit [BorelSpace M] [ConnectedSpace M] in
/-- The underlying curve is exactly the existing original additive translation. -/
theorem SourcePositiveIModelTestCurve.translate_val
    (G : SourcePositiveIModelTestCurve α) (C : ℝ) :
    (G.translate C).val = G.val.translate C := rfl

/-- Genuine I-envelope transitions commute with every finite real translation. -/
theorem sourceIModelTestCurveTransition_translate (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : SourcePositiveIModelTestCurve α) (C : ℝ) :
    sourceIModelTestCurveTransition omega hαβ (G.translate C) =
      (sourceIModelTestCurveTransition omega hαβ G).translate C := by
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · simp only [sourceIModelTestCurveTransition_max,
      SourcePositiveIModelTestCurve.translate_val, SourceTestCurve.translate_max]
  · intro r hr hs
    have hleft : r < (G.translate C).val.max := by
      simpa only [sourceIModelTestCurveTransition_max] using hr
    have hbase : r - C < G.val.max := by
      rw [SourcePositiveIModelTestCurve.translate_val, SourceTestCurve.translate_max] at hleft
      linarith
    have htarget : r - C < (sourceIModelTestCurveTransition omega hαβ G).val.max := by
      rw [sourceIModelTestCurveTransition_max]
      exact hbase
    rw [sourceIModelTestCurveTransition_potential omega hαβ (G.translate C) r hleft hr]
    change sourceIEnvelope β ((G.val.translate C).potential ⟨r, hleft⟩) =
      ((sourceIModelTestCurveTransition omega hαβ G).val.translate C).potential ⟨r, hs⟩
    rw [SourceTestCurve.translate_potential, SourceTestCurve.translate_potential,
      sourceIModelTestCurveTransition_potential omega hαβ G (r - C) hbase htarget]

/-- The original translation, as an actual compatible inverse-system element. -/
def SourceNAPotential.translate (Γ : SourceNAPotential θ) (C : ℝ) :
    SourceNAPotential θ where
  component ω := (Γ.component ω).translate C
  compatible ω η h := by
    rw [sourceIModelTestCurveTransition_translate, Γ.compatible ω η h]

/-- Every original geometric component is the literal translated original curve. -/
theorem SourceNAPotential.translate_component (Γ : SourceNAPotential θ) (C : ℝ)
    (ω : SourceKahlerForm n M) :
    (Γ.translate C).component ω = (Γ.component ω).translate C := rfl

/-- The component prescription determines the entire original translated metric. -/
theorem SourceNAPotential.translate_unique (Γ Δ : SourceNAPotential θ) (C : ℝ)
    (h : ∀ ω : SourceKahlerForm n M,
      Δ.component ω = (Γ.component ω).translate C) : Δ = Γ.translate C :=
  SourceNAPotential.ext h

/-- Translation commutes with projection to every literal smooth background θ+ω. -/
theorem SourceNAPotential.translate_realizedComponent (Γ : SourceNAPotential θ)
    (C : ℝ) (omega : KahlerBackground n M) :
    (Γ.translate C).realizedComponent omega = (Γ.realizedComponent omega).translate C := by
  dsimp only [SourceNAPotential.realizedComponent,
    sourceIModelTestCurvePresentationEquiv, Equiv.coe_fn_mk]
  rw [Γ.translate_component C, sourceIModelTestCurveTransition_translate]

/-- The full original common cutoff shifts by the same real constant. -/
theorem sourceNAPotentialCutoff_translate (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (C : ℝ) :
    sourceNAPotentialCutoff omega (Γ.translate C) = sourceNAPotentialCutoff omega Γ + C :=
  SourceTestCurve.translate_max _ C

/-- This genuinely extends the canonical inclusion of positive model test curves. -/
theorem sourcePositiveTestCurveToNA_translate (G : SourcePositiveIModelTestCurve θ)
    (C : ℝ) :
    sourcePositiveTestCurveToNA (G.translate C) = (sourcePositiveTestCurveToNA G).translate C := by
  apply SourceNAPotential.ext
  intro ω
  exact sourceIModelTestCurveTransition_translate (sourceKahlerFormRepresentative ω)
    (sourceNAComponentBackground_positive θ ω) G C

/-- Zero translation preserves the entire original system. -/
theorem SourceNAPotential.translate_zero (Γ : SourceNAPotential θ) : Γ.translate 0 = Γ := by
  apply SourceNAPotential.ext
  intro ω
  apply Subtype.ext
  exact (Γ.component ω).val.translate_zero

/-- The additive action law, without claiming the separate sum-of-metrics clause. -/
theorem SourceNAPotential.translate_translate (Γ : SourceNAPotential θ) (C D : ℝ) :
    (Γ.translate C).translate D = Γ.translate (C + D) := by
  apply SourceNAPotential.ext
  intro ω
  apply Subtype.ext
  exact (Γ.component ω).val.translate_translate C D

/-- Every real translation has its original inverse on the full compatible system. -/
theorem SourceNAPotential.translate_neg (Γ : SourceNAPotential θ) (C : ℝ) :
    (Γ.translate C).translate (-C) = Γ := by
  rw [Γ.translate_translate C (-C), add_neg_cancel, Γ.translate_zero]

/-- The actual spatial limit function is unchanged at every geometric index. -/
theorem SourceNAPotential.translate_component_limit (Γ : SourceNAPotential θ)
    (C : ℝ) (ω : SourceKahlerForm n M) :
    sourceTestCurveLimit ((Γ.translate C).component ω).val.toSourceTestCurvePredata =
      sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata :=
  (Γ.component ω).val.translate_limit C

/-- The actual genuine component mass is unchanged, before taking any infimum. -/
theorem sourceNAComponentMass_translate (Γ : SourceNAPotential θ) (C : ℝ)
    (ω : SourceKahlerForm n M) :
    sourceNAComponentMass (Γ.translate C) ω = sourceNAComponentMass Γ ω :=
  sourcePotentialMass_congr (Γ.translate_component_limit C ω) _ _

/-- Whole original volume invariance, including metrics of zero NA volume. -/
theorem sourceNAVolume_translate (Γ : SourceNAPotential θ) (C : ℝ) :
    sourceNAVolume (Γ.translate C) = sourceNAVolume Γ := by
  unfold sourceNAVolume
  simp only [sourceNAComponentMass_translate]

end SGPT.PSH.VariableComplexAtlas
