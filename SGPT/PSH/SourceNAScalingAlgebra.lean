import SGPT.PSH.SourceNAPositiveScaling
import SGPT.PSH.SourceTestCurveScalingAlgebra

/-! # Finite positive-scaling algebra of full original NA systems

Only the first three clauses of `prop:resclacompat2` are addressed.
Arbitrary-family supremum and decreasing-net infimum remain unproved here.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Whole original sum backgrounds distribute under rescaling. -/
theorem sourceNAScaledSumBackground_eq
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (c : ℝ) :
    sourceNAScaledBackground (θ.add σ) c =
      (sourceNAScaledBackground θ c).add (sourceNAScaledBackground σ c) := by
  apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNAScaledBackground, sourceNativeAtlasForm_roundTrip,
    sourceNativeClosedForm_add, smul_add]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The exact finite composition law on genuine positive I-model subtypes. -/
theorem SourcePositiveIModelTestCurve.positiveScale_positiveScale
    (omega : KahlerBackground n M) (G : SourcePositiveIModelTestCurve θ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ((G.positiveScale omega hd).positiveScale omega hc).castBackground
      (sourceTCScaledCompositionBackground_eq θ c d) =
      G.positiveScale omega (mul_pos hc hd) := by
  apply Subtype.ext
  erw [SourcePositiveIModelTestCurve.castBackground_val]
  exact G.val.positiveScale_positiveScale hc hd

/-- The exact finite sum law on genuine positive I-model subtypes. -/
theorem SourcePositiveIModelTestCurve.positiveScale_sum
    (omega : KahlerBackground n M) (G : SourcePositiveIModelTestCurve θ)
    (H : SourcePositiveIModelTestCurve σ) {c : ℝ} (hc : 0 < c) :
    ((G.sum omega H).positiveScale omega hc).castBackground
      (sourceTCScaledSumBackground_eq θ σ c) =
      (G.positiveScale omega hc).sum omega (H.positiveScale omega hc) := by
  apply Subtype.ext
  erw [SourcePositiveIModelTestCurve.castBackground_val]
  exact G.val.positiveScale_sum omega H.val hc

/-- The exact finite translation law on genuine positive I-model subtypes. -/
theorem SourcePositiveIModelTestCurve.positiveScale_translate
    (omega : KahlerBackground n M) (G : SourcePositiveIModelTestCurve θ)
    {c : ℝ} (hc : 0 < c) (C : ℝ) :
    (G.translate C).positiveScale omega hc = (G.positiveScale omega hc).translate (c*C) := by
  apply Subtype.ext
  exact G.val.positiveScale_translate hc C

/-- Any scaled component has the type of scaling ANY original reader,
without assuming chosen Kähler representatives are equal as structures. -/
theorem SourceNAPotential.positiveScaleComponent_POrder_equivalent_curve
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (κ : SourceKahlerForm n M)
    (omega : KahlerBackground n M) :
    SourceTestCurvePOrder (Γ.positiveScaleComponent hc κ).val
      ((Γ.realizedComponent omega).val.positiveScale hc) ∧
    SourceTestCurvePOrder ((Γ.realizedComponent omega).val.positiveScale hc)
      (Γ.positiveScaleComponent hc κ).val := by
  have h := Γ.positiveScaleComponent_POrder_equivalent_reader hc κ
    (KahlerBackground.smul hc omega)
  rw [sourceNADividedKahlerBackground_scaled] at h
  exact h

/-- Independently chosen literal output and input readers have exactly the
corresponding scaled global P-type in both directions. -/
theorem SourceNAPotential.positiveScale_reader_POrder_equivalent
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c)
    (omega omega' : KahlerBackground n M) :
    SourceTestCurvePOrder ((Γ.positiveScale hc).realizedComponent omega).val
      ((Γ.realizedComponent omega').val.positiveScale hc) ∧
    SourceTestCurvePOrder ((Γ.realizedComponent omega').val.positiveScale hc)
      ((Γ.positiveScale hc).realizedComponent omega).val := by
  let κ := sourceKahlerFormOfBackground omega
  have hR := (Γ.positiveScale hc).realizedComponent_component_POrder_equivalent omega κ
  have hS := Γ.positiveScaleComponent_POrder_equivalent_curve hc κ omega'
  exact ⟨SourceTestCurvePOrder.trans omega hR.1 hS.1,
    SourceTestCurvePOrder.trans omega hS.2 hR.2⟩

/-- Finite translation compatibility for the FULL original NA system. -/
theorem SourceNAPotential.positiveScale_translate
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    (Γ.translate C).positiveScale hc = (Γ.positiveScale hc).translate (c*C) := by
  apply SourceNAPotential.ext_of_realizedComponent
  intro omega
  rw [← (Γ.translate C).positiveScale_realizedComponent hc omega,
    (Γ.positiveScale hc).translate_realizedComponent (c*C) omega,
    ← Γ.positiveScale_realizedComponent hc omega,
    Γ.translate_realizedComponent C (sourceNADividedKahlerBackground hc omega),
    SourcePositiveIModelTestCurve.positiveScale_translate,
    SourcePositiveIModelTestCurve.castBackground_translate]

/-- Finite composition compatibility for FULL original NA systems. -/
theorem SourceNAPotential.positiveScale_positiveScale
    (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ((Γ.positiveScale hd).positiveScale hc).castBackground
      (sourceTCScaledCompositionBackground_eq θ c d) =
      Γ.positiveScale (mul_pos hc hd) := by
  have hL := (Γ.positiveScale hd).positiveScale_reader_POrder_equivalent hc omega omega
  have hD := Γ.positiveScale_reader_POrder_equivalent hd omega omega
  have hR := Γ.positiveScale_reader_POrder_equivalent (mul_pos hc hd) omega omega
  have hF := SourcePositiveIModelTestCurve.castBackground_POrder_equivalent omega
    (((Γ.realizedComponent omega).positiveScale omega hd).positiveScale omega hc)
      (sourceTCScaledCompositionBackground_eq _ c d)
  rw [SourcePositiveIModelTestCurve.positiveScale_positiveScale] at hF
  have hLR : SourceNAPOrder ((Γ.positiveScale hd).positiveScale hc)
      (Γ.positiveScale (mul_pos hc hd)) :=
    (sourceNAPOrder_iff_realizedComponents _ _ omega omega).mpr
      (SourceTestCurvePOrder.trans omega hL.1
        (SourceTestCurvePOrder.trans omega (hD.1.positiveScale hc)
          (SourceTestCurvePOrder.trans omega hF.1 hR.2)))
  have hRL : SourceNAPOrder (Γ.positiveScale (mul_pos hc hd))
      ((Γ.positiveScale hd).positiveScale hc) :=
    (sourceNAPOrder_iff_realizedComponents _ _ omega omega).mpr
      (SourceTestCurvePOrder.trans omega hR.1
        (SourceTestCurvePOrder.trans omega hF.2
          (SourceTestCurvePOrder.trans omega (hD.2.positiveScale hc) hL.2)))
  have hC := ((Γ.positiveScale hd).positiveScale hc).castBackground_POrder_equivalent omega
    (sourceTCScaledCompositionBackground_eq θ c d)
  exact SourceNAPOrder.antisymm (hC.2.trans hLR) (hRL.trans hC.1)

/-- Finite sum compatibility for FULL original NA systems, using actual
independent readers and exact entire background equality. -/
theorem SourceNAPotential.positiveScale_sum
    (omega : KahlerBackground n M) (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    {c : ℝ} (hc : 0 < c) :
    ((Γ.sum Δ).positiveScale hc).castBackground (sourceNAScaledSumBackground_eq θ σ c) =
      (Γ.positiveScale hc).sum (Δ.positiveScale hc) := by
  have hL := (Γ.sum Δ).positiveScale_reader_POrder_equivalent hc omega (omega.add omega)
  have hS := ((Γ.realizedComponent omega).sum omega
    (Δ.realizedComponent omega)).castBackground_POrder_equivalent omega
      (sourceNASumSplitBackground_eq θ σ omega omega)
  rw [Γ.sum_realizedComponent Δ omega omega] at hS
  have hG := Γ.positiveScale_reader_POrder_equivalent hc omega omega
  have hH := Δ.positiveScale_reader_POrder_equivalent hc omega omega
  have hT := SourceTestCurve.sum_POrder_equivalent omega omega
    ((Γ.positiveScale hc).realizedComponent omega).val
    ((Δ.positiveScale hc).realizedComponent omega).val
    ((Γ.realizedComponent omega).val.positiveScale hc)
    ((Δ.realizedComponent omega).val.positiveScale hc) hG.1 hG.2 hH.1 hH.2
  have hF := SourcePositiveIModelTestCurve.castBackground_POrder_equivalent omega
    (((Γ.realizedComponent omega).sum omega (Δ.realizedComponent omega)).positiveScale omega hc)
      (sourceTCScaledSumBackground_eq _ _ c)
  rw [SourcePositiveIModelTestCurve.positiveScale_sum] at hF
  have hR := (((Γ.positiveScale hc).realizedComponent omega).sum omega
    ((Δ.positiveScale hc).realizedComponent omega)).castBackground_POrder_equivalent omega
      (sourceNASumSplitBackground_eq (sourceNAScaledBackground θ c)
        (sourceNAScaledBackground σ c) omega omega)
  rw [(Γ.positiveScale hc).sum_realizedComponent (Δ.positiveScale hc) omega omega] at hR
  have hLR : SourceNAPOrder ((Γ.sum Δ).positiveScale hc)
      ((Γ.positiveScale hc).sum (Δ.positiveScale hc)) :=
    (sourceNAPOrder_iff_realizedComponents _ _ omega (omega.add omega)).mpr
      (SourceTestCurvePOrder.trans omega hL.1
        (SourceTestCurvePOrder.trans omega (hS.2.positiveScale hc)
          (SourceTestCurvePOrder.trans omega hF.1
            (SourceTestCurvePOrder.trans omega hT.2 hR.1))))
  have hRL : SourceNAPOrder ((Γ.positiveScale hc).sum (Δ.positiveScale hc))
      ((Γ.sum Δ).positiveScale hc) :=
    (sourceNAPOrder_iff_realizedComponents _ _ (omega.add omega) omega).mpr
      (SourceTestCurvePOrder.trans omega hR.2
        (SourceTestCurvePOrder.trans omega hT.1
          (SourceTestCurvePOrder.trans omega hF.2
            (SourceTestCurvePOrder.trans omega (hS.1.positiveScale hc) hL.2))))
  have hC := ((Γ.sum Δ).positiveScale hc).castBackground_POrder_equivalent omega
    (sourceNAScaledSumBackground_eq θ σ c)
  exact SourceNAPOrder.antisymm (hC.2.trans hLR) (hRL.trans hC.1)

end SGPT.PSH.VariableComplexAtlas
