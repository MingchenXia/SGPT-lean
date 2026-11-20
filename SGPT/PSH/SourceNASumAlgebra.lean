import SGPT.PSH.SourceNASum
import SGPT.PSH.SourceTestCurveSumSemipositiveProjection
import SGPT.PSH.SourceTestCurveSumAssociativity
import SGPT.PSH.SourceTestCurveSumTranslation

/-! # Whole original NA sum algebra

Only existing genuine global P-type producers are used. Full systems are
identified by original antisymmetry after exact whole-background transport.
No extra compatibility, mass positivity or ideal-equivalence hypothesis appears.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {α β θ σ χ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Commutativity of the exact entire original sum backgrounds. -/
theorem sourceNASumBackground_comm
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) : θ.add σ = σ.add θ := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeClosedForm_add]
  abel

/-- Associativity of the exact entire original sum backgrounds. -/
theorem sourceNASumBackground_assoc
    (θ σ χ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    (θ.add σ).add χ = θ.add (σ.add χ) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeClosedForm_add]
  abel

/-- The four actual original smooth backgrounds, with their exact grouping. -/
theorem sourceNASumBackgroundChange_eq
    (θ σ η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    (θ.add σ).add (η.add ζ) = (θ.add η).add (σ.add ζ) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeClosedForm_add]
  abel

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Equality of entire backgrounds transports the same original NA system. -/
def SourceNAPotential.castBackground (Γ : SourceNAPotential α) (h : α = β) :
    SourceNAPotential β := h ▸ Γ

/-- Equality transport preserves both original intrinsic comparisons. -/
theorem SourceNAPotential.castBackground_POrder_equivalent
    (omega : KahlerBackground n M) (Γ : SourceNAPotential α) (h : α = β) :
    SourceNAPOrder Γ (Γ.castBackground h) ∧ SourceNAPOrder (Γ.castBackground h) Γ := by
  cases h
  exact ⟨SourceNAPOrder.refl omega Γ, SourceNAPOrder.refl omega Γ⟩

/-- Original NA comparison can be read at ANY two independently chosen
actual Kähler presentations, even across different original base forms. -/
theorem sourceNAPOrder_iff_realizedComponents (Γ : SourceNAPotential θ)
    (Δ : SourceNAPotential σ) (omega omega' : KahlerBackground n M) :
    SourceNAPOrder Γ Δ ↔
      SourceTestCurvePOrder (Γ.realizedComponent omega).val (Δ.realizedComponent omega').val := by
  let κ := sourceKahlerFormOfBackground omega
  have hΓ := Γ.realizedComponent_component_POrder_equivalent omega κ
  have hΔ := Δ.realizedComponent_component_POrder_equivalent omega' κ
  constructor
  · intro h
    exact SourceTestCurvePOrder.trans omega hΓ.1
      (SourceTestCurvePOrder.trans omega ((sourceNAPOrder_iff_component Γ Δ κ).mp h) hΔ.2)
  · intro h
    exact ⟨κ, SourceTestCurvePOrder.trans omega hΓ.2
      (SourceTestCurvePOrder.trans omega h hΔ.1)⟩

/-- Arbitrary semipositive FULL NA background change preserves the original
intrinsic type, including the zero-form case. -/
theorem SourceNAPotential.backgroundChange_POrder_equivalent
    (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    SourceNAPOrder Γ (Γ.backgroundChange η hη) ∧
      SourceNAPOrder (Γ.backgroundChange η hη) Γ := by
  let κ := sourceKahlerFormOfBackground omega
  let B := sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative κ)
  have hr := Γ.realizedComponent_component_POrder_equivalent B κ
  have hc := (Γ.realizedComponent B).castBackground_POrder_equivalent omega
    (sourceNAAugmentedComponentBackground_eq θ η hη κ)
  exact ⟨⟨κ, SourceTestCurvePOrder.trans omega hr.2 hc.1⟩,
    ⟨κ, SourceTestCurvePOrder.trans omega hc.2 hr.1⟩⟩

/-- Both intrinsic comparisons of inputs give both comparisons of their
actual NA sums, allowing FOUR independent original base forms. -/
theorem SourceNAPotential.sum_POrder_equivalent (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (Γ' : SourceNAPotential α) (Δ' : SourceNAPotential β)
    (hΓ : SourceNAPOrder Γ Γ') (hΓ' : SourceNAPOrder Γ' Γ)
    (hΔ : SourceNAPOrder Δ Δ') (hΔ' : SourceNAPOrder Δ' Δ) :
    SourceNAPOrder (Γ.sum Δ) (Γ'.sum Δ') ∧ SourceNAPOrder (Γ'.sum Δ') (Γ.sum Δ) := by
  let κ := sourceKahlerFormOfBackground omega
  have hs := Γ.sumComponent_POrder_equivalent_sum Δ κ omega omega
  have ht := Γ'.sumComponent_POrder_equivalent_sum Δ' κ omega omega
  have hu := SourceTestCurve.sum_POrder_equivalent omega omega
    (Γ.realizedComponent omega).val (Δ.realizedComponent omega).val
    (Γ'.realizedComponent omega).val (Δ'.realizedComponent omega).val
    ((sourceNAPOrder_iff_realizedComponents Γ Γ' omega omega).mp hΓ)
    ((sourceNAPOrder_iff_realizedComponents Γ' Γ omega omega).mp hΓ')
    ((sourceNAPOrder_iff_realizedComponents Δ Δ' omega omega).mp hΔ)
    ((sourceNAPOrder_iff_realizedComponents Δ' Δ omega omega).mp hΔ')
  exact ⟨⟨κ, SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega hs.1 hu.1) ht.2⟩,
    ⟨κ, SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega ht.1 hu.2) hs.2⟩⟩

/-- WHOLE original L321: equality of FULL NA-to-NA background changes and
sums for independent arbitrary semipositive additions, with exact entire forms. -/
theorem SourceNAPotential.sum_backgroundChange (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hζ : (atlasClosedFormToNative ζ).val.IsSemipositive) :
    ((Γ.sum Δ).backgroundChange (η.add ζ)
      (sourceSemipositiveSum_isSemipositive η ζ hη hζ)).castBackground
        (sourceNASumBackgroundChange_eq θ σ η ζ) =
      (Γ.backgroundChange η hη).sum (Δ.backgroundChange ζ hζ) := by
  have hΓ := Γ.backgroundChange_POrder_equivalent omega η hη
  have hΔ := Δ.backgroundChange_POrder_equivalent omega ζ hζ
  have hs := Γ.sum_POrder_equivalent omega Δ (Γ.backgroundChange η hη)
    (Δ.backgroundChange ζ hζ) hΓ.1 hΓ.2 hΔ.1 hΔ.2
  have hb := (Γ.sum Δ).backgroundChange_POrder_equivalent omega (η.add ζ)
    (sourceSemipositiveSum_isSemipositive η ζ hη hζ)
  have hc := ((Γ.sum Δ).backgroundChange (η.add ζ)
    (sourceSemipositiveSum_isSemipositive η ζ hη hζ)).castBackground_POrder_equivalent omega
      (sourceNASumBackgroundChange_eq θ σ η ζ)
  exact SourceNAPOrder.antisymm (hc.2.trans (hb.2.trans hs.1))
    (hs.2.trans (hb.1.trans hc.1))

/-- The exact original positive-subtype sum commutativity, using the
already proved whole original test-curve equality. -/
theorem SourcePositiveIModelTestCurve.sum_comm (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ) :
    (G.sum omega H).castBackground (sourceTestCurveSumBackground_comm θ σ) = H.sum omega G := by
  apply Subtype.ext
  rw [SourcePositiveIModelTestCurve.castBackground_val]
  exact SourceTestCurve.sum_comm omega G.val H.val

/-- The exact original positive-subtype sum associativity, with unchanged
cutoffs and potentials and the entire original background identification. -/
theorem SourcePositiveIModelTestCurve.sum_assoc (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ)
    (L : SourcePositiveIModelTestCurve χ) :
    ((G.sum omega H).sum omega L).castBackground (sourceTestCurveSumBackground_assoc θ σ χ) =
      G.sum omega (H.sum omega L) := by
  apply Subtype.ext
  rw [SourcePositiveIModelTestCurve.castBackground_val]
  exact SourceTestCurve.sum_assoc omega G.val H.val L.val

/-- The existing literal sum/left-translation equality in the actual positive union. -/
theorem SourcePositiveIModelTestCurve.sum_translate_left (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ) (C : ℝ) :
    (G.sum omega H).translate C = (G.translate C).sum omega H := by
  apply Subtype.ext
  exact SourceTestCurve.sum_translate_left omega G.val H.val C

/-- The existing literal sum/right-translation equality in the actual positive union. -/
theorem SourcePositiveIModelTestCurve.sum_translate_right (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ) (C : ℝ) :
    (G.sum omega H).translate C = G.sum omega (H.translate C) := by
  apply Subtype.ext
  exact SourceTestCurve.sum_translate_right omega G.val H.val C

/-- The two full NA sums compare in both original intrinsic directions
before identifying their entire commuted backgrounds. -/
theorem SourceNAPotential.sum_comm_POrder_equivalent (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder (Γ.sum Δ) (Δ.sum Γ) ∧ SourceNAPOrder (Δ.sum Γ) (Γ.sum Δ) := by
  let κ := sourceKahlerFormOfBackground omega
  have hs := Γ.sumComponent_POrder_equivalent_sum Δ κ omega omega
  have ht := Δ.sumComponent_POrder_equivalent_sum Γ κ omega omega
  have hc := ((Γ.realizedComponent omega).sum omega
    (Δ.realizedComponent omega)).castBackground_POrder_equivalent omega
      (sourceTestCurveSumBackground_comm (sourceTestCurveEnlargedBackground omega θ)
        (sourceTestCurveEnlargedBackground omega σ))
  rw [SourcePositiveIModelTestCurve.sum_comm] at hc
  exact ⟨⟨κ, SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega hs.1 hc.1) ht.2⟩,
    ⟨κ, SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega ht.1 hc.2) hs.2⟩⟩

/-- Whole original NA commutativity, as equality of the full systems
after the exact whole original closed-background identification. -/
theorem SourceNAPotential.sum_comm (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    (Γ.sum Δ).castBackground (sourceNASumBackground_comm θ σ) = Δ.sum Γ := by
  have hs := Γ.sum_comm_POrder_equivalent omega Δ
  have hc := (Γ.sum Δ).castBackground_POrder_equivalent omega (sourceNASumBackground_comm θ σ)
  exact SourceNAPOrder.antisymm (hc.2.trans hs.1) (hs.2.trans hc.1)

/-- Both full NA parenthesizations have the same intrinsic type. The
three literal readers share omega; the two inner sums are read at 2 omega. -/
theorem SourceNAPotential.sum_assoc_POrder_equivalent (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (Λ : SourceNAPotential χ) :
    SourceNAPOrder ((Γ.sum Δ).sum Λ) (Γ.sum (Δ.sum Λ)) ∧
      SourceNAPOrder (Γ.sum (Δ.sum Λ)) ((Γ.sum Δ).sum Λ) := by
  let κ := sourceKahlerFormOfBackground omega
  let G := Γ.realizedComponent omega
  let H := Δ.realizedComponent omega
  let L := Λ.realizedComponent omega
  let GH := G.sum omega H
  let HL := H.sum omega L
  let A := (Γ.sum Δ).realizedComponent (omega.add omega)
  let B := (Δ.sum Λ).realizedComponent (omega.add omega)
  have hA := GH.castBackground_POrder_equivalent omega
    (sourceNASumSplitBackground_eq θ σ omega omega)
  have hB := HL.castBackground_POrder_equivalent omega
    (sourceNASumSplitBackground_eq σ χ omega omega)
  have heA : GH.castBackground (sourceNASumSplitBackground_eq θ σ omega omega) = A :=
    Γ.sum_realizedComponent Δ omega omega
  have heB : HL.castBackground (sourceNASumSplitBackground_eq σ χ omega omega) = B :=
    Δ.sum_realizedComponent Λ omega omega
  rw [heA] at hA
  rw [heB] at hB
  have hG := SourceTestCurvePOrder.refl omega G.val
  have hL := SourceTestCurvePOrder.refl omega L.val
  have hs := (Γ.sum Δ).sumComponent_POrder_equivalent_sum Λ κ (omega.add omega) omega
  have ht := Γ.sumComponent_POrder_equivalent_sum (Δ.sum Λ) κ omega (omega.add omega)
  have hleft := SourceTestCurve.sum_POrder_equivalent (omega.add omega) omega
    A.val L.val GH.val L.val hA.2 hA.1 hL hL
  have hright := SourceTestCurve.sum_POrder_equivalent omega omega
    G.val B.val G.val HL.val hG hG hB.2 hB.1
  have hassoc := (GH.sum omega L).castBackground_POrder_equivalent omega
    (sourceTestCurveSumBackground_assoc (sourceTestCurveEnlargedBackground omega θ)
      (sourceTestCurveEnlargedBackground omega σ) (sourceTestCurveEnlargedBackground omega χ))
  have he : (GH.sum omega L).castBackground
      (sourceTestCurveSumBackground_assoc (sourceTestCurveEnlargedBackground omega θ)
        (sourceTestCurveEnlargedBackground omega σ) (sourceTestCurveEnlargedBackground omega χ)) =
      G.sum omega HL := G.sum_assoc omega H L
  rw [he] at hassoc
  exact ⟨⟨κ, SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega
        (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hs.1 hleft.1)
          hassoc.1) hright.2) ht.2⟩,
    ⟨κ, SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega
        (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega ht.1 hright.1)
          hassoc.2) hleft.2) hs.2⟩⟩

/-- Whole original NA associativity after exact equality of the actual
entire original backgrounds, rather than incompatible nested half-index equations. -/
theorem SourceNAPotential.sum_assoc (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (Λ : SourceNAPotential χ) :
    ((Γ.sum Δ).sum Λ).castBackground (sourceNASumBackground_assoc θ σ χ) = Γ.sum (Δ.sum Λ) := by
  have hs := Γ.sum_assoc_POrder_equivalent omega Δ Λ
  have hc := ((Γ.sum Δ).sum Λ).castBackground_POrder_equivalent omega (sourceNASumBackground_assoc θ σ χ)
  exact SourceNAPOrder.antisymm (hc.2.trans hs.1) (hs.2.trans hc.1)

/-- Translation of the full original sum is the full sum with translated left input. -/
theorem SourceNAPotential.sum_translate_left
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (C : ℝ) :
    (Γ.sum Δ).translate C = (Γ.translate C).sum Δ := by
  apply SourceNAPotential.ext
  intro κ
  change (Γ.sumComponent Δ κ).translate C = (Γ.translate C).sumComponent Δ κ
  simp only [SourceNAPotential.sumComponent, SourceNAPotential.translate_realizedComponent,
    ← SourcePositiveIModelTestCurve.castBackground_translate,
    SourcePositiveIModelTestCurve.sum_translate_left]

/-- Translation of the full original sum is the full sum with translated right input. -/
theorem SourceNAPotential.sum_translate_right
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (C : ℝ) :
    (Γ.sum Δ).translate C = Γ.sum (Δ.translate C) := by
  apply SourceNAPotential.ext
  intro κ
  change (Γ.sumComponent Δ κ).translate C = Γ.sumComponent (Δ.translate C) κ
  simp only [SourceNAPotential.sumComponent, SourceNAPotential.translate_realizedComponent,
    ← SourcePositiveIModelTestCurve.castBackground_translate,
    SourcePositiveIModelTestCurve.sum_translate_right]

/-- BOTH clauses of the whole original prop:NAmetricplusC, retaining all
original systems and every finite real translation parameter. -/
theorem source_na_translation_whole
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (C D : ℝ) :
    (Γ.sum Δ).translate C = Γ.sum (Δ.translate C) ∧
      Γ.sum (Δ.translate C) = (Γ.translate C).sum Δ ∧
      Γ.translate (C + D) = (Γ.translate C).translate D :=
  ⟨Γ.sum_translate_right Δ C,
    (Γ.sum_translate_right Δ C).symm.trans (Γ.sum_translate_left Δ C),
    (Γ.translate_translate C D).symm⟩

end SGPT.PSH.VariableComplexAtlas
