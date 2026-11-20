import SGPT.PSH.SourceTestCurveSumPType

/-! # Genuine sum of the original non-Archimedean inverse systems

The components are actual sums at half a Kähler presentation. Their
compatibility is manufactured from genuine global P-type independence and
ordinary-model antisymmetry. It is not an input certificate.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Half of the actual smooth Kähler form is still an actual Kähler form. -/
def sourceNAHalfKahlerBackground (omega : KahlerBackground n M) : KahlerBackground n M :=
  KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) omega

/-- Every literal Kähler presentation is twice its actual positive half. -/
theorem sourceNAHalfKahlerBackground_add_self (omega : KahlerBackground n M) :
    (sourceNAHalfKahlerBackground omega).add (sourceNAHalfKahlerBackground omega) = omega := by
  cases omega
  dsimp [sourceNAHalfKahlerBackground, KahlerBackground.smul, KahlerBackground.add]
  congr 1
  module

/-- The existing native sum is the entire original atlas sum. -/
theorem sourceNAOriginalSumBackground_eq
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ) = θ.add σ := by
  rw [← sourceNativeClosedForm_add, sourceAtlasNativeForm_roundTrip]

/-- The entire background identity for arbitrary independent positive splits. -/
theorem sourceNASumSplitBackground_eq
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (omega omega' : KahlerBackground n M) :
    nativeClosedFormToAtlas
        (atlasClosedFormToNative (sourceTestCurveEnlargedBackground omega θ) +
          atlasClosedFormToNative (sourceTestCurveEnlargedBackground omega' σ)) =
      sourceTestCurveEnlargedBackground (omega.add omega') (θ.add σ) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeAtlasForm_roundTrip, sourceTestCurveEnlargedBackground_native,
    sourceNativeClosedForm_add, KahlerBackground.add_form]
  abel

/-- The full sum background at the two halves is exactly the required
whole original NA background, not just its cohomology class. -/
theorem sourceNASumHalfBackground_eq
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (omega : KahlerBackground n M) :
    nativeClosedFormToAtlas
        (atlasClosedFormToNative (sourceTestCurveEnlargedBackground (sourceNAHalfKahlerBackground omega) θ) +
          atlasClosedFormToNative (sourceTestCurveEnlargedBackground (sourceNAHalfKahlerBackground omega) σ)) =
      sourceTestCurveEnlargedBackground omega (θ.add σ) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeAtlasForm_roundTrip, sourceTestCurveEnlargedBackground_native,
    sourceNativeClosedForm_add, sourceNAHalfKahlerBackground, KahlerBackground.smul_form]
  module

/-- The same exact background identity at a geometric component index. -/
theorem sourceNASumComponentBackground_eq
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (κ : SourceKahlerForm n M) :
    nativeClosedFormToAtlas
        (atlasClosedFormToNative (sourceTestCurveEnlargedBackground
          (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ)) θ) +
        atlasClosedFormToNative (sourceTestCurveEnlargedBackground
          (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ)) σ)) =
      sourceNAComponentBackground (θ.add σ) κ :=
  sourceNASumHalfBackground_eq θ σ (sourceKahlerFormRepresentative κ)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α β θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Equal original cutoffs and open functions give both intrinsic comparisons. -/
theorem sourceTestCurvePOrder_equivalent_of_functions (omega : KahlerBackground n M)
    (G : SourceTestCurve α) (H : SourceTestCurve β) (hc : G.max = H.max)
    (hp : ∀ (r : ℝ) (hr : r < G.max) (hs : r < H.max),
      G.potential ⟨r, hr⟩ = H.potential ⟨r, hs⟩) :
    SourceTestCurvePOrder G H ∧ SourceTestCurvePOrder H G := by
  have hg := SourceTestCurvePOrder.refl omega G
  refine ⟨?_, ?_⟩
  · exact (sourceTestCurvePOrder_congr_functions G G G H rfl hc
      (fun _ _ _ ↦ rfl) hp).mp hg
  · exact (sourceTestCurvePOrder_congr_functions G H G G hc rfl
      hp (fun _ _ _ ↦ rfl)).mp hg

/-- All original geometric components of one system have the same genuine
global P-type, by transitions to a common upper component. -/
theorem SourceNAPotential.component_POrder_equivalent (Γ : SourceNAPotential θ)
    (κ ζ : SourceKahlerForm n M) :
    SourceTestCurvePOrder (Γ.component κ).val (Γ.component ζ).val ∧
      SourceTestCurvePOrder (Γ.component ζ).val (Γ.component κ).val := by
  let ν := sourceKahlerFormCommonUpper κ ζ
  let omega := sourceKahlerFormRepresentative ν
  have hk := sourceIModelTestCurveTransition_POrder_equivalent omega
    (sourceNAComponentBackground_difference θ (sourceKahlerFormLE_commonUpper_left κ ζ))
    (Γ.component κ)
  have hz := sourceIModelTestCurveTransition_POrder_equivalent omega
    (sourceNAComponentBackground_difference θ (sourceKahlerFormLE_commonUpper_right κ ζ))
    (Γ.component ζ)
  rw [Γ.compatible κ ν (sourceKahlerFormLE_commonUpper_left κ ζ)] at hk
  rw [Γ.compatible ζ ν (sourceKahlerFormLE_commonUpper_right κ ζ)] at hz
  exact ⟨SourceTestCurvePOrder.trans omega hk.1 hz.2,
    SourceTestCurvePOrder.trans omega hz.1 hk.2⟩

/-- Every actual realized component retains the global P-type of any
specified original geometric component, with all cutoffs unchanged. -/
theorem SourceNAPotential.realizedComponent_component_POrder_equivalent
    (Γ : SourceNAPotential θ) (omega : KahlerBackground n M) (κ : SourceKahlerForm n M) :
    SourceTestCurvePOrder (Γ.realizedComponent omega).val (Γ.component κ).val ∧
      SourceTestCurvePOrder (Γ.component κ).val (Γ.realizedComponent omega).val := by
  have hr := sourceTestCurvePOrder_equivalent_of_functions omega
    (Γ.realizedComponent omega).val
    (Γ.component (sourceKahlerFormOfBackground omega)).val
    (Γ.realizedComponent_max omega)
    (fun r hr hs ↦ Γ.realizedComponent_potential omega r hs hr)
  have hc := Γ.component_POrder_equivalent (sourceKahlerFormOfBackground omega) κ
  exact ⟨SourceTestCurvePOrder.trans omega hr.1 hc.1,
    SourceTestCurvePOrder.trans omega hc.2 hr.2⟩

/-- The readers at ANY two literal Kähler forms have the same original
global P-type; neither form is required to dominate the other. -/
theorem SourceNAPotential.realizedComponent_POrder_equivalent
    (Γ : SourceNAPotential θ) (omega omega' : KahlerBackground n M) :
    SourceTestCurvePOrder (Γ.realizedComponent omega).val (Γ.realizedComponent omega').val ∧
      SourceTestCurvePOrder (Γ.realizedComponent omega').val (Γ.realizedComponent omega).val := by
  let κ := sourceKahlerFormOfBackground omega
  have h := Γ.realizedComponent_component_POrder_equivalent omega κ
  have h' := Γ.realizedComponent_component_POrder_equivalent omega' κ
  exact ⟨SourceTestCurvePOrder.trans omega h.1 h'.2,
    SourceTestCurvePOrder.trans omega h'.1 h.2⟩

/-- Transport by an equality of whole forms changes no genuine curve type. -/
theorem SourcePositiveIModelTestCurve.castBackground_POrder_equivalent
    (omega : KahlerBackground n M) (G : SourcePositiveIModelTestCurve α) (h : α = β) :
    SourceTestCurvePOrder G.val (G.castBackground h).val ∧
      SourceTestCurvePOrder (G.castBackground h).val G.val := by
  cases h
  exact ⟨SourceTestCurvePOrder.refl omega G.val, SourceTestCurvePOrder.refl omega G.val⟩

/-- The literal original sum of positive I-model curves is again an actual
member of the original positive I-model union. -/
def SourcePositiveIModelTestCurve.sum (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ) :
    SourcePositiveIModelTestCurve
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) :=
  ⟨SourceTestCurve.sum omega G.val H.val,
    (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
      (SourceTestCurve.sum_isIModel omega G.val H.val
        ((sourceIModelTestCurvesPositive_iff_slices omega _).mp G.property)
        ((sourceIModelTestCurvesPositive_iff_slices omega _).mp H.property))⟩

/-- The actual NA sum component, in its exact original target background. -/
def SourceNAPotential.sumComponent (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (κ : SourceKahlerForm n M) : SourcePositiveIModelTestCurve
      (sourceNAComponentBackground (θ.add σ) κ) :=
  ((Γ.realizedComponent (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ))).sum
    (sourceKahlerFormRepresentative κ)
    (Δ.realizedComponent (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ)))).castBackground
      (sourceNASumComponentBackground_eq θ σ κ)

/-- All sum components have the sum of the original two common cutoffs. -/
theorem SourceNAPotential.sumComponent_max (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (κ : SourceKahlerForm n M) :
    (Γ.sumComponent Δ κ).val.max = sourceNAPotentialCutoff omega Γ + sourceNAPotentialCutoff omega Δ := by
  simp only [SourceNAPotential.sumComponent, SourcePositiveIModelTestCurve.castBackground_max,
    SourcePositiveIModelTestCurve.sum, SourceTestCurve.sum_max,
    SourceNAPotential.realizedComponent_max_eq_cutoff omega]

/-- These actual component sums have the same P-type for ANY two indices. -/
theorem SourceNAPotential.sumComponent_POrder_equivalent
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (κ ζ : SourceKahlerForm n M) :
    SourceTestCurvePOrder (Γ.sumComponent Δ κ).val (Γ.sumComponent Δ ζ).val ∧
      SourceTestCurvePOrder (Γ.sumComponent Δ ζ).val (Γ.sumComponent Δ κ).val := by
  let omega := sourceKahlerFormRepresentative κ
  let omega' := sourceKahlerFormRepresentative ζ
  let G := Γ.realizedComponent (sourceNAHalfKahlerBackground omega)
  let H := Δ.realizedComponent (sourceNAHalfKahlerBackground omega)
  let G' := Γ.realizedComponent (sourceNAHalfKahlerBackground omega')
  let H' := Δ.realizedComponent (sourceNAHalfKahlerBackground omega')
  have hG := Γ.realizedComponent_POrder_equivalent
    (sourceNAHalfKahlerBackground omega) (sourceNAHalfKahlerBackground omega')
  have hH := Δ.realizedComponent_POrder_equivalent
    (sourceNAHalfKahlerBackground omega) (sourceNAHalfKahlerBackground omega')
  have hs := SourceTestCurve.sum_POrder_equivalent omega omega' G.val H.val G'.val H'.val
    hG.1 hG.2 hH.1 hH.2
  have hk := (G.sum omega H).castBackground_POrder_equivalent omega
    (sourceNASumComponentBackground_eq θ σ κ)
  have hz := (G'.sum omega' H').castBackground_POrder_equivalent omega
    (sourceNASumComponentBackground_eq θ σ ζ)
  exact ⟨SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hk.2 hs.1) hz.1,
    SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hz.2 hs.2) hk.1⟩

/-- Compatibility is PROVED for the literal original I-transition of the
constructed curves, by same-background ordinary-model antisymmetry. -/
theorem SourceNAPotential.sumComponent_compatible
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (κ ζ : SourceKahlerForm n M) (h : sourceKahlerFormLE κ ζ) :
    sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
      (sourceNAComponentBackground_difference (θ.add σ) h) (Γ.sumComponent Δ κ) =
        Γ.sumComponent Δ ζ := by
  let omega := sourceKahlerFormRepresentative ζ
  have ht := sourceIModelTestCurveTransition_POrder_equivalent omega
    (sourceNAComponentBackground_difference (θ.add σ) h) (Γ.sumComponent Δ κ)
  have hs := Γ.sumComponent_POrder_equivalent Δ κ ζ
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omega
    (SourceTestCurvePOrder.trans omega ht.2 hs.1)
    (SourceTestCurvePOrder.trans omega hs.2 ht.1)

/-- The full original NA sum, with genuine compatible I-model components. -/
def SourceNAPotential.sum (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPotential (θ.add σ) where
  component κ := Γ.sumComponent Δ κ
  compatible κ ζ h := Γ.sumComponent_compatible Δ κ ζ h

/-- The original common cutoff of the actual sum is the sum of the cutoffs. -/
theorem sourceNAPotentialCutoff_sum (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    sourceNAPotentialCutoff omega (Γ.sum Δ) =
      sourceNAPotentialCutoff omega Γ + sourceNAPotentialCutoff omega Δ :=
  Γ.sumComponent_max omega Δ (sourceKahlerFormOfBackground omega)

/-- Any constructed component sum has the P-type of the literal sum of
the two readers at ANY independently chosen positive backgrounds. -/
theorem SourceNAPotential.sumComponent_POrder_equivalent_sum
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) (κ : SourceKahlerForm n M)
    (omega omega' : KahlerBackground n M) :
    SourceTestCurvePOrder (Γ.sumComponent Δ κ).val
      (SourceTestCurve.sum omega (Γ.realizedComponent omega).val (Δ.realizedComponent omega').val) ∧
    SourceTestCurvePOrder
      (SourceTestCurve.sum omega (Γ.realizedComponent omega).val (Δ.realizedComponent omega').val)
      (Γ.sumComponent Δ κ).val := by
  let B := sourceKahlerFormRepresentative κ
  let G := Γ.realizedComponent (sourceNAHalfKahlerBackground B)
  let H := Δ.realizedComponent (sourceNAHalfKahlerBackground B)
  have hG := Γ.realizedComponent_POrder_equivalent (sourceNAHalfKahlerBackground B) omega
  have hH := Δ.realizedComponent_POrder_equivalent (sourceNAHalfKahlerBackground B) omega'
  have hs := SourceTestCurve.sum_POrder_equivalent B omega G.val H.val
    (Γ.realizedComponent omega).val (Δ.realizedComponent omega').val hG.1 hG.2 hH.1 hH.2
  have hc := (G.sum B H).castBackground_POrder_equivalent B
    (sourceNASumComponentBackground_eq θ σ κ)
  exact ⟨SourceTestCurvePOrder.trans B hc.2 hs.1,
    SourceTestCurvePOrder.trans B hs.2 hc.1⟩

/-- The FULL original positive splitting prescription, as equality of
actual positive I-model curves after exact whole-form identification. -/
theorem SourceNAPotential.sum_realizedComponent
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (omega omega' : KahlerBackground n M) :
    (((Γ.realizedComponent omega).sum omega (Δ.realizedComponent omega')).castBackground
      (sourceNASumSplitBackground_eq θ σ omega omega')) =
        (Γ.sum Δ).realizedComponent (omega.add omega') := by
  let κ := sourceKahlerFormOfBackground (omega.add omega')
  have hs := Γ.sumComponent_POrder_equivalent_sum Δ κ omega omega'
  have hr := (Γ.sum Δ).realizedComponent_component_POrder_equivalent (omega.add omega') κ
  have hc := ((Γ.realizedComponent omega).sum omega
    (Δ.realizedComponent omega')).castBackground_POrder_equivalent omega
      (sourceNASumSplitBackground_eq θ σ omega omega')
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omega
    (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hc.2 hs.2) hr.2)
    (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hr.1 hs.1) hc.1)

/-- Equality of every literal realized reader identifies the entire
original inverse-system objects, by the existing genuine presentation equivalence. -/
theorem SourceNAPotential.ext_of_realizedComponent {Γ Δ : SourceNAPotential θ}
    (h : ∀ omega : KahlerBackground n M, Γ.realizedComponent omega = Δ.realizedComponent omega) :
    Γ = Δ := by
  apply SourceNAPotential.ext
  intro κ
  let omega := sourceKahlerFormRepresentative κ
  have he := (sourceIModelTestCurvePresentationEquiv omega
    (sourceNAComponentBackground_geometricallyEq (θ := θ) omega)).injective (h omega)
  change Γ.component (sourceKahlerFormOfBackground (sourceKahlerFormRepresentative κ)) =
    Δ.component (sourceKahlerFormOfBackground (sourceKahlerFormRepresentative κ)) at he
  rw [sourceKahlerFormRepresentative_class] at he
  exact he

/-- The book's identical-split prescription at every 2 omega uniquely
determines the entire genuine NA sum; positivity of the NA volume is unnecessary. -/
theorem SourceNAPotential.sum_unique (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (E : SourceNAPotential (θ.add σ))
    (h : ∀ omega : KahlerBackground n M,
      E.realizedComponent (omega.add omega) =
        ((Γ.realizedComponent omega).sum omega (Δ.realizedComponent omega)).castBackground
          (sourceNASumSplitBackground_eq θ σ omega omega)) :
    E = Γ.sum Δ := by
  apply SourceNAPotential.ext_of_realizedComponent
  intro omega
  have he := (h (sourceNAHalfKahlerBackground omega)).trans
    (Γ.sum_realizedComponent Δ (sourceNAHalfKahlerBackground omega) (sourceNAHalfKahlerBackground omega))
  rw [sourceNAHalfKahlerBackground_add_self] at he
  exact he

/-- Every reader of the canonical positive inclusion retains the original
positive I-model curve's global P-type. -/
theorem sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent
    (G : SourcePositiveIModelTestCurve θ) (omega : KahlerBackground n M) :
    SourceTestCurvePOrder ((sourcePositiveTestCurveToNA G).realizedComponent omega).val G.val ∧
      SourceTestCurvePOrder G.val ((sourcePositiveTestCurveToNA G).realizedComponent omega).val := by
  let κ := sourceKahlerFormOfBackground omega
  have hr := (sourcePositiveTestCurveToNA G).realizedComponent_component_POrder_equivalent omega κ
  have ht := sourceIModelTestCurveTransition_POrder_equivalent (sourceKahlerFormRepresentative κ)
    (sourceNAComponentBackground_positive θ κ) G
  exact ⟨SourceTestCurvePOrder.trans omega hr.1 ht.2,
    SourceTestCurvePOrder.trans omega ht.1 hr.2⟩

/-- The canonical positive inclusion intertwines the SAME original
positive test-curve sum and the full constructed NA sum. -/
theorem sourcePositiveTestCurveToNA_sum (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ) :
    (sourcePositiveTestCurveToNA G).sum (sourcePositiveTestCurveToNA H) =
      sourcePositiveTestCurveToNA
        ((G.sum omega H).castBackground (sourceNAOriginalSumBackground_eq θ σ)) := by
  apply SourceNAPotential.ext
  intro κ
  let B := sourceKahlerFormRepresentative κ
  let Γ := sourcePositiveTestCurveToNA G
  let Δ := sourcePositiveTestCurveToNA H
  let S := (G.sum omega H).castBackground (sourceNAOriginalSumBackground_eq θ σ)
  have hs := Γ.sumComponent_POrder_equivalent_sum Δ κ B B
  have hG := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent G B
  have hH := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent H B
  have hp := SourceTestCurve.sum_POrder_equivalent B omega
    (Γ.realizedComponent B).val (Δ.realizedComponent B).val G.val H.val hG.1 hG.2 hH.1 hH.2
  have hc := (G.sum omega H).castBackground_POrder_equivalent B (sourceNAOriginalSumBackground_eq θ σ)
  have ht := sourceIModelTestCurveTransition_POrder_equivalent B
    (sourceNAComponentBackground_positive (θ.add σ) κ) S
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm B
    (SourceTestCurvePOrder.trans B
      (SourceTestCurvePOrder.trans B (SourceTestCurvePOrder.trans B hs.1 hp.1) hc.1) ht.1)
    (SourceTestCurvePOrder.trans B
      (SourceTestCurvePOrder.trans B (SourceTestCurvePOrder.trans B ht.2 hc.2) hp.2) hs.2)

end SGPT.PSH.VariableComplexAtlas
