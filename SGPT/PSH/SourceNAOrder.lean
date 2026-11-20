import SGPT.PSH.SourceNABackgroundChange
import SGPT.PSH.SourceTestCurveIncreasingSup

/-! # Original cross-background NA order and actual volume monotonicity

The positive I-model hypothesis is used to identify each ordered I-transition
with the ordinary envelope in the original global P-type. Independent
transitions therefore preserve comparison across DIFFERENT backgrounds.
Common upper indices give the exact original some/every-index relation.
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
  {α β γ δ θ σ χ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A genuine positive I-model slice and its actual ordered transition have
the same original global P-type, by the EXISTING ordinary-envelope producer. -/
theorem sourceIModelTestCurveTransition_slice_PEquivalent (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : SourcePositiveIModelTestCurve α) (r : ℝ) (hr : r < G.val.max)
    (hs : r < (sourceIModelTestCurveTransition omega hαβ G).val.max) :
    SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n)
      (G.val.potential ⟨r, hr⟩)
      ((sourceIModelTestCurveTransition omega hαβ G).val.potential ⟨r, hs⟩) := by
  rw [sourceIModelTestCurveTransition_potential omega hαβ G r hr hs]
  have hi : sourceIModel α (G.val.potential ⟨r, hr⟩) :=
    (sourceIModel_iff_native α _).mpr
      (((sourceIModelTestCurvesPositive_iff_slices omega G.val).mp G.property) ⟨r, hr⟩)
  have hPI := (sourceIModel_transition_envelope_and_mass omega hαβ hi
    (G.val.mass_positive omega ⟨r, hr⟩)).1
  have hv := sourceThetaPSH_of_semipositive_difference hαβ hi.1
  have hp := Pending.SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
    omega (atlasClosedFormToNative β)
    ((isThetaPSH_iff_nativeThetaPotential β _).mp hv)
  rw [← sourceSingularityEnvelope_eq_native, hPI] at hp
  exact hp

/-- Both full intrinsic curve comparisons, retaining the actual original cutoffs. -/
theorem sourceIModelTestCurveTransition_POrder_equivalent (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : SourcePositiveIModelTestCurve α) :
    SourceTestCurvePOrder G.val (sourceIModelTestCurveTransition omega hαβ G).val ∧
      SourceTestCurvePOrder (sourceIModelTestCurveTransition omega hαβ G).val G.val := by
  have hm := sourceIModelTestCurveTransition_max omega hαβ G
  refine ⟨⟨hm.ge, ?_⟩, ⟨hm.le, ?_⟩⟩
  · intro r hr
    exact (sourceIModelTestCurveTransition_slice_PEquivalent omega hαβ G r hr
      (hr.trans_le hm.ge)).1
  · intro r hr
    exact (sourceIModelTestCurveTransition_slice_PEquivalent omega hαβ G r
      (hr.trans_le hm.le) hr).2

/-- Independent ordered transitions preserve intrinsic order even when the
two ORIGINAL backgrounds differ. No generic I-equivalence shortcut is used. -/
theorem sourceIModelTestCurveTransition_POrder_iff (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (hγδ : (atlasClosedFormToNative δ - atlasClosedFormToNative γ).val.IsSemipositive)
    (G : SourcePositiveIModelTestCurve α) (H : SourcePositiveIModelTestCurve γ) :
    SourceTestCurvePOrder G.val H.val ↔
      SourceTestCurvePOrder (sourceIModelTestCurveTransition omega hαβ G).val
        (sourceIModelTestCurveTransition omega hγδ H).val := by
  obtain ⟨hG, hG'⟩ := sourceIModelTestCurveTransition_POrder_equivalent omega hαβ G
  obtain ⟨hH, hH'⟩ := sourceIModelTestCurveTransition_POrder_equivalent omega hγδ H
  exact ⟨fun h ↦ SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega hG' h) hH,
    fun h ↦ SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega hG h) hH'⟩

/-- Original compatibility identifies comparison at ordered geometric indices. -/
theorem sourceNAComponentPOrder_iff_of_LE (Γ : SourceNAPotential θ)
    (Δ : SourceNAPotential σ) {ω η : SourceKahlerForm n M} (h : sourceKahlerFormLE ω η) :
    SourceTestCurvePOrder (Γ.component ω).val (Δ.component ω).val ↔
      SourceTestCurvePOrder (Γ.component η).val (Δ.component η).val := by
  have he := sourceIModelTestCurveTransition_POrder_iff (sourceKahlerFormRepresentative η)
    (sourceNAComponentBackground_difference θ h) (sourceNAComponentBackground_difference σ h)
    (Γ.component ω) (Δ.component ω)
  rwa [Γ.compatible ω η h, Δ.compatible ω η h] at he

/-- Comparison is independent of ANY chosen geometric Kähler index, across
different original base forms, by a genuine common UPPER index. -/
theorem sourceNAComponentPOrder_iff (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω η : SourceKahlerForm n M) :
    SourceTestCurvePOrder (Γ.component ω).val (Δ.component ω).val ↔
      SourceTestCurvePOrder (Γ.component η).val (Δ.component η).val :=
  (sourceNAComponentPOrder_iff_of_LE Γ Δ (sourceKahlerFormLE_commonUpper_left ω η)).trans
    (sourceNAComponentPOrder_iff_of_LE Γ Δ (sourceKahlerFormLE_commonUpper_right ω η)).symm

/-- The literal original existential order, allowing DIFFERENT base forms. -/
def SourceNAPOrder (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) : Prop :=
  ∃ ω : SourceKahlerForm n M, SourceTestCurvePOrder (Γ.component ω).val (Δ.component ω).val

/-- Any specified actual component reads precisely the original full NA order. -/
theorem sourceNAPOrder_iff_component (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω : SourceKahlerForm n M) :
    SourceNAPOrder Γ Δ ↔ SourceTestCurvePOrder (Γ.component ω).val (Δ.component ω).val := by
  constructor
  · rintro ⟨η, hη⟩
    exact (sourceNAComponentPOrder_iff Γ Δ η ω).mp hη
  · exact fun h ↦ ⟨ω, h⟩

/-- The original some/every equivalence retains the standing actual Kähler witness. -/
theorem sourceNAPOrder_iff_every_component (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder Γ Δ ↔ ∀ ω : SourceKahlerForm n M,
      SourceTestCurvePOrder (Γ.component ω).val (Δ.component ω).val := by
  constructor
  · exact fun h ω ↦ (sourceNAPOrder_iff_component Γ Δ ω).mp h
  · exact fun h ↦ ⟨sourceKahlerFormOfBackground omega, h _⟩

/-- Reflexivity uses an actual index, rather than an empty-index assumption. -/
theorem SourceNAPOrder.refl (omega : KahlerBackground n M) (Γ : SourceNAPotential θ) :
    SourceNAPOrder Γ Γ :=
  ⟨sourceKahlerFormOfBackground omega, SourceTestCurvePOrder.refl omega _⟩

/-- Actual intrinsic transitivity also permits three different original backgrounds. -/
theorem SourceNAPOrder.trans {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    {Ξ : SourceNAPotential χ} (h : SourceNAPOrder Γ Δ) (k : SourceNAPOrder Δ Ξ) :
    SourceNAPOrder Γ Ξ := by
  obtain ⟨ω, hω⟩ := h
  exact ⟨ω, SourceTestCurvePOrder.trans (sourceKahlerFormRepresentative ω) hω
    ((sourceNAPOrder_iff_component Δ Ξ ω).mp k)⟩

/-- Mutual comparison identifies the full original system in a fixed background. -/
theorem SourceNAPOrder.antisymm {Γ Δ : SourceNAPotential θ}
    (h : SourceNAPOrder Γ Δ) (k : SourceNAPOrder Δ Γ) : Γ = Δ := by
  apply SourceNAPotential.ext
  intro ω
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm (sourceKahlerFormRepresentative ω)
    ((sourceNAPOrder_iff_component Γ Δ ω).mp h)
    ((sourceNAPOrder_iff_component Δ Γ ω).mp k)

/-- A genuine partial order with the original relation and original Kähler geometry. -/
@[instance_reducible]
def sourceNAPartialOrder (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) : PartialOrder (SourceNAPotential θ) where
  le := SourceNAPOrder
  le_refl := SourceNAPOrder.refl omega
  le_trans := fun _ _ _ ↦ SourceNAPOrder.trans
  le_antisymm := fun _ _ ↦ SourceNAPOrder.antisymm

/-- Original cross-background comparison orders the actual common real cutoffs. -/
theorem sourceNAPotentialCutoff_mono (omega : KahlerBackground n M)
    {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ} (h : SourceNAPOrder Γ Δ) :
    sourceNAPotentialCutoff omega Γ ≤ sourceNAPotentialCutoff omega Δ :=
  ((sourceNAPOrder_iff_component Γ Δ (sourceKahlerFormOfBackground omega)).mp h).cutoff_le

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal cutoff and function readers transport the entire intrinsic order.
This auxiliary equality dictionary assumes no analytic order conclusion. -/
theorem sourceTestCurvePOrder_congr_functions
    (G : SourceTestCurve α) (G' : SourceTestCurve β)
    (H : SourceTestCurve γ) (H' : SourceTestCurve δ)
    (hG : G.max = G'.max) (hH : H.max = H'.max)
    (eG : ∀ (r : ℝ) (hr : r < G.max) (hs : r < G'.max),
      G.potential ⟨r, hr⟩ = G'.potential ⟨r, hs⟩)
    (eH : ∀ (r : ℝ) (hr : r < H.max) (hs : r < H'.max),
      H.potential ⟨r, hr⟩ = H'.potential ⟨r, hs⟩) :
    SourceTestCurvePOrder G H ↔ SourceTestCurvePOrder G' H' := by
  constructor
  · intro h
    have hc : G'.max ≤ H'.max := by simpa only [← hG, ← hH] using h.cutoff_le
    refine ⟨hc, ?_⟩
    intro r hr'
    have hr : r < G.max := by rwa [hG]
    rw [← eG r hr hr', ← eH r (hr.trans_le h.cutoff_le) (hr'.trans_le hc)]
    exact h.slice_le r hr
  · intro h
    have hc : G.max ≤ H.max := by simpa only [hG, hH] using h.cutoff_le
    refine ⟨hc, ?_⟩
    intro r hr
    have hr' : r < G'.max := by rwa [← hG]
    rw [eG r hr hr', eH r (hr.trans_le hc) (hr'.trans_le h.cutoff_le)]
    exact h.slice_le r hr'

/-- Realizing components in literal smooth backgrounds changes no intrinsic order. -/
theorem sourceNARealizedComponentPOrder_iff (Γ Δ : SourceNAPotential θ)
    (omega : KahlerBackground n M) :
    SourceTestCurvePOrder (Γ.realizedComponent omega).val (Δ.realizedComponent omega).val ↔
      SourceTestCurvePOrder (Γ.component (sourceKahlerFormOfBackground omega)).val
        (Δ.component (sourceKahlerFormOfBackground omega)).val :=
  sourceTestCurvePOrder_congr_functions _ _ _ _
    (Γ.realizedComponent_max omega) (Δ.realizedComponent_max omega)
    (fun r hr hs ↦ Γ.realizedComponent_potential omega r hs hr)
    (fun r hr hs ↦ Δ.realizedComponent_potential omega r hs hr)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Entire background equality preserves intrinsic comparison of actual curves. -/
theorem sourcePositiveIModelTestCurve_castBackground_POrder_iff
    (G H : SourcePositiveIModelTestCurve α) (h : α = β) :
    SourceTestCurvePOrder (G.castBackground h).val (H.castBackground h).val ↔
      SourceTestCurvePOrder G.val H.val := by
  cases h
  rfl

/-- Whole original order/projection proposition, for FULL NA-to-NA change
by every semipositive form, including the zero form. -/
theorem sourceNAPOrder_backgroundChange_iff (omega : KahlerBackground n M)
    (Γ Δ : SourceNAPotential θ) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    SourceNAPOrder Γ Δ ↔ SourceNAPOrder (Γ.backgroundChange η hη) (Δ.backgroundChange η hη) := by
  let ω := sourceKahlerFormOfBackground omega
  let B := sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative ω)
  calc
    SourceNAPOrder Γ Δ ↔
        SourceTestCurvePOrder (Γ.realizedComponent B).val (Δ.realizedComponent B).val :=
      (sourceNAPOrder_iff_component Γ Δ (sourceKahlerFormOfBackground B)).trans
        (sourceNARealizedComponentPOrder_iff Γ Δ B).symm
    _ ↔ SourceTestCurvePOrder (Γ.reindexedComponent η hη ω).val
        (Δ.reindexedComponent η hη ω).val :=
      (sourcePositiveIModelTestCurve_castBackground_POrder_iff _ _
        (sourceNAAugmentedComponentBackground_eq θ η hη ω)).symm
    _ ↔ SourceNAPOrder (Γ.backgroundChange η hη) (Δ.backgroundChange η hη) :=
      (sourceNAPOrder_iff_component (Γ.backgroundChange η hη) (Δ.backgroundChange η hη) ω).symm

/-- The original positive-curve inclusion retains its intrinsic order,
including comparisons between DIFFERENT original backgrounds. -/
theorem sourcePositiveTestCurveToNA_POrder_iff (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) (H : SourcePositiveIModelTestCurve σ) :
    SourceNAPOrder (sourcePositiveTestCurveToNA G) (sourcePositiveTestCurveToNA H) ↔
      SourceTestCurvePOrder G.val H.val := by
  let ω := sourceKahlerFormOfBackground omega
  rw [sourceNAPOrder_iff_component _ _ ω]
  exact (sourceIModelTestCurveTransition_POrder_iff (sourceKahlerFormRepresentative ω)
    (sourceNAComponentBackground_positive θ ω) (sourceNAComponentBackground_positive σ ω) G H).symm

/-- The existing WHOLE-extension and USC-limit theorems retain the actual limits. -/
theorem SourceTestCurvePOrder.limit_le (omega : KahlerBackground n M)
    {G H : SourceTestCurve θ} (h : SourceTestCurvePOrder G H) :
    sourceTestCurveLimit G.toSourceTestCurvePredata ≤
      sourceTestCurveLimit H.toSourceTestCurvePredata :=
  sourceTestCurveLimit_mono_of_extension G H ((sourceTestCurvePOrder_iff_extension omega G H).mp h)

/-- Actual non-pluripolar masses of the same original component limits are monotone. -/
theorem sourceNAComponentMass_mono_of_POrder (omega : KahlerBackground n M)
    {Γ Δ : SourceNAPotential θ} (h : SourceNAPOrder Γ Δ) (ω : SourceKahlerForm n M) :
    sourceNAComponentMass Γ ω ≤ sourceNAComponentMass Δ ω := by
  have hlim := SourceTestCurvePOrder.limit_le omega
    ((sourceNAPOrder_iff_component Γ Δ ω).mp h)
  exact sourcePotentialNonPluripolarMass_mono omega
    (Γ.component ω).val.limit_thetaPSH (Δ.component ω).val.limit_thetaPSH
    (MoreSingularOn.of_le (fun x _ ↦ hlim x))

/-- Whole original NA-volume monotonicity, preserving possible zero infima. -/
theorem sourceNAVolume_mono (omega : KahlerBackground n M)
    {Γ Δ : SourceNAPotential θ} (h : SourceNAPOrder Γ Δ) :
    sourceNAVolume Γ ≤ sourceNAVolume Δ :=
  iInf_mono (fun ω ↦ sourceNAComponentMass_mono_of_POrder omega h ω)

end SGPT.PSH.VariableComplexAtlas
