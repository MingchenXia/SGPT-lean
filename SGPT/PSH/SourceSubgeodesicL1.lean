import SGPT.PSH.SourceSubgeodesicOperations
import SGPT.Foundations.Analysis.Pending.SubgeodesicL1Compactness
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open ThetaPshL1Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The ENTIRE original theta-PSH class, retaining actual functions and
poles. Its genuine L1 topology is explicitly installed below. -/
def SourceThetaPotentialL1 (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :=
  {u : M → EReal // (ofFixedModel n M).IsThetaPSH θ u}

/-- Complete actual SAME-function original/native theta-PSH equivalence,
without normalized classes or bounded-potential restrictions. -/
def sourceThetaPotentialL1EquivNative
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    SourceThetaPotentialL1 θ ≃ ThetaPshL1 (atlasClosedFormToNative θ).val where
  toFun u := ⟨u.val, (isThetaPSH_iff_nativeThetaPotential θ _).mp u.property⟩
  invFun u := ⟨u.val, (isThetaPSH_iff_nativeThetaPotential θ _).mpr u.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The actual original L1 topology is induced from the GENUINE native
chart-Lp topology, named explicitly. No inherited pointwise topology. -/
@[instance_reducible]
def sourceThetaPotentialL1Topology
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    TopologicalSpace (SourceThetaPotentialL1 θ) :=
  TopologicalSpace.induced (sourceThetaPotentialL1EquivNative θ)
    (ThetaPshL1Topology.instTopologicalSpaceThetaPshL1)

/-- The SAME-function full-class dictionary is a genuine homeomorphism
for the explicitly selected actual original and native L1 topologies. -/
def sourceThetaPotentialL1Homeomorph
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
    letI : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
      ThetaPshL1Topology.instTopologicalSpaceThetaPshL1
    SourceThetaPotentialL1 θ ≃ₜ ThetaPshL1 (atlasClosedFormToNative θ).val := by
  letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
  letI : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    ThetaPshL1Topology.instTopologicalSpaceThetaPshL1
  exact (sourceThetaPotentialL1EquivNative θ).toHomeomorphOfIsInducing (Topology.IsInducing.induced _)

/-- The genuine original topology has its ACTUAL global L1 meaning for
EVERY filter. Actual PSH measurability/integrability/AE finiteness and
actual Kähler-volume chart densities are produced internally. -/
theorem sourceThetaPotentialL1_tendsto_iff_global (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {I : Type*} {F : Filter I}
    (ui : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
    Tendsto ui F (𝓝 v) ↔
      Tendsto (fun i ↦ sourceGlobalL1Distance omega (ui i).val v.val) F (𝓝 0) := by
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
  let : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    ThetaPshL1Topology.instTopologicalSpaceThetaPshL1
  rw [(sourceThetaPotentialL1Homeomorph θ).isInducing.tendsto_nhds_iff,
    ThetaPshL1Topology.tendsto_iff_manifoldL1LocallyTendsto]
  change ManifoldL1LocallyTendsto (n := n) (fun i ↦ (ui i).val) F v.val ↔ _
  apply manifoldL1LocallyTendsto_iff_global_of_eventually_measurable
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
  · exact Eventually.of_forall fun i ↦
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (ui i).property).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  · exact ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property).1.quasiPlurisubharmonic.upperSemicontinuous.measurable

variable {omega : KahlerBackground n M}
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}

/-- The original closed source curve in its ACTUAL original L1 class,
with the SAME potential at every original time and both endpoints. -/
def sourceSubgeodesicClosedL1
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve) :
    Icc (0 : ℝ) 1 → SourceThetaPotentialL1 θ :=
  fun t ↦ ⟨curve t.val, h.thetaPSH_unit t.property⟩

/-- Genuine closed chart-L1 continuity transported to the entire SAME
original curve, in the explicitly selected original L1 topology. -/
theorem continuous_sourceSubgeodesicClosedL1
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve) :
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
    Continuous (sourceSubgeodesicClosedL1 h) := by
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
  let : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    ThetaPshL1Topology.instTopologicalSpaceThetaPshL1
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve (curve 0) (curve 1)).mp
    (sourceSubgeodesicClosedInterval_unit_iff.mp h)
  have heq : sourceSubgeodesicClosedL1 h =
      (sourceThetaPotentialL1Homeomorph θ).symm ∘ SubgeodesicL1Compactness.closedSliceL1 hn := by
    funext t
    apply Subtype.ext
    change curve t.val = closedSubgeodesicSlice curve (curve 0) (curve 1) t.val
    rw [sourceAssignedClosedTrace_self]
  rw [heq]
  exact (sourceThetaPotentialL1Homeomorph θ).symm.continuous.comp
    (SubgeodesicL1Compactness.continuous_closedSliceL1 hn)

/-- The ENTIRE original closed family is genuinely compact in the actual
original L1 topology, as the continuous image of the compact time interval. -/
theorem isCompact_range_sourceSubgeodesicClosedL1
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve) :
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
    IsCompact (range (sourceSubgeodesicClosedL1 h)) := by
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
  exact isCompact_range (continuous_sourceSubgeodesicClosedL1 h)

/-- Whole original relative-compactness consequence: the actual closure
is compact in the SAME genuine original L1 topology. Regularity is
produced by the genuine chart-Lp topology, not inherited pointwise. -/
theorem isCompact_closure_range_sourceSubgeodesicClosedL1
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve) :
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
    IsCompact (closure (range (sourceSubgeodesicClosedL1 h))) := by
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
  let : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    ThetaPshL1Topology.instTopologicalSpaceThetaPshL1
  let : RegularSpace (SourceThetaPotentialL1 θ) :=
    (sourceThetaPotentialL1Homeomorph θ).isInducing.regularSpace
  exact (isCompact_range_sourceSubgeodesicClosedL1 h).closure

variable [ConnectedSpace M]

/-- BOTH literal original spatial-supremum inequalities. Actual compact
endpoint upper bounds and genuine nondegeneracy exclude BOTH extended
endpoints of their global suprema BEFORE any real readback. -/
theorem sourceSubgeodesic_sup_bounds
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (⨆ x, sourceSliceInfimum curve x) ≤ (⨆ x, curve t x) ∧
      (⨆ x, curve t x) ≤ max (⨆ x, curve 0 x) (⨆ x, curve 1 x) := by
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve (curve 0) (curve 1)).mp
    (sourceSubgeodesicClosedInterval_unit_iff.mp h)
  constructor
  · exact iSup_mono fun x ↦ iInf_le (fun s : Ioo (0 : ℝ) 1 ↦ curve s.val x) ⟨t, ht⟩
  · have hf0 := ModelRaySupremum.iSup_ne_top_ne_bot hn.left_endpoint
    have hf1 := ModelRaySupremum.iSup_ne_top_ne_bot hn.right_endpoint
    let A : ℝ := (⨆ x, curve 0 x).toReal
    let B : ℝ := (⨆ x, curve 1 x).toReal
    let C : ℝ := max A B
    have hA : (A : EReal) = ⨆ x, curve 0 x := EReal.coe_toReal hf0.1 hf0.2
    have hB : (B : EReal) = ⨆ x, curve 1 x := EReal.coe_toReal hf1.1 hf1.2
    have hC : (C : EReal) = max (⨆ x, curve 0 x) (⨆ x, curve 1 x) := by
      rw [← hA, ← hB]
      dsimp only [C]
      rcases le_total A B with hAB | hBA
      · rw [max_eq_right hAB, max_eq_right (EReal.coe_le_coe_iff.mpr hAB)]
      · rw [max_eq_left hBA, max_eq_left (EReal.coe_le_coe_iff.mpr hBA)]
    have hu0 (x : M) : curve 0 x ≤ (C : EReal) := by
      calc
        curve 0 x ≤ ⨆ y, curve 0 y := le_iSup (curve 0) x
        _ = (A : EReal) := hA.symm
        _ ≤ (C : EReal) := EReal.coe_le_coe_iff.mpr (le_max_left A B)
    have hu1 (x : M) : curve 1 x ≤ (C : EReal) := by
      calc
        curve 1 x ≤ ⨆ y, curve 1 y := le_iSup (curve 1) x
        _ = (B : EReal) := hB.symm
        _ ≤ (C : EReal) := EReal.coe_le_coe_iff.mpr (le_max_right A B)
    apply le_trans (b := (C : EReal)) ?_ hC.le
    apply iSup_le
    intro x
    calc
      curve t x ≤ eRealChord (curve 0 x) (curve 1 x) t := hn.le_eRealChord ht x
      _ ≤ eRealChord (C : EReal) (C : EReal) t :=
        eRealChord_mono (hu0 x) (hu1 x) ht.1.le ht.2.le
      _ = (C : EReal) := by
        rw [SubgeodesicInfimum.eRealChord_coe_coe]
        congr 1
        ring

/-- WHOLE original cor:convexsubgeod, INCLUDING its relative-compactness
consequence: BOTH spatial bounds, genuine CLOSED original L1 continuity,
and actual compact closure, with the actual L1 topology explicitly bound. -/
theorem source_subgeodesic_l1_whole
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve) :
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
    (∀ t ∈ Ioo (0 : ℝ) 1,
      (⨆ x, sourceSliceInfimum curve x) ≤ (⨆ x, curve t x) ∧
        (⨆ x, curve t x) ≤ max (⨆ x, curve 0 x) (⨆ x, curve 1 x)) ∧
      Continuous (sourceSubgeodesicClosedL1 h) ∧
        IsCompact (closure (range (sourceSubgeodesicClosedL1 h))) := by
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceThetaPotentialL1Topology θ
  exact ⟨fun _ ht ↦ sourceSubgeodesic_sup_bounds h ht,
    continuous_sourceSubgeodesicClosedL1 h, isCompact_closure_range_sourceSubgeodesicClosedL1 h⟩

end SGPT.PSH.VariableComplexAtlas
