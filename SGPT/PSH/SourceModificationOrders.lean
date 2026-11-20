import SGPT.PSH.GlobalPComparison
import SGPT.PSH.SourceIEnvelope
import SGPT.PSH.NativeQPSHPullback
import SGPT.Okounkov.ModificationNativeConvergence
import SGPT.Okounkov.NativeFlagBaseGeometry
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders
import SGPT.Foundations.Analysis.Pending.GenuineModificationIdealOrderInvariance
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

set_option autoImplicit false

/-! # Both original global orders under a general proper modification

The actual general native pullback and all-level multiplier invariance
theorems retain the original Kahler source Y, every dimension, all genuine
QPSH inputs and their literal extended pullbacks. No blowup factorization
or positive original mass is an assumption.
-/

open Set Filter
open scoped Topology

namespace SGPT.PSH.ModificationOrders

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
  SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  VariableComplexAtlas GlobalPComparison

noncomputable section

private theorem native_of_source {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

private theorem native_const_iff {n : ℕ} {M : Type*}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (p q : ThetaPshL1 θ.val) :
    Tendsto (fun _ : ℕ => p) atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace q) ↔
      sourcePEquivalent (n := n) p.val q.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  change Tendsto (fun _ : ℕ => p) atTop (𝓝 q) ↔ _
  rw [tendsto_iff_dist_tendsto_zero]
  constructor
  · intro h
    have hz : dist p q = 0 := tendsto_nhds_unique tendsto_const_nhds h
    obtain ⟨m, _, _, _, hm⟩ :=
      exists_tendsto_singularityDistance omega θ hbig p.property q.property
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hm, EReal.toReal_coe] at hz
    have hD : singularityDistance omega θ hbig p.val q.val = 0 := by
      simpa only [hz, EReal.coe_zero] using hm
    exact (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      p.property q.property).mp hD
  · intro h
    have hD := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      p.property q.property).mpr h
    have hd : dist p q = 0 := by
      rw [dist_eq_singularityDistance_toReal omega θ hbig, hD, EReal.toReal_zero]
    simpa only [hd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

universe u

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Genuine general modification convergence preserves and reflects the actual
GLOBAL P-equivalence of arbitrary genuine source QPSH inputs, in every dimension. -/
theorem sourcePEquivalent_modification_pullback_iff {π : Y → X}
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    sourcePEquivalent (n := n) u v ↔ sourcePEquivalent (n := n) (u ∘ π) (v ∘ π) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  obtain ⟨C, hC, huC, hvC, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omegaX
      (native_of_source hu) (native_of_source hv)
  let θ : ClosedRealOneOneForm n X := C • omegaX.form
  have hθ : IsBigClass (RealBottChern.ofRepresentative θ) :=
    PluripolarCapacityDichotomy.isBigClass_kahler (KahlerBackground.smul hC omegaX)
  let β := ClosedRealOneOneForm.pullback hπ.1 θ
  have hβ : IsBigClass (RealBottChern.ofRepresentative β) :=
    SGPT.Okounkov.isBigClass_modification_pullback hπ omegaX omegaY θ hθ
  let U : ThetaPshL1 θ.val := ⟨u, huC⟩
  let V : ThetaPshL1 θ.val := ⟨v, hvC⟩
  let Up : ThetaPshL1 β.val :=
    ⟨u ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ θ huC⟩
  let Vp : ThetaPshL1 β.val :=
    ⟨v ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ θ hvC⟩
  have ht := SGPT.Okounkov.native_tendsto_modification_pullback_iff hπ omegaX omegaY θ hθ
    (atTop : Filter ℕ) (fun _ => U) V
  exact (native_const_iff omegaX θ hθ U V).symm.trans
    (ht.symm.trans (native_const_iff omegaY β hβ Up Vp))

/-- The original GLOBAL P-order is preserved and reflected by every genuine
proper bimeromorphic analytic modification from the given Kahler manifold Y. -/
theorem sourcePOrder_modification_pullback_iff {π : Y → X}
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    sourcePOrder (n := n) u v ↔ sourcePOrder (n := n) (u ∘ π) (v ∘ π) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  have hU := hu.max_compactKahler omegaX hv
  have hX := GlobalQuasiPshMaximumOrders.sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    omegaX (native_of_source hu) (native_of_source hv)
  have hY := GlobalQuasiPshMaximumOrders.sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    omegaY (native_of_source (hu.comp_native_analyticModification hπ))
      (native_of_source (hv.comp_native_analyticModification hπ))
  have he := sourcePEquivalent_modification_pullback_iff omegaX omegaY hπ hU hv
  exact hX.trans (he.trans hY.symm)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] in
/-- Actual all-level, all-chart source multiplier order is preserved and
reflected by a general modification, with genuine source domains manufactured. -/
theorem sourceIOrder_modification_pullback_iff {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIOrder (ofFixedModel n X) u v ↔
      sourceIOrder (ofFixedModel n Y) (u ∘ π) (v ∘ π) := by
  have hX := sourceIOrder_iff_native hu hv
  have hY := sourceIOrder_iff_native (hu.comp_native_analyticModification hπ)
    (hv.comp_native_analyticModification hπ)
  exact hX.trans ((GenuineModificationIdealOrderInvariance.iOrder_iff_comp hπ
    (native_of_source hu).1 (native_of_source hv)).trans hY.symm)

/-- The WHOLE original `lma:Ipartorderinv`: both actual GLOBAL P and source
all-level I order are invariant under a genuine proper bimeromorphic morphism
from the given Kahler manifold Y. Upstairs compactness and connectedness are outputs. -/
theorem sourceGlobalOrders_modification_iff {π : Y → X}
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    (sourcePOrder (n := n) u v ↔ sourcePOrder (n := n) (u ∘ π) (v ∘ π)) ∧
      (sourceIOrder (ofFixedModel n X) u v ↔
        sourceIOrder (ofFixedModel n Y) (u ∘ π) (v ∘ π)) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  exact ⟨sourcePOrder_modification_pullback_iff omegaX omegaY hπ hu hv,
    sourceIOrder_modification_pullback_iff hπ hu hv⟩

end
end SGPT.PSH.ModificationOrders
