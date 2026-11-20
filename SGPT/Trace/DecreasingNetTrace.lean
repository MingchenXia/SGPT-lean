import SGPT.Trace.SmoothTarget
import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

/-!
# Traces along decreasing nets exist

Source `prop:tracedeclimit` (`chapter_trace.tex`) speaks of `Tr_Y(φ_j)` for a decreasing
net `φ_j → φ` in `d_S` with `ν(φ, Y) = 0`. This file proves that these traces exist on a
smooth target: `φ ⪯_P φ_j` (the `P`-order passes to `d_S`-limits), hence
`φ ⪯_𝓘 φ_j`, hence `ν(φ_j, Y) ≤ ν(φ, Y) = 0` (Skoda integrability and the
unit-multiplier Lelong bound).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal NNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- If `u ⪯_𝓘 v` (both `θ`-psh) and `ν(u, Y) = 0`, then `ν(v, Y) = 0`. -/
theorem sourceGenericLelongNumber_eq_zero_of_iOrder {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (huv : FirstPass.IEnvelope.IOrderOnManifold (n := n) u v)
    {ι : V → M} (hgen : sourceGenericLelongNumber (n := n) ι u = 0) :
    sourceGenericLelongNumber (n := n) ι v = 0 := by
  by_cases hn : n = 0
  · subst n
    exact sourceGenericLelongNumber_zero_dimension rfl ι v
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hgenN := (nativeGeneric_zero_iff_source hn ι u).mpr hgen
  apply (nativeGeneric_zero_iff_source hn ι v).mp
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  let F : ℝ := (Module.finrank ℝ (ComplexModel n) : ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  let c : ℝ := F / δ + 1
  have hc : 0 < c := by positivity
  have hFc : F / c ≤ δ := by
    rw [div_le_iff₀ hc]
    have : F = δ * (F / δ) := by field_simp
    nlinarith
  -- a point of the target where `ν(u, ·) < 2 / c`
  have hlt : (⨅ y : V, lelongNumber (n := n) u (ι y)) < ENNReal.ofReal (2 / c) := by
    rw [hgenN]
    exact ENNReal.ofReal_pos.mpr (div_pos two_pos hc)
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hlt
  have hmem₀ : (multiplierIdeal (n := n) c u).mem (ι y) (fun _ => (1 : ℂ)) :=
    SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hu.1 hc hy
  have hmem : (multiplierIdeal (n := n) c v).mem (ι y) (fun _ => (1 : ℂ)) :=
    PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold huv hc _ _ hmem₀
  have hbound := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal hnpos hmem
  calc (⨅ y', lelongNumber (n := n) v (ι y'))
      ≤ lelongNumber (n := n) v (ι y) := iInf_le _ y
    _ ≤ ENNReal.ofReal (F / c) := hbound
    _ ≤ 0 + (δ : ℝ≥0∞) := by
      rw [zero_add]
      exact (ENNReal.ofReal_le_ofReal hFc).trans_eq (ENNReal.ofReal_coe_nnreal)

/-- Source `prop:tracedeclimit`, existence of the traces: let `(u_i)_{i ∈ I}` be a
decreasing net in `PSH(X,θ)` (`θ` big) converging in `d_S` to `u` with `ν(u, Y) = 0`.
Then every `u_i` satisfies `ν(u_i, Y) = 0` and has a trace operator along `ι` (for all
auxiliary Kähler forms). -/
theorem exists_trace_of_antitone_net (hk : k ≤ n) (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun i => (ui i).val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgen : sourceGenericLelongNumber (n := n) ι u.val = 0) (i : I) :
    sourceGenericLelongNumber (n := n) ι (ui i).val = 0 ∧
      ∀ (omega₀ : KahlerBackground n M) (omegaV₀ : KahlerBackground k V),
        ∃ τ : V → EReal, IsSourceTraceRepresentativeAlong omega₀ omegaV₀ hι (ui i).val τ := by
  have horder : SourcePOrder (n := n) u.val (ui i).val := by
    refine SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits omega θ hbig atTop
      ui (fun _ => ui i) u (ui i) hlim
      (@tendsto_const_nhds (ThetaPshL1 θ.val) (singularityPseudoMetricSpace omega θ
        hbig).toUniformSpace.toTopologicalSpace I (ui i) atTop) ?_
    filter_upwards [eventually_ge_atTop i] with j hj
    exact sourcePOrder_of_moreSingularOn omega θ θ (ui j).property (ui i).property
      (MoreSingularOn.of_le fun x _ => hanti x hj)
  have hzero := sourceGenericLelongNumber_eq_zero_of_iOrder u.property
    (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder horder) hgen
  refine ⟨hzero, fun omega₀ omegaV₀ => ?_⟩
  exact SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega₀ omegaV₀
    (ui i).property.quasiPshPotential hι hzero

end SGPT.Trace
