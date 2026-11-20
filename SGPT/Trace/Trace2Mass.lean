import SGPT.Trace.TraceMass

/-!
# `ex:tracedefinedposmass` in ambient dimension zero

Source: `chapter_trace.tex`, `ex:tracedefinedposmass`: for `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0`,
the mass `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^{dim Y}` (understood as `0` if `Tr^θ_Y(φ)` is not defined)
is `lim_{ε ↘ 0} ∫_Y (θ|_Y + ε ω|_Y + dd^c Tr^{θ+εω}_Y(φ))^{dim Y}`, and if this limit is positive
then `Tr^θ_Y(φ)` is defined and its mass is the limit. Blueprint: `claude-trace2.tex`.

The positive-dimensional case is `SGPT.Trace.tendsto_sourceTraceMass_add_smul_right` and
`SGPT.Trace.hasPositiveSourceTraceAlong_of_tendsto_pos`. Here the remaining case of ambient
dimension `0` (`X` a point, so `Y = X`): every `Tr^{θ'}_Y(φ)` is defined, for every closed form
`θ'`, and its mass is the number of points of the target (`sourceTraceMass_of_dim_zero`), so the
masses are constant in `ε`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.Trace2Mass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition DiagonalMass

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- In ambient dimension `0`, for every quasi-psh `u` and every closed real `(1,1)`-form `θ`,
`Tr^θ_Y(u)` is defined and its mass is the number of points of the target. -/
theorem sourceTraceMass_of_dim_zero (hk : k ≤ n) (hn : n = 0) (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u) :
    HasPositiveSourceTraceAlong omega omegaV hι θ u ∧
      sourceTraceMass omega omegaV hι θ u = (Nat.card V : ℝ≥0∞) := by
  obtain ⟨τ, hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega
    omegaV hu hι (sourceGenericLelongNumber_zero_dimension hn ι u)
  have hdef := hasPositiveSourceTraceAlong_of_dim_zero hk hn θ hT
  refine ⟨hdef, ?_⟩
  have hk0 : k = 0 := by omega
  subst hk0
  unfold sourceTraceMass
  rw [dif_pos hdef]
  exact (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count (M := V)
    (fun _ => ClosedRealOneOneForm.pullback hι θ)
    (fun _ => sourceTraceEnvelope omega omegaV hι θ u hdef)
    (fun _ => (isThetaPshPotential_sourceTraceEnvelope omega omegaV hι θ u hdef).1)).2.1

/-- **Source `ex:tracedefinedposmass`, the formula, in ambient dimension `0`.** For
`u ∈ PSH(X, θ)` and every Kähler form `ω`, the mass of `Tr^θ_Y(u)` is the limit, as `ε ↘ 0`, of
the masses of `Tr^{θ+εω}_Y(u)` (all of them equal the number of points of `Y`). -/
theorem tendsto_sourceTraceMass_add_smul_right_of_dim_zero (hk : k ≤ n) (hn : n = 0)
    (omega₀ omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    Tendsto (fun ε : ℝ => sourceTraceMass omega₀ omegaV hι (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 (sourceTraceMass omega₀ omegaV hι θ u)) := by
  have hq : IsGlobalQuasiPshPotential (n := n) u := hu.quasiPshPotential
  rw [(sourceTraceMass_of_dim_zero hk hn omega₀ omegaV hι θ hq).2]
  refine tendsto_const_nhds.congr fun ε => ?_
  exact ((sourceTraceMass_of_dim_zero hk hn omega₀ omegaV hι (θ + ε • omega.form) hq).2).symm

/-- **Source `ex:tracedefinedposmass`, in ambient dimension `0`.** If the limit `L` of the
masses of `Tr^{θ+εω}_Y(u)` is positive, then `Tr^θ_Y(u)` is defined and its mass is `L`. -/
theorem hasPositiveSourceTraceAlong_of_tendsto_pos_of_dim_zero (hk : k ≤ n) (hn : n = 0)
    (omega₀ omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {L : ℝ≥0∞}
    (hL : Tendsto (fun ε : ℝ => sourceTraceMass omega₀ omegaV hι (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 L)) (_hLpos : 0 < L) :
    HasPositiveSourceTraceAlong omega₀ omegaV hι θ u ∧
      sourceTraceMass omega₀ omegaV hι θ u = L := by
  have hlim := tendsto_sourceTraceMass_add_smul_right_of_dim_zero hk hn omega₀ omega omegaV hι θ hu
  exact ⟨(sourceTraceMass_of_dim_zero hk hn omega₀ omegaV hι θ hu.quasiPshPotential).1,
    tendsto_nhds_unique hlim hL⟩

end SGPT.Trace.Trace2Mass
