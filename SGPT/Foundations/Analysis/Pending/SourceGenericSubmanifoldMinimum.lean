import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import SGPT.Foundations.Analysis.Pending.SourceGenericPrimeIdealOrder
import SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition

set_option autoImplicit false

/-! # Attainment of the ambient source generic number on the original submanifold

The natural closed connected submanifold internally supplies its irreducible
analytic carrier. The subtype complex structure is used for irreducibility;
all point Lelong readers remain on the original ambient manifold, including
the source convention in dimension zero. No minimum witness is an input.
-/

open Set
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum

open FirstPass FirstPass.BlowupSequences FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation SquaredLogLelongSourceNormalization

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {W : Set M}

/-- The subtype atlas proves irreducibility of the same ambient carrier. -/
theorem isComplexAnalyticallyIrreducible_of_submanifold
    (hW : IsClosedConnectedSubmanifold n W k) :
    IsComplexAnalyticallyIrreducible (n := n) W := by
  classical
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W :=
    SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have hinc : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : W → M) :=
    SubmanifoldChartedSpace.contMDiff_val hk hW.2.2
  have hWa : IsComplexAnalyticSubset (n := n) W :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨hW.1, fun x hx => ⟨k, hW.2.2 x hx⟩⟩
  refine ⟨hWa, hW.2.1.nonempty, ?_⟩
  intro B C hB hC hBW hCW hcover
  have hBp : IsComplexAnalyticSubset (n := k)
      ((Subtype.val : W → M) ⁻¹' B) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hinc hB
  have hCp : IsComplexAnalyticSubset (n := k)
      ((Subtype.val : W → M) ⁻¹' C) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hinc hC
  have hpcover : (univ : Set W) =
      (Subtype.val : W → M) ⁻¹' B ∪ (Subtype.val : W → M) ⁻¹' C := by
    apply Set.Subset.antisymm
    · intro y _
      have hy : (y : M) ∈ B ∪ C :=
        (Set.ext_iff.mp hcover (y : M)).mp y.property
      exact hy
    · intro y _
      exact mem_univ y
  have hirr : IsComplexAnalyticallyIrreducible (n := k) (univ : Set W) :=
    AnalyticIrreducibleComponents.isComplexAnalyticallyIrreducible_univ
  rcases hirr.eq_left_or_eq_right hBp hCp (subset_univ _) (subset_univ _) hpcover
      with hBfull | hCfull
  · left
    apply Set.Subset.antisymm ?_ hBW
    intro x hx
    have hp : (⟨x, hx⟩ : W) ∈ (Subtype.val : W → M) ⁻¹' B := by
      rw [← hBfull]
      exact mem_univ _
    exact hp
  · right
    apply Set.Subset.antisymm ?_ hCW
    intro x hx
    have hp : (⟨x, hx⟩ : W) ∈ (Subtype.val : W → M) ⁻¹' C := by
      rw [← hCfull]
      exact mem_univ _
    exact hp

/-- The original connected submanifold supplies every carrier field internally. -/
theorem exists_subvariety_carrier_eq_of_submanifold
    (hW : IsClosedConnectedSubmanifold n W k) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety n M, V.carrier = W ∧ V.dim = k := by
  obtain ⟨x, hx⟩ := hW.2.1.nonempty
  let V : ClosedIrreducibleAnalyticSubvariety n M :=
    { carrier := W
      isClosed_carrier := hW.1
      irreducible_carrier := isComplexAnalyticallyIrreducible_of_submanifold hW
      dim := k
      dim_le := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
      regularLocus_nonempty := ⟨x, hW.2.2 x hx⟩ }
  exact ⟨V, rfl, rfl⟩

omit [IsComplexManifold n M] in
/-- Reindexing uses the whole carrier, including an empty carrier. -/
theorem sourceGeneric_subtype_eq_iInf (u : M → EReal) :
    SourceTraceRepresentativeDefinition.sourceGenericLelongNumber
        (n := n) (Subtype.val : W → M) u =
      ⨅ x ∈ W, squaredLogLelongNumber (n := n) u x := by
  change (⨅ y : W, squaredLogLelongNumber (n := n) u (y : M)) = _
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => ?_
    exact iInf_le_of_le (⟨x, hx⟩ : W) le_rfl
  · refine le_iInf fun y => ?_
    exact iInf₂_le_of_le (y : M) y.property le_rfl

/-- Attainment follows from the natural domain, with no prescribed minimum. -/
theorem exists_sourceGeneric_subtype_minimum
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hW : IsClosedConnectedSubmanifold n W k) :
    ∃ y : W, squaredLogLelongNumber (n := n) u (y : M) =
      SourceTraceRepresentativeDefinition.sourceGenericLelongNumber
        (n := n) (Subtype.val : W → M) u := by
  obtain ⟨V, hVW, _⟩ := exists_subvariety_carrier_eq_of_submanifold hW
  have hVU : (V.carrier ∩ (univ : Set M)).Nonempty := by
    simpa only [hVW, inter_univ] using hW.2.1.nonempty
  obtain ⟨x, hx, hxmin⟩ :=
    SourceGenericPrimeIdealOrder.exists_source_minimum_on_open_piece
      hu V isOpen_univ hVU
  have hxW : x ∈ W := by simpa only [hVW] using hx.1
  refine ⟨⟨x, hxW⟩, ?_⟩
  rw [sourceGeneric_subtype_eq_iInf]
  simpa only [hVW] using hxmin

/-- The genuine QEA target is the original ambient quasi-PSH potential. -/
theorem exists_sourceGeneric_subtype_minimum_of_QEA
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (hqea : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hW : IsClosedConnectedSubmanifold n W k) :
    ∃ y : W, squaredLogLelongNumber (n := n) u (y : M) =
      SourceTraceRepresentativeDefinition.sourceGenericLelongNumber
        (n := n) (Subtype.val : W → M) u := by
  have hu : ManifoldQuasiPlurisubharmonic (n := n) u :=
    hqea.target.1.quasiPlurisubharmonic
  exact exists_sourceGeneric_subtype_minimum hu hW

/-- A generic zero on the original domain is an actual point zero. -/
theorem exists_sourceGeneric_subtype_zero_of_QEA
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (hqea : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hW : IsClosedConnectedSubmanifold n W k)
    (hzero : SourceTraceRepresentativeDefinition.sourceGenericLelongNumber
      (n := n) (Subtype.val : W → M) u = 0) :
    ∃ y : W, squaredLogLelongNumber (n := n) u (y : M) = 0 := by
  obtain ⟨y, hy⟩ := exists_sourceGeneric_subtype_minimum_of_QEA omega θ hqea hW
  exact ⟨y, hy.trans hzero⟩

end

end SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
