import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffSlices
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicIncreasingEndpoints

set_option autoImplicit false

/-! # Genuine cutoff common-tail identification and directed Darvas-energy limits -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffTailLimits

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelNormalizedMixedCutoff SingularCanonicalCutoffStages
  SingularCanonicalCutoffStageOrder SingularCanonicalCutoffSlices

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u : M → EReal}

/-- Actual stage monotonicity constructs the common-tail cofinal indices and proves equality of the genuine raw pointwise stage suprema. -/
theorem iSup_cutoffStage_common_tail_eq (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {s B : ℝ} (hs : 0 ≤ s) (hsB : s ≤ B) :
    (⨆ T : {T : ℝ // s < T}, cutoffStage θ φ u T.val s) =
      ⨆ T : {T : ℝ // B < T}, cutoffStage θ φ u T.val s := by
  apply le_antisymm
  · apply iSup_le
    intro T
    let S : {T : ℝ // B < T} :=
      ⟨max T.val (B + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
    have hT : 0 < T.val := lt_of_le_of_lt hs T.property
    have hTS : T.val ≤ S.val := le_max_left _ _
    have hst : s ∈ Icc (0 : ℝ) T.val := ⟨hs, T.property.le⟩
    exact (cutoffStage_mono_horizon omega hφ hu hup hT hTS hst).trans
      (le_iSup (fun R : {T : ℝ // B < T} => cutoffStage θ φ u R.val s) S)
  · apply iSup_le
    intro T
    exact le_iSup (fun R : {T : ℝ // s < T} => cutoffStage θ φ u R.val s)
      ⟨T.val, lt_of_le_of_lt hsB T.property⟩

/-- The actual defined regularized join slice is exactly the regularized stage supremum on any genuine common terminal tail above its nonnegative time. -/
theorem cutoffSlice_eq_regularized_common_tail (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {s B : ℝ} (hs : 0 ≤ s) (hsB : s ≤ B) :
    cutoffSlice θ φ u s =
      uscRegularization (⨆ T : {T : ℝ // B < T}, cutoffStage θ φ u T.val s) := by
  unfold cutoffSlice
  rw [max_eq_left hs]
  exact congrArg (fun f : M → EReal => uscRegularization f)
    (iSup_cutoffStage_common_tail_eq omega hφ hu hup hs hsB)

/-- True internally produced cutoff endpoint classes, monotonicity and the genuine common-tail identity yield actual Darvas, real-energy and defining extended-energy convergence. -/
theorem tendsto_cutoffStage_common_tail (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {s B : ℝ} (hs : 0 ≤ s) (hsB : s ≤ B) :
    Tendsto (fun C : {C : ℝ // B < C} =>
      relativeD1 θ φ hφ (cutoffStage θ φ u C.val s) (cutoffSlice θ φ u s)) atTop (𝓝 0) ∧
    Tendsto (fun C : {C : ℝ // B < C} =>
      (energy θ φ hφ (cutoffStage θ φ u C.val s)).toReal) atTop
        (𝓝 (energy θ φ hφ (cutoffSlice θ φ u s)).toReal) ∧
    Tendsto (fun C : {C : ℝ // B < C} =>
      energy θ φ hφ (cutoffStage θ φ u C.val s)) atTop
        (𝓝 (energy θ φ hφ (cutoffSlice θ φ u s))) := by
  let I := {C : ℝ // B < C}
  let : Nonempty I := ⟨⟨B + 1, by linarith⟩⟩
  have hC (C : I) : 0 < C.val := lt_of_le_of_lt (hs.trans hsB) C.property
  have hsC (C : I) : s ∈ Icc (0 : ℝ) C.val := ⟨hs, hsB.trans C.property.le⟩
  let stages : I → M → EReal := fun C => cutoffStage θ φ u C.val s
  have hst (C : I) : RelativeFiniteEnergyPreceq θ φ (stages C) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffStage omega hφ hu hup (hC C) (hsC C))
  have hlim : RelativeFiniteEnergyPreceq θ φ (cutoffSlice θ φ u s) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffSlice omega hφ hu hup s)
  have hm : ∀ x, Monotone fun C : I => stages C x := by
    intro x C D hCD
    exact cutoffStage_mono_horizon omega hφ hu hup (hC C) hCD (hsC C) x
  have hreg : uscRegularization (⨆ C : I, stages C) = cutoffSlice θ φ u s :=
    (cutoffSlice_eq_regularized_common_tail omega hφ hu hup hs hsB).symm
  exact ⟨SingularModelDarvasEnergyContinuity.relativeD1_tendsto_zero_of_directed_monotone_regularized
      omega hst hlim hm hreg,
    SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
      omega hst hlim hm hreg,
    SingularModelEnergyIncreasingDirectedNets.energy_tendsto_of_directed_monotone_regularized
      omega hst hlim hm hreg⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffTailLimits
