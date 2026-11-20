import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-!
# Closed-interval L¹ continuity and compactness of subgeodesics

Xia's SGPT Corollary 4.1.2 (PDF page 0150) states that the closed family of
subgeodesic slices is continuous and relatively compact in L¹. We join the
proved interior chart-local continuity to the two defining endpoint limits,
then extract a convergent time subsequence in any compact subset of [0, 1].
The limit is an actual slice of the same family. On a compact complex manifold,
chartwise convergence is also global L¹ convergence for every smooth positive
volume, with no boundedness assumption on the potentials.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicL1Compactness

open FirstPass ChartwiseGlobalL1 ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}

/-- Every closed slice, including the prescribed endpoints, is theta-PSH. -/
theorem isThetaPshPotential_closedSlice (h : IsSubgeodesicFrom θ curve u₀ u₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsThetaPshPotential θ (closedSubgeodesicSlice curve u₀ u₁ t) := by
  by_cases ht0 : t = 0
  · subst t
    simpa using h.left_endpoint
  by_cases ht1 : t = 1
  · subst t
    simpa using h.right_endpoint
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  rw [closedSubgeodesicSlice_eq_curve htI]
  exact h.interior.thetaPshPotential htI

/-- The prescribed endpoint slices make a subgeodesic continuous on the whole
closed time interval in the genuine chart-local L¹ topology. -/
theorem manifoldL1LocallyContinuousWithinAt_closedSlice
    (h : IsSubgeodesicFrom θ curve u₀ u₁) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    ManifoldL1LocallyTendsto (n := n) (closedSubgeodesicSlice curve u₀ u₁)
      (𝓝[Icc (0 : ℝ) 1] c) (closedSubgeodesicSlice curve u₀ u₁ c) := by
  by_cases hc0 : c = 0
  · subst c
    have hright : ManifoldL1LocallyTendsto (n := n)
        (closedSubgeodesicSlice curve u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ := by
      apply h.tendsto_left.congr'
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds] with t ht0 ht1
      exact (closedSubgeodesicSlice_eq_curve ⟨ht0, ht1⟩).symm
    have hset : Icc (0 : ℝ) 1 = insert 0 (Ioc 0 1) := by
      ext t
      simp only [mem_Icc, mem_insert_iff, mem_Ioc]
      constructor
      · rintro ⟨ht0, ht1⟩
        rcases eq_or_lt_of_le ht0 with ht0 | ht0
        · exact Or.inl ht0.symm
        · exact Or.inr ⟨ht0, ht1⟩
      · rintro (rfl | ⟨ht0, ht1⟩)
        · norm_num
        · exact ⟨ht0.le, ht1⟩
    intro e K hK hKe
    rw [closedSubgeodesicSlice_zero, hset, nhdsWithin_insert, tendsto_sup]
    constructor
    · simpa only [closedSubgeodesicSlice_zero,
        chartL1EDistance_self_of_ne_top u₀
          h.left_endpoint.1.quasiPlurisubharmonic.ne_top e K] using tendsto_pure_nhds
        (fun t => chartL1EDistance (closedSubgeodesicSlice curve u₀ u₁ t) u₀ e K) 0
    · exact (hright e K hK hKe).mono_left
        (nhdsWithin_mono _ fun t ht => ht.1)
  by_cases hc1 : c = 1
  · subst c
    have hleft : ManifoldL1LocallyTendsto (n := n)
        (closedSubgeodesicSlice curve u₀ u₁) (𝓝[<] (1 : ℝ)) u₁ := by
      apply h.tendsto_right.congr'
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds] with t ht1 ht0
      exact (closedSubgeodesicSlice_eq_curve ⟨ht0, ht1⟩).symm
    have hset : Icc (0 : ℝ) 1 = insert 1 (Ico 0 1) := by
      ext t
      simp only [mem_Icc, mem_insert_iff, mem_Ico]
      constructor
      · rintro ⟨ht0, ht1⟩
        rcases eq_or_lt_of_le ht1 with ht1 | ht1
        · exact Or.inl ht1
        · exact Or.inr ⟨ht0, ht1⟩
      · rintro (rfl | ⟨ht0, ht1⟩)
        · norm_num
        · exact ⟨ht0, ht1.le⟩
    intro e K hK hKe
    rw [closedSubgeodesicSlice_one, hset, nhdsWithin_insert, tendsto_sup]
    constructor
    · simpa only [closedSubgeodesicSlice_one,
        chartL1EDistance_self_of_ne_top u₁
          h.right_endpoint.1.quasiPlurisubharmonic.ne_top e K] using tendsto_pure_nhds
        (fun t => chartL1EDistance (closedSubgeodesicSlice curve u₀ u₁ t) u₁ e K) 1
    · exact (hleft e K hK hKe).mono_left
        (nhdsWithin_mono _ fun t ht => ht.2)
  have hcI : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1⟩
  rw [closedSubgeodesicSlice_eq_curve hcI]
  apply (h.manifoldL1LocallyContinuousAt hcI).mono_left nhdsWithin_le_nhds |>.congr'
  have hnear : ∀ᶠ t in 𝓝 c, t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hcI.1 hcI.2
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
  exact (closedSubgeodesicSlice_eq_curve ht).symm

/-- Any convergent time family within the closed interval gives chart-local
L¹ convergence of its closed slices, including at endpoint limit times. -/
theorem manifoldL1LocallyTendsto_closedSlice
    (h : IsSubgeodesicFrom θ curve u₀ u₁) {α : Type*} {l : Filter α}
    {s : α → ℝ} {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hs : ∀ᶠ i in l, s i ∈ Icc (0 : ℝ) 1) (hsc : Tendsto s l (𝓝 c)) :
    ManifoldL1LocallyTendsto (n := n)
      (fun i => closedSubgeodesicSlice curve u₀ u₁ (s i)) l
      (closedSubgeodesicSlice curve u₀ u₁ c) :=
  (manifoldL1LocallyContinuousWithinAt_closedSlice h hc).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hsc, hs⟩)

/-- Every sequence of slices in a compact time set has a strictly increasing
subsequence converging in chart-local L¹ to a slice in the same set. -/
theorem exists_subseq_manifoldL1LocallyTendsto_closedSlice
    (h : IsSubgeodesicFrom θ curve u₀ u₁) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Icc (0 : ℝ) 1) {s : ℕ → ℝ} (hs : ∀ j, s j ∈ K) :
    ∃ c ∈ K, ∃ a : ℕ → ℕ, StrictMono a ∧
      Tendsto (s ∘ a) atTop (𝓝 c) ∧
      ManifoldL1LocallyTendsto (n := n)
        (fun j => closedSubgeodesicSlice curve u₀ u₁ (s (a j))) atTop
        (closedSubgeodesicSlice curve u₀ u₁ c) := by
  obtain ⟨c, hc, a, ha, hsc⟩ := hK.tendsto_subseq hs
  exact ⟨c, hc, a, ha, hsc, manifoldL1LocallyTendsto_closedSlice h (hKI hc)
    (Eventually.of_forall fun j => hKI (hs (a j))) hsc⟩

/-- The closed subgeodesic as a map into the genuine chart-local L¹ space of
theta-PSH potentials. The domain is exactly the closed time interval. -/
def closedSliceL1 (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    Icc (0 : ℝ) 1 → ThetaPshL1 θ :=
  fun t => ⟨closedSubgeodesicSlice curve u₀ u₁ t,
    isThetaPshPotential_closedSlice h t.2⟩

/-- The closed subgeodesic is a continuous map to the genuine L¹ topology. -/
theorem continuous_closedSliceL1 (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    Continuous (closedSliceL1 h) := by
  rw [continuous_iff_continuousAt]
  intro c
  apply tendsto_iff_manifoldL1LocallyTendsto.mpr
  exact manifoldL1LocallyTendsto_closedSlice h c.2
    (Eventually.of_forall fun t : Icc (0 : ℝ) 1 => t.2)
    continuous_subtype_val.continuousAt

/-- The slices over any compact time set form a compact set of theta-PSH
potentials in the actual chart-local L¹ topology. -/
theorem isCompact_closedSliceL1_image (h : IsSubgeodesicFrom θ curve u₀ u₁)
    {K : Set ℝ} (hK : IsCompact K) :
    IsCompact (closedSliceL1 h '' (Subtype.val ⁻¹' K)) := by
  have htime : IsCompact ((Subtype.val : Icc (0 : ℝ) 1 → ℝ) ⁻¹' K) :=
    (hK.isClosed.preimage continuous_subtype_val).isCompact
  exact htime.image (continuous_closedSliceL1 h)

/-- Relative compactness of subgeodesic slices: their closure in the genuine
L¹ topology is compact, with no nonempty or boundedness hypothesis. -/
theorem isCompact_closure_closedSliceL1_image (h : IsSubgeodesicFrom θ curve u₀ u₁)
    {K : Set ℝ} (hK : IsCompact K) :
    IsCompact (closure (closedSliceL1 h '' (Subtype.val ⁻¹' K))) :=
  (isCompact_closedSliceL1_image h hK).closure

/-- The entire closed subgeodesic is a compact L¹ family. -/
theorem isCompact_range_closedSliceL1 (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    IsCompact (range (closedSliceL1 h)) :=
  isCompact_range (continuous_closedSliceL1 h)

/-- The entire closed subgeodesic is relatively compact in L¹. -/
theorem isCompact_closure_range_closedSliceL1 (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    IsCompact (closure (range (closedSliceL1 h))) :=
  (isCompact_range_closedSliceL1 h).closure

section Global

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Closed slices converge in the global L¹ distance for every smooth positive
volume whenever their times converge within the closed time interval. -/
theorem tendsto_globalL1EDistance_closedSlice
    (h : IsSubgeodesicFrom θ curve u₀ u₁) {μ : Measure M}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {α : Type*} {l : Filter α}
    {s : α → ℝ} {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) (hsc : Tendsto s l (𝓝 c)) :
    Tendsto (fun i => globalL1EDistance μ
      (closedSubgeodesicSlice curve u₀ u₁ (s i))
      (closedSubgeodesicSlice curve u₀ u₁ c)) l (𝓝 0) := by
  apply (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hμ
    (fun i => (isThetaPshPotential_closedSlice h (hs i)).1.quasiPlurisubharmonic)
    (isThetaPshPotential_closedSlice h hc).1.quasiPlurisubharmonic).mp
  exact manifoldL1LocallyTendsto_closedSlice h hc (Eventually.of_forall hs) hsc

/-- Every sequence of slices in a compact parameter set has a subsequence
converging in global L¹ to a slice of that family, for any smooth positive volume. -/
theorem exists_subseq_tendsto_globalL1EDistance_closedSlice
    (h : IsSubgeodesicFrom θ curve u₀ u₁) {μ : Measure M}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Icc (0 : ℝ) 1) {s : ℕ → ℝ} (hs : ∀ j, s j ∈ K) :
    ∃ c ∈ K, ∃ a : ℕ → ℕ, StrictMono a ∧
      Tendsto (s ∘ a) atTop (𝓝 c) ∧
      Tendsto (fun j => globalL1EDistance μ
        (closedSubgeodesicSlice curve u₀ u₁ (s (a j)))
        (closedSubgeodesicSlice curve u₀ u₁ c)) atTop (𝓝 0) := by
  obtain ⟨c, hc, a, ha, hsc⟩ := hK.tendsto_subseq hs
  exact ⟨c, hc, a, ha, hsc, tendsto_globalL1EDistance_closedSlice h hμ
    (hKI hc) (fun j => hKI (hs (a j))) hsc⟩

end Global

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicL1Compactness
