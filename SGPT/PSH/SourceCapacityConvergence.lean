import SGPT.PSH.SourceQuasiContinuity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped ENNReal Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- The first original order gap, as an ambient subset of the original open domain. -/
def sourceCapacityUpperGap (U : Opens M) (f g : U → EReal) (δ : ℝ) : Set M :=
  Subtype.val '' {x : U | g x + (δ : EReal) < f x}

/-- The second original order gap. Finite subtraction retains both common poles. -/
def sourceCapacityLowerGap (U : Opens M) (f g : U → EReal) (δ : ℝ) : Set M :=
  Subtype.val '' {x : U | f x < g x - (δ : EReal)}

@[simp] theorem mem_sourceCapacityUpperGap (U : Opens M) (f g : U → EReal)
    (δ : ℝ) (x : U) :
    x.1 ∈ sourceCapacityUpperGap U f g δ ↔ g x + (δ : EReal) < f x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    simpa only [show y = x from Subtype.ext hxy, Set.mem_ofPred_eq] using hy
  · exact fun h ↦ ⟨x, h, rfl⟩

@[simp] theorem mem_sourceCapacityLowerGap (U : Opens M) (f g : U → EReal)
    (δ : ℝ) (x : U) :
    x.1 ∈ sourceCapacityLowerGap U f g δ ↔ f x < g x - (δ : EReal) := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    simpa only [show y = x from Subtype.ext hxy, Set.mem_ofPred_eq] using hy
  · exact fun h ↦ ⟨x, h, rfl⟩

/-- No unqualified extended-real absolute difference is used at either common pole. -/
theorem sourceCapacityGap_common_pole (U : Opens M) (f g : U → EReal)
    (δ : ℝ) (x : U)
    (hp : (f x = ⊥ ∧ g x = ⊥) ∨ (f x = ⊤ ∧ g x = ⊤)) :
    x.1 ∉ sourceCapacityUpperGap U f g δ ∪ sourceCapacityLowerGap U f g δ := by
  simp only [mem_union, mem_sourceCapacityUpperGap, mem_sourceCapacityLowerGap]
  rcases hp with ⟨hf, hg⟩ | ⟨hf, hg⟩ <;> simp [hf, hg, sub_eq_add_neg]

/-- For genuine real values, and only then, the original two gaps equal the
ordinary absolute-difference gap. -/
theorem sourceCapacityGap_coe_iff (U : Opens M) (f g : U → ℝ)
    (δ : ℝ) (x : U) :
    x.1 ∈ sourceCapacityUpperGap U (fun y ↦ (f y : EReal)) (fun y ↦ (g y : EReal)) δ ∪
      sourceCapacityLowerGap U (fun y ↦ (f y : EReal)) (fun y ↦ (g y : EReal)) δ ↔
        δ < |f x - g x| := by
  simp only [mem_union, mem_sourceCapacityUpperGap, mem_sourceCapacityLowerGap,
    ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_lt_coe_iff, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

theorem sourceCapacityUpperGap_self (U : Opens M) (f : U → EReal)
    {δ : ℝ} (hδ : 0 ≤ δ) : sourceCapacityUpperGap U f f δ = ∅ := by
  apply subset_antisymm ?_ (empty_subset _)
  rintro _ ⟨x, hx, rfl⟩
  exact (not_lt_of_ge (le_add_of_nonneg_right (show (0 : EReal) ≤ (δ : EReal) from
    EReal.coe_le_coe_iff.mpr hδ))) hx

theorem sourceCapacityLowerGap_self (U : Opens M) (f : U → EReal)
    {δ : ℝ} (hδ : 0 ≤ δ) : sourceCapacityLowerGap U f f δ = ∅ := by
  apply subset_antisymm ?_ (empty_subset _)
  rintro _ ⟨x, hx, rfl⟩
  have hle : f x - (δ : EReal) ≤ f x :=
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ))
      (Or.inl (EReal.coe_ne_top δ))).mpr
        (le_add_of_nonneg_right (EReal.coe_le_coe_iff.mpr hδ))
  exact (not_lt_of_ge hle) hx

/-- Reversing the source arguments interchanges the two literal order gaps,
including at either infinite endpoint. -/
theorem sourceCapacityLowerGap_eq_upper_swap (U : Opens M) (f g : U → EReal) (δ : ℝ) :
    sourceCapacityLowerGap U f g δ = sourceCapacityUpperGap U g f δ := by
  apply congrArg (Set.image Subtype.val)
  ext x
  exact EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))

variable [MeasurableSpace M] [BorelSpace M]

/-- Actual Borel order gaps in the ambient manifold, including either pole. -/
theorem measurableSet_sourceCapacityUpperGap (U : Opens M) {f g : U → EReal}
    (hf : Measurable f) (hg : Measurable g) (δ : ℝ) :
    MeasurableSet (sourceCapacityUpperGap U f g δ) := by
  exact (MeasurableEmbedding.subtype_coe U.isOpen.measurableSet).measurableSet_image.mpr
    (measurableSet_lt (hg.add measurable_const) hf)

theorem measurableSet_sourceCapacityLowerGap (U : Opens M) {f g : U → EReal}
    (hf : Measurable f) (hg : Measurable g) (δ : ℝ) :
    MeasurableSet (sourceCapacityLowerGap U f g δ) := by
  exact (MeasurableEmbedding.subtype_coe U.isOpen.measurableSet).measurableSet_image.mpr
    (measurableSet_lt hf (by
      change Measurable (fun x : U ↦ g x + -(δ : EReal))
      exact hg.add measurable_const))

variable [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Original `def:conv_cap` on an arbitrary filter, with literal Borel functions
and BOTH original finite-translation order gaps. There is no sequence restriction. -/
def SourceTendstoInCapacity (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) {I : Type*} (f : I → U → EReal) (l : Filter I) (g : U → EReal) : Prop :=
  (∀ i, Measurable (f i)) ∧ Measurable g ∧ ∀ δ : ℝ, 0 < δ →
    Tendsto (fun i ↦ sourceThetaCapacity θ (sourceCapacityUpperGap U (f i) g δ)) l (𝓝 0) ∧
    Tendsto (fun i ↦ sourceThetaCapacity θ (sourceCapacityLowerGap U (f i) g δ)) l (𝓝 0)

/-- Exact directed-net specialization; directedness is the usual tail-filter
convention, while the filter definition also permits every other source indexing. -/
def SourceNetConvergesInCapacity (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (f : I → U → EReal) (g : U → EReal) : Prop :=
  SourceTendstoInCapacity θ U f atTop g

omit [BorelSpace M] in
/-- Literal native-capacity reading with the same arbitrary filter and two gaps. -/
theorem sourceTendstoInCapacity_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {I : Type*} (f : I → U → EReal) (l : Filter I) (g : U → EReal) :
    SourceTendstoInCapacity θ U f l g ↔ (∀ i, Measurable (f i)) ∧ Measurable g ∧
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun i ↦ ThetaCapacity.thetaCapacityV (atlasClosedFormToNative θ)
          (sourceCapacityUpperGap U (f i) g δ)) l (𝓝 0) ∧
        Tendsto (fun i ↦ ThetaCapacity.thetaCapacityV (atlasClosedFormToNative θ)
          (sourceCapacityLowerGap U (f i) g δ)) l (𝓝 0) := by
  simp only [SourceTendstoInCapacity, sourceThetaCapacity_eq_native]

omit [BorelSpace M] in
/-- The two source limits are equivalent to the capacity of their union tending
to zero. This uses actual monotonicity and subadditivity, never an undefined
extended-real absolute difference. -/
theorem sourceTendstoInCapacity_iff_union
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {I : Type*} (f : I → U → EReal) (l : Filter I) (g : U → EReal) :
    SourceTendstoInCapacity θ U f l g ↔ (∀ i, Measurable (f i)) ∧ Measurable g ∧
      ∀ δ : ℝ, 0 < δ → Tendsto (fun i ↦ sourceThetaCapacity θ
        (sourceCapacityUpperGap U (f i) g δ ∪ sourceCapacityLowerGap U (f i) g δ)) l (𝓝 0) := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, fun δ hδ ↦ ?_⟩
    have hsum := (h.2.2 δ hδ).1.add (h.2.2 δ hδ).2
    have hsum' : Tendsto (fun i ↦
        sourceThetaCapacity θ (sourceCapacityUpperGap U (f i) g δ) +
          sourceThetaCapacity θ (sourceCapacityLowerGap U (f i) g δ)) l (𝓝 0) := by
      simpa only [zero_add] using hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum'
      (fun _ ↦ zero_le) (fun i ↦ sourceThetaCapacity_union_le θ _ _)
  · rintro ⟨hf, hg, hlim⟩
    refine ⟨hf, hg, fun δ hδ ↦ ⟨?_, ?_⟩⟩
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim δ hδ)
        (fun _ ↦ zero_le) (fun _ ↦ sourceThetaCapacity_mono θ subset_union_left)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim δ hδ)
        (fun _ ↦ zero_le) (fun _ ↦ sourceThetaCapacity_mono θ subset_union_right)

omit [BorelSpace M] in
/-- Every original Borel function is its own constant capacity limit, poles included. -/
theorem sourceTendstoInCapacity_const
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {I : Type*} (l : Filter I) {g : U → EReal} (hg : Measurable g) :
    SourceTendstoInCapacity θ U (fun _ : I ↦ g) l g := by
  refine ⟨fun _ ↦ hg, hg, ?_⟩
  intro δ hδ
  simp only [sourceCapacityUpperGap_self U g hδ.le,
    sourceCapacityLowerGap_self U g hδ.le, sourceThetaCapacity_empty]
  exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

omit [BorelSpace M] in
/-- Composition of filters transports both original capacity limits. -/
theorem SourceTendstoInCapacity.comp
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {U : Opens M}
    {I J : Type*} {f : I → U → EReal} {g : U → EReal} {l : Filter I} {k : Filter J}
    (h : SourceTendstoInCapacity θ U f l g) {a : J → I} (ha : Tendsto a k l) :
    SourceTendstoInCapacity θ U (f ∘ a) k g :=
  ⟨fun j ↦ h.1 (a j), h.2.1, fun δ hδ ↦
    ⟨(h.2.2 δ hδ).1.comp ha, (h.2.2 δ hδ).2.comp ha⟩⟩

end SGPT.PSH.VariableComplexAtlas
