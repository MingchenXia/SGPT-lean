import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.CommonStrictUnramifiedPoint
import SGPT.Foundations.Analysis.Pending.UnramifiedNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.CoherentIdealCommonModelOrder

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  UnramifiedNormalOrder HironakaHolomorphicJetRankLoci RelativePrincipalizationSpan

universe u

variable {m : ℕ} {Y Z : Type u}
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

/-- The literal whole pullback is computed by the same original source generators. -/
theorem originalStalkNormalOrder_pullback_eq_source_generators
    {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    {z : Z} {E' : Set Z} (Ψ : DivisorFlattening (m := m) E' z)
    (A : GermIdeal (m + 1) Y) {N : ℕ} (s : Fin N → Y → ℂ)
    (hs : ∀ i, HolomorphicAt (m + 1) (s i) (g z))
    (hgen : ∀ f, A.mem (g z) f ↔ IsInSpanAt (n := m + 1) (· ∈ range s) (g z) f) :
    originalStalkNormalOrder Ψ (GermIdeal.pullback (m := m + 1) g A) =
      ⨅ i, functionNormalOrder Ψ (s i ∘ g)
        ((hs i).comp_contMDiff (Eventually.of_forall fun _ => hg.contMDiffAt)) := by
  have hpullgen : ∀ f, (GermIdeal.pullback (m := m + 1) g A).mem z f ↔
      IsInSpanAt (n := m + 1) (· ∈ range (fun i => s i ∘ g)) z f := by
    intro f
    constructor
    · intro hf
      change IsInSpanAt (fun t => ∃ a, A.mem (g z) a ∧ t = a ∘ g) z f at hf
      refine IsInSpanAt.trans ?_ hf
      rintro t ⟨a, ha, rfl⟩
      refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp hg ((hgen a).mp ha))
      rintro t ⟨b, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · intro hf
      change IsInSpanAt (fun t => ∃ a, A.mem (g z) a ∧ t = a ∘ g) z f
      refine IsInSpanAt.mono ?_ hf
      rintro t ⟨i, rfl⟩
      exact ⟨s i, (hgen (s i)).mpr
        (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hs i)), rfl⟩
  exact originalStalkNormalOrder_eq_generators Ψ _ (fun i => s i ∘ g)
    (fun i => (hs i).comp_contMDiff (Eventually.of_forall fun _ => hg.contMDiffAt)) hpullgen

/-- Coherence manufactures the whole family; actual IFT geometry preserves every member order. -/
theorem originalStalkNormalOrder_comp_eq_of_not_exceptional
    {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    {z : Z} (hz : z ∉ exceptionalLocus (m + 1) g)
    {E : Set Y} {E' : Set Z}
    (Φ : DivisorFlattening (m := m) E (g z)) (Ψ : DivisorFlattening (m := m) E' z)
    (hsets : ∀ᶠ z' in 𝓝 z, z' ∈ E' ↔ g z' ∈ E)
    (A : GermIdeal (m + 1) Y) (hA : A.IsCoherent) :
    originalStalkNormalOrder Ψ (GermIdeal.pullback (m := m + 1) g A) =
      originalStalkNormalOrder Φ A := by
  obtain ⟨U, hU, hzU, N, s, hs, hgen⟩ := hA (g z)
  have hshol (i : Fin N) : HolomorphicAt (m + 1) (s i) (g z) :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs i) hzU
  rw [originalStalkNormalOrder_pullback_eq_source_generators hg Ψ A s hshol
    (hgen (g z) hzU), originalStalkNormalOrder_eq_generators Φ A s hshol (hgen (g z) hzU)]
  exact iInf_congr fun i => functionNormalOrder_comp_eq_of_not_exceptional
    hg hz Φ Ψ hsets (s i) (hshol i)

/-- Genuine common-model geometry compares entire ideals from the SAME original coherent ideal. -/
theorem exists_common_originalStalkNormalOrder_eq
    {X Y₀ Y₁ W : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel (m + 1)) Y₀] [IsComplexManifold (m + 1) Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (m + 1)) Y₁] [IsComplexManifold (m + 1) Y₁]
    [TopologicalSpace W] [ChartedSpace (ComplexModel (m + 1)) W] [IsComplexManifold (m + 1) W]
    {π₀ : Y₀ → X} {π₁ : Y₁ → X} {g₀ : W → Y₀} {g₁ : W → Y₁}
    (hπ₀ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π₀)
    (hπ₁ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π₁)
    (hg₀ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) g₀)
    (hg₁ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) g₁)
    (hcomm : π₀ ∘ g₀ = π₁ ∘ g₁)
    (V₀ : ClosedIrreducibleAnalyticSubvariety (m + 1) Y₀)
    (V₁ : ClosedIrreducibleAnalyticSubvariety (m + 1) Y₁)
    (hE₀ : ∀ y ∈ V₀.carrier, RegularAtDim (n := m + 1) V₀.carrier y m)
    (hE₁ : ∀ y ∈ V₁.carrier, RegularAtDim (n := m + 1) V₁.carrier y m)
    (hstrict : strictTransform (m + 1) g₀ V₀.carrier = strictTransform (m + 1) g₁ V₁.carrier)
    (A : GermIdeal (m + 1) X) (hA : A.IsCoherent) :
    ∃ (z : W) (Φ₀ : DivisorFlattening (m := m) V₀.carrier (g₀ z))
      (Φ₁ : DivisorFlattening (m := m) V₁.carrier (g₁ z)),
      g₀ z ∈ V₀.carrier ∧ g₁ z ∈ V₁.carrier ∧
        originalStalkNormalOrder Φ₀ (GermIdeal.pullback (m := m + 1) π₀ A) =
          originalStalkNormalOrder Φ₁ (GermIdeal.pullback (m := m + 1) π₁ A) := by
  obtain ⟨y₀, hy₀⟩ := V₀.nonempty
  have hdim : V₀.dim = m :=
    (AnalyticIrreducibleComponents.eq_dim_of_regularAtDim V₀ (hE₀ y₀ hy₀)).symm
  have hcodim : V₀.dim + 1 = m + 1 := by rw [hdim]
  obtain ⟨D, hD₀, _, _, _⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hg₀ V₀ hcodim
  have hD₁ : D.carrier = strictTransform (m + 1) g₁ V₁.carrier := hD₀.trans hstrict
  obtain ⟨z, _hzreg, hz₀, hz₁⟩ :=
    CommonStrictUnramifiedPoint.exists_common_regular_unramified_point
      hg₀.1 hg₁.1 V₀ V₁ D hD₀ hD₁
  have hzD : z ∈ D.carrier := _hzreg.2.1
  have hzg₀ : g₀ z ∈ V₀.carrier := by
    have h : z ∈ strictTransform (m + 1) g₀ V₀.carrier := hD₀ ▸ hzD
    exact closure_minimal sdiff_subset (V₀.isClosed_carrier.preimage hg₀.1.continuous) h
  have hzg₁ : g₁ z ∈ V₁.carrier := by
    have h : z ∈ strictTransform (m + 1) g₁ V₁.carrier := hD₁ ▸ hzD
    exact closure_minimal sdiff_subset (V₁.isClosed_carrier.preimage hg₁.1.continuous) h
  obtain ⟨Φ₀⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE₀ (g₀ z) hzg₀)
  obtain ⟨Φ₁⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE₁ (g₁ z) hzg₁)
  have hO₀ : IsOpen (exceptionalLocus (m + 1) g₀)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg₀.1
  have hO₁ : IsOpen (exceptionalLocus (m + 1) g₁)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg₁.1
  have hDO₀ : ∀ w ∈ (exceptionalLocus (m + 1) g₀)ᶜ, w ∈ D.carrier ↔ g₀ w ∈ V₀.carrier := by
    intro w hw
    rw [hD₀]
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hg₀.1.continuous V₀.isClosed_carrier hw
  have hDO₁ : ∀ w ∈ (exceptionalLocus (m + 1) g₁)ᶜ, w ∈ D.carrier ↔ g₁ w ∈ V₁.carrier := by
    intro w hw
    rw [hD₁]
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hg₁.1.continuous V₁.isClosed_carrier hw
  have hDreg : RegularAtDim (n := m + 1) D.carrier z m :=
    RegularAtDimTransport.regularAtDim_of_preimage hg₀.1 hz₀ hO₀ hz₀ hDO₀ (hE₀ (g₀ z) hzg₀)
  obtain ⟨Ω⟩ := DivisorFlattening.nonempty_of_regularAtDim hDreg
  have hsets₀ : ∀ᶠ w in 𝓝 z, w ∈ D.carrier ↔ g₀ w ∈ V₀.carrier := by
    filter_upwards [hO₀.mem_nhds hz₀] with w hw
    exact hDO₀ w hw
  have hsets₁ : ∀ᶠ w in 𝓝 z, w ∈ D.carrier ↔ g₁ w ∈ V₁.carrier := by
    filter_upwards [hO₁.mem_nhds hz₁] with w hw
    exact hDO₁ w hw
  have hbase : π₀ (g₀ z) = π₁ (g₁ z) := congrFun hcomm z
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := hA (π₀ (g₀ z))
  have hshol₀ (i : Fin N) : HolomorphicAt (m + 1) (s i) (π₀ (g₀ z)) :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs i) hxU
  have hxU₁ : π₁ (g₁ z) ∈ U := hbase ▸ hxU
  have hshol₁ (i : Fin N) : HolomorphicAt (m + 1) (s i) (π₁ (g₁ z)) :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs i) hxU₁
  refine ⟨z, Φ₀, Φ₁, hzg₀, hzg₁, ?_⟩
  rw [originalStalkNormalOrder_pullback_eq_source_generators hπ₀ Φ₀ A s hshol₀
    (hgen _ hxU), originalStalkNormalOrder_pullback_eq_source_generators hπ₁ Φ₁ A s hshol₁
    (hgen _ hxU₁)]
  apply iInf_congr
  intro i
  have hf₀ : HolomorphicAt (m + 1) (s i ∘ π₀) (g₀ z) :=
    (hshol₀ i).comp_contMDiff (Eventually.of_forall fun _ => hπ₀.contMDiffAt)
  have hf₁ : HolomorphicAt (m + 1) (s i ∘ π₁) (g₁ z) :=
    (hshol₁ i).comp_contMDiff (Eventually.of_forall fun _ => hπ₁.contMDiffAt)
  have horder₀ := functionNormalOrder_comp_eq_of_not_exceptional
    hg₀.1 hz₀ Φ₀ Ω hsets₀ (s i ∘ π₀) hf₀
  have horder₁ := functionNormalOrder_comp_eq_of_not_exceptional
    hg₁.1 hz₁ Φ₁ Ω hsets₁ (s i ∘ π₁) hf₁
  have heq : (s i ∘ π₀) ∘ g₀ = (s i ∘ π₁) ∘ g₁ := by
    funext w
    exact congrArg (s i) (congrFun hcomm w)
  have hsame := functionNormalOrder_congr Ω
    (hf₀.comp_contMDiff (Eventually.of_forall fun _ => hg₀.1.contMDiffAt))
    (hf₁.comp_contMDiff (Eventually.of_forall fun _ => hg₁.1.contMDiffAt))
    (Eventually.of_forall (congrFun heq))
  exact horder₀.symm.trans (hsame.trans horder₁)

end SGPT.Foundations.Analysis.Pending.CoherentIdealCommonModelOrder
