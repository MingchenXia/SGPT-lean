import SGPT.PSH.AtlasVanishingIdeal

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

private theorem dimension_cast_restricted_scalar {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (h : d = n)
    (U : Opens X) (hU : Nonempty U) (g : U → ℂ) (V : Set U) :
    DifferentiableOn ℂ (g ∘ ((nativeCoordinateDimensionTransport e h).subtypeRestr hU).symm)
      (((nativeCoordinateDimensionTransport e h).subtypeRestr hU).target ∩
        ((nativeCoordinateDimensionTransport e h).subtypeRestr hU).symm ⁻¹' V) ↔
      DifferentiableOn ℂ (g ∘ (e.subtypeRestr hU).symm)
        ((e.subtypeRestr hU).target ∩ (e.subtypeRestr hU).symm ⁻¹' V) := by
  subst n
  rfl

/-- Every actual inherited ORIGINAL component chart has exactly the scalar
holomorphy of the internally derived native atlas, on the SAME subset/function. -/
theorem chartHolomorphicOn_component_iff_nativeAtlas (A : VariableComplexAtlas X) (x : X)
    (g : A.componentOpen x → ℂ) (V : Set (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    (A.openRestriction (A.componentOpen x)).ChartHolomorphicOn g V ↔
      (ofFixedModel (A.pointDimension x) (A.componentOpen x)).ChartHolomorphicOn g V := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  have hU := A.componentNonempty x
  unfold openRestriction
  rw [dif_pos hU]
  change (∀ i, DifferentiableOn ℂ (g ∘ ((A.chart i).subtypeRestr hU).symm)
    (((A.chart i).subtypeRestr hU).target ∩ ((A.chart i).subtypeRestr hU).symm ⁻¹' V)) ↔ _
  constructor
  · intro h e
    obtain ⟨i, hi⟩ := e.property
    change DifferentiableOn ℂ (g ∘ e.val.symm) (e.val.target ∩ e.val.symm ⁻¹' V)
    rw [← hi]
    have hc := dimension_cast_restricted_scalar (A.chart i.val) (A.componentChartDimension x i)
      (A.componentOpen x) hU g V
    change DifferentiableOn ℂ (g ∘ (A.componentChart x i).symm)
      ((A.componentChart x i).target ∩ (A.componentChart x i).symm ⁻¹' V) ↔ _ at hc
    exact hc.mpr (h i.val)
  · intro h i
    by_cases hmeet : ((A.chart i).source ∩ connectedComponent x).Nonempty
    · let j : A.ComponentChartIndex x := ⟨i, hmeet⟩
      have hn := h ⟨A.componentChart x j, ⟨j, rfl⟩⟩
      have hc := dimension_cast_restricted_scalar (A.chart i) (A.componentChartDimension x j)
        (A.componentOpen x) hU g V
      change DifferentiableOn ℂ (g ∘ (A.componentChart x j).symm)
        ((A.componentChart x j).target ∩ (A.componentChart x j).symm ⁻¹' V) ↔ _ at hc
      exact hc.mp hn
    · have ht : ((A.chart i).subtypeRestr hU).target = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hs := ((A.chart i).subtypeRestr hU).map_target hz
        have hs' : (((A.chart i).subtypeRestr hU).symm z).val ∈ (A.chart i).source := by
          simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hs
        exact hmeet ⟨_, hs', (((A.chart i).subtypeRestr hU).symm z).property⟩
      rw [ht, empty_inter]
      exact differentiableOn_empty

/-- ORIGINAL A,x and original Hausdorff/paracompact topology internally give
exactly the SAME genuine native scalar germ on their SAME component. -/
theorem atlasHolomorphicAt_component_iff_native [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (x : X) (g : A.componentOpen x → ℂ)
    (p : A.componentOpen x) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (A.openRestriction (A.componentOpen x)).AtlasHolomorphicAt g p ↔
      HolomorphicAt (A.pointDimension x) g p := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  have hiff : (A.openRestriction (A.componentOpen x)).AtlasHolomorphicAt g p ↔
      (ofFixedModel (A.pointDimension x) (A.componentOpen x)).AtlasHolomorphicAt g p := by
    constructor
    · rintro ⟨V, hV, hpV, hg⟩
      exact ⟨V, hV, hpV, (chartHolomorphicOn_component_iff_nativeAtlas A x g V).mp hg⟩
    · rintro ⟨V, hV, hpV, hg⟩
      exact ⟨V, hV, hpV, (chartHolomorphicOn_component_iff_nativeAtlas A x g V).mpr hg⟩
  exact hiff.trans atlasHolomorphicAt_iff_native

/-- BOTH full finite-span inclusions retain ALL actual family members,
cofactors and the SAME eventual finite sum on the SAME original component. -/
theorem atlasIsInSpanAt_component_iff_native [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (x : X) (S : (A.componentOpen x → ℂ) → Prop)
    (g : A.componentOpen x → ℂ) (p : A.componentOpen x) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (A.openRestriction (A.componentOpen x)).AtlasIsInSpanAt S p g ↔
      IsInSpanAt (n := A.pointDimension x) S p g := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  simp only [AtlasIsInSpanAt, IsInSpanAt, atlasHolomorphicAt_component_iff_native A x]

/-- The ENTIRE reduced vanishing ideal is genuinely native at EVERY SAME
original component stalk, for EVERY scalar and ANY set, including singular points. -/
theorem atlasVanishingIdeal_component_mem_iff_native [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (x : X) (S : Set (A.componentOpen x))
    (g : A.componentOpen x → ℂ) (p : A.componentOpen x) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (atlasVanishingIdeal (A.openRestriction (A.componentOpen x)) S).mem p g ↔
      (vanishingIdeal (n := A.pointDimension x) S).mem p g := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact and_congr (atlasHolomorphicAt_component_iff_native A x g p) Iff.rfl

end SGPT.PSH.VariableComplexAtlas
