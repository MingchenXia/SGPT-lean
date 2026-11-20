import SGPT.PSH.AtlasNativeComponentHolomorphicOn
import SGPT.PSH.AtlasModificationComponentProper
import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- ANY original empty-interior set retains actual empty interior under the
SAME open component inclusion. This is genuine open-map topology only. -/
theorem interior_component_preimage_eq_empty (A : VariableComplexAtlas X)
    {T : Set X} (hT : interior T = ∅) (x : X) :
    interior (Subtype.val ⁻¹' T : Set (A.componentOpen x)) = ∅ := by
  apply subset_empty_iff.mp
  have hmap : IsOpenMap (Subtype.val : A.componentOpen x → X) :=
    (A.componentOpen x).isOpen.isOpenMap_subtype_val
  have h : interior (Subtype.val ⁻¹' T : Set (A.componentOpen x)) ⊆
      (Subtype.val : A.componentOpen x → X) ⁻¹' interior T :=
    hmap.interior_preimage_subset_preimage_interior
  simpa only [hT, preimage_empty] using h

/-- Pure model-index substitution. All actual native geometric fields are
inputs of this private generic link; the original-input producer below
manufactures each of them before applying it. -/
private theorem native_modification_of_dimension_eq
    {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [csM : ChartedSpace (ComplexModel n) M] [cmM : IsComplexManifold n M]
    [csN : ChartedSpace (ComplexModel m) N] [cmN : IsComplexManifold m N]
    (h : n = m) {F : M → N}
    (hF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ F)
    (hp : IsProperMap F) (E : Set M) (S : Set N) (g : N → M)
    (hEc : IsClosed E) (hEa : IsComplexAnalyticSubset (n := n) E)
    (hEi : interior E = ∅)
    (hSc : IsClosed S) (hSa : IsComplexAnalyticSubset (n := m) S)
    (hSi : interior S = ∅) (hpre : F ⁻¹' S = E)
    (hg : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g Sᶜ)
    (hright : ∀ p ∉ S, F (g p) = p) (hleft : ∀ p ∉ E, g (F p) = p) :
    letI : ChartedSpace (ComplexModel n) N := h.symm ▸ csN
    letI : IsComplexManifold n N := by cases h; exact cmN
    IsAnalyticModification (n := n) F := by
  subst m
  exact ⟨hF, hp, E, S, g, hEc, hEa, hEi, hSc, hSa, hSi, hpre, hg, hright, hleft⟩

/-- ORIGINAL modification geometry manufactures a complete actual native
modification on SAME component subtypes. The common dimension is OUTPUT,
and native charts are only the genuine derived charts with index transport.
All joint exceptional data are retained from the original hypothesis. -/
theorem IsAtlasAnalyticModification.exists_native_component_modification
    [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) (x : X) :
    ∃ (n : ℕ) (hn : n = A.pointDimension x) (hm : n = B.pointDimension (f x)),
      letI csX : ChartedSpace (ComplexModel n) (A.componentOpen x) :=
        hn.symm ▸ A.componentChartedSpace x
      letI cmX : IsComplexManifold n (A.componentOpen x) := by
        cases hn
        exact A.componentComplexManifold_of_paracompact x
      letI csY : ChartedSpace (ComplexModel n) (B.componentOpen (f x)) :=
        hm.symm ▸ B.componentChartedSpace (f x)
      letI cmY : IsComplexManifold n (B.componentOpen (f x)) := by
        cases hm
        exact B.componentComplexManifold_of_paracompact (f x)
      @IsAnalyticModification n (B.componentOpen (f x)) _ csY cmY
        (A.componentOpen x) _ csX cmX (hf.1.componentMap x) := by
  classical
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let := B.componentChartedSpace (f x)
  let := B.componentComplexManifold_of_paracompact (f x)
  have hdim := hf.componentDimension_eq x
  obtain ⟨E, S, s, hE, hEi, hS, hSi, hpre, hs, hright, hleft⟩ := hf.2.2
  have hdense : Dense Eᶜ := interior_eq_empty_iff_dense_compl.mp hEi
  obtain ⟨a, haE, haC⟩ := hdense.exists_mem_open (A.isOpen_component x)
    ⟨x, mem_connectedComponent⟩
  have haS : f a ∉ S := by
    intro h
    apply haE
    rw [← hpre]
    exact h
  let D := B.componentOpen (f x)
  let T : Set D := (Subtype.val ⁻¹' S)ᶜ
  let G : D → X := fun p => s p.val
  have hpreconnected : IsPreconnected (G '' T) :=
    (hS.isPreconnected_component_compl hSi (f x)).image G
      (hs.1.comp continuous_subtype_val.continuousOn (fun _ hp => hp))
  have haimage : a ∈ G '' T :=
    ⟨⟨f a, hf.1.1.mapsTo_connectedComponent x haC⟩, haS, hleft a haE⟩
  have hmap : MapsTo s (connectedComponent (f x) ∩ Sᶜ) (connectedComponent x) := by
    intro y hy
    have h := hpreconnected.subset_connectedComponent haimage
      (show s y ∈ G '' T from ⟨⟨y, hy.1⟩, hy.2, rfl⟩)
    rwa [← connectedComponent_eq haC] at h
  let g : B.componentOpen (f x) → A.componentOpen x := fun p =>
    if hp : p.val ∉ S then ⟨s p.val, hmap ⟨p.property, hp⟩⟩
    else ⟨x, mem_connectedComponent⟩
  have hgval (p : B.componentOpen (f x)) (hp : p.val ∉ S) :
      (g p).val = s p.val := by
    dsimp only [g]
    rw [dif_pos hp]
  have hg : ContMDiffOn 𝓘(ℂ, ComplexModel (B.pointDimension (f x)))
      𝓘(ℂ, ComplexModel (A.pointDimension x)) ∞ g
      (Subtype.val ⁻¹' S : Set (B.componentOpen (f x)))ᶜ :=
    hs.component_restriction_contMDiffOn (hS.isClosed B).isOpen_compl
      (f x) x g hgval
  have hrightC : ∀ p : B.componentOpen (f x), p.val ∉ S →
      hf.1.componentMap x (g p) = p := by
    intro p hp
    apply Subtype.ext
    change f (g p).val = p.val
    rw [hgval p hp]
    exact hright p.val hp
  have hleftC : ∀ p : A.componentOpen x, p.val ∉ E →
      g (hf.1.componentMap x p) = p := by
    intro p hp
    have hfp : (hf.1.componentMap x p).val ∉ S := by
      intro h
      apply hp
      rw [← hpre]
      exact h
    apply Subtype.ext
    rw [hgval _ hfp]
    exact hleft p.val hp
  have hpreC : (hf.1.componentMap x) ⁻¹' (Subtype.val ⁻¹' S) =
      (Subtype.val ⁻¹' E : Set (A.componentOpen x)) := by
    ext p
    change p.val ∈ f ⁻¹' S ↔ p.val ∈ E
    rw [hpre]
  refine ⟨A.pointDimension x, rfl, hdim, ?_⟩
  exact native_modification_of_dimension_eq hdim (hf.1.componentMap_contMDiff x)
    (hf.componentMap_isProperMap x) (Subtype.val ⁻¹' E) (Subtype.val ⁻¹' S) g
    ((hE.isClosed A).preimage continuous_subtype_val) (hE.componentAnalytic x)
    (A.interior_component_preimage_eq_empty hEi x)
    ((hS.isClosed B).preimage continuous_subtype_val) (hS.componentAnalytic (f x))
    (B.interior_component_preimage_eq_empty hSi (f x)) hpreC hg hrightC hleftC

end SGPT.PSH.VariableComplexAtlas
