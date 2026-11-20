import SGPT.Projective.SourceFamilyFiberCoordinates
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Genuine holomorphy of BOTH actual total-space fiber-equivalence maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeKodairaPullback
open Bundle Set Filter
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual fiber maps give a genuinely holomorphic map of the ORIGINAL
native total spaces. A single nonzero family member near each original point
and its literal quotient formula remove all pointwise choice regularity.
There is no incoming holomorphic bundle-map or local compatibility premise. -/
theorem sourceNativeGeneratingFamilies_contMDiff_totalMap
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x) :
    ContMDiff ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ))
      ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ)) ∞
      (fun V : TotalSpace ℂ E.Fiber =>
        (⟨V.proj, sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame V.proj V.snd⟩ :
          TotalSpace ℂ F.Fiber)) := by
  let Φ := sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame
  let Φtotal : TotalSpace ℂ E.Fiber → TotalSpace ℂ F.Fiber := fun V => ⟨V.proj, Φ V.proj V.snd⟩
  intro V
  change ContMDiffAt ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ))
    ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ)) ∞ Φtotal V
  let x := V.proj
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x, inferInstance⟩
  let : MemTrivializationAtlas e.val := e.property
  let : MemTrivializationAtlas f.val := f.property
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ F.Fiber x
  obtain ⟨j, hj⟩ := hs x
  let A := e.val.linearEquivAt ℂ x he
  have hden : (e.val ⟨x, s j x⟩).2 ≠ 0 := by
    intro hz
    apply hj
    apply A.injective
    exact hz.trans (map_zero A).symm
  have hS : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun y => (e.val ⟨y, s j y⟩).2) x :=
    (e.val.contMDiffAt_section_iff he).mp ((s j).contMDiff x)
  have hT : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun y => (f.val ⟨y, t j y⟩).2) x :=
    (f.val.contMDiffAt_section_iff hf).mp ((t j).contMDiff x)
  have hRatio : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun y => (f.val ⟨y, t j y⟩).2 / (e.val ⟨y, s j y⟩).2) x := hT.div₀ hS hden
  have hProj : ContMDiffAt ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ))
      𝓘(ℂ, ComplexModel n) ∞ (fun W : TotalSpace ℂ E.Fiber => W.proj) V :=
    contMDiffAt_proj E.Fiber
  have heV : V ∈ e.val.source := e.val.mem_source.mpr he
  have hE : ContMDiffAt ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ∞
      (fun W : TotalSpace ℂ E.Fiber => (e.val W).2) V :=
    ((e.val.contMDiffOn (IB := 𝓘(ℂ, ComplexModel n)) (n := ∞)).contMDiffAt
      (e.val.open_source.mem_nhds heV)).snd
  have hRatioTotal : ContMDiffAt ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ∞
      (fun W : TotalSpace ℂ E.Fiber =>
        (f.val ⟨W.proj, t j W.proj⟩).2 / (e.val ⟨W.proj, s j W.proj⟩).2) V := by
    exact hRatio.comp V hProj
  have hProduct : ContMDiffAt ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ∞
      (fun W : TotalSpace ℂ E.Fiber =>
        ((f.val ⟨W.proj, t j W.proj⟩).2 / (e.val ⟨W.proj, s j W.proj⟩).2) * (e.val W).2) V :=
    by
      apply (hRatioTotal.mul hE).congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun _ => rfl)
  have hTarget : Φtotal V ∈ f.val.source := f.val.mem_source.mpr hf
  apply (f.val.contMDiffAt_iff (f := Φtotal) (x₀ := V) hTarget).mpr
  refine ⟨hProj, ?_⟩
  apply hProduct.congr_of_eventuallyEq
  filter_upwards [hProj.continuousAt.tendsto.eventually (e.val.open_baseSet.mem_nhds he),
    hProj.continuousAt.tendsto.eventually (f.val.open_baseSet.mem_nhds hf),
    hProj.continuousAt.tendsto.eventually (hS.continuousAt.eventually_ne hden)] with W hWe hWf hWden
  exact sourceNativeGeneratingFamilies_fiberEquiv_frame_formula E F s t hs ht hSame e f
    W.proj hWe hWf j hWden W.snd

/-- The ACTUAL inverse total-space map is genuinely holomorphic as well.
The inverse is the same manufactured map for the swapped true section
families, by actual fiber uniqueness; no inverse regularity is assumed. -/
theorem sourceNativeGeneratingFamilies_contMDiff_totalInverse
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x) :
    ContMDiff ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ))
      ((𝓘(ℂ, ComplexModel n)).prod 𝓘(ℂ, ℂ)) ∞
      (fun V : TotalSpace ℂ F.Fiber =>
        (⟨V.proj, (sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame V.proj).symm V.snd⟩ :
          TotalSpace ℂ E.Fiber)) := by
  have h := sourceNativeGeneratingFamilies_contMDiff_totalMap F E t s ht hs
    (fun x => (hSame x).symm)
  have hfun : (fun V : TotalSpace ℂ F.Fiber =>
      (⟨V.proj, (sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame V.proj).symm V.snd⟩ :
        TotalSpace ℂ E.Fiber)) =
      (fun V : TotalSpace ℂ F.Fiber =>
        (⟨V.proj, sourceNativeGeneratingFamilies_fiberEquiv F E t s ht hs
          (fun x => (hSame x).symm) V.proj V.snd⟩ : TotalSpace ℂ E.Fiber)) := by
    funext V
    exact congrArg (fun u : E.Fiber V.proj => (⟨V.proj, u⟩ : TotalSpace ℂ E.Fiber))
      (sourceNativeGeneratingFamilies_fiberEquiv_symm_eq_swapped E F s t hs ht hSame V.proj V.snd)
  rw [hfun]
  exact h

end SGPT.Bergman.NativeKodairaPullback
