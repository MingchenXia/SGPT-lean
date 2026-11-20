import SGPT.Unibranch.OriginalNativeModification
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage

/-! Exact original good loci from an actual holomorphic open inverse.
These ordinary geometry lemmas retain the prescribed exceptional set for the
singular-base common-resolution proof; no common resolution is an input.
Blueprint first: `prime-nov16-original-prime-models.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16OriginalOpenInverse
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

/-- The prescribed actual good-open inverse reflects the EXACT original native
isomorphism locus, with full locally ringed maps and no unspecified bad set. -/
theorem isIsoOver_nativeMorphism_of_open_inverse {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {D : Set N} (hDa : IsComplexAnalyticSubset (n := n) D)
    (s : (⟨Dᶜ, hDa.isClosed.isOpen_compl⟩ : Opens N) → M)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s)
    (hright : ∀ x, f (s x) = x.val)
    (hleft : ∀ y (hy : f y ∉ D), s ⟨f y, hy⟩ = y) :
    IsIsoOver (nativeMorphism hf)
      ((Subtype.val : ↥(univ : Set N) → N) ⁻¹' D)ᶜ := by
  let U : Opens M := ⟨f ⁻¹' Dᶜ, hDa.isClosed.isOpen_compl.preimage hf.continuous⟩
  let V : Opens N := ⟨Dᶜ, hDa.isClosed.isOpen_compl⟩
  have hsU (x : V) : s x ∈ U := by
    change f (s x) ∉ D
    rw [hright x]
    exact x.property
  let e : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V :=
    { toFun := fun y => ⟨f y.val, y.property⟩
      invFun := fun x => ⟨s x, hsU x⟩
      left_inv := fun y => Subtype.ext (hleft y.val y.property)
      right_inv := fun x => Subtype.ext (hright x)
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
        (hf.comp contMDiff_subtype_val) (fun y => y.property)
      contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk hs hsU }
  let E := actualSubspaceBiholomorphicIso e (univ : Set U) (univ : Set V) (fun _ => Iff.rfl)
  let J := actualOpenSubspaceMap (n := n) (univ : Set M) U
  let K := actualOpenSubspaceMap (n := n) (univ : Set N) V
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set M) U
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set N) V
  have hfacCat : nativeMorphism (M := U) (N := M) contMDiff_subtype_val ≫ nativeMorphism hf =
      nativeMorphism e.contMDiff ≫ nativeMorphism (M := V) (N := N) contMDiff_subtype_val :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  have hfac : J ≫ (nativeMorphism hf).hom.left = E.hom ≫ K :=
    congrArg (fun H : wholeModel (n := n) U ⟶ wholeModel (n := n) N => H.hom.left) hfacCat
  refine ⟨_, J, hJ, ?_, ?_, ?_⟩
  · exact (range_actualOpenSubspaceMap (n := n) (univ : Set M) U).trans (by
      ext y
      rfl)
  · have hcomp : LocallyRingedSpace.IsOpenImmersion (E.hom ≫ K) :=
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) K hK
    exact hfac.symm ▸ hcomp
  · exact (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n)
        (univ : Set U) ⟶ (wholeModel (n := n) N).obj.left => range H.base) hfac).trans
      ((range_iso_hom_comp_base E K).trans
        ((range_actualOpenSubspaceMap (n := n) (univ : Set N) V).trans (by rfl)))

/-- Analytic continuation gives exact source thinness from ONE actual good
point; no modification or target-resolution certificate is supplied. -/
theorem interior_preimage_eq_empty_of_good_point [ConnectedSpace M] {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {D : Set N} (hD : IsComplexAnalyticSubset (n := n) D)
    (hgood : ∃ z, f z ∉ D) : interior (f ⁻¹' D) = ∅ := by
  have ha : IsComplexAnalyticSubset (n := n) (f ⁻¹' D) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hD
  have hproper : f ⁻¹' D ≠ univ := by
    intro h
    obtain ⟨z, hz⟩ := hgood
    have hzpre : z ∈ f ⁻¹' D := by rw [h]; exact mem_univ z
    exact hz hzpre
  rw [← not_nonempty_iff_eq_empty]
  exact fun h => hproper (ha.eq_univ_of_interior_nonempty h)

/-- An actual proper holomorphic map and actual good-open inverse manufacture
its complete analytic-modification dictionary on the prescribed bad set. -/
theorem isAnalyticModification_of_open_inverse [ConnectedSpace M] {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hproper : IsProperMap f) {D : Set N}
    (hDa : IsComplexAnalyticSubset (n := n) D) (hDi : interior D = ∅)
    (s : (⟨Dᶜ, hDa.isClosed.isOpen_compl⟩ : Opens N) → M)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s)
    (hright : ∀ x, f (s x) = x.val)
    (hleft : ∀ y (hy : f y ∉ D), s ⟨f y, hy⟩ = y) :
    IsAnalyticModification (n := n) f := by
  classical
  let : Nonempty N := Nonempty.map f inferInstance
  let O : Opens N := ⟨Dᶜ, hDa.isClosed.isOpen_compl⟩
  have hsubrange : Dᶜ ⊆ range f := fun x hx => ⟨s ⟨x, hx⟩, hright ⟨x, hx⟩⟩
  have hdense : Dense (range f) := (interior_eq_empty_iff_dense_compl.mp hDi).mono hsubrange
  have hrange : range f = univ := hproper.isClosed_range.closure_eq.symm.trans hdense.closure_eq
  have hsurj : Function.Surjective f := Set.range_eq_univ.mp hrange
  let t : N → M := fun x => Classical.choose (hsurj x)
  have ht (x : N) : f (t x) = x := Classical.choose_spec (hsurj x)
  have heq : (fun x : O => t x.val) = s := by
    funext x
    have hnot : f (t x.val) ∉ D := by rw [ht]; exact x.property
    exact (hleft _ hnot).symm.trans (congrArg s (Subtype.ext (ht x.val)))
  have htsmooth : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ t Dᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : O => t x.val) := heq.symm ▸ hs
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest ⟨x, hx⟩)).contMDiffWithinAt
  have hAa : IsComplexAnalyticSubset (n := n) (f ⁻¹' D) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hDa
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hDi).nonempty
  have hAi : interior (f ⁻¹' D) = ∅ :=
    interior_preimage_eq_empty_of_good_point hf hDa ⟨s ⟨x, hx⟩, by
      rw [hright]
      exact hx⟩
  refine ⟨hf, hproper, f ⁻¹' D, D, t, hDa.isClosed.preimage hf.continuous,
    hAa, hAi, hDa.isClosed, hDa, hDi, rfl, htsmooth, (fun x _ => ht x), ?_⟩
  intro y hy
  exact (congrFun heq (⟨f y, hy⟩ : O)).trans (hleft y hy)

end SGPT.PSH.PrimeNov16OriginalOpenInverse
