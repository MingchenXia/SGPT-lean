import SGPT.Unibranch.HironakaG1NativeDisjointCoproduct
import SGPT.Unibranch.OriginalAnalyticCover

/-! Arbitrary disjoint native proper-bimeromorphic descent.
Reuse the held full good-locus/sheaf proof and held actual arbitrary native
proper coproduct theorem. No finite/compact/source-output certificate enters.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology

namespace SGPT.PSH.PrimeNov16DisjointBimeromorphic

open SGPT.Unibranch

open SourceReducedComplexSpace

noncomputable section

-- Native source-cover topology and true stalk cancellation, not an incoming
-- desired stalk isomorphism or full-map inverse certificate.
private theorem openImmersion_of_cover_and_injective
    {κ : Type} {W T : LocallyRingedSpace} {V : κ → LocallyRingedSpace}
    (l : ∀ i, V i ⟶ W) (hl : ∀ i, LocallyRingedSpace.IsOpenImmersion (l i))
    (hcover : ∀ w : W, ∃ (i : κ) (v : V i), (l i).base v = w)
    (K : W ⟶ T) (hinj : Function.Injective K.base)
    (hcomp : ∀ i, LocallyRingedSpace.IsOpenImmersion (l i ≫ K)) :
    LocallyRingedSpace.IsOpenImmersion K := by
  let s : (Σ i, V i) → W := fun v => (l v.1).base v.2
  have hs : Continuous s := continuous_sigma (fun i => (l i).base.hom.continuous)
  have hsurj : Function.Surjective s := by
    intro w
    obtain ⟨i, v, hv⟩ := hcover w
    exact ⟨⟨i, v⟩, hv⟩
  have hopen : IsOpenMap (K.base ∘ s) :=
    isOpenMap_sigma.mpr (fun i => (hcomp i).base_open.isOpenMap)
  have hemb : IsOpenEmbedding K.base :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap K.base.hom.continuous hinj
      (IsOpenMap.of_comp hs hsurj hopen)
  have : ∀ w : W, IsIso (K.stalkMap w) := by
    intro w
    obtain ⟨i, v, rfl⟩ := hcover w
    have : LocallyRingedSpace.IsOpenImmersion (l i) := hl i
    have : LocallyRingedSpace.IsOpenImmersion (l i ≫ K) := hcomp i
    have hc : IsIso ((l i ≫ K).stalkMap v) := by infer_instance
    rw [LocallyRingedSpace.stalkMap_comp] at hc
    have : IsIso (K.stalkMap ((l i).base v) ≫ (l i).stalkMap v) := hc
    exact IsIso.of_isIso_comp_right _ ((l i).stalkMap v)
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso K hemb

/-- Genuine local ORIGINAL PB maps over a true disjoint target cover derive
the global ORIGINAL predicate for the SAME full actual coproduct descent. -/
theorem isProperBimeromorphic_desc
    {ι : Type} {T : SourceReducedComplexSpace}
    {A Z : ι → SourceReducedComplexSpace}
    (j : ∀ i, A i ⟶ T)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ y : T.obj.left, ∃ (i : ι) (a : (A i).obj.left), (j i).hom.left.base a = y)
    (hdisj : Pairwise (fun i k =>
      Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (g : ∀ i, Z i ⟶ A i) (hg : ∀ i, IsProperBimeromorphic (g i)) :
    IsProperBimeromorphic (HironakaG1NativeDisjointCoproduct.desc Z (fun i => g i ≫ j i)) := by
  choose E hEa hEt hpre hiso using fun i => (hg i).2
  choose V u hu hrange hgu hgrange using hiso
  let S := HironakaG1NativeDisjointCoproduct.coproduct Z
  let k (i : ι) : Z i ⟶ S := HironakaG1NativeDisjointCoproduct.inclusion Z i
  let G : S ⟶ T := HironakaG1NativeDisjointCoproduct.desc Z (fun i => g i ≫ j i)
  change IsProperBimeromorphic G
  let D := OriginalAnalyticCover.unionImages j E
  have hDa : T.IsAnalyticSubset D :=
    OriginalAnalyticCover.unionImages_isAnalyticSubset j hj hcover hdisj E hEa
  have hDt : interior D = ∅ :=
    OriginalAnalyticCover.unionImages_interior_eq_empty j hj hcover hdisj E hEt
  have hDpre (i : ι) : (j i).hom.left.base ⁻¹' D = E i :=
    OriginalAnalyticCover.preimage_unionImages_eq j hj hdisj E i
  have hG (i : ι) : k i ≫ G = g i ≫ j i :=
    HironakaG1NativeDisjointCoproduct.inclusion_desc Z (fun i => g i ≫ j i) i
  have hSourcePre (i : ι) : (k i).hom.left.base ⁻¹' (G.hom.left.base ⁻¹' D) =
      (g i).hom.left.base ⁻¹' E i :=
    (congrArg (fun F : Z i ⟶ T => F.hom.left.base ⁻¹' D) (hG i)).trans
      (congrArg (fun C : Set (A i).obj.left => (g i).hom.left.base ⁻¹' C) (hDpre i))
  have hSourceThin : interior (G.hom.left.base ⁻¹' D) = ∅ :=
    OriginalAnalyticCover.interior_eq_empty_of_openImmersion_cover k
      (fun i => HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion Z i)
      (HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective Z) _
      (fun i => (congrArg interior (hSourcePre i)).trans (hpre i))
  let Q : Opens S.obj.left :=
    ⟨G.hom.left.base ⁻¹' Dᶜ, hDa.isClosed.isOpen_compl.preimage G.hom.left.base.hom.continuous⟩
  let W := S.obj.left.restrict Q.isOpenEmbedding
  let J : W ⟶ S.obj.left := S.obj.left.ofRestrict Q.isOpenEmbedding
  have hJ : LocallyRingedSpace.IsOpenImmersion J := by
    dsimp only [J]
    infer_instance
  have : LocallyRingedSpace.IsOpenImmersion J := hJ
  let f (i : ι) : V i ⟶ S.obj.left := u i ≫ (k i).hom.left
  let L (i : ι) : V i ⟶ T.obj.left := (u i ≫ (g i).hom.left) ≫ (j i).hom.left
  have hf (i : ι) : LocallyRingedSpace.IsOpenImmersion (f i) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (u i) (hu i) _
      (HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion Z i)
  have hL (i : ι) : LocallyRingedSpace.IsOpenImmersion (L i) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (u i ≫ (g i).hom.left) (hgu i) _ (hj i)
  have hfG (i : ι) : f i ≫ G.hom.left = L i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun F : Z i ⟶ T => u i ≫ F.hom.left) (hG i)).trans
        (Category.assoc _ _ _).symm)
  have hRange (i : ι) : range (f i).base ⊆ range J.base := by
    rintro _ ⟨v, rfl⟩
    refine ⟨⟨(f i).base v, ?_⟩, rfl⟩
    intro hD
    have hgood : (g i).hom.left.base ((u i).base v) ∉ E i :=
      (Set.ext_iff.mp (hrange i) ((u i).base v)).mp ⟨v, rfl⟩
    exact hgood ((Set.ext_iff.mp (hSourcePre i) ((u i).base v)).mp hD)
  let l (i : ι) : V i ⟶ W := LocallyRingedSpace.IsOpenImmersion.lift J (f i) (hRange i)
  have hlJ (i : ι) : l i ≫ J = f i :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac J (f i) (hRange i)
  have hl (i : ι) : LocallyRingedSpace.IsOpenImmersion (l i) := by
    have : LocallyRingedSpace.IsOpenImmersion (f i) := hf i
    have : IsIso (pullback.snd J (f i)) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset J (f i) (hRange i)
    dsimp only [l, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hlcover : ∀ w : W, ∃ (i : ι) (v : V i), (l i).base v = w := by
    intro w
    obtain ⟨i, x, hx⟩ := HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective Z w.val
    have hxgood : x ∈ (g i).hom.left.base ⁻¹' (E i)ᶜ := by
      intro hxE
      have hS : (k i).hom.left.base x ∈ G.hom.left.base ⁻¹' D :=
        (Set.ext_iff.mp (hSourcePre i) x).mpr hxE
      exact w.property (hx ▸ hS)
    have hxrange : x ∈ range (u i).base := (Set.ext_iff.mp (hrange i) x).mpr hxgood
    obtain ⟨v, hv⟩ := hxrange
    have hwf : J.base w ∈ range (f i).base :=
      ⟨v, (congrArg (k i).hom.left.base hv).trans hx⟩
    have hwl : w ∈ range (l i).base :=
      (Set.ext_iff.mp
        (LocallyRingedSpace.IsOpenImmersion.lift_range J (f i) (hRange i)) w).mpr hwf
    obtain ⟨v, hv⟩ := hwl
    exact ⟨i, v, hv⟩
  let K := J ≫ G.hom.left
  have hlK (i : ι) : l i ≫ K = L i :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun H => H ≫ G.hom.left) (hlJ i)).trans (hfG i))
  have hKinj : Function.Injective K.base := by
    intro w w' hww
    obtain ⟨i, v, rfl⟩ := hlcover w
    obtain ⟨q, z, rfl⟩ := hlcover w'
    have hEq : (L i).base v = (L q).base z :=
      (congrArg (fun H => H.base v) (hlK i)).symm.trans
        (hww.trans (congrArg (fun H => H.base z) (hlK q)))
    by_cases hiq : i = q
    · subst q
      exact congrArg (l i).base ((hL i).base_open.injective hEq)
    · exact (Set.disjoint_left.mp (hdisj hiq)
        ⟨(u i ≫ (g i).hom.left).base v, rfl⟩
        ⟨(u q ≫ (g q).hom.left).base z, hEq.symm⟩).elim
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    openImmersion_of_cover_and_injective l hl hlcover K hKinj
      (fun i => (hlK i).symm ▸ hL i)
  have hKrange : range K.base = Dᶜ := by
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact w.property
    · intro y hy
      obtain ⟨i, a, ha⟩ := hcover y
      have haE : a ∈ (E i)ᶜ := by
        intro hE
        have hD : (j i).hom.left.base a ∈ D := (Set.ext_iff.mp (hDpre i) a).mpr hE
        exact hy (ha ▸ hD)
      have harange : a ∈ range (u i ≫ (g i).hom.left).base :=
        (Set.ext_iff.mp (hgrange i) a).mpr haE
      obtain ⟨v, hv⟩ := harange
      refine ⟨(l i).base v, ?_⟩
      exact (congrArg (fun H => H.base v) (hlK i)).trans
        ((congrArg (j i).hom.left.base hv).trans ha)
  have hIso : IsIsoOver G Dᶜ := ⟨W, J, hJ, Subtype.range_coe, hK, hKrange⟩
  refine ⟨?_, D, hDa, hDt, hSourceThin, hIso⟩
  exact HironakaG1NativeDisjointCoproduct.desc_isProperMap_of_disjoint_cover Z
    j hj hcover hdisj g (fun i => (hg i).1)

end

end SGPT.PSH.PrimeNov16DisjointBimeromorphic
