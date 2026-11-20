import SGPT.Unibranch.CHPrimeRealizationTools
import SGPT.Unibranch.HironakaG10Complete
import SGPT.Unibranch.HironakaG10EpBimeromorphicCancel
import SGPT.Unibranch.HironakaG10MwRemmertTheorem
import SGPT.Unibranch.HironakaG10SourceCSet
import SGPT.Unibranch.HironakaG10GenDisjointModification
import SGPT.Unibranch.HironakaG10GenBlowupBridge
import SGPT.Unibranch.HironakaG11PresUnconditional
import SGPT.Unibranch.HironakaG1NativeModificationIsoTransport
import SGPT.Unibranch.OriginalProperBimeromorphicNative
import SGPT.PSH.PrimeNov16OriginalPrimeQuotient
import SGPT.PSH.PrimeNov16OriginalFibreDictionary
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# `cor:primerealization` over an arbitrary compact complex space

Source `cor:primerealization` (`appendix_unibranch.tex`, line 96): *let `X` be an irreducible
compact complex space and `E` a prime divisor over `X` (`def:primdiv`). Then there is a
modification `π : Y → X` (`def:modif`: a finite composition of blowups with smooth centres) such
that `Y` is smooth and `E` can be realized as a prime divisor on `Y`.*

Objects (all existing, verified formalizations):

* complex spaces: `SGPT.Unibranch.SourceReducedComplexSpace` (reduced, Hausdorff, paracompact);
* prime divisors over `X` (`def:primdiv`, arbitrary singular base):
  `SGPT.PSH.PrimeNov16OriginalPrimePresentation.PrimePresentation X` — a smooth `model`, a
  resolution `projection : model ⟶ X` and a connected smooth hypersurface `divisor` of the model;
  their equivalence is `commonResolutionRelation` (a common smooth resolution on which the
  strict transforms coincide), the classes are `PrimeNov16OriginalPrimeQuotient.PrimeOver X`;
* modifications (`def:modif`): `SGPT.Unibranch.SmoothCentreModification.IsModification`.

Main results:

* `isProperBimeromorphic_comp` — proper bimeromorphic morphisms of arbitrary (singular) reduced
  complex spaces compose (Remmert's proper mapping theorem makes the image of the bad set
  analytic); hence `isProperBimeromorphic_of_isModification`: every finite composition of
  smooth-centre blowups is proper bimeromorphic;
* `exists_modification_realization` — **`cor:primerealization`**: for every compact complex space
  `X` and every prime divisor `p` over `X` there is a prime divisor `q` over `X`, equivalent to
  `p`, whose model `q.model` (smooth) is a modification `q.projection : q.model ⟶ X` of `X`;
* `exists_modification_realization_primeOver` — the same for classes: every element of
  `PrimeOver X` is the class of a prime divisor on a smooth modification of `X`.

The irreducibility hypothesis of the book is not needed. The proof follows the book: the smooth
model `X' → X` of `E` is dominated by a modification `Y₀ → X` (Hironaka's Chow lemma,
`HironakaG10Complete.hironakaChowLemmaGeneral`), `Y₀` is resolved by finitely many smooth-centre
blowups (G11, `HironakaG11PresUnconditional.exists_endpoint`), the strict transform of `E` is
resolved by an embedded resolution of the component carrying it (blowups of that component,
extended to the whole space by `HironakaG10GenDisjointModification.exists_modification_extension`),
and the resolved strict transform realizes the same prime divisor
(`CHPrimeRealization.originalStrictTransform_eq_image`, `StrictTransformComposition`).

Blueprint: `blueprint/src/ch.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.CHPrimeRealization

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch SourceReducedComplexSpace SmoothCentreModification OriginalNativeModification
  OriginalSmoothSourceAnalytic OriginalProperBimeromorphicNative HironakaG10ChowTowerDomination
  HironakaG10GenChow HironakaG10ChowNativeIsoCriterion
open SGPT.PSH PrimeNov16OriginalHypersurface PrimeNov16OriginalStrictTransform
  PrimeNov16OriginalPrimePresentation PrimeNov16OriginalPrimeQuotient

/-! ### Composition of proper bimeromorphic morphisms -/

private theorem isProperBimeromorphic_id' (Y : SourceReducedComplexSpace) :
    IsProperBimeromorphic (𝟙 Y) := by
  refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
  exact IsIsoOver.id_of_isOpen Y (by simp)

/-- A morphism which is an isomorphism over the complement of a thin set `T` maps thin sets to
sets with empty interior. -/
theorem interior_image_eq_empty_of_isIsoOver {X Y : SourceReducedComplexSpace} {G : Y ⟶ X}
    {T : Set X.obj.left} (hTi : interior T = ∅) (hG : IsIsoOver G Tᶜ) {U : Set Y.obj.left}
    (hU : interior U = ∅) : interior (G.hom.left.base '' U) = ∅ := by
  have hTc : IsClosed T := isClosed_of_isIsoOver hG
  have hinj := injOn_of_isIsoOver hG
  have hsurj : ∀ x ∈ Tᶜ, ∃ y, G.hom.left.base y = x := by
    obtain ⟨V, j, -, -, -, hjGr⟩ := hG
    intro x hx
    rw [← hjGr] at hx
    obtain ⟨v, rfl⟩ := hx
    exact ⟨j.base v, rfl⟩
  let W := interior (G.hom.left.base '' U) \ T
  have hWo : IsOpen W := isOpen_interior.sdiff hTc
  have hOU : G.hom.left.base ⁻¹' W ⊆ U := by
    intro y hy
    obtain ⟨u, hu, hGu⟩ := interior_subset hy.1
    have hyT : G.hom.left.base y ∈ Tᶜ := hy.2
    have huT : G.hom.left.base u ∈ Tᶜ := by
      rw [hGu]
      exact hyT
    rw [← hinj huT hyT hGu]
    exact hu
  have hOe : G.hom.left.base ⁻¹' W = ∅ := by
    have h := interior_maximal hOU (hWo.preimage G.hom.left.base.hom.continuous)
    rw [hU] at h
    exact subset_empty_iff.mp h
  have hWT : interior (G.hom.left.base '' U) ⊆ T := by
    intro z hz
    by_contra hzT
    obtain ⟨y, hy⟩ := hsurj z hzT
    have hyW : y ∈ G.hom.left.base ⁻¹' W := by
      change G.hom.left.base y ∈ W
      rw [hy]
      exact ⟨hz, hzT⟩
    rw [hOe] at hyW
    exact hyW
  have h := interior_maximal hWT isOpen_interior
  rw [hTi] at h
  exact subset_empty_iff.mp h

/-- **Proper bimeromorphic morphisms compose**, for arbitrary reduced complex spaces. If `F` is an
isomorphism off the thin analytic set `U` and `G` off `T`, then `F ≫ G` is an isomorphism off
`T ∪ G(U)`, which is analytic by Remmert's proper mapping theorem and thin. -/
theorem isProperBimeromorphic_comp {S Y X : SourceReducedComplexSpace} {F : S ⟶ Y} {G : Y ⟶ X}
    (hF : IsProperBimeromorphic F) (hG : IsProperBimeromorphic G) :
    IsProperBimeromorphic (F ≫ G) := by
  have hFo := isOpenOffThin_of_isProperBimeromorphic hF
  have hGo := isOpenOffThin_of_isProperBimeromorphic hG
  obtain ⟨hFp, U, hUa, hUi, -, hFU⟩ := hF
  obtain ⟨hGp, T, hTa, hTi, -, hGT⟩ := hG
  have hTc : IsClosed T := isClosed_of_isIsoOver hGT
  have hGUa : X.IsAnalyticSubset (G.hom.left.base '' U) :=
    HironakaG10MwRemmertTheorem.isAnalyticSubset_image_of_isProperMap G hGp hUa
  have hGUi : interior (G.hom.left.base '' U) = ∅ :=
    interior_image_eq_empty_of_isIsoOver hTi hGT hUi
  have hBa : X.IsAnalyticSubset (T ∪ G.hom.left.base '' U) :=
    HironakaG10SourceCSet.analytic_union hTa hGUa
  have hBi : interior (T ∪ G.hom.left.base '' U) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hTc hGUi, hTi]
  have hBo : IsOpen (T ∪ G.hom.left.base '' U)ᶜ := hBa.isClosed.isOpen_compl
  refine ⟨hGp.comp hFp, T ∪ G.hom.left.base '' U, hBa, hBi, ?_, ?_⟩
  · have hcomp : IsOpenOffThin (F ≫ G).hom.left.base := by
      change IsOpenOffThin (G.hom.left.base ∘ F.hom.left.base)
      exact hFo.comp F.hom.left.base.hom.continuous hGo
    exact hcomp.interior_preimage_eq_empty hBi
  · apply IsIsoOver.comp (hGT.of_isOpen_subset hBo (fun x hx h => hx (Or.inl h)))
    apply hFU.of_isOpen_subset (hBo.preimage G.hom.left.base.hom.continuous)
    intro y hy hyU
    exact hy (Or.inr ⟨y, hyU, rfl⟩)

/-- **Modifications are proper bimeromorphic.** Every finite composition of blowups with smooth
centres (`def:modif`) of a reduced complex space is proper bimeromorphic. -/
theorem isProperBimeromorphic_of_isModification {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsModification p) : IsProperBimeromorphic p := by
  induction hp with
  | id => exact isProperBimeromorphic_id' _
  | cons f g hf _ ih => exact isProperBimeromorphic_comp hf.isProperBimeromorphic ih

/-- A modification with smooth source is a resolution (`def:primdiv`). -/
theorem isResolution_of_isModification {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsModification p) (hY : Y.IsSmooth) : IsResolution p :=
  ⟨hY, isProperBimeromorphic_of_isModification hp⟩

/-! ### `cor:primerealization` -/

/-- **`cor:primerealization`.** Let `X` be a compact complex space (irreducibility is not needed)
and `p` a prime divisor over `X` (`def:primdiv`: a connected smooth hypersurface `p.divisor` of a
smooth complex space `p.model` with a resolution `p.projection : p.model ⟶ X`). Then there is a
prime divisor `q` over `X`, equivalent to `p` (`commonResolutionRelation p q`: a common smooth
resolution on which both strict transforms coincide), realized on a modification of `X`: its
model `q.model` is smooth and `q.projection : q.model ⟶ X` is a finite composition of blowups
with smooth centres (`def:modif`); its divisor is a prime divisor on `q.model`. -/
theorem exists_modification_realization (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] (p : PrimePresentation X) :
    ∃ q : PrimePresentation X, IsModification q.projection ∧ commonResolutionRelation p q := by
  classical
  have hf : IsProperBimeromorphic p.projection := p.resolution.2
  -- Hironaka's Chow lemma: the smooth model is dominated by a modification `Y₀ → X`.
  obtain ⟨Y₀, σ₀, g₀, hσ₀, hg₀⟩ :=
    HironakaG10Complete.hironakaChowLemmaGeneral X p.model p.projection inferInstance hf
  have hY₀c : CompactSpace Y₀.obj.left := hσ₀.source_compact
  -- Resolution of `Y₀` by smooth-centre blowups (G11).
  obtain ⟨Y₁, r, -, hr, hY₁, -⟩ := HironakaG11PresUnconditional.exists_endpoint Y₀ hY₀c
  let σ₁ : Y₁ ⟶ X := r ≫ σ₀
  have hσ₁ : IsModification σ₁ := hr.comp hσ₀
  let g₁ : Y₁ ⟶ p.model := r ≫ g₀
  have hg₁f : g₁ ≫ p.projection = σ₁ := by
    simp only [g₁, σ₁, Category.assoc, hg₀]
  have hg₁ : IsProperBimeromorphic g₁ :=
    HironakaG10EpBimeromorphicCancel.isProperBimeromorphic_of_comp g₁ hf
      (isProperBimeromorphic_of_isModification hσ₁) hg₁f
  have hY₁c : CompactSpace Y₁.obj.left := hσ₁.source_compact
  -- The component of the model carrying `E`, and its native manifold model `M`.
  obtain ⟨c, hEc⟩ := exists_component_containing_divisor p
  obtain ⟨n, M, ⟨I⟩⟩ :=
    HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model p.smooth c
  let K : wholeModel (n := n) M ⟶ p.model :=
    I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion p.smooth c
  obtain ⟨k, hEM₀, hk, hEimage₀⟩ :=
    native_pullback_of_original_hypersurface p.smooth p.hypersurface c hEc M I
  have hEM : IsClosedConnectedSubmanifold n (pointMap K ⁻¹' p.divisor) k := hEM₀
  have hEimage : pointMap K '' (pointMap K ⁻¹' p.divisor) = p.divisor := hEimage₀
  -- The native component lift `gN : N → M` of `g₁`.
  obtain ⟨cY, N, J, G, hGpb, hGsq⟩ :=
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hY₁ p.smooth g₁ hg₁
      c M I
  let gN : N → M := nativePointMap G
  have hgN : IsAnalyticModification (n := n) gN :=
    isAnalyticModification_of_isProperBimeromorphic G hGpb
  let jc := HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₁ cY
  have hfull : nativeMorphism hgN.1 ≫ K = J.hom ≫ jc ≫ g₁ := by
    rw [show nativeMorphism hgN.1 = G from nativeMorphism_nativePointMap G]
    exact hGsq
  have hjco : LocallyRingedSpace.IsOpenImmersion jc.hom.left :=
    HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY₁ cY
  have hjcr : range jc.hom.left.base = OriginalSmoothComponents.componentSet cY :=
    HironakaG1NoncompactSmoothComponentModel.componentInclusion_range hY₁ cY
  have hjcc : IsClosed (range jc.hom.left.base) := by
    rw [hjcr]
    exact (OriginalSmoothComponents.component_isClopen hY₁ cY).1
  let inclusion :
      (HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ cY).obj.left → Y₁.obj.left :=
    jc.hom.left.base
  have : CompactSpace
      (HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ cY).obj.left :=
    (show Topology.IsClosedEmbedding inclusion from ⟨hjco.base_open.isEmbedding, hjcc⟩).compactSpace
  have : CompactSpace N := ((Homeomorph.Set.univ N).symm.trans (isoHomeomorph J)).symm.compactSpace
  -- The strict transform of `E` on the component and its embedded resolution.
  obtain ⟨VD, hVD, hdimD⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hEM
  have hcodim : VD.dim + 1 = n := by
    rw [hdimD]
    exact hk
  obtain ⟨VL, hVL, hdimL, -, -⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hgN VD hcodim
  obtain ⟨N', tN', cN', mN', μ, hμ, hres⟩ := EmbeddedResolution.exists_embeddedResolution VL
  let := tN'
  let := cN'
  let := mN'
  have hμmod : IsAnalyticModification (n := n) μ :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hμ
  -- The blowups of the component, extended to all of `Y₁`.
  let ρ₀ : wholeModel (n := n) N' ⟶ HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ cY :=
    nativeMorphism (n := n) (m := n) hμ.contMDiff ≫ J.hom
  have hρ₀ : IsModification ρ₀ :=
    HironakaG1NativeModificationIsoTransport.isModification_postcomp_iso
      (HironakaG10GenBlowupBridge.isModification_nativeMorphism hμ) J
  obtain ⟨Y₂, ρ, j', hρ, hj', hcomm, hrange, hiso⟩ :=
    HironakaG10GenDisjointModification.exists_modification_extension hρ₀ jc hjco hjcc
  have hY₂ : Y₂.IsSmooth := isSmooth_of_openImmersion_of_isIsoOver hY₁ j' hj' ρ _ hrange hiso
  have hj'c : IsClosed (range j'.hom.left.base) := by
    rw [hrange]
    exact hjcc.preimage ρ.hom.left.base.hom.continuous
  -- The realized prime divisor on the modification `Y₂ → X`.
  have hSdim : VL.dim + 1 = n := by
    rw [hdimL]
    exact hcodim
  obtain ⟨D, hDdef⟩ : ∃ D : Set Y₂.obj.left, D = pointMap j' '' strictTransform n μ VL.carrier :=
    ⟨_, rfl⟩
  have hD : IsOriginalHypersurface Y₂ D := by
    rw [hDdef]
    exact isOriginalHypersurface_image hY₂ j' hj' hj'c _ VL.dim hres.2 hSdim
  have hπ : IsModification (ρ ≫ σ₁) := hρ.comp hσ₁
  let q : PrimePresentation X :=
    { model := Y₂
      smooth := hY₂
      projection := ρ ≫ σ₁
      resolution := isResolution_of_isModification hπ hY₂
      divisor := D
      hypersurface := hD }
  refine ⟨q, hπ, ⟨?_⟩⟩
  have hρg₁ : IsProperBimeromorphic (ρ ≫ g₁) :=
    isProperBimeromorphic_comp (isProperBimeromorphic_of_isModification hρ) hg₁
  -- Pointwise squares.
  have hptG : ∀ x : N, pointMap K (gN x) =
      g₁.hom.left.base (jc.hom.left.base (J.hom.hom.left.base ⟨x, mem_univ x⟩)) := fun x =>
    congrArg (fun F : wholeModel (n := n) N ⟶ p.model => F.hom.left.base ⟨x, mem_univ x⟩) hfull
  have hptρ : ∀ z : N', ρ.hom.left.base (pointMap j' z) =
      jc.hom.left.base (J.hom.hom.left.base ⟨μ z, mem_univ (μ z)⟩) := fun z =>
    congrArg (fun F : wholeModel (n := n) N' ⟶ Y₁ => F.hom.left.base ⟨z, mem_univ z⟩) hcomm
  have hsq : ∀ z : N', (ρ ≫ g₁).hom.left.base (pointMap j' z) = pointMap K (gN (μ z)) := by
    intro z
    change g₁.hom.left.base (ρ.hom.left.base (pointMap j' z)) = _
    rw [hptρ, hptG]
  have hK : Function.Injective (pointMap K) := by
    let H : M ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject p.smooth c).obj.left :=
      (Homeomorph.Set.univ M).symm.trans (isoHomeomorph I)
    exact fun a b h => H.injective (Subtype.ext h)
  have hcomp : g₁.hom.left.base ⁻¹' OriginalSmoothComponents.componentSet c =
      OriginalSmoothComponents.componentSet cY :=
    PrimeNov16OriginalFibreDictionary.component_preimage_eq_of_actual_native_lift hY₁ p.smooth g₁
      hg₁ cY c N M J I gN hgN hfull
  have hpre : (ρ ≫ g₁).hom.left.base ⁻¹' range (pointMap K) ⊆ range (pointMap j') := by
    rintro t ⟨a, ha⟩
    have hc : g₁.hom.left.base (ρ.hom.left.base t) ∈ OriginalSmoothComponents.componentSet c := by
      change (ρ ≫ g₁).hom.left.base t ∈ _
      rw [← ha]
      exact (I.hom.hom.left.base ⟨a, mem_univ a⟩).property
    have hρt : ρ.hom.left.base t ∈ range jc.hom.left.base := by
      rw [hjcr, ← hcomp]
      exact hc
    have ht : t ∈ range j'.hom.left.base := by
      rw [hrange]
      exact hρt
    obtain ⟨b, rfl⟩ := ht
    exact ⟨b.1, rfl⟩
  have hA : p.divisor ⊆ range (pointMap K) := by
    intro e he
    rw [← hEimage] at he
    obtain ⟨z, -, rfl⟩ := he
    exact ⟨z, rfl⟩
  have hsingle : singletonLocus (𝟙 Y₂) = univ := by
    ext x
    simp only [singletonLocus, Set.mem_ofPred_eq, mem_univ, iff_true]
    intro t ht
    exact ht
  have hR : originalStrictTransform (𝟙 Y₂) D = D := by
    change closure ((𝟙 Y₂ : Y₂ ⟶ Y₂).hom.left.base ⁻¹' D ∩ singletonLocus (𝟙 Y₂)) = D
    rw [hsingle, inter_univ]
    exact hD.1.closure_eq
  refine
    { model := Y₂
      smooth := hY₂
      left := ρ ≫ g₁
      right := 𝟙 Y₂
      left_modification := hρg₁
      right_modification := isProperBimeromorphic_id' Y₂
      over_base := ?_
      resolution := ⟨hY₂, isProperBimeromorphic_comp hρg₁ hf⟩
      strict_equal := ?_ }
  · change (ρ ≫ g₁) ≫ p.projection = 𝟙 Y₂ ≫ (ρ ≫ σ₁)
    rw [Category.assoc, hg₁f, Category.id_comp]
  · change originalStrictTransform (ρ ≫ g₁) p.divisor = originalStrictTransform (𝟙 Y₂) D
    rw [hR, originalStrictTransform_eq_image (ρ ≫ g₁) j' hj' hj'c K hK
      (AnalyticModificationComposition.isAnalyticModification_comp hgN hμmod) hsq hpre
      p.divisor hA]
    rw [StrictTransformComposition.strictTransform_comp hgN.1 hμ.contMDiff, ← hVD, ← hVL, hDdef]

/-- **`cor:primerealization`, for classes of prime divisors.** Every prime divisor over a compact
complex space `X` (an element of `PrimeOver X`, `def:primdiv`) is the class of a prime divisor on a
smooth modification of `X`. -/
theorem exists_modification_realization_primeOver (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] (e : PrimeOver X) :
    ∃ q : PrimePresentation X, IsModification q.projection ∧
      (Quot.mk commonResolutionRelation q : PrimeOver X) = e := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep e
  obtain ⟨q, hq, hpq⟩ := exists_modification_realization X p
  exact ⟨q, hq, (mk_eq_iff q p).mpr (commonResolutionRelation_symm hpq)⟩

end SGPT.Unibranch.CHPrimeRealization
