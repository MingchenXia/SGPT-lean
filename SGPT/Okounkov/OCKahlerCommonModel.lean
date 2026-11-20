import SGPT.Okounkov.OCLiftableFlag
import SGPT.Okounkov.ResolvedStrictTransformModification
import SGPT.PSH.PrimeNov16OriginalComponentGoodRestriction
import SGPT.PSH.PrimeNov16OriginalGoodTransition
import SGPT.PSH.PrimeNov16OriginalPairedCommon
import SGPT.Foundations.Analysis.Pending.HironakaResolutionKahler
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict

/-!
# Kähler common models over a reduced space

Source `lma:modelvalcurrbir` (`chapter_Okounkov.tex`), proof of independence of the choice of `h`:
"Let `h_i : Ẑ_i → Z`, `i = 1, 2`, be two choices ... Choose a common modification over `Z`,
`q_i : U → Ẑ_i`". The valuation of currents is only available on compact Kähler manifolds, so the
common model must be a compact Kähler manifold.

`exists_kahler_commonModel`: for two compact connected Kähler manifolds `Y₀, Y₁` with proper
bimeromorphic morphisms `F_i : (Y_i, 𝒪) ⟶ Z` to an arbitrary reduced complex space `Z`, there is a
compact connected Kähler manifold `U` with analytic modifications `g_i : U → Y_i` such that
`g₀ ≫ F₀ = g₁ ≫ F₁`. The model is the Kähler embedded resolution of the closure `V` of the graph of
the bimeromorphic map `Y₁ ⇢ Y₀` inside the compact Kähler manifold `Y₀ × Y₁`
(`HironakaResolutionKahler.exists_kahler_strictTransform_resolution`); the graph construction and
the good-open transition are the existing ones of the smooth common resolution
(`PrimeNov16OriginalTransitionGraph`, `PrimeNov16OriginalGoodTransition`). No Chow lemma is used.

Blueprint: `blueprint/src/oc.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OCKahlerCommonModel

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaResolutionSpaceComplex HironakaResolutionSpace BlowupTowers
open HironakaEmbeddedAnalytic (singularSet)
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
  OriginalProperBimeromorphicNative OriginalSmoothSourceAnalytic
open SGPT.PSH
open scoped Topology Manifold ContDiff ProductComplexManifold

section Core

variable {X : SourceReducedComplexSpace} {n : ℕ} {Y₀ Y₁ : Type}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [CompactSpace Y₀] [CompactSpace Y₁] [ConnectedSpace Y₁]

/-- **Kähler common model from good-open transition data.** The Kähler embedded resolution of
the closure of the transition graph in `Y₀ × Y₁` is a compact connected Kähler manifold with two
analytic modifications over the same map to `X`. -/
theorem exists_kahler_paired_common_maps
    (ω₀ : KahlerBackground n Y₀) (ω₁ : KahlerBackground n Y₁)
    (F₀ : wholeModel (n := n) Y₀ ⟶ X) (F₁ : wholeModel (n := n) Y₁ ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B)
    (hA₀ : IsComplexAnalyticSubset (n := n) (pointMap F₀ ⁻¹' B))
    (hA₁ : IsComplexAnalyticSubset (n := n) (pointMap F₁ ⁻¹' B))
    (hn₀ : interior (pointMap F₀ ⁻¹' B) = ∅) (hn₁ : interior (pointMap F₁ ⁻¹' B) = ∅)
    (e : OriginalCommonResolution.goodOpen F₁ B hBc
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      OriginalCommonResolution.goodOpen F₀ B hBc)
    (he : ∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val)
    (hinj : InjOn (pointMap F₀) (pointMap F₀ ⁻¹' Bᶜ)) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : ChartedSpace (ComplexModel n) U)
      (_ : IsComplexManifold n U) (_ : CompactSpace U) (_ : ConnectedSpace U)
      (_ : KahlerBackground n U) (g₀ : U → Y₀) (g₁ : U → Y₁)
      (hg₀ : IsAnalyticModification (n := n) g₀) (hg₁ : IsAnalyticModification (n := n) g₁),
      nativeMorphism hg₀.1 ≫ F₀ = nativeMorphism hg₁.1 ≫ F₁ := by
  classical
  obtain ⟨V, hVdim, hVclosure, hVF, hGreg, -⟩ :=
    PrimeNov16OriginalTransitionGraph.exists_actual_transition_graph_manifold
      F₀ F₁ B hBc hA₀ hA₁ hn₁ e he hinj
  let S : Set (Y₀ × Y₁) := {p | pointMap F₀ p.1 = pointMap F₁ p.2 ∧ pointMap F₀ p.1 ∉ B}
  -- The Kähler embedded resolution of `V` in the compact Kähler manifold `Y₀ × Y₁`.
  have hVa : IsComplexAnalyticSubset (n := n + n) V.carrier := V.irreducible_carrier.analytic
  have hpure : AnalyticDimensionBasics.IsPureDim (n := n + n) V.carrier n :=
    fun y j hy => (PureDimension.eq_dim_of_regularAtDim V hy).trans hVdim
  have hd : n ≤ n + n := Nat.le_add_right n n
  obtain ⟨M', topM', chartsM', complexM', σ, E, hST, hreg, _ω', hCM, hcpt, ωT, -, hval⟩ :=
    HironakaResolutionKahler.exists_kahler_strictTransform_resolution hVa hpure hd
      (ProductComplexManifold.prodKahlerBackground ω₀ ω₁)
  let := topM'
  let := chartsM'
  have := complexM'
  let := SubmanifoldChartedSpace.chartedSpace hd hreg
  have := hCM
  have := hcpt
  have hSgc : IsClosed (singularSet (n := n + n) V.carrier) :=
    HironakaEmbeddedAnalytic.isClosed_singularSet V.isClosed_carrier
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞ σ :=
    hST.contMDiff
  have hiso : IsIsomorphismOver (n + n) σ (singularSet (n := n + n) V.carrier)ᶜ :=
    hST.isIsomorphismOver
  -- Regular graph points.
  have hSV : S ⊆ V.carrier := by
    rw [hVclosure]
    exact subset_closure
  have hSreg : ∀ p ∈ S, p ∉ singularSet (n := n + n) V.carrier := by
    intro p hp hpS
    exact ((HironakaEmbeddedAnalytic.mem_singularSet_iff.mp hpS).2 n) (hGreg p hp)
  -- The projections from the resolved graph.
  let q : strictTransform (n + n) σ V.carrier → Y₀ × Y₁ := fun t => σ t.val
  have hq : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ q := hσ.comp hval
  have hqV : ∀ t, q t ∈ V.carrier := by
    intro t
    have hmem := mem_image_of_mem σ t.property
    rw [hST.image_eq] at hmem
    exact hmem
  let g₀ : strictTransform (n + n) σ V.carrier → Y₀ := fun t => (q t).1
  let g₁ : strictTransform (n + n) σ V.carrier → Y₁ := fun t => (q t).2
  have hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀ :=
    (ProductComplexManifold.contMDiff_fst (n := n) (m := n)).comp hq
  have hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ :=
    (ProductComplexManifold.contMDiff_snd (n := n) (m := n)).comp hq
  have hbase (t : strictTransform (n + n) σ V.carrier) : pointMap F₀ (g₀ t) = pointMap F₁ (g₁ t) := hVF (hqV t)
  have hgp₀ : IsProperMap g₀ := hg₀.continuous.isProperMap
  have hgp₁ : IsProperMap g₁ := hg₁.continuous.isProperMap
  -- The inverse of `σ` over the regular part.
  have hnonempty : Nonempty M' := by
    obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hn₁).nonempty
    let x' : OriginalCommonResolution.goodOpen F₁ B hBc := ⟨x, hx⟩
    have hp : ((e x').val, x) ∈ S := ⟨he x', by rw [he x']; exact hx⟩
    have hpV : ((e x').val, x) ∈ σ '' strictTransform (n + n) σ V.carrier := by
      rw [hST.image_eq]
      exact hSV hp
    obtain ⟨t, -, -⟩ := hpV
    exact ⟨t⟩
  let τ : Y₀ × Y₁ → M' := ModificationMassInvariance.invOver σ (singularSet (n := n + n) V.carrier)ᶜ
  have hτ : ContMDiffOn 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞ τ
      (singularSet (n := n + n) V.carrier)ᶜ :=
    contMDiffOn_invOver_of_isIsomorphismOver hσ hSgc.isOpen_compl hiso
  have hτS (p : Y₀ × Y₁) (hp : p ∈ S) :
      τ p ∈ strictTransform (n + n) σ V.carrier ∧ σ (τ p) = p := by
    obtain ⟨-, heq0⟩ := ModificationMassInvariance.invOver_mem hiso (hSreg p hp)
    have heq : σ (τ p) = p := heq0
    refine ⟨?_, heq⟩
    have hin : τ p ∈ σ ⁻¹' (V.carrier \ singularSet (n := n + n) V.carrier) := by
      change σ (τ p) ∈ V.carrier \ singularSet (n := n + n) V.carrier
      rw [heq]
      exact ⟨hSV hp, hSreg p hp⟩
    rw [← hST.inter_preimage_compl] at hin
    exact hin.1
  have hτapp : ∀ y : M', y ∈ σ ⁻¹' (singularSet (n := n + n) V.carrier)ᶜ → τ (σ y) = y :=
    fun y hy => ModificationMassInvariance.invOver_apply hiso hy
  have hτσ (t : strictTransform (n + n) σ V.carrier)
      (ht : q t ∉ singularSet (n := n + n) V.carrier) : τ (q t) = t.val :=
    ModificationMassInvariance.invOver_apply hiso ht
  -- Inverse on the good open of `Y₁`.
  let U₁ := OriginalCommonResolution.goodOpen F₁ B hBc
  let U₀ := OriginalCommonResolution.goodOpen F₀ B hBc
  let γ₁ : U₁ → Y₀ × Y₁ := fun x => ((e x).val, x.val)
  have hγ₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ γ₁ :=
    ProductComplexManifold.contMDiff_prodMk (contMDiff_subtype_val.comp e.contMDiff)
      contMDiff_subtype_val
  have hγ₁S (x : U₁) : γ₁ x ∈ S := by
    refine ⟨he x, ?_⟩
    rw [he x]
    exact x.property
  have hσ₁' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ (τ ∘ γ₁) :=
    hτ.comp_contMDiff hγ₁ (fun x => hSreg _ (hγ₁S x))
  let σ₁ : U₁ → strictTransform (n + n) σ V.carrier := fun x => ⟨τ (γ₁ x), (hτS _ (hγ₁S x)).1⟩
  have hσ₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ₁ :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hd hreg hσ₁' (fun x => (hτS _ (hγ₁S x)).1)
  have hqσ₁ (x : U₁) : q (σ₁ x) = γ₁ x := (hτS _ (hγ₁S x)).2
  have hg₁σ₁ (x : U₁) : g₁ (σ₁ x) = x.val := congrArg Prod.snd (hqσ₁ x)
  have hσ₁g₁ (t : strictTransform (n + n) σ V.carrier) (ht : g₁ t ∉ pointMap F₁ ⁻¹' B) : σ₁ ⟨g₁ t, ht⟩ = t := by
    let x : U₁ := ⟨g₁ t, ht⟩
    have hSt : q t ∈ S := by
      refine ⟨hbase t, ?_⟩
      change pointMap F₁ (g₁ t) ∉ B at ht
      exact (hbase t) ▸ ht
    have hx : (e x).val = g₀ t := hinj (e x).property hSt.2 ((he x).trans (hbase t).symm)
    have hpair : γ₁ x = q t := Prod.ext hx rfl
    apply Subtype.ext
    change τ (γ₁ x) = t.val
    rw [hpair]
    exact hτσ t (hSreg _ hSt)
  -- Inverse on the good open of `Y₀`.
  let γ₀ : U₀ → Y₀ × Y₁ := fun x => (x.val, (e.symm x).val)
  have hγ₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ γ₀ :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_subtype_val
      (contMDiff_subtype_val.comp e.symm.contMDiff)
  have hγ₀S (x : U₀) : γ₀ x ∈ S := by
    refine ⟨?_, x.property⟩
    simpa only [e.apply_symm_apply] using he (e.symm x)
  have hσ₀' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ (τ ∘ γ₀) :=
    hτ.comp_contMDiff hγ₀ (fun x => hSreg _ (hγ₀S x))
  let σ₀ : U₀ → strictTransform (n + n) σ V.carrier := fun x => ⟨τ (γ₀ x), (hτS _ (hγ₀S x)).1⟩
  have hσ₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ₀ :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hd hreg hσ₀' (fun x => (hτS _ (hγ₀S x)).1)
  have hqσ₀ (x : U₀) : q (σ₀ x) = γ₀ x := (hτS _ (hγ₀S x)).2
  have hg₀σ₀ (x : U₀) : g₀ (σ₀ x) = x.val := congrArg Prod.fst (hqσ₀ x)
  have hσ₀g₀ (t : strictTransform (n + n) σ V.carrier) (ht : g₀ t ∉ pointMap F₀ ⁻¹' B) : σ₀ ⟨g₀ t, ht⟩ = t := by
    let x : U₀ := ⟨g₀ t, ht⟩
    have hSt : q t ∈ S := ⟨hbase t, ht⟩
    let y : U₁ := ⟨g₁ t, by
      change pointMap F₁ (g₁ t) ∉ B
      exact (hbase t).symm ▸ ht⟩
    have hy : e y = x := Subtype.ext (hinj (e y).property ht ((he y).trans (hbase t).symm))
    have hxy : e.symm x = y := by
      apply e.injective
      exact (e.apply_symm_apply x).trans hy.symm
    have hpair : γ₀ x = q t := Prod.ext rfl (congrArg Subtype.val hxy)
    apply Subtype.ext
    change τ (γ₀ x) = t.val
    rw [hpair]
    exact hτσ t (hSreg _ hSt)
  -- Connectedness of the resolved graph: the regular graph is connected and dense.
  have hUne : ((pointMap F₁ ⁻¹' B)ᶜ).Nonempty :=
    (interior_eq_empty_iff_dense_compl.mp hn₁).nonempty
  have hDne : pointMap F₁ ⁻¹' B ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := hUne
    exact hx (h ▸ mem_univ x)
  have hUconn : IsConnected (pointMap F₁ ⁻¹' B)ᶜ :=
    ⟨hUne, AnalyticComplementConnected.isPreconnected_compl hA₁ hDne⟩
  let : ConnectedSpace U₁ := by
    change ConnectedSpace ↥((pointMap F₁ ⁻¹' B)ᶜ)
    exact isConnected_iff_connectedSpace.mp hUconn
  have hRconn : IsConnected (range σ₁) := isConnected_range hσ₁.continuous
  have hsub : σ ⁻¹' (V.carrier \ singularSet (n := n + n) V.carrier) ⊆
      closure (Subtype.val '' range σ₁) := by
    intro y hy
    have hyc : σ y ∈ closure S := hVclosure ▸ hy.1
    have hcont : ContinuousAt τ (σ y) :=
      hτ.continuousOn.continuousAt (hSgc.isOpen_compl.mem_nhds hy.2)
    have hmem := mem_closure_image hcont hyc
    rw [hτapp y hy.2] at hmem
    refine closure_mono ?_ hmem
    rintro _ ⟨p, hp, rfl⟩
    let x : U₁ := ⟨p.2, by
      change pointMap F₁ p.2 ∉ B
      rw [← hp.1]
      exact hp.2⟩
    have hx : (e x).val = p.1 := hinj (e x).property hp.2 ((he x).trans hp.1.symm)
    have hγ : γ₁ x = p := Prod.ext hx rfl
    exact ⟨σ₁ x, ⟨x, rfl⟩, by change τ (γ₁ x) = τ p; rw [hγ]⟩
  have hRdense : Dense (range σ₁) := by
    rw [Subtype.dense_iff]
    intro t ht
    rw [hST.eq_closure] at ht
    exact closure_minimal hsub isClosed_closure ht
  have : ConnectedSpace (strictTransform (n + n) σ V.carrier) :=
    connectedSpace_iff_univ.mpr (hRdense.closure_eq ▸ hRconn.closure)
  -- Analytic modifications.
  have hm₀ : IsAnalyticModification (n := n) g₀ :=
    PrimeNov16OriginalOpenInverse.isAnalyticModification_of_open_inverse hg₀ hgp₀ hA₀ hn₀
      σ₀ hσ₀ hg₀σ₀ hσ₀g₀
  have hm₁ : IsAnalyticModification (n := n) g₁ :=
    PrimeNov16OriginalOpenInverse.isAnalyticModification_of_open_inverse hg₁ hgp₁ hA₁ hn₁
      σ₁ hσ₁ hg₁σ₁ hσ₁g₁
  refine ⟨strictTransform (n + n) σ V.carrier, inferInstance, inferInstance, hCM, hcpt,
    inferInstance, ωT, g₀, g₁, hm₀, hm₁, ?_⟩
  exact SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun t => hbase t.val)

end Core

/-! ### Two compact connected Kähler choices over a reduced space -/

private theorem native_bad_thin' {X Y : SourceReducedComplexSpace}
    (hY : Y.IsSmooth) (F : Y ⟶ X) (B : Set X.obj.left)
    (ht : interior (F.hom.left.base ⁻¹' B) = ∅)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (E : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    interior (pointMap (E.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c ≫
      F) ⁻¹' B) = ∅ := by
  let C := HironakaG1NoncompactSmoothComponentModel.componentObject hY c
  let j := HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  let H : M ≃ₜ C.obj.left := (Homeomorph.Set.univ M).symm.trans (isoHomeomorph E)
  have hjo : IsOpenMap (j.hom.left.base ∘ H) :=
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY
      c).base_open.isOpenMap.comp H.isOpenMap
  have hjc : Continuous (j.hom.left.base ∘ H) := j.hom.left.base.hom.continuous.comp H.continuous
  have hi := hjo.preimage_interior_eq_interior_preimage hjc (F.hom.left.base ⁻¹' B)
  exact hi.symm.trans (congrArg (fun A : Set Y.obj.left => (j.hom.left.base ∘ H) ⁻¹' A) ht)

/-- **Kähler common model of two choices.** For compact connected Kähler manifolds `Y₀, Y₁` and
proper bimeromorphic morphisms `F_i : (Y_i, 𝒪) ⟶ X` to an arbitrary reduced complex space, there
is a compact connected Kähler manifold `U` with analytic modifications `g_i : U → Y_i` and
`g₀ ≫ F₀ = g₁ ≫ F₁`. -/
theorem exists_kahler_commonModel {X : SourceReducedComplexSpace} {n : ℕ} {Y₀ Y₁ : Type}
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [CompactSpace Y₀] [CompactSpace Y₁] [ConnectedSpace Y₀] [ConnectedSpace Y₁]
    (ω₀ : KahlerBackground n Y₀) (ω₁ : KahlerBackground n Y₁)
    (F₀ : wholeModel (n := n) Y₀ ⟶ X) (F₁ : wholeModel (n := n) Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : ChartedSpace (ComplexModel n) U)
      (_ : IsComplexManifold n U) (_ : CompactSpace U) (_ : ConnectedSpace U)
      (_ : KahlerBackground n U) (g₀ : U → Y₀) (g₁ : U → Y₁)
      (hg₀ : IsAnalyticModification (n := n) g₀) (hg₁ : IsAnalyticModification (n := n) g₁),
      nativeMorphism hg₀.1 ≫ F₀ = nativeMorphism hg₁.1 ≫ F₁ := by
  obtain ⟨E₀, E₁, hE₀, hE₁, hi₀, hi₁, ht₀, ht₁, pair, hpair⟩ :=
    PrimeNov16OriginalComponentPairing.exists_original_good_component_pairing
      (isSmooth_wholeModel (n := n) (M := Y₀)) (isSmooth_wholeModel (n := n) (M := Y₁))
      F₀ F₁ hF₀ hF₁
  let B := E₀ ∪ E₁
  have hBc : IsClosed B := hE₀.isClosed.union hE₁.isClosed
  obtain ⟨y1⟩ := (inferInstance : Nonempty Y₁)
  let c₁ : ConnectedComponents (wholeModel (n := n) Y₁).obj.left :=
    ConnectedComponents.mk (⟨y1, mem_univ y1⟩ : (univ : Set Y₁))
  let c₀ := pair c₁
  let I₀ := OCLiftableFlag.wholeModelComponentIso (n := n) Y₀ c₀
  let I₁ := OCLiftableFlag.wholeModelComponentIso (n := n) Y₁ c₁
  have hI₀ : I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion
      (isSmooth_wholeModel (n := n) (M := Y₀)) c₀ = 𝟙 _ :=
    OCLiftableFlag.wholeModelComponentIso_hom_comp_inclusion (n := n) Y₀ c₀
  have hI₁ : I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion
      (isSmooth_wholeModel (n := n) (M := Y₁)) c₁ = 𝟙 _ :=
    OCLiftableFlag.wholeModelComponentIso_hom_comp_inclusion (n := n) Y₁ c₁
  let P₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion
    (isSmooth_wholeModel (n := n) (M := Y₀)) c₀ ≫ F₀
  let P₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion
    (isSmooth_wholeModel (n := n) (M := Y₁)) c₁ ≫ F₁
  have hP₀ : P₀ = F₀ := by
    change I₀.hom ≫ _ ≫ F₀ = F₀
    rw [← Category.assoc, hI₀, Category.id_comp]
  have hP₁ : P₁ = F₁ := by
    change I₁.hom ≫ _ ≫ F₁ = F₁
    rw [← Category.assoc, hI₁, Category.id_comp]
  have hn₀ := native_bad_thin' isSmooth_wholeModel F₀ B ht₀ c₀ (CMfd.of (n := n) Y₀) I₀
  have hn₁ := native_bad_thin' isSmooth_wholeModel F₁ B ht₁ c₁ (CMfd.of (n := n) Y₁) I₁
  obtain ⟨r₀, hr₀⟩ := PrimeNov16OriginalComponentGoodRestriction.native_component_good_restriction
    isSmooth_wholeModel F₀ B hBc hi₀ c₀ (CMfd.of (n := n) Y₀) I₀
  obtain ⟨r₁, hr₁⟩ := PrimeNov16OriginalComponentGoodRestriction.native_component_good_restriction
    isSmooth_wholeModel F₁ B hBc hi₁ c₁ (CMfd.of (n := n) Y₁) I₁
  have hrange := hr₁.trans ((hpair c₁).symm.trans hr₀.symm)
  obtain ⟨e, he, hinj⟩ :=
    PrimeNov16OriginalGoodTransition.exists_actual_good_transition P₀ P₁ B hBc r₀ r₁ hrange
  have hA₀ : IsComplexAnalyticSubset (n := n) (pointMap P₀ ⁻¹' B) := by
    rw [show B = E₀ ∪ E₁ from rfl, preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage P₀ hE₀) (isComplexAnalyticSubset_preimage P₀ hE₁)
  have hA₁ : IsComplexAnalyticSubset (n := n) (pointMap P₁ ⁻¹' B) := by
    rw [show B = E₀ ∪ E₁ from rfl, preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage P₁ hE₀) (isComplexAnalyticSubset_preimage P₁ hE₁)
  obtain ⟨U, topU, chartsU, complexU, compactU, connU, ωU, g₀, g₁, hg₀, hg₁, hsq⟩ :=
    exists_kahler_paired_common_maps ω₀ ω₁ P₀ P₁ B hBc hA₀ hA₁ hn₀ hn₁ e he hinj
  refine ⟨U, topU, chartsU, complexU, compactU, connU, ωU, g₀, g₁, hg₀, hg₁, ?_⟩
  rwa [hP₀, hP₁] at hsq

end SGPT.Okounkov.OCKahlerCommonModel
