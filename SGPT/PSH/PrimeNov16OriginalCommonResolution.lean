import SGPT.PSH.PrimeNov16OriginalGraphManifold
import SGPT.PSH.PrimeNov16OriginalOpenInverse
import SGPT.PSH.PrimeNov16IsoOverLift
import SGPT.Unibranch.OriginalProperBimeromorphicNative
import SGPT.Foundations.Analysis.Pending.AnalyticFibreProductProperProjections

/-! Actual ORIGINAL noncompact common resolutions over possibly singular bases.
The SAME actual composite is proved a resolution on the exact original bad
union. No general PB-composition or desired common-resolution input is assumed.
Connected native source and equal dimensions remain explicit intermediate scope.
Blueprint first: `prime-nov16-original-prime-models.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16OriginalCommonResolution
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaResolutionSpaceComplex HironakaIntrinsicComplexAnalyticRegularLocus BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
  OriginalProperBimeromorphicNative OriginalSmoothSourceAnalytic
open scoped Topology Manifold ContDiff ProductComplexManifold

variable {X : SourceReducedComplexSpace} {n : ℕ} {Y₀ Y₁ : Type}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [ConnectedSpace Y₁]

/-- ORIGINAL proper-bimeromorphic maps to an arbitrary possibly singular X
construct genuine common maps and an actual resolution of the SAME composite.
There is no supplied common model/resolution and no compactness assumption. -/
theorem exists_actual_original_common_resolution
    (F₀ : wholeModel (n := n) Y₀ ⟶ X) (F₁ : wholeModel (n := n) Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (M : CMfd.{0} n) (_ : ConnectedSpace M) (g₀ : M → Y₀) (g₁ : M → Y₁)
      (hg₀ : IsAnalyticModification (n := n) g₀)
      (hg₁ : IsAnalyticModification (n := n) g₁),
      nativeMorphism hg₀.1 ≫ F₀ = nativeMorphism hg₁.1 ≫ F₁ ∧
      IsResolution (nativeMorphism hg₁.1 ≫ F₁) := by
  classical
  obtain ⟨B, hBc, hBa, hBt, hA₀, hA₁, hn₀, hn₁, _hi₀, hi₁,
    e, he, hinj, V, _hVdim, hVclosure, hVF, hGreg, M, hMconn, ⟨E⟩⟩ :=
    PrimeNov16OriginalGraphManifold.exists_actual_original_graph_manifold F₀ F₁ hF₀ hF₁
  let : ConnectedSpace M := hMconn
  let A := ofClosedAnalytic V.carrier V.analytic
  let R := OriginalNativeHSGlobalResolution.source A
  let ρ : R ⟶ A := OriginalNativeHSGlobalResolution.projection A
  let q : wholeModel (n := n) M ⟶ A := E.hom ≫ ρ
  let p₀ : A ⟶ wholeModel (n := n) Y₀ := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ProductComplexManifold.contMDiff_fst (n := n) (m := n)) (fun _ _ => mem_univ _))
    (actualSubspaceMap_point (ProductComplexManifold.contMDiff_fst (n := n) (m := n)) (fun _ _ => mem_univ _)))
  let p₁ : A ⟶ wholeModel (n := n) Y₁ := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ProductComplexManifold.contMDiff_snd (n := n) (m := n)) (fun _ _ => mem_univ _))
    (actualSubspaceMap_point (ProductComplexManifold.contMDiff_snd (n := n) (m := n)) (fun _ _ => mem_univ _)))
  let g₀ : M → Y₀ := nativePointMap (q ≫ p₀)
  let g₁ : M → Y₁ := nativePointMap (q ≫ p₁)
  have hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀ := nativePointMap_contMDiff (q ≫ p₀)
  have hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ := nativePointMap_contMDiff (q ≫ p₁)
  let Q : M → V.carrier := fun z => q.hom.left.base ⟨z, mem_univ z⟩
  have hQproper : IsProperMap Q := (OriginalNativeHSGlobalResolution.proper A).comp
    ((isoHomeomorph E).isProperMap.comp (Homeomorph.Set.univ M).symm.isProperMap)
  have hc₀proper : IsProperMap (pointMap F₀) :=
    hF₀.1.comp (Homeomorph.Set.univ Y₀).symm.isProperMap
  have hc₁proper : IsProperMap (pointMap F₁) :=
    hF₁.1.comp (Homeomorph.Set.univ Y₁).symm.isProperMap
  have hp₀ : IsProperMap (fun v : V.carrier => v.val.1) :=
    AnalyticFibreProductProperProjections.isProperMap_fst_of_closed_fibreProduct
      (continuous_pointMap F₀) hc₁proper V.isClosed_carrier hVF
  have hp₁ : IsProperMap (fun v : V.carrier => v.val.2) :=
    AnalyticFibreProductProperProjections.isProperMap_snd_of_closed_fibreProduct
      hc₀proper (continuous_pointMap F₁) V.isClosed_carrier hVF
  have hgp₀ : IsProperMap g₀ := hp₀.comp hQproper
  have hgp₁ : IsProperMap g₁ := hp₁.comp hQproper
  have hbase (z : M) : pointMap F₀ (g₀ z) = pointMap F₁ (g₁ z) := hVF (Q z).property
  let U₀ := OriginalCommonResolution.goodOpen F₀ B hBc
  let U₁ := OriginalCommonResolution.goodOpen F₁ B hBc
  let S : Set (Y₀ × Y₁) := {v | pointMap F₀ v.1 = pointMap F₁ v.2 ∧ pointMap F₀ v.1 ∉ B}
  have hregular (v : V.carrier) (hv : v.val ∈ S) : intrinsicRegularAtDim A.obj v n := by
    obtain ⟨O, i, hi, hp, hx⟩ := exists_native_chart V.carrier (hGreg _ hv)
    exact ⟨O, i, hi, hp, hx⟩
  have hQinj {w z : M} (hw : (Q w).val ∈ S) (hz : (Q z).val ∈ S) (heq : Q w = Q z) : w = z := by
    have hwreg : Q w ∈ intrinsicRegularLocus A.obj := ⟨n, hregular _ hw⟩
    have hzreg : Q z ∈ intrinsicRegularLocus A.obj := ⟨n, hregular _ hz⟩
    have hEeq := PrimeNov16IsoOverLift.injOn_preimage (OriginalNativeHSGlobalResolution.originalReg A)
      hwreg hzreg heq
    exact congrArg Subtype.val ((isoHomeomorph E).injective hEeq)
  let γ₁ : U₁ → Y₀ × Y₁ := fun x => ((e x).val, x.val)
  have hγ₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n+n)) ∞ γ₁ :=
    ProductComplexManifold.contMDiff_prodMk (contMDiff_subtype_val.comp e.contMDiff) contMDiff_subtype_val
  have hγ₁S (x : U₁) : γ₁ x ∈ S := by
    refine ⟨he x, ?_⟩
    rw [he x]
    exact x.property
  have hγ₁V (x : U₁) : γ₁ x ∈ V.carrier := hVclosure.symm ▸ subset_closure (hγ₁S x)
  let L₁ : wholeModel (n := n) U₁ ⟶ A := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hγ₁ (fun x _ => hγ₁V x)) (actualSubspaceMap_point hγ₁ (fun x _ => hγ₁V x)))
  have hL₁ : range L₁.hom.left.base ⊆ intrinsicRegularLocus A.obj := by
    rintro _ ⟨x, rfl⟩
    exact ⟨n, hregular _ (hγ₁S x.val)⟩
  obtain ⟨T₁, hT₁⟩ := PrimeNov16IsoOverLift.exists_native_lift ρ
    (OriginalNativeHSGlobalResolution.originalReg A) E L₁ hL₁
  let σ₁ : U₁ → M := nativePointMap T₁
  have hσ₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ₁ := nativePointMap_contMDiff T₁
  have hQσ₁ (x : U₁) : (Q (σ₁ x)).val = γ₁ x :=
    congrArg (fun H : wholeModel (n := n) U₁ ⟶ A => (H.hom.left.base ⟨x, mem_univ x⟩).val) hT₁
  have hg₁σ₁ (x : U₁) : g₁ (σ₁ x) = x.val := congrArg Prod.snd (hQσ₁ x)
  have hσ₁g₁ (z : M) (hz : g₁ z ∉ pointMap F₁ ⁻¹' B) : σ₁ ⟨g₁ z, hz⟩ = z := by
    let x : U₁ := ⟨g₁ z, hz⟩
    have hSz : (Q z).val ∈ S := by
      change pointMap F₀ (g₀ z) = pointMap F₁ (g₁ z) ∧ pointMap F₀ (g₀ z) ∉ B
      refine ⟨hbase z, ?_⟩
      change pointMap F₁ (g₁ z) ∉ B at hz
      exact (hbase z) ▸ hz
    have hx : (e x).val = g₀ z := hinj (e x).property hSz.2 ((he x).trans (hbase z).symm)
    have hpair : (Q z).val = γ₁ x := Prod.ext hx.symm rfl
    apply hQinj (w := σ₁ x) (z := z) (by rw [hQσ₁ x]; exact hγ₁S x) hSz
    exact Subtype.ext ((hQσ₁ x).trans hpair.symm)
  let γ₀ : U₀ → Y₀ × Y₁ := fun x => (x.val, (e.symm x).val)
  have hγ₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n+n)) ∞ γ₀ :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_subtype_val (contMDiff_subtype_val.comp e.symm.contMDiff)
  have hγ₀S (x : U₀) : γ₀ x ∈ S := by
    refine ⟨?_, x.property⟩
    simpa only [e.apply_symm_apply] using he (e.symm x)
  have hγ₀V (x : U₀) : γ₀ x ∈ V.carrier := hVclosure.symm ▸ subset_closure (hγ₀S x)
  let L₀ : wholeModel (n := n) U₀ ⟶ A := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hγ₀ (fun x _ => hγ₀V x)) (actualSubspaceMap_point hγ₀ (fun x _ => hγ₀V x)))
  have hL₀ : range L₀.hom.left.base ⊆ intrinsicRegularLocus A.obj := by
    rintro _ ⟨x, rfl⟩
    exact ⟨n, hregular _ (hγ₀S x.val)⟩
  obtain ⟨T₀, hT₀⟩ := PrimeNov16IsoOverLift.exists_native_lift ρ
    (OriginalNativeHSGlobalResolution.originalReg A) E L₀ hL₀
  let σ₀ : U₀ → M := nativePointMap T₀
  have hσ₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ₀ := nativePointMap_contMDiff T₀
  have hQσ₀ (x : U₀) : (Q (σ₀ x)).val = γ₀ x :=
    congrArg (fun H : wholeModel (n := n) U₀ ⟶ A => (H.hom.left.base ⟨x, mem_univ x⟩).val) hT₀
  have hg₀σ₀ (x : U₀) : g₀ (σ₀ x) = x.val := congrArg Prod.fst (hQσ₀ x)
  have hσ₀g₀ (z : M) (hz : g₀ z ∉ pointMap F₀ ⁻¹' B) : σ₀ ⟨g₀ z, hz⟩ = z := by
    let x : U₀ := ⟨g₀ z, hz⟩
    have hSz : (Q z).val ∈ S := ⟨hbase z, hz⟩
    let y : U₁ := ⟨g₁ z, by
      change pointMap F₁ (g₁ z) ∉ B
      exact (hbase z).symm ▸ hz⟩
    have hy : e y = x := Subtype.ext (hinj (e y).property hz ((he y).trans (hbase z).symm))
    have hxy : e.symm x = y := by
      apply e.injective
      exact (e.apply_symm_apply x).trans hy.symm
    have hpair : (Q z).val = γ₀ x := Prod.ext rfl (congrArg Subtype.val hxy.symm)
    apply hQinj (w := σ₀ x) (z := z) (by rw [hQσ₀ x]; exact hγ₀S x) hSz
    exact Subtype.ext ((hQσ₀ x).trans hpair.symm)
  have hm₀ : IsAnalyticModification (n := n) g₀ :=
    PrimeNov16OriginalOpenInverse.isAnalyticModification_of_open_inverse hg₀ hgp₀ hA₀ hn₀ σ₀ hσ₀ hg₀σ₀ hσ₀g₀
  have hm₁ : IsAnalyticModification (n := n) g₁ :=
    PrimeNov16OriginalOpenInverse.isAnalyticModification_of_open_inverse hg₁ hgp₁ hA₁ hn₁ σ₁ hσ₁ hg₁σ₁ hσ₁g₁
  have hmap₀ : nativeMorphism hm₀.1 = q ≫ p₀ := nativeMorphism_nativePointMap (q ≫ p₀)
  have hmap₁ : nativeMorphism hm₁.1 = q ≫ p₁ := nativeMorphism_nativePointMap (q ≫ p₁)
  have hfull : (q ≫ p₀) ≫ F₀ = (q ≫ p₁) ≫ F₁ :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun z => hbase z.val)
  have hisog : IsIsoOver (nativeMorphism hm₁.1) (F₁.hom.left.base ⁻¹' Bᶜ) := by
    exact PrimeNov16OriginalOpenInverse.isIsoOver_nativeMorphism_of_open_inverse
      hm₁.1 hA₁ σ₁ hσ₁ hg₁σ₁ hσ₁g₁
  have hisocomp : IsIsoOver (nativeMorphism hm₁.1 ≫ F₁) Bᶜ := hi₁.comp hisog
  have hnativeproper : IsProperMap (nativeMorphism hm₁.1).hom.left.base :=
    (Homeomorph.Set.univ Y₁).symm.isProperMap.comp (hgp₁.comp (Homeomorph.Set.univ M).isProperMap)
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hn₁).nonempty
  have hsourceThin : interior (g₁ ⁻¹' (pointMap F₁ ⁻¹' B)) = ∅ :=
    PrimeNov16OriginalOpenInverse.interior_preimage_eq_empty_of_good_point hg₁ hA₁
      ⟨σ₁ ⟨x, hx⟩, by change pointMap F₁ (g₁ (σ₁ ⟨x, hx⟩)) ∉ B; rw [hg₁σ₁]; exact hx⟩
  have hwholeThin : interior ((Subtype.val : ↥(univ : Set M) → M) ⁻¹'
      (g₁ ⁻¹' (pointMap F₁ ⁻¹' B))) = ∅ := by
    have hi := isOpen_univ.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      (continuous_subtype_val : Continuous (Subtype.val : ↥(univ : Set M) → M))
      (g₁ ⁻¹' (pointMap F₁ ⁻¹' B))
    exact hi.symm.trans (congrArg (fun D : Set M => (Subtype.val : ↥(univ : Set M) → M) ⁻¹' D) hsourceThin)
  have hresolution : IsResolution (nativeMorphism hm₁.1 ≫ F₁) := by
    refine ⟨isSmooth_wholeModel, hF₁.1.comp hnativeproper, B, hBa, hBt, ?_, hisocomp⟩
    exact hwholeThin
  refine ⟨M, hMconn, g₀, g₁, hm₀, hm₁, ?_, hresolution⟩
  rw [hmap₀, hmap₁]
  exact hfull

end SGPT.PSH.PrimeNov16OriginalCommonResolution
