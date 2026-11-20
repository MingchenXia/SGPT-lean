import SGPT.PSH.PrimeNov16NativeManifold
import SGPT.Unibranch.OriginalNativeHSGlobalResolution
import SGPT.Unibranch.OriginalCommonResolution

/-! SAME actual regular graph and native global resolution over an arbitrary
possibly singular ORIGINAL target. All original good-open data are generated
from the actual given original maps. No desired common model is supplied.
Blueprint first: `prime-nov16-original-prime-models.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16OriginalGraphManifold
open Set CategoryTheory TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaIntrinsicComplexAnalyticRegularLocus
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
  OriginalSmoothSourceAnalytic
open scoped Topology Manifold ContDiff ProductComplexManifold

private theorem analytic_union {X : SourceReducedComplexSpace} {A B : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) : X.IsAnalyticSubset (A ∪ B) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val '' (e.toPoint ⁻¹' A)) ∪ (Subtype.val '' (e.toPoint ⁻¹' B)),
    ConstantRankImage.IsComplexAnalyticSubset.union
      (hA.analytic_image_localEmbedding e) (hB.analytic_image_localEmbedding e), ?_⟩
  rw [Set.preimage_union, Set.preimage_union,
    Set.preimage_image_eq _ Subtype.val_injective,
    Set.preimage_image_eq _ Subtype.val_injective]

private theorem thin_of_univ_preimage {T : Type} [TopologicalSpace T] {D : Set T}
    (h : interior ((Subtype.val : ↥(univ : Set T) → T) ⁻¹' D) = ∅) : interior D = ∅ := by
  have hi := isOpen_univ.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    (continuous_subtype_val : Continuous (Subtype.val : ↥(univ : Set T) → T)) D
  rw [h] at hi
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hm : (⟨y, mem_univ y⟩ : ↥(univ : Set T)) ∈
      (Subtype.val : ↥(univ : Set T) → T) ⁻¹' interior D := hy
  rw [hi] at hm
  exact hm

variable {X : SourceReducedComplexSpace} {n : ℕ} {Y₀ Y₁ : Type}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [ConnectedSpace Y₁]

/-- The two actual ORIGINAL maps construct their exact good transition,
genuine regular graph and an n-manifold model of its SAME assigned native
resolution source. Connected source and equal native dimensions are explicit
at this intermediate stage, not silently claimed for the full book definition. -/
theorem exists_actual_original_graph_manifold
    (F₀ : wholeModel (n := n) Y₀ ⟶ X) (F₁ : wholeModel (n := n) Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (B : Set X.obj.left) (hBc : IsClosed B),
      X.IsAnalyticSubset B ∧ interior B = ∅ ∧
      IsComplexAnalyticSubset (n := n) (pointMap F₀ ⁻¹' B) ∧
      IsComplexAnalyticSubset (n := n) (pointMap F₁ ⁻¹' B) ∧
      interior (pointMap F₀ ⁻¹' B) = ∅ ∧ interior (pointMap F₁ ⁻¹' B) = ∅ ∧
      IsIsoOver F₀ Bᶜ ∧ IsIsoOver F₁ Bᶜ ∧
      ∃ e : OriginalCommonResolution.goodOpen F₁ B hBc
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        OriginalCommonResolution.goodOpen F₀ B hBc,
        (∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val) ∧
        InjOn (pointMap F₀) (pointMap F₀ ⁻¹' Bᶜ) ∧
        ∃ V : ClosedIrreducibleAnalyticSubvariety (n+n) (Y₀ × Y₁),
          V.dim = n ∧
          V.carrier = closure {p : Y₀ × Y₁ |
            pointMap F₀ p.1 = pointMap F₁ p.2 ∧ pointMap F₀ p.1 ∉ B} ∧
          V.carrier ⊆ {p : Y₀ × Y₁ | pointMap F₀ p.1 = pointMap F₁ p.2} ∧
          (∀ p ∈ {q : Y₀ × Y₁ |
            pointMap F₀ q.1 = pointMap F₁ q.2 ∧ pointMap F₀ q.1 ∉ B},
            RegularAtDim (n := n+n) V.carrier p n) ∧
          ∃ (M : CMfd.{0} n) (_ : ConnectedSpace M),
            Nonempty (wholeModel (n := n) M ≅ OriginalNativeHSGlobalResolution.source
              (ofClosedAnalytic V.carrier V.analytic)) := by
  classical
  obtain ⟨_hp₀, E₀, hE₀a, hE₀t, hpre₀, hiso₀⟩ := hF₀
  obtain ⟨_hp₁, E₁, hE₁a, hE₁t, hpre₁, hiso₁⟩ := hF₁
  let B : Set X.obj.left := E₀ ∪ E₁
  have hBa : X.IsAnalyticSubset B := analytic_union hE₀a hE₁a
  have hBc : IsClosed B := hBa.isClosed
  have hBt : interior B = ∅ := by
    change interior (E₀ ∪ E₁) = ∅
    rw [interior_union_isClosed_of_interior_empty hE₀a.isClosed hE₁t]
    exact hE₀t
  have hi₀ : IsIsoOver F₀ Bᶜ :=
    hiso₀.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inl h))
  have hi₁ : IsIsoOver F₁ Bᶜ :=
    hiso₁.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inr h))
  have hcross₀ : interior (F₀.hom.left.base ⁻¹' E₁) = ∅ :=
    hiso₀.interior_preimage_eq_empty hpre₀ hE₁t
  have hcross₁ : interior (F₁.hom.left.base ⁻¹' E₀) = ∅ :=
    hiso₁.interior_preimage_eq_empty hpre₁ hE₀t
  have ht₀ : interior (F₀.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀a.isClosed.preimage F₀.hom.left.base.hom.continuous) hcross₀]
    exact hpre₀
  have ht₁ : interior (F₁.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀a.isClosed.preimage F₁.hom.left.base.hom.continuous) hpre₁]
    exact hcross₁
  have hn₀ : interior (pointMap F₀ ⁻¹' B) = ∅ := thin_of_univ_preimage ht₀
  have hn₁ : interior (pointMap F₁ ⁻¹' B) = ∅ := thin_of_univ_preimage ht₁
  have hA₀ : IsComplexAnalyticSubset (n := n) (pointMap F₀ ⁻¹' B) :=
    isComplexAnalyticSubset_preimage F₀ hBa
  have hA₁ : IsComplexAnalyticSubset (n := n) (pointMap F₁ ⁻¹' B) :=
    isComplexAnalyticSubset_preimage F₁ hBa
  obtain ⟨e, he, hinj⟩ := OriginalCommonResolution.exists_original_native_transition
    F₀ F₁ B hBc hi₀ hi₁
  obtain ⟨V, hVdim, _hVcomponent, hVclosure, hVF, hGreg⟩ :=
    HironakaNativeTargetCommon.exists_mainComponent_of_open_transition
      (continuous_pointMap F₀) (continuous_pointMap F₁) hBc
      (isComplexAnalyticSubset_equalityLocus F₀ F₁) hA₀ hA₁ hn₁ e he hinj
  let A := ofClosedAnalytic V.carrier V.analytic
  let U₁ := OriginalCommonResolution.goodOpen F₁ B hBc
  let S : Set (Y₀ × Y₁) := {p | pointMap F₀ p.1 = pointMap F₁ p.2 ∧ pointMap F₀ p.1 ∉ B}
  have hγS (x : U₁) : ((e x).val, x.val) ∈ S := by
    refine ⟨he x, ?_⟩
    rw [he x]
    exact x.property
  let γ : U₁ → V.carrier := fun x => ⟨((e x).val, x.val), by
    rw [hVclosure]
    exact subset_closure (hγS x)⟩
  have hγ : Continuous γ :=
    ((continuous_subtype_val.comp e.continuous).prodMk continuous_subtype_val).subtype_mk _
  have hUne : ((pointMap F₁ ⁻¹' B)ᶜ).Nonempty :=
    (interior_eq_empty_iff_dense_compl.mp hn₁).nonempty
  have hDne : pointMap F₁ ⁻¹' B ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := hUne
    have hxD : x ∈ pointMap F₁ ⁻¹' B := by rw [h]; exact mem_univ x
    exact hx hxD
  have hUconn : IsConnected (pointMap F₁ ⁻¹' B)ᶜ :=
    ⟨hUne, AnalyticComplementConnected.isPreconnected_compl hA₁ hDne⟩
  let : ConnectedSpace U₁ := by
    change ConnectedSpace ↥((pointMap F₁ ⁻¹' B)ᶜ)
    exact isConnected_iff_connectedSpace.mp hUconn
  let G : Set A.obj.left := range γ
  have hGconn : IsConnected G := isConnected_range hγ
  have himage : (Subtype.val : V.carrier → Y₀ × Y₁) '' G = S := by
    ext p
    constructor
    · rintro ⟨v, ⟨x, rfl⟩, rfl⟩
      exact hγS x
    · intro hp
      let x : U₁ := ⟨p.2, by
        change pointMap F₁ p.2 ∉ B
        rw [← hp.1]
        exact hp.2⟩
      have hx : (e x).val = p.1 := hinj (e x).property hp.2 ((he x).trans hp.1.symm)
      exact ⟨γ x, ⟨x, rfl⟩, Prod.ext hx rfl⟩
  have hGdense : Dense G := by
    intro v
    apply closure_subtype.mpr
    rw [himage, ← hVclosure]
    exact v.property
  have hGn (v : A.obj.left) (hv : v ∈ G) : intrinsicRegularAtDim A.obj v n := by
    obtain ⟨x, rfl⟩ := hv
    obtain ⟨O, i, hi, hp, hx⟩ := exists_native_chart V.carrier (hGreg _ (hγS x))
    exact ⟨O, i, hi, hp, hx⟩
  obtain ⟨x, hx⟩ := hGconn.nonempty
  obtain ⟨M, hM⟩ := PrimeNov16NativeManifold.exists_native_manifold_of_connected_dense_subset
    (OriginalNativeHSGlobalResolution.projection A) (OriginalNativeHSGlobalResolution.resolution A)
    (OriginalNativeHSGlobalResolution.originalReg A) hGconn hGdense
    (fun v hv => ⟨n, hGn v hv⟩) x hx (hGn x hx)
  let R := OriginalNativeHSGlobalResolution.source A
  let ρ : R ⟶ A := OriginalNativeHSGlobalResolution.projection A
  have hpreconn : IsConnected (ρ.hom.left.base ⁻¹' G) :=
    (OriginalNativeHSGlobalResolution.originalReg A).isConnected_preimage_of_subset hGconn
      (fun v hv => ⟨n, hGn v hv⟩)
  have hpredense : Dense (ρ.hom.left.base ⁻¹' G) :=
    (OriginalNativeHSGlobalResolution.resolution A).2.dense_preimage hGdense
  let : ConnectedSpace R.obj.left := connectedSpace_iff_univ.mpr (hpredense.closure_eq ▸ hpreconn.closure)
  let E := Classical.choice hM
  have hwholeconn : ConnectedSpace ↥(univ : Set M) := (isoHomeomorph E).connectedSpace_iff.mpr inferInstance
  let : ConnectedSpace M := (Homeomorph.Set.univ M).connectedSpace_iff.mp hwholeconn
  exact ⟨B, hBc, hBa, hBt, hA₀, hA₁, hn₀, hn₁, hi₀, hi₁,
    e, he, hinj, V, hVdim, hVclosure, hVF, hGreg, M, inferInstance, hM⟩

end SGPT.PSH.PrimeNov16OriginalGraphManifold
