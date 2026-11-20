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
namespace SGPT.PSH.PrimeNov16OriginalTransitionGraph
open Set CategoryTheory TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaIntrinsicComplexAnalyticRegularLocus
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
  OriginalSmoothSourceAnalytic
open scoped Topology Manifold ContDiff ProductComplexManifold

variable {X : SourceReducedComplexSpace} {n : ℕ} {Y₀ Y₁ : Type}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [ConnectedSpace Y₁]

theorem exists_actual_transition_graph_manifold
    (F₀ : wholeModel (n := n) Y₀ ⟶ X) (F₁ : wholeModel (n := n) Y₁ ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B)
    (hA₀ : IsComplexAnalyticSubset (n := n) (pointMap F₀ ⁻¹' B))
    (hA₁ : IsComplexAnalyticSubset (n := n) (pointMap F₁ ⁻¹' B))
    (hn₁ : interior (pointMap F₁ ⁻¹' B) = ∅)
    (e : OriginalCommonResolution.goodOpen F₁ B hBc
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      OriginalCommonResolution.goodOpen F₀ B hBc)
    (he : ∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val)
    (hinj : InjOn (pointMap F₀) (pointMap F₀ ⁻¹' Bᶜ)) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (n+n) (Y₀ × Y₁),
      V.dim = n ∧
      V.carrier = closure {p : Y₀ × Y₁ |
        pointMap F₀ p.1 = pointMap F₁ p.2 ∧ pointMap F₀ p.1 ∉ B} ∧
      V.carrier ⊆ {p : Y₀ × Y₁ | pointMap F₀ p.1 = pointMap F₁ p.2} ∧
      (∀ p ∈ {q : Y₀ × Y₁ | pointMap F₀ q.1 = pointMap F₁ q.2 ∧ pointMap F₀ q.1 ∉ B},
        RegularAtDim (n := n+n) V.carrier p n) ∧
      ∃ (M : CMfd.{0} n) (_ : ConnectedSpace M),
        Nonempty (wholeModel (n := n) M ≅ OriginalNativeHSGlobalResolution.source
          (ofClosedAnalytic V.carrier V.analytic)) := by
  classical
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
  exact ⟨V, hVdim, hVclosure, hVF, hGreg, M, inferInstance, hM⟩

end SGPT.PSH.PrimeNov16OriginalTransitionGraph
