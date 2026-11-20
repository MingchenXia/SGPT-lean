import SGPT.PSH.PrimeNov16ResolvedGraph
import SGPT.PSH.PrimeNov16NativeManifold

/-! A genuine n-manifold model of the SAME actual noncompact resolved graph.
The connected dense graph and every native regular chart are constructed from
original modifications; no manifold model or common-model certificate is input.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16GraphManifold
open Set CategoryTheory TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaResolutionSpaceComplex BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace
open scoped Topology Manifold ContDiff ProductComplexManifold

variable {n : ℕ} {X Y₀ Y₁ : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- Actual graph closure and full n-manifold model of its SAME assigned
native global resolution source, without compactness or supplied certificates. -/
theorem exists_actual_graph_manifold {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (B : Set X) (s₀ : X → Y₀) (s₁ : X → Y₁),
      IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ Bᶜ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₁ Bᶜ ∧
      (∀ x ∉ B, c₀ (s₀ x) = x) ∧ (∀ x ∉ B, c₁ (s₁ x) = x) ∧
      (∀ y, c₀ y ∉ B → s₀ (c₀ y) = y) ∧
      (∀ y, c₁ y ∉ B → s₁ (c₁ y) = y) ∧
      ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
        V.dim = n ∧
        V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
        V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
        (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
          RegularAtDim (n := n + n) V.carrier p n) ∧
        ∃ (M : CMfd.{0} n) (_ : ConnectedSpace M),
          Nonempty (OriginalNativeModification.wholeModel (n := n) M ≅
            OriginalNativeHSGlobalResolution.source (ofClosedAnalytic V.carrier V.analytic)) := by
  classical
  obtain ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀, hs₁, hr₀, hr₁,
    hl₀, hl₁, V, hVdim, _hVcomp, hVclosure, hVF, hGreg, hGimage⟩ :=
    AnalyticFibreProductRegularGraph.exists_actual_mainComponent_regular_graph hc₀ hc₁
  let A := ofClosedAnalytic V.carrier V.analytic
  let S : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B}
  have hγS (x : ↥(Bᶜ)) : (s₀ x.val, s₁ x.val) ∈ S := by
    change c₀ (s₀ x.val) = c₁ (s₁ x.val) ∧ c₀ (s₀ x.val) ∉ B
    rw [hr₀ x.val x.property, hr₁ x.val x.property]
    exact ⟨rfl, x.property⟩
  let γ : ↥(Bᶜ) → V.carrier := fun x =>
    ⟨(s₀ x.val, s₁ x.val), hVclosure.symm ▸ subset_closure (hγS x)⟩
  have hγ : Continuous γ :=
    ((continuousOn_iff_continuous_domRestrict.mp hs₀.continuousOn).prodMk
      (continuousOn_iff_continuous_domRestrict.mp hs₁.continuousOn)).subtype_mk _
  have hUne : (Bᶜ).Nonempty := (interior_eq_empty_iff_dense_compl.mp hBi).nonempty
  have hBne : B ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := hUne
    exact hx (h.symm ▸ mem_univ x)
  have hUconn : IsConnected Bᶜ :=
    ⟨hUne, AnalyticComplementConnected.isPreconnected_compl hBa hBne⟩
  let : ConnectedSpace ↥(Bᶜ) := isConnected_iff_connectedSpace.mp hUconn
  let G : Set A.obj.left := range γ
  have hGconn : IsConnected G := isConnected_range hγ
  have himage : (Subtype.val : V.carrier → Y₀ × Y₁) '' G = S := by
    ext p
    constructor
    · rintro ⟨v, ⟨x, rfl⟩, rfl⟩
      exact hγS x
    · intro hp
      change p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B} at hp
      rw [hGimage] at hp
      obtain ⟨x, hx, hxp⟩ := hp
      exact ⟨γ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, hxp⟩
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
    (OriginalNativeHSGlobalResolution.projection A)
    (OriginalNativeHSGlobalResolution.resolution A)
    (OriginalNativeHSGlobalResolution.originalReg A)
    hGconn hGdense (fun v hv => ⟨n, hGn v hv⟩) x hx (hGn x hx)
  let R := OriginalNativeHSGlobalResolution.source A
  let ρ : R ⟶ A := OriginalNativeHSGlobalResolution.projection A
  have hpreconn : IsConnected (ρ.hom.left.base ⁻¹' G) :=
    (OriginalNativeHSGlobalResolution.originalReg A).isConnected_preimage_of_subset
      hGconn (fun v hv => ⟨n, hGn v hv⟩)
  have hpredense : Dense (ρ.hom.left.base ⁻¹' G) :=
    (OriginalNativeHSGlobalResolution.resolution A).2.dense_preimage hGdense
  let : ConnectedSpace R.obj.left :=
    connectedSpace_iff_univ.mpr (hpredense.closure_eq ▸ hpreconn.closure)
  let E := Classical.choice hM
  have hwholeconn : ConnectedSpace ↥(univ : Set M) :=
    (isoHomeomorph E).connectedSpace_iff.mpr inferInstance
  let : ConnectedSpace M := (Homeomorph.Set.univ M).connectedSpace_iff.mp hwholeconn
  exact ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀, hs₁, hr₀, hr₁, hl₀, hl₁,
    V, hVdim, hVclosure, hVF, hGreg, M, inferInstance, hM⟩

end SGPT.PSH.PrimeNov16GraphManifold
