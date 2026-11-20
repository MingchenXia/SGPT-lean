import SGPT.PSH.PrimeNov16ConnectedCommonModel
import SGPT.PSH.PrimeNov16DisjointBimeromorphic
import SGPT.PSH.PrimeNov16ProperNativeManifold
import SGPT.PSH.RIsoACommonModel
import SGPT.Unibranch.OriginalBimeromorphicSourceIso

/-! Actual noncompact common models over arbitrary (including disconnected) smooth bases.
Actual native component models assemble through held arbitrary coproducts;
proper domination derives countability and the genuine global manifold model.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16CommonModel
open Set CategoryTheory AlgebraicGeometry TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy HironakaActualAnalyticSubspaceOpenRestriction
  HironakaResolutionSpaceComplex BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
  OriginalProperBimeromorphicNative
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X Y₀ Y₁ : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- Actual whole common models from ONLY the two original analytic modifications,
without compactness, connectedness, finite components or supplied model certificates. -/
theorem exists_actual_common_model {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (N : CMfd.{0} n) (g₀ : N → Y₀) (g₁ : N → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
      c₀ ∘ g₀ = c₁ ∘ g₁ := by
  classical
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (ComplexModel n) X
  let I := ConnectedComponents X
  have hclopen (c : I) : IsClopen (ConnectedComponents.mk ⁻¹' {c}) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isClopen_connectedComponent
  let U (c : I) : Opens X := ⟨ConnectedComponents.mk ⁻¹' {c}, (hclopen c).isOpen⟩
  have hUconn (c : I) : ConnectedSpace (U c) := by
    apply isConnected_iff_connectedSpace.mp
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
    rw [connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  let V₀ (c : I) := RIsoACommonModel.preOpen hc₀.1.continuous (U c)
  let V₁ (c : I) := RIsoACommonModel.preOpen hc₁.1.continuous (U c)
  have hex (c : I) : ∃ (M : CMfd.{0} n) (_ : ConnectedSpace M)
      (a : M → V₀ c) (b : M → V₁ c),
      IsAnalyticModification (n := n) a ∧ IsAnalyticModification (n := n) b ∧
      RIsoACommonModel.restrictMap hc₀.1.continuous (U c) ∘ a =
        RIsoACommonModel.restrictMap hc₁.1.continuous (U c) ∘ b := by
    let := hUconn c
    exact PrimeNov16ConnectedCommonModel.exists_actual_connected_common_model
      (RIsoACommonModel.isAnalyticModification_restrictMap hc₀ (U c))
      (RIsoACommonModel.isAnalyticModification_restrictMap hc₁ (U c))
  choose M _hMconn a b ha hb hab using hex
  let Z (c : I) := wholeModel (n := n) (M c)
  let A₀ (c : I) := wholeModel (n := n) (V₀ c)
  let A₁ (c : I) := wholeModel (n := n) (V₁ c)
  let j₀ (c : I) : A₀ c ⟶ wholeModel (n := n) Y₀ := nativeMorphism contMDiff_subtype_val
  let j₁ (c : I) : A₁ c ⟶ wholeModel (n := n) Y₁ := nativeMorphism contMDiff_subtype_val
  have hj₀ (c : I) : LocallyRingedSpace.IsOpenImmersion (j₀ c).hom.left :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set Y₀) (V₀ c)
  have hj₁ (c : I) : LocallyRingedSpace.IsOpenImmersion (j₁ c).hom.left :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set Y₁) (V₁ c)
  have hcvr₀ : ∀ y : (wholeModel (n := n) Y₀).obj.left,
      ∃ (c : I) (v : (A₀ c).obj.left), (j₀ c).hom.left.base v = y := by
    intro y
    exact ⟨ConnectedComponents.mk (c₀ y.val), ⟨⟨y.val, rfl⟩, mem_univ _⟩, rfl⟩
  have hcvr₁ : ∀ y : (wholeModel (n := n) Y₁).obj.left,
      ∃ (c : I) (v : (A₁ c).obj.left), (j₁ c).hom.left.base v = y := by
    intro y
    exact ⟨ConnectedComponents.mk (c₁ y.val), ⟨⟨y.val, rfl⟩, mem_univ _⟩, rfl⟩
  have hdisj₀ : Pairwise (fun c d =>
      Disjoint (range (j₀ c).hom.left.base) (range (j₀ d).hom.left.base)) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro y ⟨v, hv⟩ ⟨w, hw⟩
    apply hcd
    have hvc : ConnectedComponents.mk (c₀ y.val) = c := by
      rw [← hv]
      exact v.val.property
    have hwd : ConnectedComponents.mk (c₀ y.val) = d := by
      rw [← hw]
      exact w.val.property
    exact hvc.symm.trans hwd
  have hdisj₁ : Pairwise (fun c d =>
      Disjoint (range (j₁ c).hom.left.base) (range (j₁ d).hom.left.base)) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro y ⟨v, hv⟩ ⟨w, hw⟩
    apply hcd
    have hvc : ConnectedComponents.mk (c₁ y.val) = c := by
      rw [← hv]
      exact v.val.property
    have hwd : ConnectedComponents.mk (c₁ y.val) = d := by
      rw [← hw]
      exact w.val.property
    exact hvc.symm.trans hwd
  let q₀ (c : I) : Z c ⟶ A₀ c := nativeMorphism (ha c).1
  let q₁ (c : I) : Z c ⟶ A₁ c := nativeMorphism (hb c).1
  have hq₀ (c : I) : IsProperBimeromorphic (q₀ c) := nativeMorphism_isProperBimeromorphic (ha c)
  have hq₁ (c : I) : IsProperBimeromorphic (q₁ c) := nativeMorphism_isProperBimeromorphic (hb c)
  let S := HironakaG1NativeDisjointCoproduct.coproduct Z
  let k (c : I) : Z c ⟶ S := HironakaG1NativeDisjointCoproduct.inclusion Z c
  let G₀ : S ⟶ wholeModel (n := n) Y₀ :=
    HironakaG1NativeDisjointCoproduct.desc Z (fun c => q₀ c ≫ j₀ c)
  let G₁ : S ⟶ wholeModel (n := n) Y₁ :=
    HironakaG1NativeDisjointCoproduct.desc Z (fun c => q₁ c ≫ j₁ c)
  have hG₀ : IsProperBimeromorphic G₀ :=
    PrimeNov16DisjointBimeromorphic.isProperBimeromorphic_desc j₀ hj₀ hcvr₀ hdisj₀ q₀ hq₀
  have hG₁ : IsProperBimeromorphic G₁ :=
    PrimeNov16DisjointBimeromorphic.isProperBimeromorphic_desc j₁ hj₁ hcvr₁ hdisj₁ q₁ hq₁
  have hmodels : PrimeNov16SecondCountableNativeModel.UniformSmoothModels S n := by
    intro s
    obtain ⟨c, z, rfl⟩ := HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective Z s
    obtain ⟨O, i, hi, hp, hz⟩ := exists_native_chart (n := n) (univ : Set (M c))
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := n) z.val)
    let i' : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) O ⟶ (Z c).obj.left := i
    have hi' : LocallyRingedSpace.IsOpenImmersion i' := hi
    have hp' : i' ≫ (Z c).obj.hom = _ := hp
    let hk := HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion Z c
    refine ⟨O, i' ≫ (k c).hom.left,
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ i' hi' _ hk, ?_, ?_⟩
    · exact (Category.assoc i' (k c).hom.left S.obj.hom).trans
        ((congrArg (fun F => i' ≫ F) (Over.w (k c).hom)).trans hp')
    · obtain ⟨v, hv⟩ := hz
      exact ⟨v, congrArg (k c).hom.left.base hv⟩
  let f : S.obj.left → Y₀ := fun s => (G₀.hom.left.base s).val
  have hf : IsProperMap f := (Homeomorph.Set.univ Y₀).isProperMap.comp hG₀.1
  obtain ⟨N, ⟨E⟩⟩ := PrimeNov16ProperNativeManifold.exists_native_manifold_of_proper_map (m := n) hmodels f hf
  let H₀ := E.hom ≫ G₀
  let H₁ := E.hom ≫ G₁
  let g₀ : N → Y₀ := nativePointMap H₀
  let g₁ : N → Y₁ := nativePointMap H₁
  have hg₀ : IsAnalyticModification (n := n) g₀ :=
    isAnalyticModification_of_isProperBimeromorphic H₀ (hG₀.precomp_iso E)
  have hg₁ : IsAnalyticModification (n := n) g₁ :=
    isAnalyticModification_of_isProperBimeromorphic H₁ (hG₁.precomp_iso E)
  let C₀ := nativeMorphism hc₀.1
  let C₁ := nativeMorphism hc₁.1
  have hsq : G₀ ≫ C₀ = G₁ ≫ C₁ := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext Z
    intro c
    rw [← Category.assoc, ← Category.assoc,
      HironakaG1NativeDisjointCoproduct.inclusion_desc Z (fun c => q₀ c ≫ j₀ c) c,
      HironakaG1NativeDisjointCoproduct.inclusion_desc Z (fun c => q₁ c ≫ j₁ c) c]
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    change c₀ (a c z.val).val = c₁ (b c z.val).val
    exact congrArg (fun u : U c => u.val) (congrFun (hab c) z.val)
  have hwhole : H₀ ≫ C₀ = H₁ ≫ C₁ := by
    simpa only [H₀, H₁, Category.assoc] using congrArg (fun F => E.hom ≫ F) hsq
  refine ⟨N, g₀, g₁, hg₀, hg₁, ?_⟩
  funext z
  exact congrArg (fun H : wholeModel (n := n) N ⟶ wholeModel (n := n) X =>
    (H.hom.left.base ⟨z, mem_univ z⟩).val) hwhole

end SGPT.PSH.PrimeNov16CommonModel
