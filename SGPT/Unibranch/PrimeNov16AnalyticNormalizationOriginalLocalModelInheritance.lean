import SGPT.Unibranch.NativeNov16LocalModelMorphismExt
import SGPT.Foundations.Analysis.Pending.HironakaIntrinsicMorphismGluingAnalytic

/-! Actual raw local models pass through scalar-compatible open immersions without global topology assumptions.
Blueprint: prime-nov16-analytic-normalization-original-local-model-inheritance.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceLocalFunctions HironakaResolutionSpaceComplex
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalLocalModelInheritance
open NativeNov16LocalModelMorphismExt

theorem hasLocalModels_of_openImmersion {A B : LocallyRingedSpace}
    (σA : A ⟶ complexPoint) (σB : B ⟶ complexPoint)
    (hB : HasLocalModels B σB)
    (j : A ⟶ B) [hj : LocallyRingedSpace.IsOpenImmersion j]
    (hjσ : j ≫ σB = σA) : HasLocalModels A σA := by
  intro x
  obtain ⟨n, V, C, hC, i, hi, hip, c, hcx⟩ := hB (j.base x)
  change i ≫ σB = subspacePointMap (n := n) C at hip
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let Q : Opens (TopCat.of C) :=
    ⟨i.base ⁻¹' range j.base, hj.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  obtain ⟨O, hO, hOQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let A : Opens V := ⟨O, hO⟩
  have hcA : c.val ∈ A := by
    change c ∈ Subtype.val ⁻¹' O
    rw [hOQ]
    change i.base c ∈ range j.base
    rw [hcx]
    exact ⟨x, rfl⟩
  let C' : Set A := (Subtype.val : A → V) ⁻¹' C
  let R := actualOpenSubspaceMap (n := n) C A ≫ i
  have : LocallyRingedSpace.IsOpenImmersion R := by
    dsimp [R]
    infer_instance
  have hR : range R.base ⊆ range j.base := by
    rintro _ ⟨y, rfl⟩
    have hy : (⟨y.val.val, y.property⟩ : C) ∈ Q := by
      change (⟨y.val.val, y.property⟩ : C) ∈ (Q : Set C)
      rw [← hOQ]
      exact y.val.property
    exact hy
  let L := LocallyRingedSpace.IsOpenImmersion.lift j R hR
  have hfac : L ≫ j = R := LocallyRingedSpace.IsOpenImmersion.lift_fac j R hR
  have : LocallyRingedSpace.IsOpenImmersion L := by
    let : IsIso (pullback.snd j R) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j R hR
    dsimp [L, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hLp : L ≫ σA = subspacePointMap (n := n) C' := by
    rw [← hjσ, ← Category.assoc, hfac]
    dsimp [R]
    rw [Category.assoc, hip]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  let c' : C' := ⟨⟨c.val, hcA⟩, c.property⟩
  have hLc : L.base c' = x := by
    apply hj.base_open.injective
    calc
      j.base (L.base c') = R.base c' := congrArg (fun f => f.base c') hfac
      _ = j.base x := hcx
  have hC' : IsComplexAnalyticSubset (n := n) C' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC A
  obtain ⟨V', D, hD, k, hk, hkp, z, hzc⟩ := exists_model_chart hC' c'
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨n, V', D, hD, k ≫ L, inferInstance, ?_, z, ?_⟩
  · rw [Category.assoc, hLp]
    exact hkp
  · change L.base (k.base z) = x
    rw [hzc, hLc]
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalLocalModelInheritance
