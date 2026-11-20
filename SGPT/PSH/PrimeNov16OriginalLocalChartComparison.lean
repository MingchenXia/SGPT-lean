import SGPT.Unibranch.OriginalSmoothDimension
import SGPT.Unibranch.OriginalCommonResolution
import SGPT.Foundations.Analysis.Pending.CodimOnePartCanonical

/-! Genuine original chart overlaps derive dimension and every-subset regularity.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalLocalChartComparison
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism
open SGPT.Unibranch SourceReducedComplexSpace

private theorem nativeMap_point {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) :
    ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap m N = ambientPointMap n M :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel m)) (IP := 𝓘(ℂ, ComplexModel 0)) hf
    (show ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : N => (0 : ComplexModel 0)) from contMDiff_const)).symm

theorem dimension_and_regularity_of_original_charts
    {Y : SourceReducedComplexSpace} {m n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (i₀ : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel m) M ⟶ Y.obj.left)
    (i₁ : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) N ⟶ Y.obj.left)
    (hi₀ : LocallyRingedSpace.IsOpenImmersion i₀) (hi₁ : LocallyRingedSpace.IsOpenImmersion i₁)
    (hp₀ : i₀ ≫ Y.obj.hom = ambientPointMap m M)
    (hp₁ : i₁ ≫ Y.obj.hom = ambientPointMap n N)
    (a : M) (b : N) (hab : i₀.base a = i₁.base b) (D : Set Y.obj.left) (k : ℕ) :
    m = n ∧ (RegularAtDim (n := m) ((fun x : M => i₀.base x) ⁻¹' D) a k ↔
      RegularAtDim (n := n) ((fun x : N => i₁.base x) ⁻¹' D) b k) := by
  let := hi₀
  let := hi₁
  let O₀ : Opens M := ⟨i₀.base ⁻¹' range i₁.base, hi₁.base_open.isOpen_range.preimage i₀.base.hom.continuous⟩
  let O₁ : Opens N := ⟨i₁.base ⁻¹' range i₀.base, hi₀.base_open.isOpen_range.preimage i₁.base.hom.continuous⟩
  let j₀ := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O₀ → M)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel m)))
  let j₁ := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O₁ → N)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)))
  let f₀ := j₀ ≫ i₀
  let f₁ := j₁ ≫ i₁
  have hf₀ : LocallyRingedSpace.IsOpenImmersion f₀ := by dsimp only [f₀, j₀]; infer_instance
  have hf₁ : LocallyRingedSpace.IsOpenImmersion f₁ := by dsimp only [f₁, j₁]; infer_instance
  have hr : range f₀.base = range f₁.base := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := u.property
      exact ⟨⟨v, ⟨u.val, hv.symm⟩⟩, hv⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := v.property
      exact ⟨⟨u, ⟨v.val, hu.symm⟩⟩, hu⟩
  let E := @openImmersionIsoOfRangeEq _ _ _ f₀ f₁ hf₀ hf₁ hr
  have he : E.hom ≫ f₁ = f₀ := @openImmersionIsoOfRangeEq_hom_fac _ _ _ f₀ f₁ hf₀ hf₁ hr
  have hfp₀ : f₀ ≫ Y.obj.hom = ambientPointMap m O₀ := by
    rw [show f₀ = j₀ ≫ i₀ from rfl, Category.assoc, hp₀]
    exact nativeMap_point contMDiff_subtype_val
  have hfp₁ : f₁ ≫ Y.obj.hom = ambientPointMap n O₁ := by
    rw [show f₁ = j₁ ≫ i₁ from rfl, Category.assoc, hp₁]
    exact nativeMap_point contMDiff_subtype_val
  have hep : E.hom ≫ ambientPointMap n O₁ = ambientPointMap m O₀ := by
    rw [← hfp₁, ← Category.assoc, he, hfp₀]
  let aO : O₀ := ⟨a, ⟨b, hab.symm⟩⟩
  let bO : O₁ := ⟨b, ⟨a, hab⟩⟩
  have hdim := OriginalSmoothDimension.native_iso_dimension_eq E hep aO
  subst m
  have heip : E.inv ≫ ambientPointMap n O₀ = ambientPointMap n O₁ := by
    rw [← hep, ← Category.assoc, E.inv_hom_id, Category.id_comp]
  let e : O₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ O₁ :=
    { toFun := E.hom.base
      invFun := E.inv.base
      left_inv := fun u => congrArg (fun f => f.base u) E.hom_inv_id
      right_inv := fun v => congrArg (fun f => f.base v) E.inv_hom_id
      contMDiff_toFun := contMDiff_native_morphism E.hom hep
      contMDiff_invFun := contMDiff_native_morphism E.inv heip }
  have hepoint (u : O₀) : i₁.base (e u).val = i₀.base u.val :=
    congrArg (fun f : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) O₀ ⟶ Y.obj.left => f.base u) he
  have habO : e aO = bO := Subtype.ext (hi₁.base_open.injective ((hepoint aO).trans hab))
  let C₀ : Set O₀ := Subtype.val ⁻¹' ((fun x : M => i₀.base x) ⁻¹' D)
  let C₁ : Set O₁ := Subtype.val ⁻¹' ((fun x : N => i₁.base x) ⁻¹' D)
  have htrace : e ⁻¹' C₁ = C₀ := by
    ext u
    change i₁.base (e u).val ∈ D ↔ i₀.base u.val ∈ D
    rw [hepoint u]
  have hr₀ : RegularAtDim (n := n) C₀ aO k ↔ RegularAtDim (n := n) ((fun x : M => i₀.base x) ⁻¹' D) a k :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff
  have hr₁ : RegularAtDim (n := n) C₁ bO k ↔ RegularAtDim (n := n) ((fun x : N => i₁.base x) ⁻¹' D) b k :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff
  have hreg := CodimOnePartCanonical.regularAtDim_preimage_iff (A := C₁) (x := aO) (k := k) e
  rw [htrace, habO] at hreg
  exact ⟨rfl, hr₀.symm.trans (hreg.trans hr₁)⟩

end SGPT.PSH.PrimeNov16OriginalLocalChartComparison
