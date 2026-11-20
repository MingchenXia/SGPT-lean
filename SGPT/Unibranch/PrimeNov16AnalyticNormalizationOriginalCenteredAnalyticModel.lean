import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartRegularity
import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

/-! Actual centered chart open immersion, retaining the original quotient sheaves.
Blueprint: prime-nov16-analytic-normalization-original-centered-analytic-model.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredAnalyticModel
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def centeredOpen (x : M) : Opens (ComplexModel n) :=
  ⟨{w | w + chartAt (ComplexModel n) x x ∈ chartImage (n := n) x},
    (chartImage (n := n) x).isOpen.preimage (continuous_id.add continuous_const)⟩

def centeredDiffeo (x : M) :
    centeredOpen (n := n) x ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ chartImage (n := n) x where
  toEquiv :=
    { toFun := fun w => ⟨w.val + chartAt (ComplexModel n) x x,w.property⟩
      invFun := fun u => ⟨u.val - chartAt (ComplexModel n) x x,by
        change u.val - _ + _ ∈ chartImage (n := n) x
        simpa only [sub_add_cancel] using u.property⟩
      left_inv := fun w => Subtype.ext (add_sub_cancel_right _ _)
      right_inv := fun u => Subtype.ext (sub_add_cancel _ _) }
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.add contMDiff_const) (fun w => w.property)
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.sub contMDiff_const) (fun u => by
      change u.val - _ + _ ∈ chartImage (n := n) x
      simpa only [sub_add_cancel] using u.property)

def centeredCarrier (C : Set M) (x : M) : Set (centeredOpen (n := n) x) :=
  (Subtype.val : centeredOpen (n := n) x → ComplexModel n) ⁻¹'
    AnalyticDescendingChain.chartGerm (n := n) C x

theorem centeredCarrier_iff (C : Set M) (x : M) (w : centeredOpen (n := n) x) :
    w ∈ centeredCarrier (n := n) C x ↔ centeredDiffeo (n := n) x w ∈ chartTrace (n := n) C x := by
  change (w.val + chartAt (ComplexModel n) x x ∈ (chartAt (ComplexModel n) x).target ∧
    (chartAt (ComplexModel n) x).symm (w.val + chartAt (ComplexModel n) x x) ∈ C) ↔
      (chartAt (ComplexModel n) x).symm (w.val + chartAt (ComplexModel n) x x) ∈ C
  exact and_iff_right w.property

theorem centeredCarrier_analytic {C : Set M} (hC : IsComplexAnalyticSubset (n := n) C)
    (x : M) : IsComplexAnalyticSubset (n := n) (centeredCarrier (n := n) C x) := by
  have he : centeredCarrier (n := n) C x = (centeredDiffeo (n := n) x) ⁻¹' chartTrace (n := n) C x :=
    Set.ext (centeredCarrier_iff (n := n) C x)
  rw [he]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (centeredDiffeo (n := n) x).contMDiff
    (isComplexAnalyticSubset_chartTrace hC x)

theorem centeredGerm_analytic {C : Set M} (hC : IsComplexAnalyticSubset (n := n) C)
    (x : M) : AnalyticGermDecomposition.IsAnalyticGerm
      (AnalyticDescendingChain.chartGerm (n := n) C x) :=
  AnalyticDescendingChain.isAnalyticGerm_chartGerm hC x

def centeredMap (C : Set M) (x : M) :
    (modelOver (centeredOpen (n := n) x) (centeredCarrier (n := n) C x)).left ⟶
      actualSubspaceLocallyRingedSpace (n := n) C :=
  (actualSubspaceBiholomorphicIso (centeredDiffeo (n := n) x) (centeredCarrier (n := n) C x)
    (chartTrace (n := n) C x) (centeredCarrier_iff (n := n) C x)).hom ≫ chartModelMap (n := n) C x

instance centeredMap_isOpenImmersion (C : Set M) (x : M) :
    LocallyRingedSpace.IsOpenImmersion (centeredMap (n := n) C x) := by
  unfold centeredMap
  infer_instance

theorem centeredMap_point (C : Set M) (x : M) :
    centeredMap (n := n) C x ≫ subspacePointMap (n := n) C =
      (modelOver (centeredOpen (n := n) x) (centeredCarrier (n := n) C x)).hom := by
  unfold centeredMap
  rw [Category.assoc,chartModelMap_point]
  exact actualSubspaceMap_point (centeredDiffeo (n := n) x).contMDiff _

omit [IsComplexManifold n M] in
theorem zero_mem_centeredOpen (x : M) : (0 : ComplexModel n) ∈ centeredOpen (n := n) x := by
  change 0 + chartAt (ComplexModel n) x x ∈ (chartAt (ComplexModel n) x).target
  simpa only [zero_add] using (chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)

omit [IsComplexManifold n M] in
theorem zero_mem_chartGerm (C : Set M) (x : C) :
    (0 : ComplexModel n) ∈ AnalyticDescendingChain.chartGerm (n := n) C x.val := by
  change 0 + chartAt (ComplexModel n) x.val x.val ∈ (chartAt (ComplexModel n) x.val).target ∧
    (chartAt (ComplexModel n) x.val).symm (0 + chartAt (ComplexModel n) x.val x.val) ∈ C
  simpa only [zero_add,(chartAt (ComplexModel n) x.val).left_inv (mem_chart_source _ x.val)]
    using And.intro ((chartAt (ComplexModel n) x.val).map_source (mem_chart_source _ x.val)) x.property

theorem centeredMap_origin (C : Set M) (x : C) :
    (centeredMap (n := n) C x.val).base
      ⟨⟨0,zero_mem_centeredOpen (n := n) x.val⟩,zero_mem_chartGerm (n := n) C x⟩ = x := by
  apply Subtype.ext
  change (chartAt (ComplexModel n) x.val).symm (0 + chartAt (ComplexModel n) x.val x.val) = x.val
  rw [zero_add,(chartAt (ComplexModel n) x.val).left_inv (mem_chart_source _ x.val)]
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredAnalyticModel
