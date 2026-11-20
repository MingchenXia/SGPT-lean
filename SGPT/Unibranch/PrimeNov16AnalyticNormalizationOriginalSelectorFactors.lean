import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorLanding
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
import SGPT.Unibranch.OriginalClosedSubspaceFactorization

/-! Entire selector pieces manufacture actual full original component factors.
Blueprint: prime-nov16-analytic-normalization-original-selector-factors.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorFactors
open NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
open PrimeNov16AnalyticNormalizationOriginalSelectorLanding
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open HironakaActualAnalyticSubspace
open SourceReducedComplexSpace

theorem exists_actual_component_factors {n m k : ℕ}
    (P : Opens (ComplexModel n)) (C : Set P) (hC : IsComplexAnalyticSubset (n := n) C)
    (W : Opens (TopCat.of C)) (U : Opens (ComplexModel m)) (D : Set U)
    (hD : IsComplexAnalyticSubset (n := m) D)
    (B : Fin k → Set U) (hB : ∀ i,IsComplexAnalyticSubset (n := m) (B i))
    (hBD : ∀ i,B i ⊆ D) (hcover : ∀ d ∈ D,∃ i,d ∈ B i)
    (f : coordinateSource P C hC W ⟶ ofClosedAnalytic D hD)
    (num : Fin k → D → ℂ)
    (hvan : ∀ i j,i ≠ j → ∀ x : D,x.val ∈ B j → num i x=0)
    (Q : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (e : Fin k → ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hq : ∀ p : C,∀ hp : p ∈ W,(actualSubspaceSheaf (n := n) C).presheaf.germ W p hp Q ≠ 0)
    (hid : ∀ i,(e i)^2=e i) (hsum : ∑ i,e i=1)
    (horth : ∀ i j,i ≠ j → e i*e j=0)
    (hrel : ∀ i,∀ p : W,original_value_hom C W p Q*original_value_hom C W p (e i)=
      num i (f.hom.left.base p)) :
    ∃ V : Fin k → Opens (TopCat.of C),∃ hVW : ∀ i,V i ≤ W,
      (∀ i,IsClosed ((Subtype.val : W → C) ⁻¹' (V i : Set C))) ∧
      (∀ p : W,∃ i,p.val ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i : Set C) (V j : Set C)) ∧
      (∀ i,(actualSubspaceSheaf (n := n) C).presheaf.map (homOfLE (hVW i)).op (e i)=1) ∧
      ∀ i,∃! g : coordinateSource P C hC (V i) ⟶ ofClosedAnalytic (B i) (hB i),
        g ≫ OriginalClosedSubspaceFactorization.inclusion (hB i) hD (hBD i)=
          windowInclusion P C hC (V i) W (hVW i) ≫ f := by
  classical
  obtain ⟨V,hVW,hClosed,hCover,hDisjoint,hOne,hLand⟩ :=
    exists_actual_selector_landing_cover C W f.hom.left.base f.hom.left.base.hom.continuous
      (fun i => (Subtype.val : D → U) ⁻¹' B i)
      (fun i => (hB i).isClosed.preimage continuous_subtype_val)
      (fun p => hcover _ (f.hom.left.base p).property) num hvan Q e hq hid hsum horth hrel
  refine ⟨V,hVW,hClosed,hCover,hDisjoint,hOne,?_⟩
  intro i
  apply OriginalClosedSubspaceFactorization.exists_unique_factorization (hB i) hD (hBD i)
    (coordinateSource P C hC (V i)) (windowInclusion P C hC (V i) W (hVW i) ≫ f)
  intro p
  have hp : ((windowInclusion P C hC (V i) W (hVW i)).hom.left.base p).val ∈ V i := by
    rw [windowInclusion_point]
    exact p.property
  exact hLand i _ hp

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorFactors
