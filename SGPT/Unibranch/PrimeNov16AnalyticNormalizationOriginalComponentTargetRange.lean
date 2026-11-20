import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetLift

/-! SAME-witness component target immersion retains ENTIRE range and full original triangles.
Blueprint: prime-nov16-analytic-normalization-original-component-target-range.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalClosedLanding
open PrimeNov16AnalyticNormalizationLocalGraph
open SourceReducedComplexSpace

variable {n : ℕ} {B Z : Set (ComplexModel n)} (d : GraphPresentation n B)
  (P : Opens (ComplexModel n))
  (hB : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B))
  (hZ : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
  (hBP : ((Subtype.val : P → ComplexModel n) ⁻¹' B) ⊆ ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
  (hDP : ballDomain (n := n) d.radius ≤ P)
  (g : d.target ⟶ sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ)
  (U : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)
  [ParacompactSpace U]
  (hcoord : ∀ t : d.target.obj.left,(g.hom.left.base t).val.val=t.val.val.val)

include hcoord

theorem componentTarget_triangle :
    commonComponent d g U ≫ baseInclusion U=
      componentTargetInclusion d P hB hZ hDP g U ≫ OriginalClosedSubspaceFactorization.inclusion hB hZ hBP := by
  apply morphism_eq_of_pointwise_eq
  intro p
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun F => F.hom.left.base p) (commonComponent_square d g U)
  have ht := componentTargetInclusion_point d P hB hZ hDP g U p
  have hs := targetEmbedding_point d _ (commonBaseOpen_le d g U) p
  exact (congrArg (fun x => x.val.val) he).trans
    ((hcoord _).trans ((congrArg (fun x => x.val.val) hs).trans ht.symm))

theorem componentTarget_range
    (hRange : ∀ x : (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ U → (x ∈ range g.hom.left.base ↔ x.val.val ∈ B)) :
    range (componentTargetInclusion d P hB hZ hDP g U).hom.left.base=
      (OriginalClosedSubspaceFactorization.inclusion hB hZ hBP).hom.left.base ⁻¹' (U : Set (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    have he := congrArg (fun F => F.hom.left.base p)
      (componentTarget_triangle d P hB hZ hBP hDP g U hcoord)
    change ((commonComponent d g U).hom.left.base p).val=
      (OriginalClosedSubspaceFactorization.inclusion hB hZ hBP).hom.left.base
        ((componentTargetInclusion d P hB hZ hDP g U).hom.left.base p) at he
    change (OriginalClosedSubspaceFactorization.inclusion hB hZ hBP).hom.left.base
      ((componentTargetInclusion d P hB hZ hDP g U).hom.left.base p) ∈ U
    exact he ▸ ((commonComponent d g U).hom.left.base p).property
  · intro hy
    let x := (OriginalClosedSubspaceFactorization.inclusion hB hZ hBP).hom.left.base y
    obtain ⟨b,hb⟩ := (hRange x hy).mpr y.property
    have hbU : g.hom.left.base b ∈ U := hb.symm ▸ hy
    have hbV : b.val ∈ commonBaseOpen d g U :=
      (mem_commonBaseOpen d g U b.val).mpr ⟨b.property,hbU⟩
    let p : (commonGraph d g U).target.obj.left := ⟨b.val,hbV⟩
    refine ⟨p,Subtype.ext (Subtype.ext ?_)⟩
    exact (componentTargetInclusion_point d P hB hZ hDP g U p).trans
      ((hcoord b).symm.trans (congrArg (fun z => z.val.val) hb))

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
