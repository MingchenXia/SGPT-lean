import SGPT.Unibranch.UnibAnProjectiveCharts
import SGPT.Unibranch.UnibAnMorphismFunctor

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Schemes SGPT.Unibranch
open scoped Manifold ContDiff

namespace SGPT.Unibranch.UnibAn

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The true analytic inclusion of nested zero loci is compatible with the
full original map into the common ambient manifold. -/
theorem closedChartInclusion_ambient {N : ℕ} {I J : Ideal (MvPolynomial (Fin N) ℂ)}
    (hIJ : I ≤ J) :
    closedChartInclusion hIJ ≫ actualSubspaceInclusion (n := N) (polynomialZeroSet I) =
      actualSubspaceInclusion (n := N) (polynomialZeroSet J) := by
  simpa only [closedChartInclusion, ChartedSpace.locallyRingedSpace_id, Category.comp_id] using
    (actualSubspaceMap_inclusion (n := N) (m := N) (f := id) contMDiff_id
      (fun _ hx => polynomialZeroSet_subset_of_le hIJ hx)).symm

/-- The same analytic inclusion is surjective on stalks. -/
theorem closedChartInclusion_stalkMap_surjective {N : ℕ} {I J : Ideal (MvPolynomial (Fin N) ℂ)}
    (hIJ : I ≤ J) (z : polynomialZeroSet J) :
    Function.Surjective ((closedChartInclusion hIJ).stalkMap z) := by
  let F := closedChartInclusion hIJ
  let j := actualSubspaceInclusion (n := N) (polynomialZeroSet I)
  have hs : Function.Surjective ((F ≫ j).stalkMap z) := by
    rw [closedChartInclusion_ambient hIJ]
    exact actualSubspaceInclusionRingedHom_stalk_surjective (n := N) (polynomialZeroSet J) z
  rw [LocallyRingedSpace.stalkMap_comp] at hs
  intro a
  obtain ⟨r, hr⟩ := hs a
  exact ⟨j.stalkMap (F.base z) r, hr⟩

section Projective

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

local notation "n₀" => E.ambientDimension
local notation "g₀" => polynomialProjStructureMap ℂ E.ambientDimension

/-- On the fixed projective charts the reduced analytic model inclusion reads
the literal map of the original closed immersion on complex points. -/
theorem projectiveChart_inclusion_point (i : Fin (n₀ + 1))
    (z : polynomialZeroSet (projectiveSourceChart f E i).ideal) :
    chartPoint (projectiveAmbientChart n₀ i)
        ((closedChartInclusion (bot_le : ⊥ ≤ (projectiveSourceChart f E i).ideal)).base z) =
      schemeComplexPointMap f g₀ E.map E.over_base (chartPoint (projectiveSourceChart f E i) z) := by
  let s := projectiveSourceChart f E i
  let d := projectiveAmbientChart n₀ i
  let K := closedChartInclusion (bot_le : ⊥ ≤ s.ideal)
  let Q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (bot_le : ⊥ ≤ s.ideal)))
  let v := Spec.map (CommRingCat.ofHom (pointEval z))
  have hspec : Spec.map (CommRingCat.ofHom (pointEval (K.base z))) = v ≫ Q :=
    closedChartInclusion_spec (bot_le : ⊥ ≤ s.ideal) z
  have hfactor : s.map ≫ E.map = Q ≫ d.map := (projectiveSourceChartData f E i).factor
  apply Subtype.ext
  calc
    (chartPoint d (K.base z)).val = (v ≫ Q) ≫ d.map :=
      (chartPoint_val d (K.base z)).trans (congrArg (fun F => F ≫ d.map) hspec)
    _ = v ≫ (Q ≫ d.map) := Category.assoc _ _ _
    _ = v ≫ (s.map ≫ E.map) := congrArg (fun F => v ≫ F) hfactor.symm
    _ = (v ≫ s.map) ≫ E.map := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun F => F ≫ E.map) (chartPoint_val s z).symm

variable [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

/-- The global analytification morphism is exactly the native closed-subspace
inclusion inside each projective ambient chart, as a full LRS morphism. -/
theorem projectiveChart_analytificationMorphism (i : Fin (n₀ + 1)) :
    chartEmbedding (projectiveSourceChart f E i) ≫
      (analytificationMorphism E.map E.over_base).hom.left =
      closedChartInclusion (bot_le : ⊥ ≤ (projectiveSourceChart f E i).ideal) ≫
        chartEmbedding (projectiveAmbientChart n₀ i) := by
  let s := projectiveSourceChart f E i
  let d := projectiveAmbientChart n₀ i
  let K : chartModel s ⟶ chartModel d :=
    closedChartInclusion (bot_le : ⊥ ≤ s.ideal)
  let F : analytification f ⟶ analytification g₀ := analytificationMorphism E.map E.over_base
  refine @HironakaG10GenGluing.lrs_hom_eq_of_base_eq (analytification f) (analytification g₀)
    (chartModel s) (chartEmbedding s) (chartEmbedding_isOpenImmersion s) _ _ ?_ ?_ ?_
  · change (chartEmbedding s ≫ F.hom.left) ≫ structureMap g₀ =
      chartEmbedding s ≫ structureMap f
    have hOver : F.hom.left ≫ structureMap g₀ = structureMap f := Over.w F.hom
    exact (Category.assoc _ _ _).trans (congrArg (chartEmbedding s ≫ ·) hOver)
  · change (K ≫ chartEmbedding d) ≫ structureMap g₀ = chartEmbedding s ≫ structureMap f
    calc
      _ = K ≫ chartPointMap d := (Category.assoc _ _ _).trans
        (congrArg (K ≫ ·) (chartEmbedding_structureMap d))
      _ = chartPointMap s := closedChartInclusion_point (bot_le : ⊥ ≤ s.ideal)
      _ = _ := (chartEmbedding_structureMap s).symm
  · ext z
    apply pointMap_injective
    change pointMap g₀ (F.hom.left.base ((chartEmbedding s).base z)) =
      pointMap g₀ ((chartEmbedding d).base (K.base z))
    exact (pointMap_analytificationMorphism E.map E.over_base _).trans
      ((congrArg (schemeComplexPointMap f g₀ E.map E.over_base) (pointMap_chartEmbedding s z)).trans
        ((projectiveChart_inclusion_point E i z).symm.trans (pointMap_chartEmbedding d _).symm))

/-- The analytification of the literal projective embedding is surjective on
all stalk maps. The finite source chart cover keeps the calculation on the
same glued spaces, without an identification from topology alone. -/
theorem analytificationMorphism_projective_stalkMap_surjective (x : analytificationLRS f) :
    Function.Surjective ((analytificationMorphism E.map E.over_base).hom.left.stalkMap x) := by
  obtain ⟨i, z, rfl⟩ := projectiveSourceChart_covers f E x
  let s := projectiveSourceChart f E i
  let d := projectiveAmbientChart n₀ i
  let K : chartModel s ⟶ chartModel d :=
    closedChartInclusion (bot_le : ⊥ ≤ s.ideal)
  let F : analytificationLRS f ⟶ analytificationLRS g₀ :=
    (analytificationMorphism E.map E.over_base).hom.left
  have hcomp : chartEmbedding s ≫ F = K ≫ chartEmbedding d :=
    projectiveChart_analytificationMorphism E i
  have hst : Function.Surjective ((chartEmbedding s ≫ F).stalkMap z) := by
    rw [hcomp, LocallyRingedSpace.stalkMap_comp]
    exact (closedChartInclusion_stalkMap_surjective (bot_le : ⊥ ≤ s.ideal) z).comp
      (ConcreteCategory.bijective_of_isIso ((chartEmbedding d).stalkMap (K.base z))).2
  rw [LocallyRingedSpace.stalkMap_comp] at hst
  have hinj : Function.Injective ((chartEmbedding s).stalkMap z) :=
    (ConcreteCategory.bijective_of_isIso ((chartEmbedding s).stalkMap z)).1
  intro a
  obtain ⟨b, hb⟩ := hst ((chartEmbedding s).stalkMap z a)
  exact ⟨b, hinj hb⟩

end Projective

end

end SGPT.Unibranch.UnibAn
