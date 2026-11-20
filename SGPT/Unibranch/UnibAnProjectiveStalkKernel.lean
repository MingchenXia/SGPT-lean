import SGPT.Unibranch.UnibAnProjectiveStalks
import SGPT.Unibranch.OriginalAnalyticClosedSubspaceStalkQuotient

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaActualAnalyticSubspace HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback
open SGPT.Foundations.Schemes SGPT.Unibranch

namespace SGPT.Unibranch.UnibAn

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

local notation "n₀" => E.ambientDimension
local notation "g₀" => polynomialProjStructureMap ℂ E.ambientDimension

/-- The actual image restricted to the projective ambient chart is the same
local reduced carrier, using both directions of the checked source range. -/
theorem projectiveChart_inclusion_range (i : Fin (n₀ + 1)) :
    Set.range (closedChartInclusion (bot_le : ⊥ ≤ (projectiveSourceChart f E i).ideal)).base =
      (chartEmbedding (projectiveAmbientChart n₀ i)).base ⁻¹'
        Set.range (analytificationMorphism E.map E.over_base).hom.left.base := by
  let s := projectiveSourceChart f E i
  let d := projectiveAmbientChart n₀ i
  let K : chartModel s ⟶ chartModel d := closedChartInclusion (bot_le : ⊥ ≤ s.ideal)
  let F : analytification f ⟶ analytification g₀ := analytificationMorphism E.map E.over_base
  let j := chartEmbedding s
  let k := chartEmbedding d
  have hfac : j ≫ F.hom.left = K ≫ k := projectiveChart_analytificationMorphism E i
  have hbase (z : chartModel s) : F.hom.left.base (j.base z) = k.base (K.base z) :=
    congrArg (fun L : chartModel s ⟶ analytificationLRS g₀ => L.base z) hfac
  change Set.range K.base = k.base ⁻¹' Set.range F.hom.left.base
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨j.base z, hbase z⟩
  · rintro ⟨y, hy⟩
    have hp : schemeComplexPointMap f g₀ E.map E.over_base (pointMap f y) = chartPoint d v :=
      (pointMap_analytificationMorphism E.map E.over_base y).symm.trans
        ((congrArg (pointMap g₀) hy).trans (pointMap_chartEmbedding d v))
    have hd : chartPoint d v ∈ (polynomialProjRatioChart n₀ i).source :=
      (projectiveAmbientChart_complexPoint_range n₀ i) ▸ Set.mem_range_self v
    have hsource : pointMap f y ∈ Set.range (chartPoint s) := by
      change pointMap f y ∈ Set.range (chartPoint (projectiveSourceChart f E i))
      have hsr := (projectiveSourceChartData f E i).complexPoint_range
      change Set.range (chartPoint (projectiveSourceChart f E i)) = _ at hsr
      rw [hsr]
      change schemeComplexPointMap f g₀ E.map E.over_base (pointMap f y) ∈
        (polynomialProjRatioChart n₀ i).source
      exact hp.symm ▸ hd
    obtain ⟨z, hz⟩ := hsource
    have hzy : j.base z = y :=
      pointMap_injective ((pointMap_chartEmbedding s z).trans hz)
    refine ⟨z, (chartEmbedding_isOpenEmbedding d).injective ?_⟩
    exact (hbase z).symm.trans ((congrArg (fun y => F.hom.left.base y) hzy).trans hy)

/-- The full global projective morphism has precisely the intrinsic ideal of
its reduced analytic image as stalk kernel. -/
theorem analytificationMorphism_projective_stalkMap_kernel (x : analytificationLRS f) :
    let F := (analytificationMorphism E.map E.over_base).hom.left
    RingHom.ker (F.stalkMap x).hom =
      intrinsicCentreStalkRange (analytificationLRS g₀) (Set.range F.base) (F.base x) := by
  obtain ⟨i, z, rfl⟩ := projectiveSourceChart_covers f E x
  let s := projectiveSourceChart f E i
  let d := projectiveAmbientChart n₀ i
  let j := chartEmbedding s
  let k := chartEmbedding d
  let hle : (⊥ : Ideal (MvPolynomial (Fin n₀) ℂ)) ≤ s.ideal := bot_le
  let K : chartModel s ⟶ chartModel d := closedChartInclusion hle
  let F : analytificationLRS f ⟶ analytificationLRS g₀ :=
    (analytificationMorphism E.map E.over_base).hom.left
  let S := Set.range F.base
  let D := polynomialZeroSet s.ideal
  let W := polynomialZeroSet (⊥ : Ideal (MvPolynomial (Fin n₀) ℂ))
  have hcomp : j ≫ F = K ≫ k := projectiveChart_analytificationMorphism E i
  have htrace : Set.range K.base = k.base ⁻¹' S := projectiveChart_inclusion_range E i
  have hlocal : Set.range K.base = (Subtype.val : W → (⊤ : TopologicalSpace.Opens (ComplexModel n₀))) ⁻¹' D := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hw
      exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩
  have hK : RingHom.ker (K.stalkMap z).hom =
      intrinsicCentreStalkRange (chartModel d) (k.base ⁻¹' S) (K.base z) := by
    rw [← htrace, hlocal]
    exact OriginalAnalyticClosedSubspaceStalkQuotient.contained_inclusion_stalk_kernel_eq_intrinsicCentreStalkRange
      (polynomialZeroSet_isComplexAnalyticSubset s.ideal)
      (polynomialZeroSet_isComplexAnalyticSubset (⊥ : Ideal (MvPolynomial (Fin n₀) ℂ)))
      (polynomialZeroSet_subset_of_le hle) z
  let : LocallyRingedSpace.IsOpenImmersion k := chartEmbedding_isOpenImmersion d
  let : LocallyRingedSpace.IsOpenImmersion j := chartEmbedding_isOpenImmersion s
  have hkcomp : RingHom.ker ((K ≫ k).stalkMap z).hom =
      intrinsicCentreStalkRange (analytificationLRS g₀) S ((K ≫ k).base z) := by
    rw [LocallyRingedSpace.stalkMap_comp]
    change RingHom.ker ((K.stalkMap z).hom.comp (k.stalkMap (K.base z)).hom) = _
    rw [← RingHom.comap_ker, hK]
    have hk := openImmersion_pulled_stalkIdeal_eq k S (K.base z)
    change Ideal.map (k.stalkMap (K.base z)).hom
        (intrinsicCentreStalkRange (analytificationLRS g₀) S (k.base (K.base z))) =
      intrinsicCentreStalkRange (chartModel d) (k.base ⁻¹' S) (K.base z) at hk
    rw [← hk, Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]
    rfl
  have hjcomp : RingHom.ker ((j ≫ F).stalkMap z).hom =
      intrinsicCentreStalkRange (analytificationLRS g₀) S ((j ≫ F).base z) := hcomp.symm ▸ hkcomp
  rw [LocallyRingedSpace.stalkMap_comp] at hjcomp
  change RingHom.ker ((j.stalkMap z).hom.comp (F.stalkMap (j.base z)).hom) = _ at hjcomp
  rw [RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso _).1] at hjcomp
  exact hjcomp

end

end SGPT.Unibranch.UnibAn
