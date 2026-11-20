import SGPT.Unibranch.UnibAnProjectiveStalkKernel
import SGPT.Unibranch.UnibAnProjectiveAnalyticTrace
import SGPT.Unibranch.UnibAnProjectiveProper
import SGPT.Unibranch.OriginalAnalyticClosedSubspaceFactorization

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Topology
open SGPT.Foundations.Analysis.Pending.HironakaIntrinsicReducedCentreOpenPullback
open SGPT.Foundations.Schemes SGPT.Unibranch

namespace SGPT.Unibranch.UnibAn

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem bijective_of_quotient_kernel {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (a : R →+* A) (b : A →+* B) (ha : Function.Surjective a)
    (hab : Function.Surjective (b.comp a))
    (hk : RingHom.ker (b.comp a) = RingHom.ker a) : Function.Bijective b := by
  constructor
  · intro s t hst
    obtain ⟨r, hr⟩ := ha (s - t)
    have hz : (b.comp a) r = 0 := by
      change b (a r) = 0
      rw [hr, map_sub, hst, sub_self]
    have hmem : r ∈ RingHom.ker (b.comp a) := hz
    rw [hk] at hmem
    exact sub_eq_zero.mp (hr.symm.trans hmem)
  · intro t
    obtain ⟨r, hr⟩ := hab t
    exact ⟨a r, hr⟩

private theorem intrinsicIdeal_cast {B : LocallyRingedSpace.{0}} (S : Set B) {p q : B} (h : p = q) :
    Ideal.comap (eqToHom (congrArg (fun x => B.presheaf.stalk x) h)).hom
      (intrinsicCentreStalkRange B S q) = intrinsicCentreStalkRange B S p := by
  subst q
  rfl

/-- A full analytic map with the reduced quotient stalks identifies its
source with the factory on its actual closed analytic image. -/
theorem exists_iso_factory_of_projectiveStalkData
    {A B : SourceReducedComplexSpace} (F : A ⟶ B) {S : Set B.obj.left}
    (hS : B.IsAnalyticSubset S) (hrange : range F.hom.left.base = S)
    (hemb : IsClosedEmbedding F.hom.left.base)
    (hsurj : ∀ x : A.obj.left, Function.Surjective (F.hom.left.stalkMap x))
    (hker : ∀ x : A.obj.left, RingHom.ker (F.hom.left.stalkMap x).hom =
      intrinsicCentreStalkRange B.obj.left S (F.hom.left.base x)) :
    ∃ a : A ≅ OriginalAnalyticClosedSubspace.sourceObject B S hS,
      a.hom ≫ OriginalAnalyticClosedSubspace.inclusion B S hS = F := by
  let C := OriginalAnalyticClosedSubspace.sourceObject B S hS
  let j : C ⟶ B := OriginalAnalyticClosedSubspace.inclusion B S hS
  have hland (x : A.obj.left) : F.hom.left.base x ∈ S := hrange ▸ mem_range_self x
  obtain ⟨K, hK, _⟩ :=
    OriginalAnalyticClosedSubspaceFactorization.exists_unique_factorization B S hS A F hland
  let L : A.obj.left ⟶ C.obj.left := K.hom.left
  have hraw : L ≫ j.hom.left = F.hom.left := congrArg (fun T => T.hom.left) hK
  have hLemb : IsEmbedding L.base := by
    apply IsEmbedding.of_comp L.base.hom.continuous j.hom.left.base.hom.continuous
    change IsEmbedding (L ≫ j.hom.left).base
    rw [hraw]
    exact hemb.isEmbedding
  have hLsurj : Function.Surjective L.base := by
    intro y
    have hy : j.hom.left.base y ∈ S :=
      (OriginalAnalyticClosedSubspace.inclusion_range B S hS) ▸ mem_range_self y
    obtain ⟨x, hx⟩ := hrange.symm ▸ hy
    refine ⟨x, (OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding B S hS).injective ?_⟩
    exact (congrArg (fun H : A.obj.left ⟶ B.obj.left => H.base x) hraw).trans hx
  have hLopen : IsOpenEmbedding L.base := by
    refine ⟨hLemb, ?_⟩
    rw [hLsurj.range_eq]
    exact isOpen_univ
  have hbij (x : A.obj.left) : Function.Bijective (L.stalkMap x) := by
    let p : B.obj.left := j.hom.left.base (L.base x)
    let q : B.obj.left := F.hom.left.base x
    have hpq : p = q := congrArg (fun H : A.obj.left ⟶ B.obj.left => H.base x) hraw
    let ε : B.obj.left.presheaf.stalk p ≅ B.obj.left.presheaf.stalk q :=
      eqToIso (congrArg (fun y => B.obj.left.presheaf.stalk y) hpq)
    have hs : j.hom.left.stalkMap (L.base x) ≫ L.stalkMap x =
        ε.hom ≫ F.hom.left.stalkMap x := by
      rw [← LocallyRingedSpace.stalkMap_comp]
      exact PresheafedSpace.stalkMap.congr_hom
        (L ≫ j.hom.left).toHom F.hom.left.toHom
        (congrArg LocallyRingedSpace.Hom.toHom hraw) x
    let a := (j.hom.left.stalkMap (L.base x)).hom
    let b := (L.stalkMap x).hom
    let d := (F.hom.left.stalkMap x).hom
    have hsR : b.comp a = d.comp ε.hom.hom := congrArg CommRingCat.Hom.hom hs
    have ha : Function.Surjective a :=
      OriginalAnalyticClosedSubspace.inclusion_stalk_surjective B S hS (L.base x)
    have hab : Function.Surjective (b.comp a) := by
      rw [hsR]
      exact (hsurj x).comp (ConcreteCategory.bijective_of_isIso ε.hom).2
    have hk : RingHom.ker (b.comp a) = RingHom.ker a := by
      calc
        RingHom.ker (b.comp a) = RingHom.ker (d.comp ε.hom.hom) := congrArg RingHom.ker hsR
        _ = Ideal.comap ε.hom.hom (RingHom.ker d) := (RingHom.comap_ker _ _).symm
        _ = Ideal.comap ε.hom.hom (intrinsicCentreStalkRange B.obj.left S q) := by
          rw [show RingHom.ker d = intrinsicCentreStalkRange B.obj.left S q from hker x]
        _ = intrinsicCentreStalkRange B.obj.left S p := intrinsicIdeal_cast S hpq
        _ = RingHom.ker a :=
          (OriginalAnalyticClosedSubspace.inclusion_stalk_kernel B S hS (L.base x)).symm
    exact bijective_of_quotient_kernel a b ha hab hk
  have hstalk (x : A.obj.left) : IsIso (L.stalkMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij x)
  let : LocallyRingedSpace.IsOpenImmersion L :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso L hLopen (stalk_iso := hstalk)
  let : Epi L.base := (TopCat.epi_iff_surjective _).mpr hLsurj
  let : IsIso L := LocallyRingedSpace.IsOpenImmersion.to_iso L
  let a : A ≅ C := ObjectProperty.isoMk _ (Over.isoMk (asIso L) (Over.w K.hom))
  refine ⟨a, ?_⟩
  change K ≫ j = F
  exact hK

section Projective

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

local notation "g₀" => polynomialProjStructureMap ℂ E.ambientDimension

/-- The whole actual image of the projective analytification map is its
literal scheme-point trace in the glued projective ambient space. -/
theorem analytificationMorphism_projective_range :
    range (analytificationMorphism E.map E.over_base).hom.left.base =
      (schemeComplexPointImage g₀ ∘ pointMap g₀) ⁻¹' range E.map := by
  let g := g₀
  let F : analytification f ⟶ analytification g := analytificationMorphism E.map E.over_base
  have hpoints : range (schemeComplexPointMap f g E.map E.over_base) =
      {p | schemeComplexPointImage g p ∈ range E.map} := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨schemeComplexPointImage f q, (Scheme.Hom.comp_apply q.val E.map default).symm⟩
    · intro hp
      obtain ⟨q, hq⟩ := exists_closedImmersionComplexPoint g E.map p hp
      let q' : SchemeComplexPoint f := ⟨q.val,
        (congrArg (fun h : X ⟶ Spec (.of ℂ) => q.val ≫ h) E.over_base).symm.trans q.property⟩
      refine ⟨q', Subtype.ext ?_⟩
      exact congrArg Subtype.val hq
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx : pointMap g (F.hom.left.base x) ∈
        range (schemeComplexPointMap f g E.map E.over_base) :=
      ⟨pointMap f x, (pointMap_analytificationMorphism E.map E.over_base x).symm⟩
    change schemeComplexPointImage g (pointMap g (F.hom.left.base x)) ∈ range E.map
    exact (Set.ext_iff.mp hpoints _).mp hx
  · intro hy
    change schemeComplexPointImage g (pointMap g y) ∈ range E.map at hy
    have hpy : pointMap g y ∈ range (schemeComplexPointMap f g E.map E.over_base) :=
      (Set.ext_iff.mp hpoints _).mpr hy
    obtain ⟨q, hq⟩ := hpy
    obtain ⟨x, hx⟩ := pointMap_surjective q
    refine ⟨x, pointMap_injective
      ((pointMap_analytificationMorphism E.map E.over_base x).trans ?_)⟩
    exact (congrArg (schemeComplexPointMap f g E.map E.over_base) hx).trans hq

/-- The actual image is analytic by the independently constructed pullback
from native smooth projective space. -/
theorem analytificationMorphism_projective_range_isAnalyticSubset :
    (analytification g₀).IsAnalyticSubset
      (range (analytificationMorphism E.map E.over_base).hom.left.base) := by
  rw [analytificationMorphism_projective_range E]
  exact isAnalyticSubset_projective_algebraicTrace g₀
    ⟨E.ambientDimension, 𝟙 _, inferInstance, Category.id_comp _⟩
    _ E.map.isClosedEmbedding.isClosed_range

/-- The actual projective analytification morphism identifies its source with
the original reduced analytic subspace of its literal ambient image. -/
theorem exists_projectiveAnalytification_iso_reducedImage :
    let S := range (analytificationMorphism E.map E.over_base).hom.left.base
    let hS := analytificationMorphism_projective_range_isAnalyticSubset E
    ∃ a : analytification f ≅ OriginalAnalyticClosedSubspace.sourceObject (analytification g₀) S hS,
      a.hom ≫ OriginalAnalyticClosedSubspace.inclusion (analytification g₀) S hS =
        analytificationMorphism E.map E.over_base := by
  let F : analytification f ⟶ analytification g₀ := analytificationMorphism E.map E.over_base
  have hinj : Function.Injective F.hom.left.base := by
    intro x y hxy
    apply pointMap_injective
    apply Subtype.ext
    have h := (pointMap_analytificationMorphism E.map E.over_base x).symm.trans
      ((congrArg (pointMap g₀) hxy).trans (pointMap_analytificationMorphism E.map E.over_base y))
    exact (cancel_mono E.map).mp (congrArg Subtype.val h)
  have hemb : IsClosedEmbedding F.hom.left.base :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap F.hom.left.base.hom.continuous hinj
      (isProperMap_of_projective_source E F).isClosedMap
  exact exists_iso_factory_of_projectiveStalkData F
    (analytificationMorphism_projective_range_isAnalyticSubset E) rfl hemb
    (analytificationMorphism_projective_stalkMap_surjective E)
    (analytificationMorphism_projective_stalkMap_kernel E)

end Projective

end

end SGPT.Unibranch.UnibAn
