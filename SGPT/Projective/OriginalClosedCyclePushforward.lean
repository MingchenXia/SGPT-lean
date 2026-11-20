import SGPT.Projective.AlgebraicArtinianCycleDegree
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Genuine actual original closed-immersion residue/cycle weights and FULL
Artinian zero-cycle coefficient readers. Blueprint: original-closed-cycle-pushforward.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry Set
open scoped BigOperators

/-- SAME actual original closed immersion produces genuine original residue field bijection. -/
theorem originalClosedImmersion_residueFieldMap_bijective {Z X : Scheme.{0}}
    (ι : Z ⟶ X) [IsClosedImmersion ι] (z : Z) : Function.Bijective (ι.residueFieldMap z) := by
  refine ⟨(ι.residueFieldMap z).hom.injective, ?_⟩
  intro c
  obtain ⟨t, ht⟩ := Z.residue_surjective z c
  obtain ⟨s, hs⟩ := ι.stalkMap_surjective z t
  refine ⟨X.residue (ι z) s, ?_⟩
  have h := congrArg (fun q => q s) (Scheme.residue_residueFieldMap ι z)
  change ι.residueFieldMap z (X.residue (ι z) s) = Z.residue z (ι.stalkMap z s) at h
  rw [hs, ht] at h
  exact h

/-- Original actual scalar extension degree is one, from actual original residue field map. -/
theorem originalClosedImmersion_residueDegree_one {Z X : Scheme.{0}}
    (ι : Z ⟶ X) [IsClosedImmersion ι] (z : Z) : ι.residueDegree z = 1 := by
  let := (ι.residueFieldMap z).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap (originalClosedImmersion_residueFieldMap_bijective ι z)

/-- An ACTUAL original closed singleton gives actual original point dimension zero. -/
theorem originalPointDimension_zero_of_isClosed {X : Scheme.{0}} (x : X)
    (hx : IsClosed ({x} : Set X)) : pointDimension X x = 0 := by
  apply Order.height_eq_zero.mpr
  intro y hy
  have hxy : x ⤳ Specialization.ofEquiv y := hy
  have he : x = Specialization.ofEquiv y := (Set.mem_singleton_iff.mp
    (hxy.mem_closed hx (Set.mem_singleton x))).symm
  simpa only [Specialization.toEquiv_ofEquiv] using
    (le_of_eq (congrArg Specialization.toEquiv he))

/-- Genuine original AlgebraicCycle.mapCoeff is one at EVERY point of whole actual Artinian closed source. -/
theorem originalClosedImmersion_artinian_mapCoeff_one {Z X : Scheme.{0}}
    (ι : Z ⟶ X) [IsClosedImmersion ι] [IsArtinianScheme Z] (z : Z) :
    AlgebraicCycle.mapCoeff ι (pointDimension Z) (pointDimension X) z = 1 := by
  have hx : IsClosed ({ι z} : Set X) := by
    simpa only [Set.image_singleton] using ι.isClosedEmbedding.isClosedMap _
      (isClosed_singleton : IsClosed ({z} : Set Z))
  simp only [AlgebraicCycle.mapCoeff, pointDimension_eq_zero_of_discrete,
    originalPointDimension_zero_of_isClosed (ι z) hx, ↓reduceIte,
    originalClosedImmersion_residueDegree_one]

/-- ACTUAL original Artinian closed-cycle pushforward preserves SAME FULL original local multiplicity. -/
theorem originalClosedImmersion_artinianCycle_at_image {Z X : Scheme.{0}}
    (ι : Z ⟶ X) [IsClosedImmersion ι] [IsArtinianScheme Z] (z : Z) :
    AlgebraicCycle.map ι (pointDimension Z) (pointDimension X) (artinianZeroCycle Z) (ι z) =
      ((Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z)).toNat : ℤ) := by
  have hpre : ι ⁻¹' ({ι z} : Set X) = {z} := by
    ext w
    exact ι.isClosedEmbedding.injective.eq_iff
  change (∑ᶠ w ∈ ι ⁻¹' ({ι z} : Set X), artinianZeroCycle Z w *
    (AlgebraicCycle.mapCoeff ι (pointDimension Z) (pointDimension X) w : ℤ)) = _
  simp only [hpre, finsum_mem_singleton, originalClosedImmersion_artinian_mapCoeff_one,
    Nat.cast_one, mul_one, artinianZeroCycle_apply]

/-- ACTUAL original closed-cycle pushforward is zero outside its ENTIRE original point image. -/
theorem originalClosedImmersion_artinianCycle_off_image {Z X : Scheme.{0}}
    (ι : Z ⟶ X) [IsClosedImmersion ι] [IsArtinianScheme Z] (x : X) (hx : x ∉ Set.range ι) :
    AlgebraicCycle.map ι (pointDimension Z) (pointDimension X) (artinianZeroCycle Z) x = 0 := by
  have hpre : ι ⁻¹' ({x} : Set X) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hx ⟨z, hz⟩
  change (∑ᶠ w ∈ ι ⁻¹' ({x} : Set X), artinianZeroCycle Z w *
    (AlgebraicCycle.mapCoeff ι (pointDimension Z) (pointDimension X) w : ℤ)) = _
  simp only [hpre, finsum_mem_empty]

end SGPT.Projective.NumEq.AlgebraicCurveDegree
