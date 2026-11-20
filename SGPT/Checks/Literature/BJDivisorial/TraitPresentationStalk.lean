import SGPT.Checks.Literature.BJDivisorial.DVRLocalPresentation
import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeTraitCenterNativeOrders

/-!
# Canonical stalk equality from the actual finite DVR presentation

A dominant whole trait in an integral model makes its actual stalk map
injective. When the finite presentation is regular at its center, the
actual coefficient square and the localization property make that same
map surjective. Discreteness and codimension one are then conclusions.
The regular coefficients are constructed from the actual compactification
open in the proper-model producer, rather than passed to a book theorem.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Order

namespace SGPT.NAPotential.BJ.Divisorial
open SGPT.Foundations.PublishedEnvelope

universe u
section General
variable {V K : Type u} [CommRing V] [IsLocalRing V] [Field K] [Algebra V K]
  {Y : Scheme.{u}} [IsIntegral Y]
  (q : Spec (.of V) ⟶ Y)
  [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ q)]

include K

/-- Generic dominance makes the actual canonical local stalk map injective. -/
theorem trait_stalkMap_injective : Function.Injective (Scheme.stalkClosedPointTo q).hom := by
  apply Function.Injective.of_comp (f := algebraMap V K)
  change Function.Injective ((algebraMap V K).comp (Scheme.stalkClosedPointTo q).hom)
  rw [SchemeTraitCenterNativeOrders.original_coefficient_square q]
  exact (SchemeGenericFieldGraph.fieldHom
    (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ q)).hom.injective.comp
      (IsFractionRing.injective (Y.presheaf.stalk (q (closedPoint V))) Y.functionField)

/-- Regularity of the actual finite presentation derives equality of the
canonical stalk map with the whole original DVR. -/
theorem trait_stalkMap_bijective_of_localization
    {A : Type*} [CommRing A] [Algebra A V] (S : Submonoid A) [IsLocalization S V]
    (a : A →+* Y.presheaf.stalk (q (closedPoint V)))
    (ha : (Scheme.stalkClosedPointTo q).hom.comp a = algebraMap A V) :
    Function.Bijective (Scheme.stalkClosedPointTo q).hom := by
  let : Algebra A (Y.presheaf.stalk (q (closedPoint V))) := a.toAlgebra
  exact ⟨trait_stalkMap_injective (K := K) q,
    localMap_surjective_of_localization S (Scheme.stalkClosedPointTo q).hom ha⟩

end General
section DVR
variable {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] {Y : Scheme.{u}} [IsIntegral Y]
  (q : Spec (.of V) ⟶ Y)
  [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ q)]
include K

/-- The center stalk is a DVR, proved from the actual localization square. -/
theorem trait_stalk_isDVR_of_localization
    {A : Type*} [CommRing A] [Algebra A V] (S : Submonoid A) [IsLocalization S V]
    (a : A →+* Y.presheaf.stalk (q (closedPoint V)))
    (ha : (Scheme.stalkClosedPointTo q).hom.comp a = algebraMap A V) :
    IsDiscreteValuationRing (Y.presheaf.stalk (q (closedPoint V))) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.ofBijective _ (trait_stalkMap_bijective_of_localization (K := K) q S a ha)).symm

/-- The same actual point has codimension one, as a derived geometric fact. -/
theorem trait_center_coheight_of_localization
    {A : Type*} [CommRing A] [Algebra A V] (S : Submonoid A) [IsLocalization S V]
    (a : A →+* Y.presheaf.stalk (q (closedPoint V)))
    (ha : (Scheme.stalkClosedPointTo q).hom.comp a = algebraMap A V) :
    coheight (q (closedPoint V)) = 1 := by
  have hd : ringKrullDim (Y.presheaf.stalk (q (closedPoint V))) = 1 :=
    (ringKrullDim_eq_of_ringEquiv
      (RingEquiv.ofBijective _ (trait_stalkMap_bijective_of_localization (K := K) q S a ha))).trans
      (IsDiscreteValuationRing.ringKrullDim_eq_one V)
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact WithBot.coe_injective hd

end DVR
end SGPT.NAPotential.BJ.Divisorial
