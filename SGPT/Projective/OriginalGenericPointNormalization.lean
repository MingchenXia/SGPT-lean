import SGPT.Projective.OriginalFiniteNormalizationConductor
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Stalk

/-! ACTUAL original normalization scheme from the TRUE generic-point map,
and its SAME original generic coefficient/affine integral-closure readers.
No smoothness or normalization output certificate.
Blueprint: original-generic-point-normalization.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite IsLocalRing

variable (X : Scheme.{0}) [IsIntegral X]

/-- The ACTUAL original function-field point map: Spec of the original
GENERIC STALK to the SAME original scheme. -/
def originalGenericPointMap : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

instance originalGenericPointMap_quasiCompact : QuasiCompact (originalGenericPointMap X) := by
  constructor
  intro U _ _
  exact (Set.toFinite _).isCompact

instance originalGenericPointMap_quasiSeparated : QuasiSeparated (originalGenericPointMap X) := by
  dsimp only [originalGenericPointMap]
  infer_instance

/-- EVERY actual point of the original function-field Spec maps to the
SAME TRUE original generic point. -/
theorem originalGenericPointMap_apply (q : Spec X.functionField) :
    originalGenericPointMap X q = genericPoint X := by
  have hprime : Subsingleton (PrimeSpectrum X.functionField) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField X.functionField)
  have hq := @Subsingleton.elim (PrimeSpectrum X.functionField) hprime q (closedPoint X.functionField)
  rw [hq]
  exact Scheme.fromSpecStalk_closedPoint

/-- The actual inverse image of EVERY nonempty original open is literally
the ENTIRE actual original function-field scheme. -/
theorem originalGenericPointMap_preimage_top (U : X.Opens) [Nonempty U] :
    originalGenericPointMap X ⁻¹ᵁ U = ⊤ := by
  ext q
  change originalGenericPointMap X q ∈ U ↔ True
  rw [originalGenericPointMap_apply]
  exact iff_true_intro (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U)))

/-- Actual original generic inverse-open sections identify with the SAME
function field via the TRUE inverse-open identity and genuine ΓSpec iso. -/
def originalGenericPointSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, originalGenericPointMap X ⁻¹ᵁ U) ≅ X.functionField :=
  ((Spec X.functionField).presheaf.mapIso (eqToIso (originalGenericPointMap_preimage_top X U)).op).symm ≪≫
    Scheme.ΓSpecIso X.functionField

/-- The ACTUAL original generic map's section pullback, followed by the
actual ΓSpec reader, is EXACTLY the original generic germ coefficient. -/
theorem originalGenericPointMap_app_sectionsIso (U : X.Opens) [Nonempty U] :
    (originalGenericPointMap X).app U ≫ (originalGenericPointSectionsIso X U).hom =
      X.germToFunctionField U := by
  have hU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))
  have hmap : (Spec X.functionField).presheaf.map
      (homOfLE (show originalGenericPointMap X ⁻¹ᵁ U ≤ ⊤ from le_top)).op =
      ((Spec X.functionField).presheaf.mapIso
        (eqToIso (originalGenericPointMap_preimage_top X U)).op).hom := by
    apply congrArg (Spec X.functionField).presheaf.map
    exact Subsingleton.elim _ _
  dsimp only [originalGenericPointMap]
  rw [Scheme.fromSpecStalk_app hU]
  change (X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫ _) ≫ _ = _
  rw [hmap]
  simp only [originalGenericPointSectionsIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual normalization scheme, constructed by genuine relative
normalization of the TRUE original generic-point stalk map. -/
def originalNormalizationScheme : Scheme.{0} := (originalGenericPointMap X).normalization

/-- The actual ORIGINAL normalization map; no supplied finite/smooth map. -/
def originalNormalizationMap : originalNormalizationScheme X ⟶ X :=
  (originalGenericPointMap X).fromNormalization

instance originalNormalizationMap_integral : IsIntegralHom (originalNormalizationMap X) := by
  dsimp only [originalNormalizationMap]
  infer_instance

instance originalNormalizationMap_affine : IsAffineHom (originalNormalizationMap X) := by
  dsimp only [originalNormalizationMap]
  infer_instance

instance originalNormalizationScheme_integral : IsIntegral (originalNormalizationScheme X) := by
  dsimp only [originalNormalizationScheme]
  infer_instance

/-- TRUE original affine-normalization section reader, before transporting
the actual generic inverse-open sections to the SAME original function field. -/
def originalNormalizationAffineSectionsIso {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) ≅
      (letI := ((originalGenericPointMap X).app U).hom.toAlgebra;
        CommRingCat.of (integralClosure Γ(X, U) Γ(Spec X.functionField, originalGenericPointMap X ⁻¹ᵁ U))) :=
  (originalGenericPointMap X).normalizationObjIso hU

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
