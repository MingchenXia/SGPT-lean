import SGPT.NAPotential.ProjectiveGraphCentredChart
import SGPT.NAPotential.ProjectiveGraphStalkNaturality
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual graph projection and original coefficient/stalk readback

The graph ring is the literal original `A[b]`. Its first projection is the actual
Spec map of its coefficient inclusion followed by the original affine-open map.
Blueprint: `projective-graph-projection.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjection

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Opposite

variable {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) [Nonempty U]
  (hU : IsAffineOpen U) {s : ℕ} (b : Fin s → X.functionField)

/-- The actual coefficient morphism to the actual original affine chart. -/
def affineProjection : Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))) ⟶ Spec Γ(X, U) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b))))

/-- The graph's actual first projection into the original X. -/
def projection : Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))) ⟶ X :=
  affineProjection U b ≫ hU.fromSpec

theorem projection_mem (z : Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))) :
    projection U hU b z ∈ U := by
  have hz : affineProjection U b z ∈ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
    trivial
  exact hz

/-- The actual coefficient inclusion is injective through the original generic germ map. -/
theorem coefficient_injective :
    Function.Injective (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b))) := by
  intro a a' h
  apply X.germToFunctionField_injective U
  exact congrArg Subtype.val h

/-- The actual coefficient Spec map sends the actual generic point to the actual generic point. -/
theorem affineProjection_genericPoint :
    affineProjection U b (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))))) =
      genericPoint (Spec Γ(X, U)) := by
  change PrimeSpectrum.comap (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)))
    (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))))) = _
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot _).mp (coefficient_injective U b)

/-- The original graph projection sends its actual generic point to the original generic point of X. -/
theorem projection_genericPoint :
    projection U hU b (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))))) = genericPoint X := by
  change hU.fromSpec (affineProjection U b _) = _
  rw [affineProjection_genericPoint]
  exact genericPoint_eq_of_isOpenImmersion hU.fromSpec

omit [IsIntegral X] [Nonempty U] in
/-- Original affine sections pull back to their canonical native stalk germs under the actual affine-open map. -/
theorem fromSpec_stalkMap_germ (z : Spec Γ(X, U)) (hz : hU.fromSpec z ∈ U) (a : Γ(X, U)) :
    hU.fromSpec.stalkMap z (X.presheaf.germ U (hU.fromSpec z) hz a) = StructureSheaf.toStalk Γ(X, U) z a := by
  rw [Scheme.Hom.germ_stalkMap_apply, hU.fromSpec_app_self]
  change (Spec Γ(X, U)).presheaf.germ (hU.fromSpec ⁻¹ᵁ U) z hz
    ((Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op
      ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = _
  rw [(Spec Γ(X, U)).presheaf.germ_res_apply]
  exact StructureSheaf.algebraMap_germ_apply ⊤ z trivial a

/-- **Exact original coefficient/stalk square** for the actual graph projection. -/
theorem projection_stalkMap_germ (z : Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))) (a : Γ(X, U)) :
    (projection U hU b).stalkMap z
      (X.presheaf.germ U (projection U hU b z) (projection_mem U hU b z) a) =
        StructureSheaf.toStalk (Algebra.adjoin Γ(X, U) (Set.range b)) z
          (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a) := by
  dsimp only [projection]
  rw [Scheme.Hom.stalkMap_comp]
  change (affineProjection U b).stalkMap z
    (hU.fromSpec.stalkMap (affineProjection U b z)
      (X.presheaf.germ U (hU.fromSpec (affineProjection U b z)) _ a)) = _
  rw [fromSpec_stalkMap_germ U hU]
  exact AlgebraicGeometry.stalkMap_toStalk_apply _ z a

/-- The actual generic-stalk pullback of the actual original graph projection. -/
def functionFieldPullback :
    X.functionField →+* (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).functionField :=
  ProjectiveGraphStalkNaturality.genericPullback (projection U hU b) (projection_genericPoint U hU b)

/-- The actual projection's native field pullback commutes with every actual original stalk germ. -/
theorem functionFieldPullback_stalk
    (z : Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))))
    (g : X.presheaf.stalk (projection U hU b z)) :
    functionFieldPullback U hU b (algebraMap (X.presheaf.stalk (projection U hU b z)) X.functionField g) =
      algebraMap ((Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).presheaf.stalk z)
        (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).functionField
          ((projection U hU b).stalkMap z g) :=
  ProjectiveGraphStalkNaturality.genericPullback_stalk _ _ z g

/-- **Exact original coefficient identity of the actual native generic pullback**. -/
theorem functionFieldPullback_coeff (a : Γ(X, U)) :
    functionFieldPullback U hU b (X.germToFunctionField U a) =
      StructureSheaf.toStalk (Algebra.adjoin Γ(X, U) (Set.range b))
        (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))))
          (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcast : (X.presheaf.stalkCongr (.of_eq (projection_genericPoint U hU b).symm)).hom
      (X.presheaf.germ U (genericPoint X) hηU a) =
        X.presheaf.germ U (projection U hU b
          (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))))))
          (projection_mem U hU b _) a := by
    exact X.presheaf.germ_stalkSpecializes_apply hηU
      (Inseparable.of_eq (projection_genericPoint U hU b).symm).ge a
  change (projection U hU b).stalkMap _
    ((X.presheaf.stalkCongr (.of_eq (projection_genericPoint U hU b).symm)).hom
      (X.presheaf.germ U (genericPoint X) hηU a)) = _
  rw [hcast]
  exact projection_stalkMap_germ U hU b _ a

/-- The actual native pullback is uniquely determined on the actual original affine coefficients. -/
theorem functionFieldPullback_eq_of_coeff
    (ψ : X.functionField →+* (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).functionField)
    (hψ : ∀ a : Γ(X, U), ψ (X.germToFunctionField U a) =
      StructureSheaf.toStalk (Algebra.adjoin Γ(X, U) (Set.range b))
        (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))))
          (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a)) :
    functionFieldPullback U hU b = ψ := by
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, U))
  ext a
  exact (functionFieldPullback_coeff U hU b a).trans (hψ a).symm

/-- The actual graph projection is over the original structural coefficients, by the literal original ring map. -/
theorem projection_overBase (f : X ⟶ Spec (.of ℂ)) :
    letI := affineChartAlgebra f U
    projection U hU b ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b))).comp (algebraMap ℂ Γ(X, U)))) := by
  let := affineChartAlgebra f U
  change (affineProjection U b ≫ hU.fromSpec) ≫ f = _
  rw [Category.assoc, affineChartStructuralMap_eq_affineStructuralMap f hU]
  change Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X, U))) = _
  rw [← Spec.map_comp]
  rfl

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjection
