import SGPT.Okounkov.SchemeCoordinateGlobalGerm

/-!
# Actual complex-linear global sections in analytic coordinate fractions

The exact original structure-induced scalar law has been proved. It now
bundles the actual field embedding as an algebra homomorphism and composes
with BWE's existing genuine atlas-chosen generic section evaluation. No
linearity, frame choice or injection certificate is a new premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

/-- The actual target complex algebra consists of actual constant germs. -/
@[instance_reducible] def schemeCoordinateFractionComplexAlgebra (n : ℕ) :
    Algebra ℂ (FractionRing (HolGerm (Fin n → ℂ))) :=
  ((algebraMap (HolGerm (Fin n → ℂ)) (FractionRing (HolGerm (Fin n → ℂ)))).comp
    (HolGerm.constHom : ℂ →+* HolGerm (Fin n → ℂ))).toAlgebra

/-- The TN-model target uses exactly the same actual constant-germ action. -/
@[instance_reducible] def schemeCoordinateModelFractionComplexAlgebra (n : ℕ) :
    Algebra ℂ (FractionRing (HolGerm (ComplexModel n))) :=
  ((algebraMap (HolGerm (ComplexModel n)) (FractionRing (HolGerm (ComplexModel n)))).comp
    (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n))).toAlgebra

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) [IsIntegral X]

local instance sectionCoordinateFractionAlgebra : Algebra ℂ (FractionRing (HolGerm (Fin n → ℂ))) :=
  schemeCoordinateFractionComplexAlgebra n

local instance sectionCoordinateModelFractionAlgebra :
    Algebra ℂ (FractionRing (HolGerm (ComplexModel n))) :=
  schemeCoordinateModelFractionComplexAlgebra n

/-- The exact original scalar law makes the genuine field embedding an actual
complex algebra homomorphism for the ORIGINAL structure-induced source action. -/
def schemeCoordinateFunctionFieldAlgHom :
    letI := schemeFunctionFieldAlgebra f
    X.functionField →ₐ[ℂ] FractionRing (HolGerm (Fin n → ℂ)) := by
  letI := schemeFunctionFieldAlgebra f
  exact { schemeCoordinateFunctionFieldGerm f n p with
    commutes' := schemeCoordinateFunctionFieldGerm_const f n p }

/-- The complex algebra homomorphism retains the actual function-field injection. -/
theorem schemeCoordinateFunctionFieldAlgHom_injective :
    Function.Injective (schemeCoordinateFunctionFieldAlgHom f n p) :=
  schemeCoordinateFunctionFieldGerm_injective f n p

/-- Actual model transport preserves the same DERIVED original scalar law. -/
def schemeCoordinateModelFunctionFieldAlgHom :
    letI := schemeFunctionFieldAlgebra f
    X.functionField →ₐ[ℂ] FractionRing (HolGerm (ComplexModel n)) := by
  letI := schemeFunctionFieldAlgebra f
  exact { schemeCoordinateModelFunctionFieldGerm f n p with
    commutes' := by
      intro z
      change schemeCoordinateModelFractionEquiv n
        (schemeCoordinateFunctionFieldGerm f n p (algebraMap ℂ X.functionField z)) = _
      rw [schemeCoordinateFunctionFieldGerm_const, schemeCoordinateModelFractionEquiv_algebraMap,
        schemeCoordinateModelGermEquiv_const]
      rfl }

/-- The transported complex algebra homomorphism is genuinely injective. -/
theorem schemeCoordinateModelFunctionFieldAlgHom_injective :
    Function.Injective (schemeCoordinateModelFunctionFieldAlgHom f n p) :=
  schemeCoordinateModelFunctionFieldGerm_injective f n p

/-- Actual global line-bundle sections map complex-linearly to actual analytic
fractions, using the existing atlas-chosen genuine generic evaluation. -/
def schemeCoordinateGlobalSectionsGerm {L : X.Modules} (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule f L
    bundleSections L ⊤ →ₗ[ℂ] FractionRing (HolGerm (Fin n → ℂ)) := by
  letI := schemeGlobalSectionModule f L
  letI := schemeFunctionFieldAlgebra f
  exact (schemeCoordinateFunctionFieldAlgHom f n p).toLinearMap.comp
    (a.genericEvaluationOverBase f)

/-- Injection follows from the actual integral-scheme/atlas producer and the
actual previously proved function-field injection. -/
theorem schemeCoordinateGlobalSectionsGerm_injective {L : X.Modules} (a : LineBundleAtlas L) :
    Function.Injective (schemeCoordinateGlobalSectionsGerm f n p a) := by
  let := schemeGlobalSectionModule f L
  let := schemeFunctionFieldAlgebra f
  exact (schemeCoordinateFunctionFieldAlgHom_injective f n p).comp
    (a.genericEvaluationOverBase_injective f)

/-- The SAME actual global sections map complex-linearly to the TN-model
analytic fraction field through the genuine proved model transport. -/
def schemeCoordinateModelGlobalSectionsGerm {L : X.Modules} (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule f L
    bundleSections L ⊤ →ₗ[ℂ] FractionRing (HolGerm (ComplexModel n)) := by
  letI := schemeGlobalSectionModule f L
  letI := schemeFunctionFieldAlgebra f
  exact (schemeCoordinateModelFunctionFieldAlgHom f n p).toLinearMap.comp
    (a.genericEvaluationOverBase f)

/-- The actual TN-model complex-linear global section representation is faithful. -/
theorem schemeCoordinateModelGlobalSectionsGerm_injective {L : X.Modules}
    (a : LineBundleAtlas L) :
    Function.Injective (schemeCoordinateModelGlobalSectionsGerm f n p a) := by
  let := schemeGlobalSectionModule f L
  let := schemeFunctionFieldAlgebra f
  exact (schemeCoordinateModelFunctionFieldAlgHom_injective f n p).comp
    (a.genericEvaluationOverBase_injective f)

end SGPT.Okounkov
