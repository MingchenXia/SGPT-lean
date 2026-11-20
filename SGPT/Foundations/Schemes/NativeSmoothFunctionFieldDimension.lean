import SGPT.Foundations.Schemes.NativeStandardSmoothFieldTranscendence
import SGPT.Foundations.Schemes.NativeProjectiveFano
import SGPT.Foundations.Schemes.SchemeGenericSections

/-!
# Actual smooth function-field transcendence degree

An actual standard-smooth chart around the generic point gives the intrinsic
function-field transcendence degree, with the original structural scalars.
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {K : Type} [Field K] {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of K))

/-- Actual chart constants and the actual generic germ give the true
structural scalar tower on the existing scheme function field. -/
theorem schemeFunctionField_affineChartScalarTower (V : X.Opens) [Nonempty V] :
    letI := affineChartAlgebra f V
    letI := schemeFunctionFieldAlgebra f
    IsScalarTower K Γ(X, V) X.functionField := by
  let := affineChartAlgebra f V
  let := schemeFunctionFieldAlgebra f
  apply IsScalarTower.of_algebraMap_eq
  intro k
  change X.germToFunctionField ⊤ (schemeGlobalConstants f k) =
    X.germToFunctionField V
      (X.presheaf.map V.leTop.op (schemeGlobalConstants f k))
  exact (X.presheaf.germ_res_apply V.leTop (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›))
    (schemeGlobalConstants f k)).symm

/-- Smooth relative dimension produces intrinsic function-field
transcendence degree under the ORIGINAL structural field scalars. -/
theorem nativeSmoothFunctionField_trdeg (n : ℕ) [SmoothOfRelativeDimension n f] :
    letI := schemeFunctionFieldAlgebra f
    Algebra.trdeg K X.functionField = n := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨V, hV, hx, hs⟩ := smooth_cotangent_affine_chart f n (genericPoint X)
  have : Nonempty V := ⟨⟨genericPoint X, hx⟩⟩
  let := affineChartAlgebra f V
  have : IsScalarTower K Γ(X, V) X.functionField :=
    schemeFunctionField_affineChartScalarTower f V
  have : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  have : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) := hs
  exact nativeStandardSmoothFractionField_trdeg K Γ(X, V) X.functionField n

/-- In particular, the actual native smooth projective Fano function field
has the stated dimension, without any dimension premise. -/
theorem SmoothProjectiveFano.functionField_trdeg {n : ℕ} (F : SmoothProjectiveFano n) :
    letI := schemeFunctionFieldAlgebra F.structureMap
    Algebra.trdeg ℂ F.scheme.functionField = n :=
  nativeSmoothFunctionField_trdeg F.structureMap n

end
end SGPT.Foundations.Schemes
