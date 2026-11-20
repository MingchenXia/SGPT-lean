import SGPT.Projective.OriginalNormalizationCurveDVR
import SGPT.Foundations.Schemes.SchemeModulePushforwardCech
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! TRUE finite ORIGINAL normalization defect on every original affine
curve chart, from manufactured actual nonzero conductor. The actual
structural scalar square is proved, no defect finiteness premise.
Blueprint: original-normalization-defect-finite.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Algebra
open scoped nonZeroDivisors

/-- The actual ORIGINAL affine structural scalar square of a genuine
morphism, on the literal original inverse-image open. -/
theorem originalMorphism_affineChartScalarTower {Y Z : Scheme.{0}}
    (f : Y ⟶ Spec (.of ℂ)) (g : Z ⟶ Y) (U : Y.Opens) :
    letI := affineChartAlgebra f U
    letI := affineChartAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    letI := ((g.app U).hom).toAlgebra
    IsScalarTower ℂ Γ(Y,U) Γ(Z,g ⁻¹ᵁ U) := by
  let := affineChartAlgebra f U
  let := affineChartAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  let := ((g.app U).hom).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro z
  exact (actualSchemePushforwardStructuralScalar g (schemeGlobalConstants f) U z).symm

/-- A finite actual module on a genuine one-dimensional affine curve,
annihilated by an actual nonzero function, is finite over the base field. -/
theorem originalCurveModule_finite_of_nonzero_annihilator
    (k R M : Type*) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] [Module.Finite R M]
    (hdim : ringKrullDim R = 1) (c : R) (hc : c ≠ 0)
    (hkill : Module.IsTorsionBy R M c) : Module.Finite k M := by
  let I : Ideal R := Ideal.span {c}
  have hI : Module.IsTorsionBySet R M I :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr hkill
  let := hI.module
  let : IsScalarTower R (R ⧸ I) M := hI.isScalarTower
  let : IsScalarTower k (R ⧸ I) M := hI.isScalarTower
  have hdimQ : ringKrullDim (R ⧸ I) ≤ 0 := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_iff_ne_zero.mpr hc)
    rw [hdim] at h
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_one,Nat.cast_zero,zero_add] using h
  let : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_iff.mpr hdimQ
  let : Module.Finite k (R ⧸ I) := (Module.finite_iff_krullDimLE_zero k (R ⧸ I)).mpr inferInstance
  let : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R _ _
  exact Module.Finite.trans (R ⧸ I) M

/-- The ACTUAL ordinary additive quotient by the ORIGINAL coefficient
inclusion, not a reduced support or a freely supplied defect object. -/
abbrev originalAlgebraDefect (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :=
  S ⧸ (Algebra.linearMap R S).range

/-- Primitive true conductor multiplication annihilates the ENTIRE
actual original additive normalization quotient, including nilpotent lengths. -/
theorem originalAlgebraDefect_conductor_kills
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (c : R) (hcon : ∀ x : S, ∃ r : R, algebraMap R S r = c • x) :
    Module.IsTorsionBy R (originalAlgebraDefect R S) c := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (c • x) = (0 : originalAlgebraDefect R S)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact hcon x

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include f E hcurve in
/-- The ENTIRE actual normalized inverse-affine section quotient by the
LITERAL original normalization coefficient map is a finite-dimensional
complex vector space. Actual scalar compatibility/conductor/dimension and
finiteness are manufactured, no desired defect condition is assumed. -/
theorem originalNormalizationAffineDefect_finite
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    letI := affineChartAlgebra f U
    letI := affineChartAlgebra (originalNormalizationMap X ≫ f) (originalNormalizationMap X ⁻¹ᵁ U)
    letI := (((originalNormalizationMap X).app U).hom).toAlgebra
    letI := originalMorphism_affineChartScalarTower f (originalNormalizationMap X) U
    Module.Finite ℂ (originalAlgebraDefect Γ(X,U)
      Γ(originalNormalizationScheme X,originalNormalizationMap X ⁻¹ᵁ U)) := by
  let := affineChartAlgebra f U
  let := affineChartAlgebra (originalNormalizationMap X ≫ f) (originalNormalizationMap X ⁻¹ᵁ U)
  let := (((originalNormalizationMap X).app U).hom).toAlgebra
  let := originalMorphism_affineChartScalarTower f (originalNormalizationMap X) U
  let R := Γ(X,U)
  let S := Γ(originalNormalizationScheme X,originalNormalizationMap X ⁻¹ᵁ U)
  let : Algebra.FiniteType ℂ R := by
    let := E.locallyOfFiniteType
    exact affineChartAlgebra_finiteType f hU
  let : Module.Finite R S := originalNormalizationMap_app_finite X U hU f E
  obtain ⟨c,hc,hcon⟩ := originalAffineNormalization_exists_nonzero_conductor f E hU
  have hcon' : ∀ x : S, ∃ r : R, algebraMap R S r = c • x := by
    intro x
    let e := originalNormalizationAffineAlgEquiv X U hU
    obtain ⟨r,hr⟩ := hcon (e x)
    refine ⟨r,?_⟩
    apply e.injective
    change e (algebraMap R S r) = e.toLinearEquiv (c • x)
    rw [e.toLinearEquiv.map_smul,e.commutes]
    apply Subtype.ext
    rw [Subalgebra.coe_smul]
    simpa only [Subalgebra.coe_algebraMap,Algebra.smul_def,AlgEquiv.coe_toLinearEquiv] using hr
  exact originalCurveModule_finite_of_nonzero_annihilator ℂ R (originalAlgebraDefect R S)
    (originalIntegralCurve_affine_ringKrullDim_one f E hcurve hU) c hc
    (originalAlgebraDefect_conductor_kills R S c hcon')

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
