import SGPT.Projective.OriginalFiniteColengthCancellation
import SGPT.Projective.OriginalNormalizationDefectFinite
import SGPT.Projective.OriginalNormalizationLineUnit

/-! ORIGINAL principal quotients have SAME true finite colength on the
ACTUAL affine curve normalization, from actual finite defect/true maps.
Blueprint: original-normalization-principal-colength.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Algebra

/-- TRUE finite-dimensional principal quotient from actual original curve
geometry; no finite dimension output premise, including unit coefficients. -/
theorem originalCurvePrincipalQuotient_finite
    (k R : Type*) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] (hdim : ringKrullDim R = 1) (r : R) (hr : r ≠ 0) :
    Module.Finite k (R ⧸ Ideal.span {r}) := by
  apply originalCurveModule_finite_of_nonzero_annihilator k R (R ⧸ Ideal.span {r}) hdim r hr
  intro x
  induction x using Quotient.inductionOn' with
  | _ a =>
    change Ideal.Quotient.mk (Ideal.span {r}) (r*a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨a,rfl⟩)

/-- The SAME actual regular original coefficient has EQUAL principal
colength across an actual inclusion with TRUE finite entire additive defect.
Both quotients' finiteness is manufactured; no colength equality premise. -/
theorem originalFiniteDefectPrincipalQuotient_colength
    (k R S : Type*) [Field k] [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Module.Finite k (originalAlgebraDefect R S)]
    (hi : Function.Injective (algebraMap R S))
    (hdim : ringKrullDim R = 1) (r : R) (hr : r ≠ 0) :
    Module.Finite k (R ⧸ Ideal.span {r}) ∧
    Module.Finite k (S ⧸ Ideal.span {algebraMap R S r}) ∧
      Module.finrank k (R ⧸ Ideal.span {r}) = Module.finrank k (S ⧸ Ideal.span {algebraMap R S r}) := by
  let i : R →ₗ[k] S := (IsScalarTower.toAlgHom k R S).toLinearMap
  let P := i.range
  let u : S →ₗ[k] S :=
    { toFun := fun x => algebraMap R S r * x
      map_add' := fun x y => mul_add _ x y
      map_smul' := by intro a x; simp only [Algebra.smul_def,RingHom.id_apply]; ring }
  have hu : Function.Injective u := by
    intro x y hxy
    exact mul_left_cancel₀ (show algebraMap R S r ≠ 0 from fun h => hr (hi (h.trans (map_zero _).symm))) hxy
  have hP : P.map u ≤ P := by
    rintro _ ⟨x,⟨a,rfl⟩,rfl⟩
    refine ⟨r*a,?_⟩
    exact map_mul (algebraMap R S) r a
  let I : Ideal R := Ideal.span {r}
  let A := I.restrictScalars k
  let eR := LinearEquiv.ofInjective i hi
  have heR : A.map eR.toLinearMap = (P.map u).comap P.subtype := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp ha
      refine ⟨i b,⟨b,rfl⟩,?_⟩
      change algebraMap R S r * algebraMap R S b = algebraMap R S a
      rw [← map_mul,mul_comm r b,hb]
    · rintro ⟨y,⟨b,rfl⟩,hy⟩
      refine ⟨r*b,Ideal.mem_span_singleton.mpr ⟨b,rfl⟩,?_⟩
      apply Subtype.ext
      change algebraMap R S (r*b) = (x:S)
      exact (map_mul (algebraMap R S) r b).trans hy
  let eqR : (R ⧸ I) ≃ₗ[k] P ⧸ (P.map u).comap P.subtype :=
    (Submodule.Quotient.restrictScalarsEquiv k I).symm.trans
      (Submodule.Quotient.equiv A ((P.map u).comap P.subtype) eR heR)
  let : Module.Finite k (R ⧸ I) := originalCurvePrincipalQuotient_finite k R hdim r hr
  let : Module.Finite k (P ⧸ (P.map u).comap P.subtype) := Module.Finite.equiv eqR
  let PR := (Algebra.linearMap R S).range
  have hPR : P = PR.restrictScalars k := by ext x; rfl
  let eqD : (S ⧸ P) ≃ₗ[k] originalAlgebraDefect R S :=
    (Submodule.quotEquivOfEq _ _ hPR).trans (Submodule.Quotient.restrictScalarsEquiv k PR)
  let : Module.Finite k (S ⧸ P) := Module.Finite.equiv eqD.symm
  obtain ⟨hfinite,hcount⟩ := originalInjectiveOperator_finiteColength P u hu hP
  let : Module.Finite k (S ⧸ u.range) := hfinite
  let J : Ideal S := Ideal.span {algebraMap R S r}
  have hJ : u.range = J.restrictScalars k := by
    ext x
    constructor
    · rintro ⟨s,rfl⟩
      exact Ideal.mem_span_singleton.mpr ⟨s,rfl⟩
    · intro hx
      obtain ⟨s,hs⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨s,hs.symm⟩
  let eqS : (S ⧸ u.range) ≃ₗ[k] S ⧸ J :=
    (Submodule.quotEquivOfEq _ _ hJ).trans (Submodule.Quotient.restrictScalarsEquiv k J)
  refine ⟨inferInstance,Module.Finite.equiv eqS,?_⟩
  exact eqR.finrank_eq.trans (hcount.trans eqS.finrank_eq)

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include f E hcurve in
/-- LITERAL actual original affine curve normalization preserves the
FULL actual principal quotient complex colength of EVERY nonzero original
coefficient. Original smoothness/normalized embedding/comparison absent. -/
theorem originalNormalizationAffinePrincipalQuotient_colength
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] (r : Γ(X,U)) (hr : r ≠ 0) :
    letI := affineChartAlgebra f U
    letI := affineChartAlgebra (originalNormalizationMap X ≫ f) (originalNormalizationMap X ⁻¹ᵁ U)
    Module.Finite ℂ (Γ(X,U) ⧸ Ideal.span {r}) ∧
    Module.Finite ℂ (Γ(originalNormalizationScheme X,originalNormalizationMap X ⁻¹ᵁ U) ⧸
      Ideal.span {(originalNormalizationMap X).app U r}) ∧
    Module.finrank ℂ (Γ(X,U) ⧸ Ideal.span {r}) =
      Module.finrank ℂ (Γ(originalNormalizationScheme X,originalNormalizationMap X ⁻¹ᵁ U) ⧸
        Ideal.span {(originalNormalizationMap X).app U r}) := by
  let := affineChartAlgebra f U
  let := affineChartAlgebra (originalNormalizationMap X ≫ f) (originalNormalizationMap X ⁻¹ᵁ U)
  let := (((originalNormalizationMap X).app U).hom).toAlgebra
  let := originalMorphism_affineChartScalarTower f (originalNormalizationMap X) U
  obtain ⟨a⟩ := (inferInstance : Nonempty U)
  obtain ⟨z,hz⟩ := (originalNormalizationMap X).surjective a.1
  let : Nonempty (originalNormalizationMap X ⁻¹ᵁ U) :=
    ⟨⟨z,by change originalNormalizationMap X z ∈ U; rw [hz]; exact a.property⟩⟩
  let : Algebra.FiniteType ℂ Γ(X,U) := by
    let := E.locallyOfFiniteType
    exact affineChartAlgebra_finiteType f hU
  let : Module.Finite ℂ (originalAlgebraDefect Γ(X,U)
      Γ(originalNormalizationScheme X,originalNormalizationMap X ⁻¹ᵁ U)) :=
    originalNormalizationAffineDefect_finite f E hcurve hU
  exact originalFiniteDefectPrincipalQuotient_colength ℂ Γ(X,U)
    Γ(originalNormalizationScheme X,originalNormalizationMap X ⁻¹ᵁ U)
    (originalNormalizationMap_app_injective X U)
    (originalIntegralCurve_affine_ringKrullDim_one f E hcurve hU) r hr

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
