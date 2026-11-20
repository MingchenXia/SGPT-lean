import SGPT.Projective.OriginalNormalizationStalkGeometry
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.Field

/-! ACTUAL normalization of an arbitrary integral ORIGINAL projective
curve has true DVR stalks at EVERY closed normalized point/branch.
Actual original curve dimension =function-field trdeg1, NO smoothness.
Blueprint: original-normalization-curve-dvr.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Algebra
open scoped nonZeroDivisors

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include E hcurve in
/-- Actual original curve function-field dimension gives dimension one
on EVERY SAME nonempty original affine chart; NO smoothness input. -/
theorem originalIntegralCurve_affine_ringKrullDim_one
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] : ringKrullDim Γ(X, U) = 1 := by
  let := E.locallyOfFiniteType
  let := affineChartAlgebra f U
  let := schemeFunctionFieldAlgebra f
  let : IsScalarTower ℂ Γ(X, U) X.functionField := schemeFunctionField_affineChartScalarTower f U
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra.FiniteType ℂ Γ(X, U) := affineChartAlgebra_finiteType f hU
  let : Algebra.IsAlgebraic Γ(X, U) X.functionField :=
    IsLocalization.isAlgebraic X.functionField (nonZeroDivisors Γ(X, U))
  have htr : Algebra.trdeg ℂ Γ(X, U) = 1 := by
    have h := trdeg_add_eq ℂ Γ(X, U) (A := X.functionField)
    rw [trdeg_eq_zero (R := Γ(X, U)) (A := X.functionField), add_zero, hcurve] at h
    exact h
  exact finiteTypeDomain_ringKrullDim_of_trdeg ℂ Γ(X, U) 1 htr

include E hcurve in
/-- SAME actual normalized inverse-affine section ring has TRUE dimension
one, via genuine injective integral extension and actual ring readback. -/
theorem originalNormalizationCurve_affine_ringKrullDim_one
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    ringKrullDim Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) = 1 := by
  let R := Γ(X, U)
  let S := integralClosure R X.functionField
  let : IsFractionRing R X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro a b h
    exact IsFractionRing.injective R X.functionField (congrArg (fun s : S => (s : X.functionField)) h))
  have hdimS : ringKrullDim S = 1 :=
    (integralExtension_ringKrullDim_eq R S).trans (originalIntegralCurve_affine_ringKrullDim_one f E hcurve hU)
  exact (ringKrullDim_eq_of_ringEquiv
    (originalNormalizationAffineRingIso X U hU).commRingCatIsoToRingEquiv).trans hdimS

include E hcurve in
/-- The ACTUAL normalized inverse-affine original ring is Dedekind;
normality/Noetherianness/dimension ALL produced from original curve data. -/
theorem originalNormalizationCurve_affine_isDedekindDomain
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDedekindDomain Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) := by
  let V := originalNormalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (originalNormalizationMap X)
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  obtain ⟨z,hz⟩ := (originalNormalizationMap X).surjective u.1
  let : Nonempty V := ⟨⟨z,by change originalNormalizationMap X z ∈ U; rw [hz]; exact u.property⟩⟩
  let : IsLocallyNoetherian (originalNormalizationScheme X) := originalNormalization_isLocallyNoetherian X f E
  let : IsNoetherianRing Γ(originalNormalizationScheme X, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V,hV⟩
  let : IsIntegrallyClosed Γ(originalNormalizationScheme X, V) :=
    originalNormalizationAffine_sections_isIntegrallyClosed X hU
  let : Ring.KrullDimLE 1 Γ(originalNormalizationScheme X, V) :=
    (Ring.krullDimLE_iff).mpr (originalNormalizationCurve_affine_ringKrullDim_one f E hcurve hU).le
  let : Ring.DimensionLEOne Γ(originalNormalizationScheme X, V) :=
    ⟨fun hP hprime => hprime.isMaximal_of_ne_bot hP⟩
  refine (isDedekindDomain_iff _ (FractionRing Γ(originalNormalizationScheme X, V))).mpr ?_
  exact ⟨inferInstance,inferInstance,inferInstance,(isIntegrallyClosed_iff _).mp inferInstance⟩

include E hcurve in
/-- EVERY ACTUAL closed original normalized curve point has a TRUE DVR
stalk. Closedness, dimension and real same-chart localization manufacture
nonzero prime/Noetherian/normal data internally; ALL branches retained. -/
theorem originalNormalizationCurve_closedPoint_isDiscreteValuationRing
    (z : originalNormalizationScheme X) (hz : IsClosed ({z} : Set (originalNormalizationScheme X))) :
    IsDiscreteValuationRing ((originalNormalizationScheme X).presheaf.stalk z) := by
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (originalNormalizationMap X z)) isOpen_univ
  let : Nonempty U := ⟨⟨originalNormalizationMap X z,hxU⟩⟩
  let V := originalNormalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (originalNormalizationMap X)
  have hzV : z ∈ V := hxU
  let : Nonempty V := ⟨⟨z,hzV⟩⟩
  let R := Γ(originalNormalizationScheme X, V)
  let : IsDedekindDomain R := originalNormalizationCurve_affine_isDedekindDomain f E hcurve hU
  let P := (hV.primeIdealOf ⟨z,hzV⟩).asIdeal
  have hmax : P.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨z,hzV⟩ hz
  have hnotfield : ¬ IsField R := by
    intro hf
    let := hf.toField
    have hd := originalNormalizationCurve_affine_ringKrullDim_one f E hcurve hU
    have h0 : ringKrullDim R = 0 := ringKrullDim_eq_zero_of_field R
    rw [hd] at h0
    norm_num at h0
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax hnotfield
  let : Algebra R ((originalNormalizationScheme X).presheaf.stalk z) :=
    ((originalNormalizationScheme X).presheaf.germ V z hzV).hom.toAlgebra
  let : IsLocalization.AtPrime ((originalNormalizationScheme X).presheaf.stalk z) P :=
    hV.isLocalization_stalk ⟨z,hzV⟩
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
