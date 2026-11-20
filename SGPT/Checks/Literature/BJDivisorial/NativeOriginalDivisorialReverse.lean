import SGPT.Checks.Literature.BJDivisorial.NativeFamilyBaseTransport
import SGPT.Checks.Literature.BJDivisorial.NativeRationalRestriction
import SGPT.Checks.Literature.BJDivisorial.OriginalGeometricDVRPoint
import SGPT.Checks.Literature.BJDivisorial.OriginalTrivialGenericValuation

/-! # Every actual native divisorial point is an original augmented divisorial point
The native Gauss DVR is restricted through the genuine M3 field embedding.
A trivial restriction gives the original trivial point. A nontrivial
restriction derives its geometric DVR, rational weight, normal proper
model and actual codimension-one order. The point equality uses EVERY
original field fraction, with no correspondence certificate as input.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Alterations
open scoped Classical NNReal

namespace SGPT.NAPotential.BJ.Divisorial
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.Berkovich SGPT.NAPotential.Berkovich
open Native

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance nativeOriginalProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable {r : ℕ} {d : Fin (r+1) → ℕ}
  (q : ∀ c, X ⟶ projectiveSpace ℂ (d c))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure ℂ (d c) = p)
  [IsClosedImmersion (q 0)]

private abbrev P := letI := p.stalkAlgebra (genericPoint X)
  FiniteProjectiveNativeFieldModels.model q p hp
private abbrev e := OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp

/-- The SAME actual native divisorial point, under the SAME canonical
all-point homeomorphism, lies in the original source's RATIONAL augmented
X^Div. Every geometric/rational/model correspondence is produced internally. -/
theorem nativeDivisorial_original_mem_source
    (v : letI := p.stalkAlgebra (genericPoint X); (P p q hp).an)
    (hv : letI := p.stalkAlgebra (genericPoint X); (P p q hp).IsDivisorial v) :
    (pointEquiv p).symm ((e p q hp).symm v) ∈ sourceDivisorialSet p := by
  let := p.stalkAlgebra (genericPoint X)
  let : Algebra.EssFiniteType ℂ X.functionField :=
    SchemeStalkCenteredDVR.essFiniteType_stalkAlgebra p (genericPoint X)
  let y := (e p q hp).symm v
  have hyg : y.1.point = genericPoint X := canonical_original_generic_support q p hp y
    (by simpa only [y, Homeomorph.apply_symm_apply] using hv.hasGenericSupport)
  have hyval : SchemeValuedPoint.genericValuation y.1 hyg =
      (P p q hp).fieldVal v hv.hasGenericSupport := by
    simpa only [y, Homeomorph.apply_symm_apply] using
      canonical_original_genericValuation_eq q p hp y
        (by simpa only [y, Homeomorph.apply_symm_apply] using hv.hasGenericSupport)
  obtain ⟨R',c,hc,hval⟩ := nativeDivisorial_fieldVal_eq (P p q hp) hv
  by_cases hn : (nativeIntegerFieldRestriction (P p q hp) R').IsNontrivial
  · let V := nativeRestrictedRing (P p q hp) R'
    have hV := nativeRestrictedRing_geometricDVR (P p q hp) R' hn
    let := hV.1
    let := hV.2
    let := nativeRestrictedRing_isFractionRing (P p q hp) R'
    obtain ⟨t,ht,hscale⟩ := nativeRestricted_positive_rationalScale (P p q hp) R' hn c hc
    let E := primeDivisorOfGeometricDVR p V
    have hsource := geometricDVR_originalPoint_genericValuation p V t ht
    have hpoint : y = pointEquiv p (E.ordVal p t (by exact_mod_cast ht)) := by
      apply Subtype.ext
      apply SchemeValuedPoint.eq_of_genericValuation_eq _ _ hyg
        (E.ordVal_support_eq_genericPoint (f := p) t (by exact_mod_cast ht))
      exact hyval.trans (hval.symm.trans (hscale.trans hsource.symm))
    change (pointEquiv p).symm y ∈ sourceDivisorialSet p
    rw [hpoint, Equiv.symm_apply_apply]
    exact Set.mem_insert_of_mem _ ⟨E,t,(by exact_mod_cast ht),rfl⟩
  · have hraw : nativeIntegerFieldRestriction (P p q hp) R' = 1 :=
      valuation_eq_one_of_not_nontrivial _ hn
    have hscaled : scaledModelFieldRestriction (P p q hp) R'
        ⟨(c : ℝ), (by exact_mod_cast hc.le)⟩ = 1 := by
      rw [scaledModelRestriction_eq_scale_integer, hraw]
      apply Valuation.ext
      intro a
      by_cases ha : a = 0
      · subst a
        simp
      · simp only [DiscreteValuationRealScale.valuation_apply,
          Valuation.one_apply_of_ne_zero ha, map_one]
    have hpoint : y = pointEquiv p (BerkovichPoint.trivial p) := by
      apply Subtype.ext
      apply SchemeValuedPoint.eq_of_genericValuation_eq _ _ hyg rfl
      exact hyval.trans (hval.symm.trans (hscaled.trans (original_trivial_genericValuation p).symm))
    change (pointEquiv p).symm y ∈ sourceDivisorialSet p
    rw [hpoint, Equiv.symm_apply_apply]
    exact trivial_mem_sourceDivisorialSet p

end SGPT.NAPotential.BJ.Divisorial
