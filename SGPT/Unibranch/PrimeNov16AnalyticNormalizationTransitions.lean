import SGPT.Unibranch.PrimeNov16AnalyticIntegralClosure

/-! Genuine fraction-localization functoriality gives canonical integral-closure
transition maps and exact cocycles. No analytic normalization space is assumed.
Blueprint: prime-nov16-analytic-normalization-transitions.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationTransitions

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

def fractionEquiv (e : A ≃+* B) : FractionRing A ≃+* FractionRing B :=
  IsFractionRing.ringEquivOfRingEquiv e

theorem coefficient_square (e : A ≃+* B) :
    (algebraMap B (FractionRing B)).comp e.toRingHom =
      (fractionEquiv e).toRingHom.comp (algebraMap A (FractionRing A)) := by
  ext a
  exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap e a).symm

/-- Actual monic equations are transported through the genuine coefficient square. -/
def closureEquiv (e : A ≃+* B) :
    integralClosure A (FractionRing A) ≃+* integralClosure B (FractionRing B) where
  toFun x := ⟨fractionEquiv e x,
    IsIntegral.map_of_comp_eq e.toRingHom (fractionEquiv e).toRingHom
      (coefficient_square e) x.property⟩
  invFun y := ⟨fractionEquiv e.symm y,
    IsIntegral.map_of_comp_eq e.symm.toRingHom (fractionEquiv e.symm).toRingHom
      (coefficient_square e.symm) y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (fractionEquiv e).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (fractionEquiv e).apply_symm_apply y
  map_add' x y := by
    apply Subtype.ext
    exact map_add (fractionEquiv e) (x : FractionRing A) (y : FractionRing A)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (fractionEquiv e) (x : FractionRing A) (y : FractionRing A)

/-- Literal coefficient readback in the canonical normal algebras. -/
theorem closureEquiv_algebraMap (e : A ≃+* B) (a : A) :
    closureEquiv e (algebraMap A (integralClosure A (FractionRing A)) a) =
      algebraMap B (integralClosure B (FractionRing B)) (e a) := by
  apply Subtype.ext
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e a

/-- Canonical identities follow from the fraction-localization identity law. -/
theorem closureEquiv_refl : closureEquiv (RingEquiv.refl A) = RingEquiv.refl _ := by
  ext x
  change IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl A) (x : FractionRing A) = _
  simp only [IsFractionRing.ringEquivOfRingEquiv_refl,RingEquiv.refl_apply]

/-- Exact cocycle, derived from actual fraction-localization functoriality. -/
theorem closureEquiv_trans (e : A ≃+* B) (f : B ≃+* C) :
    closureEquiv (e.trans f) = (closureEquiv e).trans (closureEquiv f) := by
  ext x
  change IsFractionRing.ringEquivOfRingEquiv (e.trans f) (x : FractionRing A) =
    IsFractionRing.ringEquivOfRingEquiv f
      (IsFractionRing.ringEquivOfRingEquiv e (x : FractionRing A))
  exact congrArg (fun g : FractionRing A ≃+* FractionRing C => g (x : FractionRing A))
    (IsFractionRing.ringEquivOfRingEquiv_comp (FractionRing A) (FractionRing B)
      (FractionRing C) e f)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationTransitions
