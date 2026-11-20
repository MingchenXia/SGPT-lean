import SGPT.Foundations.Schemes.NativeRegularProjectiveFlag

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The original literal powers at a genuine projective stratum. -/
def NativeClosedProjectiveStratum.powerSheaf {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) : T.val.left.Modules :=
  bundleTensorPower (bundleTensorPower (nativeProjectivePositiveLine ℂ N T.val.hom).sheaf 1) m

/-- Original native-power Cech complex on the actual coordinate cover and
literal composite structural scalar action. -/
def NativeClosedProjectiveStratum.powerCechComplex {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) : CochainComplex (ModuleCat ℂ) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (T.powerSheaf m)
    (actualPolynomialProjectivePullbackCoordinateOpens T.val.hom)
    (schemeGlobalConstants (T.val.hom ≫ polynomialProjStructureMap ℂ N)))

/-- Genuine positive-power, native pullback composition and inverse next
positive-power comparison identify the actual sheaves, retaining unit powers. -/
def NativeClosedProjectiveStratum.cutPowerRestrictionIso {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    (Scheme.Modules.pullback
      (sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1)
        T.cutSection)).obj (T.powerSheaf m) ≅ T.cut.powerSheaf m := by
  let g := sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection
  let C := nativePositiveProjectiveIteratedPowerPullbackIso ℂ N T.val.hom
    (nativeProjectivePositiveLine ℂ N T.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom) m
  let D := nativePositiveProjectiveIteratedPowerPullbackIso ℂ N T.cut.val.hom
    (nativeProjectivePositiveLine ℂ N T.cut.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.cut.val.hom) m
  exact (Scheme.Modules.pullback g).mapIso C ≪≫
    (Scheme.Modules.pullbackComp g T.val.hom).app
      (bundleTensorPower (polynomialProjTwistingLine ℂ N).sheaf m) ≪≫ D.symm

/-- Actual original-base diagram evaluation gives the true divisor-term to
next native-power cochain iso with genuine structural-composition equality. -/
def NativeClosedProjectiveStratum.cutRestrictedPowerCechIso {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    nativePositiveSectionZeroRestrictedCechComplex ℂ N T.val.hom
      (nativeProjectivePositiveLine ℂ N T.val.hom) 1 T.cutSection
      (T.val.hom ≫ polynomialProjStructureMap ℂ N) m ≅ T.cut.powerCechComplex m := by
  let g := sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection
  let p := T.val.hom ≫ polynomialProjStructureMap ℂ N
  let U := actualPolynomialProjectivePullbackCoordinateOpens T.val.hom
  let E := actualSchemeModuleBaseSubsetIso (T.cutPowerRestrictionIso m)
    (fun j ↦ g ⁻¹ᵁ U j) (schemeGlobalConstants (g ≫ p))
  let E' := nonemptySubsetCechComplexIso
    (Functor.isoWhiskerLeft (nonemptySubsetInclusion (Fin (N + 1))) E)
  let C (r : T.cut.val.left ⟶ Spec (.of ℂ)) :=
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (T.cut.powerSheaf m)
      (actualPolynomialProjectivePullbackCoordinateOpens T.cut.val.hom) (schemeGlobalConstants r))
  have hp : g ≫ p = T.cut.val.hom ≫ polynomialProjStructureMap ℂ N :=
    (Category.assoc g T.val.hom (polynomialProjStructureMap ℂ N)).symm
  exact E' ≪≫ eqToIso (congrArg C hp)

/-- The SAME genuine chosen-cut Euler identity becomes the actual successive
native-power recurrence after actual sheaf/complex comparison. -/
theorem NativeClosedProjectiveStratum.powerCechEuler_cut {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    (T.powerCechComplex (m + 1)).homologyEulerChar =
      (T.powerCechComplex m).homologyEulerChar +
        (T.cut.powerCechComplex (m + 1)).homologyEulerChar := by
  let : IsClosedImmersion T.val.hom := T.property
  have h := T.cut_euler m
  have hR := cochain_homologyEulerChar_eq_of_iso (T.cutRestrictedPowerCechIso (m + 1))
  exact h.trans (congrArg (fun z : ℤ ↦ (T.powerCechComplex m).homologyEulerChar + z) hR)

/-- The actual integer-valued native-cover Euler sequence. -/
def NativeClosedProjectiveStratum.powerEuler {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) : ℤ :=
  (T.powerCechComplex m).homologyEulerChar

/-- The actual successor difference equals the actual next-stage sequence,
with the genuine original shift. -/
theorem NativeClosedProjectiveStratum.powerEuler_cut_difference {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    T.powerEuler (m + 1) - T.powerEuler m = T.cut.powerEuler (m + 1) := by
  have h := T.powerCechEuler_cut m
  change T.powerEuler (m + 1) = T.powerEuler m + T.cut.powerEuler (m + 1) at h
  rw [h, add_sub_cancel_left]



end
end SGPT.Foundations.Schemes
