import SGPT.Foundations.Schemes.NativeFlagPowerCechComparison
import SGPT.Foundations.Schemes.NativePolynomialTwistingPower
import SGPT.Foundations.Schemes.BundleTensorRightUnit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projection formula and genuine unit/power comparisons retain
the literal native powers in the original ambient twist. -/
def NativeClosedProjectiveStratum.powerPushforwardTwistIso {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    polynomialProjModuleTensorTwist ℂ N
      ((Scheme.Modules.pushforward T.val.hom).obj
        (SheafOfModules.unit T.val.left.ringCatSheaf)) m ≅
      (Scheme.Modules.pushforward T.val.hom).obj (T.powerSheaf m) := by
  let f := T.val.hom
  let P := bundleTensorPower (polynomialProjTwistingLine ℂ N).sheaf m
  let C := nativePositiveProjectiveIteratedPowerPullbackIso ℂ N f
    (nativeProjectivePositiveLine ℂ N f) 1 (nativeProjectivePositiveLinePowerOneIso ℂ N f) m
  let : IsIso (nativeSchemeProjectionMap f P
      (SheafOfModules.unit T.val.left.ringCatSheaf)) :=
    nativePolynomialTwistingTensorPowerProjectionMap_isIso ℂ N f m _
  exact asIso (nativeSchemeProjectionMap f P (SheafOfModules.unit T.val.left.ringCatSheaf)) ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (bundleTensorRightUnitIso ((Scheme.Modules.pullback f).obj P) ≪≫ C.symm)

/-- Original coordinate diagrams and literal pushforward structural scalars
identify the ambient twist complex with the actual native-power complex. -/
def NativeClosedProjectiveStratum.powerTwistedCechIso {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    polynomialProjTwistedCechComplex ℂ N
      ((Scheme.Modules.pushforward T.val.hom).obj
        (SheafOfModules.unit T.val.left.ringCatSheaf)) m ≅ T.powerCechComplex m := by
  let f := T.val.hom
  let c := schemeConstantMap (polynomialProjStructureMap ℂ N)
  let U := polynomialProjCoordinateOpen ℂ N
  let E := actualSchemeModuleBaseSubsetIso (T.powerPushforwardTwistIso m) U c
  let E' := nonemptySubsetCechComplexIso
    (Functor.isoWhiskerLeft (nonemptySubsetInclusion (Fin (N + 1))) E)
  exact E' ≪≫ actualSchemeModulePushforwardCechIso f (T.powerSheaf m) c U

/-- Evaluation and the actual global pushforward comparison preserve the
original complex action on true global native-power sections. -/
def NativeClosedProjectiveStratum.powerTwistedGlobalIso {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    actualSchemeModuleBaseGlobalSections
      (polynomialProjModuleTensorTwist ℂ N
        ((Scheme.Modules.pushforward T.val.hom).obj
          (SheafOfModules.unit T.val.left.ringCatSheaf)) m)
      (schemeConstantMap (polynomialProjStructureMap ℂ N)) ≅
    actualSchemeModuleBaseGlobalSections (T.powerSheaf m)
      (schemeGlobalConstants (T.val.hom ≫ polynomialProjStructureMap ℂ N)) := by
  let f := T.val.hom
  let c := schemeConstantMap (polynomialProjStructureMap ℂ N)
  let E := (ModuleCat.restrictScalars c).mapIso
    ((SheafOfModules.evaluation (R := (polynomialProj ℂ N).ringCatSheaf) (op ⊤)).mapIso
      (T.powerPushforwardTwistIso m))
  exact E ≪≫ actualSchemeModulePushforwardGlobalSectionsIso f (T.powerSheaf m) c

/-- Actual closed geometry produces the finite quasicoherent chart inputs;
true eventual projective vanishing gives the original native Euler/H0 value. -/
theorem NativeClosedProjectiveStratum.powerEuler_eventually_eq_global_finrank {N : ℕ}
    (T : NativeClosedProjectiveStratum N) :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      T.powerEuler m = (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections
        (T.powerSheaf m) (schemeGlobalConstants
          (T.val.hom ≫ polynomialProjStructureMap ℂ N))) : ℤ) := by
  let : IsClosedImmersion T.val.hom := T.property
  let M := (Scheme.Modules.pushforward T.val.hom).obj
    (SheafOfModules.unit T.val.left.ringCatSheaf)
  have : ∀ j, Module.Finite (polynomialProjCoordinateRing ℂ N j)
      Γ(polynomialProjModuleChart M j, ⊤) := fun j ↦
    polynomialProjPushforwardChartSections_finite T.val.hom
      (trivialIntrinsicLineBundle T.val.left).atlas j
  have : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent := fun j ↦
    polynomialProjPushforwardChart_isQuasicoherent T.val.hom
      (trivialIntrinsicLineBundle T.val.left).atlas j
  obtain ⟨b, hb⟩ := polynomialProjTwistedCechEuler_eventually_eq_global_finrank ℂ N M
  refine ⟨b, fun m hm ↦ ?_⟩
  have he := cochain_homologyEulerChar_eq_of_iso (T.powerTwistedCechIso m)
  exact he.symm.trans ((hb m hm).trans
    (congrArg (fun d : ℕ ↦ (d : ℤ)) (T.powerTwistedGlobalIso m).toLinearEquiv.finrank_eq))

end
end SGPT.Foundations.Schemes
