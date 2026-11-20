import SGPT.Projective.OriginalFiniteProjectiveLineCech
import SGPT.Foundations.Schemes.NativeFlagPowerEulerGlobal
import SGPT.Foundations.Schemes.DiscreteLineTrivialization

/-! TRUE finite-map ORIGINAL Artinian Euler/global comparison on SAME
original projective inverse cover; no normalized embedding output premise.
Blueprint: original-finite-artinian-cech.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Opposite
attribute [local instance] MvPolynomial.gradedAlgebra

variable {Y : Scheme.{0}} {N : ℕ} (i : Y ⟶ polynomialProj ℂ N)

/-- Actual FINITE original geometry gives TRUE finite global sections
of ANY original line, with the literal original structural scalar action. -/
theorem originalFiniteProjectiveLineGlobalSections_finite [IsFinite i]
    {L : Y.Modules} (a : LineBundleAtlas L) :
    Module.Finite ℂ (actualSchemeModuleBaseGlobalSections L
      (schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N))) := by
  let M := (Scheme.Modules.pushforward i).obj L
  let : ∀ j, Module.Finite (polynomialProjCoordinateRing ℂ N j)
      Γ(polynomialProjModuleChart M j,⊤) :=
    fun j => originalFinitePolynomialProjPushforwardChartSections_finite i a j
  let : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent :=
    fun j => originalFinitePolynomialProjPushforwardChart_isQuasicoherent i a j
  have := polynomialProjFiniteChartGlobalSections_finite ℂ N M
  exact Module.Finite.equiv (actualSchemeModulePushforwardGlobalSectionsIso i L
    (schemeConstantMap (polynomialProjStructureMap ℂ N))).toLinearEquiv

/-- SAME actual original pulled hyperplane powers, including true unit powers. -/
def originalFiniteProjectivePowerSheaf (m : ℕ) : Y.Modules :=
  bundleTensorPower (bundleTensorPower (nativeProjectivePositiveLine ℂ N i).sheaf 1) m

/-- SAME actual original inverse-coordinate-cover power complex/scalars. -/
def originalFiniteProjectivePowerCechComplex (m : ℕ) : CochainComplex (ModuleCat ℂ) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (originalFiniteProjectivePowerSheaf i m)
    (actualPolynomialProjectivePullbackCoordinateOpens i)
    (schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N)))

/-- Genuine actual projection/unit/power maps identify actual original
pushforward powers with SAME actual ambient twists, no closedness premise. -/
def originalFiniteProjectivePowerPushforwardTwistIso (m : ℕ) :
    polynomialProjModuleTensorTwist ℂ N
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)) m ≅
    (Scheme.Modules.pushforward i).obj (originalFiniteProjectivePowerSheaf i m) := by
  let P := bundleTensorPower (polynomialProjTwistingLine ℂ N).sheaf m
  let C := nativePositiveProjectiveIteratedPowerPullbackIso ℂ N i
    (nativeProjectivePositiveLine ℂ N i) 1 (nativeProjectivePositiveLinePowerOneIso ℂ N i) m
  let : IsIso (nativeSchemeProjectionMap i P (SheafOfModules.unit Y.ringCatSheaf)) :=
    nativePolynomialTwistingTensorPowerProjectionMap_isIso ℂ N i m _
  exact asIso (nativeSchemeProjectionMap i P (SheafOfModules.unit Y.ringCatSheaf)) ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (bundleTensorRightUnitIso ((Scheme.Modules.pullback i).obj P) ≪≫ C.symm)

/-- Actual original SAME power complex reader, preserving actual original
inverse-coordinate opens and literal original composite constants. -/
def originalFiniteProjectivePowerTwistedCechIso (m : ℕ) :
    polynomialProjTwistedCechComplex ℂ N
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)) m ≅
    originalFiniteProjectivePowerCechComplex i m := by
  let c := schemeConstantMap (polynomialProjStructureMap ℂ N)
  let U := polynomialProjCoordinateOpen ℂ N
  let E := actualSchemeModuleBaseSubsetIso (originalFiniteProjectivePowerPushforwardTwistIso i m) U c
  exact nonemptySubsetCechComplexIso
    (Functor.isoWhiskerLeft (nonemptySubsetInclusion (Fin (N+1))) E) ≪≫
      actualSchemeModulePushforwardCechIso i (originalFiniteProjectivePowerSheaf i m) c U

/-- Actual original SAME power global reader with the true original
structural complex scalar action, no generic global equality premise. -/
def originalFiniteProjectivePowerTwistedGlobalIso (m : ℕ) :
    actualSchemeModuleBaseGlobalSections
      (polynomialProjModuleTensorTwist ℂ N
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)) m)
      (schemeConstantMap (polynomialProjStructureMap ℂ N)) ≅
    actualSchemeModuleBaseGlobalSections (originalFiniteProjectivePowerSheaf i m)
      (schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N)) := by
  let c := schemeConstantMap (polynomialProjStructureMap ℂ N)
  let E := (ModuleCat.restrictScalars c).mapIso
    ((SheafOfModules.evaluation (R := (polynomialProj ℂ N).ringCatSheaf) (op ⊤)).mapIso
      (originalFiniteProjectivePowerPushforwardTwistIso i m))
  exact E ≪≫ actualSchemeModulePushforwardGlobalSectionsIso i (originalFiniteProjectivePowerSheaf i m) c

/-- Actual FINITE original geometry PRODUCES true finite chart modules
and actual vanishing, hence eventual SAME original power Euler/H0 equality. -/
theorem originalFiniteProjectivePowerEuler_eventually_eq_global_finrank [IsFinite i] :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      (originalFiniteProjectivePowerCechComplex i m).homologyEulerChar =
        (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections (originalFiniteProjectivePowerSheaf i m)
          (schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N))) : ℤ) := by
  let M := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)
  let : ∀ j, Module.Finite (polynomialProjCoordinateRing ℂ N j)
      Γ(polynomialProjModuleChart M j,⊤) := fun j =>
    originalFinitePolynomialProjPushforwardChartSections_finite i (trivialIntrinsicLineBundle Y).atlas j
  let : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent := fun j =>
    originalFinitePolynomialProjPushforwardChart_isQuasicoherent i (trivialIntrinsicLineBundle Y).atlas j
  obtain ⟨b,hb⟩ := polynomialProjTwistedCechEuler_eventually_eq_global_finrank ℂ N M
  refine ⟨b,fun m hm => ?_⟩
  have he := cochain_homologyEulerChar_eq_of_iso (originalFiniteProjectivePowerTwistedCechIso i m)
  exact he.symm.trans ((hb m hm).trans
    (congrArg (fun d : ℕ => (d:ℤ)) (originalFiniteProjectivePowerTwistedGlobalIso i m).toLinearEquiv.finrank_eq))

/-- ENTIRE actual Artinian source/SAME original inverse-cover line Euler
is the genuine ORIGINAL global section dimension, without E_source or a
trivialization/acyclicity/finite dimension comparison premise. -/
theorem originalFiniteArtinianLineCechEuler_eq_global_finrank [IsFinite i] [IsArtinianScheme Y]
    {L : Y.Modules} (a : LineBundleAtlas L) :
    (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L
      (actualPolynomialProjectivePullbackCoordinateOpens i)
      (schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N)))).homologyEulerChar =
      (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections L
        (schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N))) : ℤ) := by
  obtain ⟨m,hm⟩ := originalFiniteProjectivePowerEuler_eventually_eq_global_finrank i
  let d := ((nativeProjectivePositiveLine ℂ N i).atlas.tensorPower 1).tensorPower m
  let e : L ≅ originalFiniteProjectivePowerSheaf i m := a.discreteTrivialization ≪≫ d.discreteTrivialization.symm
  let U := actualPolynomialProjectivePullbackCoordinateOpens i
  let c := schemeGlobalConstants (i ≫ polynomialProjStructureMap ℂ N)
  have hchi := cochain_homologyEulerChar_eq_of_iso
    (nonemptySubsetCechComplexIso (Functor.isoWhiskerLeft (nonemptySubsetInclusion (Fin (N+1)))
      (actualSchemeModuleBaseSubsetIso e U c)))
  let eg := (ModuleCat.restrictScalars c).mapIso
    ((SheafOfModules.evaluation (R := Y.ringCatSheaf) (op ⊤)).mapIso e)
  have hdim := eg.toLinearEquiv.finrank_eq
  exact hchi.trans ((hm m le_rfl).trans (congrArg (fun d : ℕ => (d:ℤ)) hdim.symm))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
