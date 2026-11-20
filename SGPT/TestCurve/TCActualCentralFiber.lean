import SGPT.TestCurve.TCLinPoints
import SGPT.Foundations.Schemes.NativeLinePullbackFrames
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Actual scheme-theoretic central fibre and original restricted line bundle.
Blueprint: tc-actual-central-fiber.tex. Global section base change is separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

theorem linePoint_isClosedImmersion (c : ℂ) : IsClosedImmersion (linePoint c) := by
  apply IsClosedImmersion.spec_of_surjective
  intro z
  exact ⟨Polynomial.C z,by simp⟩

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

def centralFiberScheme : Scheme.{0} := pullback T.toLine (linePoint 0)

def centralFiberInclusion : centralFiberScheme T ⟶ T.space :=
  pullback.fst T.toLine (linePoint 0)

def centralFiberStructureMap : centralFiberScheme T ⟶ Spec (.of ℂ) :=
  pullback.snd T.toLine (linePoint 0)

theorem centralFiber_condition :
    centralFiberInclusion T ≫ T.toLine = centralFiberStructureMap T ≫ linePoint 0 :=
  pullback.condition

instance centralFiberInclusion_closedImmersion :
    IsClosedImmersion (centralFiberInclusion T) := by
  let : IsClosedImmersion (linePoint 0) := linePoint_isClosedImmersion 0
  change IsClosedImmersion (pullback.fst T.toLine (linePoint 0))
  infer_instance

instance centralFiberStructureMap_proper : IsProper (centralFiberStructureMap T) := by
  change IsProper (pullback.snd T.toLine (linePoint 0))
  infer_instance

theorem centralFiber_over_base :
    centralFiberInclusion T ≫ T.structureMap = centralFiberStructureMap T := by
  change (centralFiberInclusion T ≫ T.toLine) ≫ affineLineToBase = _
  rw [centralFiber_condition,Category.assoc,linePoint_comp_toBase,Category.comp_id]

theorem centralFiber_coordinate_zero :
    (centralFiberInclusion T).appTop (tFun T.toLine) = 0 := by
  have h := congrArg (fun g => g.appTop coordT) (centralFiber_condition T)
  change (centralFiberInclusion T).appTop (T.toLine.appTop coordT) =
    (centralFiberStructureMap T).appTop ((linePoint 0).appTop coordT) at h
  simpa only [tFun,linePoint_appTop_coordT,map_zero] using h

def centralFiberLine : (centralFiberScheme T).Modules :=
  (Scheme.Modules.pullback (centralFiberInclusion T)).obj T.line

def centralFiberAtlas : LineBundleAtlas (centralFiberLine T) :=
  T.atlas.nativePullback (centralFiberInclusion T)

/-- Actual original central-fibre H0, with no quotient or reduced-fibre replacement. -/
abbrev centralFiberSectionSpace (m : ℕ) : Type :=
  SectionSpace (centralFiberStructureMap T) (centralFiberLine T) m

end SGPT.TestCurve.CentralFiber
