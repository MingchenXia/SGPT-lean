import SGPT.TestCurve.TCActualCentralFiber
import SGPT.TestCurve.TCOkoCentral
import SGPT.Projective.OriginalLinePullbackTensor

/-! Literal original section restriction to the actual central fibre and modulo-t descent.
Blueprint: tc-actual-central-restriction.tex. Eventual base change remains separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCOko
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- Actual complex constants commute with the SAME original central inclusion. -/
theorem centralFiber_constants (c : ℂ) :
    (centralFiberInclusion T).appTop (schemeGlobalConstants T.structureMap c) =
      schemeGlobalConstants (centralFiberStructureMap T) c := by
  have h := congrArg (fun g => schemeGlobalConstants g c) (centralFiber_over_base T)
  exact h

/-- The genuine original restriction, retaining the actual pullback/power comparison. -/
def centralFiberRestriction (m : ℕ) :
    SectionSpace T.structureMap T.line m →ₗ[ℂ] centralFiberSectionSpace T m := by
  let j := centralFiberInclusion T
  let N := bundleTensorPower T.line m
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (.op ⊤)
  let μ := (originalLinePullbackPowerIso j T.atlas m).hom.val.app (.op ⊤)
  refine { toFun := fun s => μ (η s), map_add' := ?_, map_smul' := ?_ }
  · intro s s'
    simp only [map_add]
  · intro c s
    let σ : Γ(N, ⊤) := s
    have he := η.hom.map_smul (schemeGlobalConstants T.structureMap c) σ
    change η (schemeGlobalConstants T.structureMap c • σ) =
      j.appTop (schemeGlobalConstants T.structureMap c) •
        (show Γ((Scheme.Modules.pullback j).obj N, ⊤) from η σ) at he
    change μ (η (schemeGlobalConstants T.structureMap c • σ)) =
      schemeGlobalConstants (centralFiberStructureMap T) c • μ (η s)
    rw [he]
    rw [μ.hom.map_smul]
    exact congrArg (fun r => r • μ (η s)) (centralFiber_constants T c)

/-- The actual map on an original section is the literal unit and genuine power isomorphism. -/
theorem centralFiberRestriction_apply (m : ℕ) (s : SectionSpace T.structureMap T.line m) :
    centralFiberRestriction T m s =
      (originalLinePullbackPowerIso (centralFiberInclusion T) T.atlas m).hom.val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (centralFiberInclusion T)).unit.app
          (bundleTensorPower T.line m)).val.app (.op ⊤) s) := rfl

/-- Literal scheme-theoretic restriction kills the SAME original multiplication by t. -/
theorem centralFiberRestriction_tMul (m : ℕ) (s : SectionSpace T.structureMap T.line m) :
    centralFiberRestriction T m (tMul T m s) = 0 := by
  let j := centralFiberInclusion T
  let N := bundleTensorPower T.line m
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (.op ⊤)
  let μ := (originalLinePullbackPowerIso j T.atlas m).hom.val.app (.op ⊤)
  let σ : Γ(N, ⊤) := s
  have he := η.hom.map_smul (tFun T.toLine) σ
  change η ((tFun T.toLine) • σ) = j.appTop (tFun T.toLine) •
    (show Γ((Scheme.Modules.pullback j).obj N, ⊤) from η σ) at he
  rw [show j.appTop (tFun T.toLine) = 0 from centralFiber_coordinate_zero T,zero_smul] at he
  change μ (η ((tFun T.toLine) • σ)) = 0
  rw [he,map_zero]

/-- Actual range containment supplies the quotient universal property. -/
theorem range_tMul_le_ker_centralFiberRestriction (m : ℕ) :
    LinearMap.range (tMul T m) ≤ LinearMap.ker (centralFiberRestriction T m) := by
  rintro _ ⟨s,rfl⟩
  exact LinearMap.mem_ker.mpr (centralFiberRestriction_tMul T m s)

/-- The original modulo-t quotient maps to the ACTUAL central-fibre H0. -/
def centralFiberQuotientRestriction (m : ℕ) :
    CentralQuotient T m →ₗ[ℂ] centralFiberSectionSpace T m :=
  (LinearMap.range (tMul T m)).liftQ (centralFiberRestriction T m)
    (range_tMul_le_ker_centralFiberRestriction T m)

theorem centralFiberQuotientRestriction_mk (m : ℕ) (s : SectionSpace T.structureMap T.line m) :
    centralFiberQuotientRestriction T m ((LinearMap.range (tMul T m)).mkQ s) =
      centralFiberRestriction T m s := rfl

end SGPT.TestCurve.CentralFiber
