import SGPT.TestCurve.TCActualCentralAction

/-! Genuine point evaluations of the actual central group-scheme action,
with literal original total/central squares before any H0 action. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- The literal original complex point and the identity on the ENTIRE central fibre. -/
def centralPointIncl (c : ℂˣ) :
    centralFiberScheme T ⟶ (GmGroup ⊗ centralFiberOverBase T).left :=
  pullback.lift (f := GmGroup.hom) (g := centralFiberStructureMap T)
    (centralFiberStructureMap T ≫ gmPoint c) (𝟙 _) (by
      rw [Category.assoc,gmPoint_comp,Category.comp_id,Category.id_comp])

theorem centralPointIncl_proj (c : ℂˣ) :
    centralPointIncl T c ≫ (snd GmGroup (centralFiberOverBase T)).left = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem centralPointIncl_fst (c : ℂˣ) :
    centralPointIncl T c ≫ (fst GmGroup (centralFiberOverBase T)).left =
      centralFiberStructureMap T ≫ gmPoint c :=
  pullback.lift_fst _ _ _

/-- The actual constant group point commutes with the literal central product inclusion. -/
theorem centralPointIncl_productInclusion (c : ℂˣ) :
    centralPointIncl T c ≫ centralGmProductInclusion T =
      centralFiberInclusion T ≫ pointIncl T c := by
  apply pullback.hom_ext
  · change (centralPointIncl T c ≫ centralGmProductInclusion T) ≫
        (fst GmGroup T.overBase).left =
      (centralFiberInclusion T ≫ pointIncl T c) ≫ (fst GmGroup T.overBase).left
    rw [Category.assoc,show centralGmProductInclusion T ≫ (fst GmGroup T.overBase).left =
      (fst GmGroup (centralFiberOverBase T)).left from Over.whiskerLeft_left_fst _,
      centralPointIncl_fst,Category.assoc,pointIncl_fst,← Category.assoc,centralFiber_over_base]
  · change (centralPointIncl T c ≫ centralGmProductInclusion T) ≫ gmProj T =
      (centralFiberInclusion T ≫ pointIncl T c) ≫ gmProj T
    rw [Category.assoc,centralGmProductInclusion_proj,← Category.assoc,
      centralPointIncl_proj,Category.id_comp,Category.assoc,pointIncl_proj,Category.comp_id]

variable (A : GmAction T)

/-- Genuine original geometric action of the complex point on the actual entire central fibre. -/
def centralActAt (c : ℂˣ) : centralFiberScheme T ⟶ centralFiberScheme T :=
  centralPointIncl T c ≫ centralGmSmul T A

/-- The true central point action has the literal original inclusion-equivariant square. -/
theorem centralActAt_inclusion (c : ℂˣ) :
    centralActAt T A c ≫ centralFiberInclusion T = centralFiberInclusion T ≫ A.actAt c := by
  change (centralPointIncl T c ≫ centralGmSmul T A) ≫ centralFiberInclusion T = _
  rw [Category.assoc,centralGmSmul_inclusion,← Category.assoc,
    centralPointIncl_productInclusion,Category.assoc]
  rfl

private theorem originalActAt_over_base (c : ℂˣ) : A.actAt c ≫ T.structureMap = T.structureMap := by
  change (pointIncl T c ≫ A.smulMap) ≫ T.structureMap = _
  calc
    _ = pointIncl T c ≫ (GmGroup ⊗ T.overBase).hom := by
      rw [Category.assoc]
      exact congrArg (fun k => pointIncl T c ≫ k) (Over.w A.act.smul)
    _ = pointIncl T c ≫ gmProj T ≫ T.structureMap := by
      have hp : gmProj T ≫ T.structureMap = (GmGroup ⊗ T.overBase).hom :=
        Over.w (snd GmGroup T.overBase)
      exact congrArg (fun k => pointIncl T c ≫ k) hp.symm
    _ = _ := by rw [← Category.assoc,pointIncl_proj,Category.id_comp]

/-- The actual original central point action preserves the SAME original complex base. -/
theorem centralActAt_over_base (c : ℂˣ) :
    centralActAt T A c ≫ centralFiberStructureMap T = centralFiberStructureMap T := by
  calc
    _ = centralActAt T A c ≫ centralFiberInclusion T ≫ T.structureMap := by
      rw [centralFiber_over_base]
    _ = centralFiberInclusion T ≫ A.actAt c ≫ T.structureMap := by
      rw [← Category.assoc,centralActAt_inclusion,Category.assoc]
    _ = _ := by rw [originalActAt_over_base,centralFiber_over_base]

end SGPT.TestCurve.CentralFiber
