import SGPT.TestCurve.TCActualCentralZero
import SGPT.TestCurve.GeomLinPoint

/-! The actual original geometric group-scheme action descends to the ENTIRE
scheme-theoretic central fibre. No quotient H0 action is used as a definition. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin
open scoped MonoidalCategory

@[instance_reducible] private def actionAlongEquivariantMono {C : Type*} [Category C] [MonoidalCategory C]
    {G U V : C} [MonObj G] (A : ModObj G V) (i : U ⟶ V) [Mono i]
    (s : G ⊗ U ⟶ U) (h : s ≫ i = (G ◁ i) ≫ A.smul) : ModObj G U := by
  letI := A
  have hunit : (η[G] ▷ V) ≫ A.smul = (λ_ V).hom := ModObj.one_smul (M := G) V
  have hprod : (μ[G] ▷ V) ≫ A.smul =
      (α_ G G V).hom ≫ G ◁ A.smul ≫ A.smul := ModObj.mul_smul (M := G) V
  refine { smul := s, one_smul := ?_, mul_smul := ?_ }
  · apply (cancel_mono i).mp
    change ((η[G] ▷ U) ≫ s) ≫ i = (λ_ U).hom ≫ i
    calc
      _ = ((𝟙_ C) ◁ i) ≫ (η[G] ▷ V) ≫ A.smul := by
        rw [Category.assoc,h,← whisker_exchange_assoc]
      _ = ((𝟙_ C) ◁ i) ≫ (λ_ V).hom := by rw [hunit]
      _ = _ := leftUnitor_naturality i
  · apply (cancel_mono i).mp
    change ((μ[G] ▷ U) ≫ s) ≫ i =
      ((α_ G G U).hom ≫ G ◁ s ≫ s) ≫ i
    calc
      _ = ((G ⊗ G) ◁ i) ≫ (μ[G] ▷ V) ≫ A.smul := by
        rw [Category.assoc,h,← whisker_exchange_assoc]
      _ = ((G ⊗ G) ◁ i) ≫ (α_ G G V).hom ≫ G ◁ A.smul ≫ A.smul := by
        rw [hprod]
      _ = (α_ G G U).hom ≫ G ◁ (G ◁ i) ≫ G ◁ A.smul ≫ A.smul := by
        rw [associator_naturality_right_assoc]
      _ = (α_ G G U).hom ≫ G ◁ ((G ◁ i) ≫ A.smul) ≫ A.smul := by
        simp only [whiskerLeft_comp,Category.assoc]
      _ = (α_ G G U).hom ≫ G ◁ (s ≫ i) ≫ A.smul := by rw [h]
      _ = _ := by
        simp only [whiskerLeft_comp,Category.assoc]
        rw [← h]

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- The original entire central fibre, as a scheme over the original complex base. -/
abbrev centralFiberOverBase : Over (Spec (.of ℂ)) := Over.mk (centralFiberStructureMap T)

/-- The literal original central closed immersion as a morphism over the original base. -/
def centralFiberInclusionOver : centralFiberOverBase T ⟶ T.overBase :=
  Over.homMk (centralFiberInclusion T) (centralFiber_over_base T)

instance centralFiberInclusionOver_mono : Mono (centralFiberInclusionOver T) := by
  unfold centralFiberInclusionOver
  infer_instance

/-- The original product inclusion `1 × j`, retaining the entire central scheme. -/
def centralGmProductInclusion :
    (GmGroup ⊗ centralFiberOverBase T).left ⟶ gmProd T :=
  (GmGroup ◁ centralFiberInclusionOver T).left

theorem centralGmProductInclusion_proj :
    centralGmProductInclusion T ≫ gmProj T =
      (snd GmGroup (centralFiberOverBase T)).left ≫ centralFiberInclusion T :=
  Over.whiskerLeft_left_snd _

variable (A : GmAction T)

/-- The actual original action after the actual original product inclusion. -/
def centralGmActToTotalOver : GmGroup ⊗ centralFiberOverBase T ⟶ T.overBase :=
  (GmGroup ◁ centralFiberInclusionOver T) ≫ A.act.smul

/-- The original global coordinate vanishes after the SAME geometric group-scheme action. -/
theorem centralGmActToTotal_coordinate_zero :
    (centralGmActToTotalOver T A).left.appTop (tFun T.toLine) = 0 := by
  have ht : A.smulMap.appTop (tFun T.toLine) =
      (fst GmGroup T.overBase).left.appTop coordGm * (gmProj T).appTop (tFun T.toLine) :=
    A.smul_tFun
  change (centralGmProductInclusion T ≫ A.smulMap).appTop (tFun T.toLine) = 0
  rw [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,ht,map_mul]
  have hzero : (centralGmProductInclusion T).appTop ((gmProj T).appTop (tFun T.toLine)) = 0 := by
    rw [← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop,centralGmProductInclusion_proj,
      Scheme.Hom.comp_appTop,CommRingCat.comp_apply]
    have hz := congrArg
      (fun r : Γ(centralFiberScheme T, ⊤) => (snd GmGroup (centralFiberOverBase T)).left.appTop r)
      (centralFiber_coordinate_zero T)
    convert hz using 1 <;> simp only [map_zero]
    rfl
  rw [hzero,mul_zero]

/-- Actual scheme-theoretic factorization of the original action through the whole central fibre. -/
def centralGmSmul : (GmGroup ⊗ centralFiberOverBase T).left ⟶ centralFiberScheme T :=
  pullback.lift (centralGmActToTotalOver T A).left
    ((centralGmActToTotalOver T A).left ≫ T.structureMap)
    (by
      simpa only [Category.assoc,TestConfiguration.structureMap] using
        toLine_eq_zeroPoint_of_coordinate_zero
          ((centralGmActToTotalOver T A).left ≫ T.toLine)
          (centralGmActToTotal_coordinate_zero T A))

/-- Literal equivariance square for the actual central closed immersion. -/
theorem centralGmSmul_inclusion :
    centralGmSmul T A ≫ centralFiberInclusion T =
      centralGmProductInclusion T ≫ A.smulMap :=
  pullback.lift_fst _ _ _

/-- The central action preserves the SAME original complex base. -/
theorem centralGmSmul_over_base :
    centralGmSmul T A ≫ centralFiberStructureMap T =
      (GmGroup ⊗ centralFiberOverBase T).hom := by
  rw [show centralGmSmul T A ≫ centralFiberStructureMap T =
      (centralGmActToTotalOver T A).left ≫ T.structureMap from pullback.lift_snd _ _ _]
  exact Over.w (centralGmActToTotalOver T A)

def centralGmSmulOver : GmGroup ⊗ centralFiberOverBase T ⟶ centralFiberOverBase T :=
  Over.homMk (centralGmSmul T A) (centralGmSmul_over_base T A)

theorem centralGmSmulOver_inclusion :
    centralGmSmulOver T A ≫ centralFiberInclusionOver T =
      (GmGroup ◁ centralFiberInclusionOver T) ≫ A.act.smul := by
  apply Over.OverMorphism.ext
  exact centralGmSmul_inclusion T A

/-- The genuine original central group-scheme action, including unit and product laws.
The action is constructed geometrically on the entire original nonreduced fibre. -/
@[instance_reducible] def centralFiberGmAction : ModObj GmGroup (centralFiberOverBase T) :=
  actionAlongEquivariantMono A.act (centralFiberInclusionOver T)
    (centralGmSmulOver T A) (centralGmSmulOver_inclusion T A)

/-- Exact central geometric action readback in the original total space. -/
theorem centralFiberGmAction_inclusion :
    (centralFiberGmAction T A).smul.left ≫ centralFiberInclusion T =
      centralGmProductInclusion T ≫ A.smulMap := by
  change centralGmSmul T A ≫ centralFiberInclusion T = _
  exact centralGmSmul_inclusion T A

end SGPT.TestCurve.CentralFiber
