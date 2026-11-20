import SGPT.TestCurve.TCActualCentralKernel
import SGPT.Foundations.Envelope.Projective.FactorizationBaseChange

/-! Actual projectivity and central ampleness from the original relative embedding.
Blueprint: tc-ample-projectivity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- Genuine dominance follows from the SAME original off-central trivialization. -/
theorem toLine_isDominant [Nonempty X] : IsDominant T.toLine := by
  let : Surjective f := inferInstance
  let : Surjective (pullback.snd f gmToBase) := inferInstance
  have : Surjective (coordLift T ≫ pullback.snd f gmToBase) := inferInstance
  have : Surjective (toGm T.toLine) := by
    simpa only [coordLift,pullback.lift_snd] using this
  have : IsDominant ((offCentral T.toLine).ι ≫ T.toLine) := by
    rw [← toGm_comp_ι]
    infer_instance
  exact IsDominant.of_comp (offCentral T.toLine).ι T.toLine

/-- The actual relative embedding gives actual finite projectivity over the SAME polynomial base. -/
theorem toLine_projectiveFactorization_of_ample (hA : T.IsAmple) :
    IsProjectiveFactorization T.toLine := by
  obtain ⟨r,hr,N,ι,h,hclosed,_⟩ := hA
  let p := polynomialProjStructureMap ℂ N
  have hp : IsProjectiveFactorization p := by
    refine ⟨N,𝟙 _,inferInstance,?_⟩
    unfold p polynomialProjStructureMap MvPolynomial.homogeneousProjπ
    simp only [Category.id_comp]
    congr 2
  have hbase : IsProjectiveFactorization (pullback.snd p affineLineToBase) := by
    exact SGPT.Foundations.Envelope.ProjectiveFactorizationBaseChange.baseChange
      (S := Polynomial ℂ) p hp
  have hj := hbase.comp_isClosedImmersion (pullback.lift ι T.toLine h) hclosed
  simpa only [pullback.lift_snd] using hj

/-- Original relative positivity manufactures an actual positive-power embedding of the ENTIRE fibre. -/
theorem centralFiber_exists_amplePolarization (hA : T.IsAmple) :
    Nonempty (AmplePolarization (centralFiberStructureMap T) (centralFiberLine T)) := by
  obtain ⟨r,hr,N,ι,h,hclosed,⟨e⟩⟩ := hA
  let p := polynomialProjStructureMap ℂ N
  let P := pullback p affineLineToBase
  let J : T.space ⟶ P := pullback.lift ι T.toLine h
  let : IsClosedImmersion J := hclosed
  let z : polynomialProj ℂ N ⟶ P :=
    pullback.lift (𝟙 _) (p ≫ linePoint 0)
      (by rw [Category.assoc,linePoint_comp_toBase,Category.comp_id,Category.id_comp])
  have hzfst : z ≫ pullback.fst p affineLineToBase = 𝟙 _ := pullback.lift_fst _ _ _
  have hzclosed : IsClosedImmersion z := by
    let : IsClosedImmersion (z ≫ pullback.fst p affineLineToBase) := by
      rw [hzfst]
      infer_instance
    exact IsClosedImmersion.of_comp z (pullback.fst p affineLineToBase)
  let i := centralFiberInclusion T ≫ ι
  have hibase : i ≫ p = centralFiberStructureMap T := by
    change (centralFiberInclusion T ≫ ι) ≫ p = _
    rw [Category.assoc,h]
    exact centralFiber_over_base T
  have hiz : i ≫ z = centralFiberInclusion T ≫ J := by
    apply pullback.hom_ext
    · simp only [Category.assoc,z,J,pullback.lift_fst,Category.comp_id]
      rfl
    · simp only [Category.assoc,z,J,pullback.lift_snd]
      rw [← Category.assoc,hibase]
      exact (centralFiber_condition T).symm
  have hiclosed : IsClosedImmersion i := by
    let : IsClosedImmersion z := hzclosed
    let : IsClosedImmersion (i ≫ z) := by
      rw [hiz]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion i z
  refine ⟨⟨r,hr,N,i,hiclosed,hibase,?_⟩⟩
  exact (originalLinePullbackPowerIso (centralFiberInclusion T) T.atlas r).symm ≪≫
    (Scheme.Modules.pullback (centralFiberInclusion T)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (centralFiberInclusion T) ι).app
      (polynomialProjTwistingLine ℂ N).sheaf

end SGPT.TestCurve.CentralFiber
