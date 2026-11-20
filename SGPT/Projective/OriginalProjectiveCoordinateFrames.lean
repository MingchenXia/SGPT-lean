import SGPT.Projective.OriginalGeneratedPointUnit
import SGPT.Foundations.Schemes.PolynomialProjectiveTwistingTransition
import SGPT.Foundations.Envelope.AlgGeom.SchemeSectionPreservingGluing

/-! Actual original projective coordinate sections are genuine local line frames. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open SGPT.Foundations.Envelope.SchemeLineSectionEvaluation
open SGPT.Foundations.Envelope.SchemeSectionPreservingGluing
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {L : X.Modules}

/-- Coefficient one gives the actual inverse whole over-site frame, on all opens. -/
theorem originalOrdinarySectionHom_over_eq_frame_inv {U : X.Opens}
    (e : LocalBundleFrame L U) (s : Γ(L, ⊤))
    (hs : ∀ (V : X.Opens) (l : V ⟶ U),
      e.coefficients l (L.val.map V.leTop.op s) = 1) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map
      (originalOrdinarySectionHom L s) = e.inv := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply (e.coefficients V.unop.hom).injective
  change e.coefficients V.unop.hom (r • L.val.map V.unop.left.leTop.op s) =
    e.coefficients V.unop.hom ((e.coefficients V.unop.hom).symm r)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul, hs, smul_eq_mul, mul_one]

/-- The genuine over/pullback natural equivalence produces the actual section isomorphism. -/
theorem originalPullbackSectionHom_isIso_of_over (U : X.Opens)
    (α : Scheme.Modules.unitObj X ⟶ L)
    (hα : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map α)) :
    IsIso (pullbackSectionHom U.ι α) := by
  let := hα
  have hn := (overPullbackIso U).hom.naturality α
  simp only [Functor.comp_map] at hn
  have hleft : IsIso ((Scheme.Modules.overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map α) ≫
        (overPullbackIso U).hom.app L) := inferInstance
  rw [hn] at hleft
  let := hleft
  have hmap : IsIso ((Scheme.Modules.pullback U.ι).map α) :=
    IsIso.of_isIso_comp_left ((overPullbackIso U).hom.app (Scheme.Modules.unitObj X)) _
  let := hmap
  dsimp only [pullbackSectionHom]
  infer_instance

/-- The literal original degree-one homogeneous coordinate morphism. -/
def originalProjectiveCoordinateSectionHom (N : ℕ) (i : Fin (N + 1)) :
    Scheme.Modules.unitObj (polynomialProj ℂ N) ⟶
      (polynomialProjTwistingLine ℂ N).sheaf :=
  originalOrdinarySectionHom _
    (projectiveTwistingCoordinateSection
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) 1
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩ ⊤)

/-- The SAME original homogeneous coordinate section is a genuine line frame on its own chart. -/
theorem originalProjectiveCoordinateSection_pullback_isIso (N : ℕ) (i : Fin (N + 1)) :
    IsIso (pullbackSectionHom (polynomialProjCoordinateOpen ℂ N i).ι
      (originalProjectiveCoordinateSectionHom N i)) := by
  let e := projectiveTwistingCoordinateFrame
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) 1
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩
  have hs (V : (polynomialProj ℂ N).Opens) (l : V ⟶ polynomialProjCoordinateOpen ℂ N i) :
      e.coefficients l ((polynomialProjTwistingLine ℂ N).sheaf.val.map V.leTop.op
        (projectiveTwistingCoordinateSection
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) 1
          ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩ ⊤)) = 1 := by
    have hg := polynomialProjTwistingFrame_generator ℂ N i 1 l
    apply (e.coefficients l).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact hg.symm
  apply originalPullbackSectionHom_isIso_of_over
  change IsIso ((SheafOfModules.overFunctor (polynomialProj ℂ N).ringCatSheaf
    (polynomialProjCoordinateOpen ℂ N i)).map (originalOrdinarySectionHom _ _))
  have he := originalOrdinarySectionHom_over_eq_frame_inv e _ hs
  exact (congrArg IsIso he).mpr (inferInstance : IsIso e.inv)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
