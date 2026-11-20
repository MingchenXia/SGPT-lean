import SGPT.Foundations.PublishedEnvelope.Source.PSHComparison

/-! One actual projective presentation of any given finite collection of
original numerical classes, with true factor lines and coefficient vectors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v
namespace SGPT.NAPotential.BJ.ExternalClassStability
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules Alterations SGPT.Foundations.PublishedEnvelope
open SGPT.Foundations.PublishedEnvelope.FiniteRelativeProjectiveProducts
open SGPT.Foundations.PublishedEnvelope.GeneratedLineFamilyProjectiveEmbedding
open SGPT.Foundations.PublishedEnvelope.NativeNumericalProjectivePresentations
open SGPT.Foundations.PublishedEnvelope.NativeRealNumericalClasses SGPT.Foundations.PublishedEnvelope.CanonicalGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- A single actual multiprojective model contains ALL given finite numerical
classes; no dimension assertion about the entire numerical space is used. -/
theorem exists_simultaneous_presentation {ι : Type v} [Fintype ι] (θ : ι → Space p) :
    ∃ (r : ℕ) (d : Fin (r+1) → ℕ) (q : ∀ c,X ⟶ projectiveSpace ℂ (d c))
      (_ : ∀ c,q c ≫ projectiveSpaceStructure ℂ (d c)=p) (_ : IsClosedImmersion (q 0))
      (a : ι → Fin (r+1) → ℝ),∀ j,
      θ j=lineFamilyMap p (Variety.presentationFactorLine d q)
        (Variety.presentationFactorLine_isInvertible d q) (a j) := by
  classical
  obtain ⟨n,d,f,_,hfp,h0,_,_,_,a,ha⟩ :=
    NativeNumericalWholeFieldPresentations.exists_simultaneous_whole_field_presentation p θ
  let q := fun j : Fin (n+1+1) => f ≫ (projection (polynomialFamily ℂ d) j).left
  have hq (j : Fin (n+1+1)) : q j ≫ projectiveSpaceStructure ℂ (d j)=p := by
    change (f ≫ (projection (polynomialFamily ℂ d) j).left) ≫ (polynomialFamily ℂ d j).hom=p
    rw [Category.assoc,(projection (polynomialFamily ℂ d) j).w]
    exact hfp
  have hF (c : Fin (n+1+1)) :
      lineClass p (Variety.presentationFactorLine d q c)
        (Variety.presentationFactorLine_isInvertible d q c)=
      lineClass p (factorLine d f c) (factorLine_isInvertible d f c) := rfl
  refine ⟨n+1,d,q,hq,h0,
    (fun j => Fin.cons (0:ℝ) (Fin.cons (-∑ i,a j i) (a j) : Fin (n+1) → ℝ)),?_⟩
  intro j
  rw [lineFamilyMap_apply,ha j,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [hF,Fin.cons_zero,Fin.cons_succ,zero_smul,zero_add,smul_sub,
    Finset.sum_sub_distrib,neg_smul,← Finset.sum_smul]
  abel

end SGPT.NAPotential.BJ.ExternalClassStability
