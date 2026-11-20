import SGPT.Checks.Comparison.ThinApprox.SourcePSHComparison

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJFinitePresentation.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! One actual projective presentation of any given finite collection of
original numerical classes, with true factor lines and coefficient vectors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
open SGPT.NAPotential.BJ.Pair3ClassStability
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules SGPT.Support.Alterations SGPT.Foundations.Envelope
open SGPT.Foundations.Envelope.FiniteRelativeProjectiveProducts
open SGPT.Foundations.Envelope.GeneratedLineFamilyProjectiveEmbedding
open SGPT.Foundations.Envelope.NativeNumericalProjectivePresentations
open SGPT.Foundations.Envelope.NativeRealNumericalClasses SGPT.Foundations.Envelope.CanonicalGeometry
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

end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
