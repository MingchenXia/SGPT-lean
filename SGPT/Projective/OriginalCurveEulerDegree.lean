import SGPT.Projective.OriginalArtinianLineEuler
import SGPT.Projective.OriginalSmoothSectionRegularity
import SGPT.Projective.OriginalCurveLineDegree

/-! PURE ORIGINAL arbitrary curve line degree equals original integer Euler
difference, via actual original zero schemes and actual Serre sections.
No metric, Chern form, native period or Riemann--Roch comparison premise.
Blueprint: original-curve-euler-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- The actual full zero-scheme inverse-image cover is LITERALLY the
coordinate cover of the SAME original composed projective embedding. -/
theorem originalSectionZeroRestrictedCechComplex_eq {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (B : X.Modules) :
    originalSectionZeroRestrictedCechComplex f E a s B =
      originalProjectiveLineCechComplex (sectionZeroι a s ≫ f) (E.sectionZero a s)
        ((Scheme.Modules.pullback (sectionZeroι a s)).obj B) := rfl

variable [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]

/-- The arbitrary original testing-line Cartier Euler difference on the
whole original smooth curve is the INDEPENDENT full original zero-cycle
structural degree. Every original nilpotent zero length is retained. -/
theorem originalWholeCurve_twistedEuler_eq_sectionZeroDegree
    {L B : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas B)
    (s : Γ(L, ⊤)) (hs : SectionNonzeroOnComponents f E s) (p : Spec (.of ℂ)) :
    originalProjectiveLineCechEuler f E (bundleTensor B L) =
      originalProjectiveLineCechEuler f E B + wholeCurveSectionZeroCycleDegree f E a s hs p := by
  let := wholeCurveSectionZero_isArtinian f E a s hs
  have hs' : OriginalSmoothSectionNonzeroOnComponents f 1 E s := hs
  have h := originalTwistedCartierEuler_eq_restricted f E a b s
    (originalSmoothSectionZeroEvaluation_injective f 1 E a s hs')
  have hD : (originalSectionZeroRestrictedCechComplex f E a s (bundleTensor B L)).homologyEulerChar =
      wholeCurveSectionZeroCycleDegree f E a s hs p := by
    rw [originalSectionZeroRestrictedCechComplex_eq]
    have hlength := originalArtinianLineCechEuler_eq_fullLength
      (sectionZeroι a s ≫ f) (E.sectionZero a s)
      (matePullbackAtlas (sectionZeroι a s) (b.tensor a))
    exact hlength.trans (wholeCurveSectionZeroCycleDegree_apply f E a s hs p).symm
  exact h.trans (congrArg (fun z : ℤ => originalProjectiveLineCechEuler f E B + z) hD)

/-- Pure original effective-section Euler/degree identity on the ENTIRE
original smooth curve, without a metric/period comparison. -/
theorem originalWholeCurve_eulerDifference_eq_sectionZeroDegree
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (hs : SectionNonzeroOnComponents f E s) (p : Spec (.of ℂ)) :
    originalProjectiveLineCechEuler f E L -
        originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) =
      wholeCurveSectionZeroCycleDegree f E a s hs p := by
  have h := originalWholeCurve_twistedEuler_eq_sectionZeroDegree f E a
    (trivialIntrinsicLineBundle X).atlas s hs p
  change originalProjectiveLineCechEuler f E (bundleTensor (SheafOfModules.unit X.ringCatSheaf) L) =
    originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) +
      wholeCurveSectionZeroCycleDegree f E a s hs p at h
  rw [originalProjectiveLineCechEuler_eq_of_iso f E (bundleTensorLeftUnitIso L)] at h
  omega

/-- PURE original ordinary numerator-minus-denominator zero-cycle degree is
the SAME original line Euler difference. The denominator is removed by
the actual arbitrary testing-line Cartier sequence, not by an analytic period. -/
theorem originalFractionalSectionDegree_eq_eulerDifference
    {L N : X.Modules} (a : LineBundleAtlas L) (c : LineBundleAtlas (bundleTensor L N))
    (b : LineBundleAtlas N) (s : Γ(bundleTensor L N, ⊤))
    (hs : SectionNonzeroOnComponents f E s) (t : Γ(N, ⊤))
    (ht : SectionNonzeroOnComponents f E t) (p : Spec (.of ℂ)) :
    originalFractionalSectionDegree f E c b s hs t ht p =
      originalProjectiveLineCechEuler f E L -
        originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) := by
  have hS := originalWholeCurve_eulerDifference_eq_sectionZeroDegree f E c s hs p
  have hT := originalWholeCurve_twistedEuler_eq_sectionZeroDegree f E b a t ht p
  change wholeCurveSectionZeroCycleDegree f E c s hs p -
    wholeCurveSectionZeroCycleDegree f E b t ht p = _
  omega

/-- ANY actual ordinary original hyperplane fractional presentation has the
SAME pure original line Euler difference; no presentation independence input. -/
theorem originalHyperplaneFractionalDegree_eq_eulerDifference
    {L : X.Modules} (a : LineBundleAtlas L)
    (P : OriginalHyperplaneFractionalPresentation f E L) (p : Spec (.of ℂ)) :
    P.degree a p = originalProjectiveLineCechEuler f E L -
      originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) :=
  originalFractionalSectionDegree_eq_eulerDifference f E a
    (pairwiseTensorAtlas a ((hyperplaneAtlas E).tensorPower P.exponent))
    ((hyperplaneAtlas E).tensorPower P.exponent) P.numerator P.numerator_nonzero
    P.denominator P.denominator_nonzero p

/-- ANY original line's independently defined original signed structural
INTEGER degree is its genuine ORIGINAL integer Euler difference, with
ordinary Serre numerator/denominator manufactured internally. -/
theorem originalCurveLineDegree_eq_eulerDifference
    {L : X.Modules} (a : LineBundleAtlas L) (p : Spec (.of ℂ)) :
    originalCurveLineDegree f E a p = originalProjectiveLineCechEuler f E L -
      originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) :=
  originalHyperplaneFractionalDegree_eq_eulerDifference f E a
    (originalCurveLinePresentation f E a) p

/-- Genuine original atlas independence of the independent original integer
degree, proved PURELY algebraically without a physical metric input. -/
theorem originalCurveLineDegree_independent_atlas_algebraic
    {L : X.Modules} (a b : LineBundleAtlas L) (p : Spec (.of ℂ)) :
    originalCurveLineDegree f E a p = originalCurveLineDegree f E b p :=
  (originalCurveLineDegree_eq_eulerDifference f E a p).trans
    (originalCurveLineDegree_eq_eulerDifference f E b p).symm

/-- Genuine original presentation independence for the integer structural
degree of ANY two ordinary original presentations of the SAME original line. -/
theorem originalHyperplaneFractionalDegree_independent_algebraic
    {L : X.Modules} (a : LineBundleAtlas L)
    (P Q : OriginalHyperplaneFractionalPresentation f E L) (p : Spec (.of ℂ)) :
    P.degree a p = Q.degree a p :=
  (originalHyperplaneFractionalDegree_eq_eulerDifference f E a P p).trans
    (originalHyperplaneFractionalDegree_eq_eulerDifference f E a Q p).symm

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
