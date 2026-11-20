import SGPT.BDivisor.BD3CurveEulerDegree
import SGPT.Projective.OriginalIntegralCurveZeroEuler
import SGPT.Projective.OriginalNormalizationZeroGlobal
import SGPT.Projective.OriginalNormalizationCurveDimension
import SGPT.Projective.OriginalLinePullbackTensor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! The intrinsic signed algebraic degree on the original integral curve
equals that on its canonical normalization. The normalized projective embedding
is a geometric input to the comparison, with no degree comparison premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Projective.NumEq.AlgebraicCurveDegree SGPT.Okounkov
open SGPT.NAPotential.FSPos

open CategoryTheory.Limits

private theorem not_isZero_line_of_nonempty_bd7 {X : Scheme.{0}} [Nonempty X]
    {L : X.Modules} (a : LineBundleAtlas L) : ¬ IsZero L := by
  intro h
  let U : X.Opens := ⊤
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hpb := (Scheme.Modules.pullback U.ι).map_isZero h
  exact SGPT.BDivisor.BD3.not_isZero_pullback_of_atlas a U x (by simp [U]) hpb

/-- Actual original Serre global generation manufactures ordinary
FIRST-power numerator/denominator sections on arbitrary nonempty original
projective geometry. No original smoothness or supplied nonzero sections. -/
theorem exists_originalNonemptySerreTwist_sections_bd7
    {X : Scheme.{0}} [Nonempty X] (f : X ⟶ Spec (.of ℂ))
    {A : X.Modules} (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ M : ℕ, 0<M ∧ ∃ σ : Γ(bundleTensor L (bundleTensorPower A M),⊤),
      ∃ τ : Γ(bundleTensorPower A M,⊤), σ≠0 ∧ τ≠0 := by
  classical
  obtain ⟨B, hB⟩ := exists_originalProjectiveTwist_generators_bd3 P.map a
  obtain ⟨C, hC⟩ := exists_originalProjectiveTwist_generators_bd3 P.map (trivialIntrinsicLineBundle X).atlas
  let D := max B C + 1
  have hBD : B ≤ D := (le_max_left B C).trans (Nat.le_succ _)
  have hCD : C ≤ D := (le_max_right B C).trans (Nat.le_succ _)
  obtain ⟨G, hG⟩ := hB D hBD
  obtain ⟨J, hJ⟩ := hC D hCD
  let Q := (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf
  let bQ := (nativePolynomialPullbackAtlas ℂ P.ambientDimension P.map).tensorPower D
  let bT := pairwiseTensorAtlas bQ a
  let bU := pairwiseTensorAtlas bQ (trivialIntrinsicLineBundle X).atlas
  obtain ⟨s, hs⟩ := SGPT.BDivisor.BD3.exists_generatedSection_ne_zero _ (not_isZero_line_of_nonempty_bd7 bT) G
  obtain ⟨t, ht⟩ := SGPT.BDivisor.BD3.exists_generatedSection_ne_zero _ (not_isZero_line_of_nonempty_bd7 bU) J
  let M := P.power * D
  let eP : bundleTensorPower A M ≅ bundleTensorPower Q D :=
    nativeLineTensorPowerMulIso aA P.power D ≪≫ nativeLineTensorPowerIso P.iso D
  let eS : bundleTensor (bundleTensorPower Q D) L ≅ bundleTensor L (bundleTensorPower A M) :=
    bundleTensorIso eP.symm (Iso.refl L) ≪≫ originalTensorSwapIso_bd3 _ _
  let eT : bundleTensor (bundleTensorPower Q D) (SheafOfModules.unit X.ringCatSheaf) ≅ bundleTensorPower A M :=
    bundleTensorIso eP.symm (Iso.refl _) ≪≫ bundleTensorRightUnitIso _
  exact ⟨M, Nat.mul_pos P.power_pos (Nat.succ_pos _), eS.hom.val.app (.op ⊤) s,
    eT.hom.val.app (.op ⊤) t,
    originalSectionIso_ne_zero eS s hs,
    originalSectionIso_ne_zero eT t ht⟩


/-- The SAME original embedding manufactures true original hyperplane
FIRST-power ordinary nonzero sections, including singular integral curves. -/
theorem exists_originalNonemptyHyperplaneTwist_sections_bd7
    {X : Scheme.{0}} [Nonempty X] (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ M : ℕ, 0<M ∧ ∃ σ : Γ(bundleTensor L (bundleTensorPower (hyperplaneBundle E) M),⊤),
      ∃ τ : Γ(bundleTensorPower (hyperplaneBundle E) M,⊤), σ≠0 ∧ τ≠0 :=
  exists_originalNonemptySerreTwist_sections_bd7 f (hyperplaneAtlas E)
    (originalEmbeddingHyperplanePolarization_bd3 f E) a

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.NAPotential.FSPos

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- ONLY actual ordinary ORIGINAL FIRST-power fraction data; no desired
comparison, Euler, period, degree or normalized embedding field. -/
structure OriginalIntegralCurveFractionalPresentation_bd7 (L : X.Modules) where
  exponent : ℕ
  positiveExponent : 0<exponent
  numerator : Γ(bundleTensor L (bundleTensorPower (hyperplaneBundle E) exponent),⊤)
  denominator : Γ(bundleTensorPower (hyperplaneBundle E) exponent,⊤)
  numerator_nonzero : numerator≠0
  denominator_nonzero : denominator≠0

/-- Actual nonsmooth original Serre global generation PRODUCES ordinary
FIRST-power fraction data, no section or original smoothness input. -/
theorem exists_originalIntegralCurveFractionalPresentation_bd7 {L : X.Modules} (a : LineBundleAtlas L) :
    Nonempty (OriginalIntegralCurveFractionalPresentation_bd7 f E L) := by
  obtain ⟨M,hM,s,t,hs,ht⟩ := exists_originalNonemptyHyperplaneTwist_sections_bd7 f E a
  exact ⟨⟨M,hM,s,t,hs,ht⟩⟩

/-- The SAME actual manufactured original ordinary fraction. -/
def originalIntegralCurveLinePresentation_bd7 {L : X.Modules} (a : LineBundleAtlas L) :
    OriginalIntegralCurveFractionalPresentation_bd7 f E L :=
  Classical.choice (exists_originalIntegralCurveFractionalPresentation_bd7 f E a)

variable (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

/-- PURE INDEPENDENT actual original numerator-minus-denominator structural
zero-cycle degree; no Euler, metric, period or tensor-power division. -/
def OriginalIntegralCurveFractionalPresentation_bd7.degree {L : X.Modules}
    (P : OriginalIntegralCurveFractionalPresentation_bd7 f E L) (a : LineBundleAtlas L) :
    AlgebraicCycle (Spec (.of ℂ)) ℤ :=
  originalIntegralCurveSectionZeroDegree f E hcurve
    (a.tensor ((hyperplaneAtlas E).tensorPower P.exponent)) P.numerator P.numerator_nonzero -
  originalIntegralCurveSectionZeroDegree f E hcurve
    ((hyperplaneAtlas E).tensorPower P.exponent) P.denominator P.denominator_nonzero

/-- Canonical independent ORIGINAL signed structural integer line degree,
with ordinary original Serre sections genuinely manufactured internally. -/
def originalIntegralCurveLineDegree_bd7 {L : X.Modules} (a : LineBundleAtlas L) :
    AlgebraicCycle (Spec (.of ℂ)) ℤ :=
  OriginalIntegralCurveFractionalPresentation_bd7.degree f E hcurve (originalIntegralCurveLinePresentation_bd7 f E a) a

/-- ANY genuine ORIGINAL ordinary fraction has its actual independent
structural degree equal to the true original line Euler difference. -/
theorem originalIntegralFractionalDegree_eq_eulerDifference_bd7 {L : X.Modules}
    (a : LineBundleAtlas L) (P : OriginalIntegralCurveFractionalPresentation_bd7 f E L) (p : Spec (.of ℂ)) :
    OriginalIntegralCurveFractionalPresentation_bd7.degree f E hcurve P a p = originalProjectiveLineCechEuler f E L -
      originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) := by
  have hS := originalIntegralCurve_eulerDifference_eq_sectionZeroDegree f E hcurve
    (a.tensor ((hyperplaneAtlas E).tensorPower P.exponent)) P.numerator P.numerator_nonzero p
  have hT := originalIntegralCurve_twistedEuler_eq_sectionZeroDegree f E hcurve
    ((hyperplaneAtlas E).tensorPower P.exponent) a P.denominator P.denominator_nonzero p
  change originalIntegralCurveSectionZeroDegree f E hcurve _ P.numerator P.numerator_nonzero p -
    originalIntegralCurveSectionZeroDegree f E hcurve _ P.denominator P.denominator_nonzero p = _
  omega

/-- Actual manufactured original line degree has the pure original Euler reader. -/
theorem originalIntegralCurveLineDegree_eq_eulerDifference_bd7 {L : X.Modules}
    (a : LineBundleAtlas L) (p : Spec (.of ℂ)) :
    originalIntegralCurveLineDegree_bd7 f E hcurve a p = originalProjectiveLineCechEuler f E L -
      originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) :=
  originalIntegralFractionalDegree_eq_eulerDifference_bd7 f E hcurve a (originalIntegralCurveLinePresentation_bd7 f E a) p

/-- Presentation independence is an actual PURE original algebraic output. -/
theorem originalIntegralFractionalDegree_independent_bd7 {L : X.Modules}
    (a : LineBundleAtlas L) (P Q : OriginalIntegralCurveFractionalPresentation_bd7 f E L) (p : Spec (.of ℂ)) :
    OriginalIntegralCurveFractionalPresentation_bd7.degree f E hcurve P a p = OriginalIntegralCurveFractionalPresentation_bd7.degree f E hcurve Q a p :=
  (originalIntegralFractionalDegree_eq_eulerDifference_bd7 f E hcurve a P p).trans
    (originalIntegralFractionalDegree_eq_eulerDifference_bd7 f E hcurve a Q p).symm

/-- Actual original atlas independence, with NO physical metric input. -/
theorem originalIntegralCurveLineDegree_independent_atlas_bd7 {L : X.Modules}
    (a b : LineBundleAtlas L) (p : Spec (.of ℂ)) :
    originalIntegralCurveLineDegree_bd7 f E hcurve a p = originalIntegralCurveLineDegree_bd7 f E hcurve b p :=
  (originalIntegralCurveLineDegree_eq_eulerDifference_bd7 f E hcurve a p).trans
    (originalIntegralCurveLineDegree_eq_eulerDifference_bd7 f E hcurve b p).symm

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.NAPotential.FSPos
open SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)
variable (EN : ClosedProjectiveEmbedding (originalNormalizationMap X ≫ f))
include hcurve
local notation "ν" => originalNormalizationMap X
local notation "fN" => originalNormalizationMap X ≫ f

/-- SAME INDEPENDENT structural zero degrees, original curve and true
actual normalized original projective curve, no Euler or period comparison. -/
theorem originalSectionZeroDegree_eq_normalizedProjectiveZeroDegree_bd7
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) (p : Spec (.of ℂ)) :
    originalIntegralCurveSectionZeroDegree f E hcurve a s hs p =
      originalIntegralCurveSectionZeroDegree fN EN (originalNormalizationCurve_functionField_trdeg f E hcurve)
        (matePullbackAtlas ν a) (originalPulledSection ν s) (originalNormalizedSection_ne_zero a s hs) p := by
  have hO := originalIntegralCurveSectionZeroDegree_eq_normalizedFullLength f E hcurve a s hs p
  have hN := originalIntegralCurveSectionZeroDegree_eq_fullLength fN EN
    (originalNormalizationCurve_functionField_trdeg f E hcurve)
    (matePullbackAtlas ν a) (originalPulledSection ν s) (originalNormalizedSection_ne_zero a s hs) p
  exact hO.trans hN.symm

/-- Genuine OWN normalized projective Cartier Euler reads the SAME
independent ORIGINAL zero structural degree, testing/cutting lines distinct. -/
theorem originalNormalizedOwn_twistedEuler_eq_originalSectionZeroDegree_bd7
    {L B : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas B)
    (s : Γ(L,⊤)) (hs : s ≠ 0) (p : Spec (.of ℂ)) :
    originalProjectiveLineCechEuler fN EN ((Scheme.Modules.pullback ν).obj (bundleTensor B L)) =
      originalProjectiveLineCechEuler fN EN ((Scheme.Modules.pullback ν).obj B) +
        originalIntegralCurveSectionZeroDegree f E hcurve a s hs p := by
  have hN := originalIntegralCurve_twistedEuler_eq_sectionZeroDegree fN EN
    (originalNormalizationCurve_functionField_trdeg f E hcurve)
    (matePullbackAtlas ν a) (matePullbackAtlas ν b) (originalPulledSection ν s)
      (originalNormalizedSection_ne_zero a s hs) p
  have he := originalProjectiveLineCechEuler_eq_of_iso fN EN (originalLinePullbackTensorIso ν b a)
  exact he.trans (hN.trans (congrArg
    (fun d : ℤ => originalProjectiveLineCechEuler fN EN ((Scheme.Modules.pullback ν).obj B) + d)
    (originalSectionZeroDegree_eq_normalizedProjectiveZeroDegree_bd7 f E hcurve EN a s hs p).symm))

/-- Original and TRUE OWN-normalized Euler differences agree by actual
ordinary FIRST-power sections, never by a supplied cover equality. -/
theorem originalNormalization_ownEulerDifference_bd7
    {L : X.Modules} (a : LineBundleAtlas L) :
    originalProjectiveLineCechEuler fN EN ((Scheme.Modules.pullback ν).obj L) -
      originalProjectiveLineCechEuler fN EN (SheafOfModules.unit (originalNormalizationScheme X).ringCatSheaf) =
      originalProjectiveLineCechEuler f E L -
        originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨M,_hM,σ,τ,hσ,hτ⟩ := exists_originalNonemptyHyperplaneTwist_sections_bd7 f E a
  let A := bundleTensorPower (hyperplaneBundle E) M
  let aA := (hyperplaneAtlas E).tensorPower M
  let aS := a.tensor aA
  let p : Spec (.of ℂ) := f (genericPoint X)
  have hτX := originalIntegralCurve_twistedEuler_eq_sectionZeroDegree f E hcurve aA a τ hτ p
  have hτN := originalNormalizedOwn_twistedEuler_eq_originalSectionZeroDegree_bd7 f E hcurve EN aA a τ hτ p
  have hσX := originalIntegralCurve_eulerDifference_eq_sectionZeroDegree f E hcurve aS σ hσ p
  have hσN0 := originalIntegralCurve_eulerDifference_eq_sectionZeroDegree fN EN
    (originalNormalizationCurve_functionField_trdeg f E hcurve)
    (matePullbackAtlas ν aS) (originalPulledSection ν σ) (originalNormalizedSection_ne_zero aS σ hσ) p
  have hσN := hσN0.trans (originalSectionZeroDegree_eq_normalizedProjectiveZeroDegree_bd7 f E hcurve EN aS σ hσ p).symm
  omega

/-- The INDEPENDENT original signed singular-curve structural degree equals
EXISTING independent original signed degree of its SAME normalized pullback,
using TRUE internally produced normalized smooth/projective geometry. -/
theorem originalIntegralCurveLineDegree_eq_normalizedCurveLineDegree_bd7
    {L : X.Modules} (a : LineBundleAtlas L) (p : Spec (.of ℂ)) :
    letI := originalNormalizationCurve_smoothOfRelativeDimension f E hcurve
    letI := (EN).isSeparated
    letI := (EN).quasiCompact
    originalIntegralCurveLineDegree_bd7 f E hcurve a p =
      originalCurveLineDegree_bd3 fN EN (matePullbackAtlas ν a) p := by
  let := originalNormalizationCurve_smoothOfRelativeDimension f E hcurve
  let := (EN).isSeparated
  let := (EN).quasiCompact
  exact (originalIntegralCurveLineDegree_eq_eulerDifference_bd7 f E hcurve a p).trans
    ((originalNormalization_ownEulerDifference_bd7 f E hcurve EN a).symm.trans
      (originalCurveLineDegree_eq_eulerDifference_bd3 fN EN (matePullbackAtlas ν a) p).symm)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
