import SGPT.BDivisor.BD3ProjectiveTwistGeneration
import SGPT.Projective.OriginalSectionIsoTransport
import SGPT.LineBundle.RiemannRochAmple
import SGPT.NAPotential.FSPosMetric
import SGPT.Foundations.Schemes.BundleTensorRightUnit

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalSerreCurveSections`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalSerreCurveSections`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Ordinary FIRST-power original Serre presentations on the whole curve.
Blueprint: original-serre-curve-sections.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
local instance originalSwapPresheafMonoidal_bd3 {X : Scheme.{0}} : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
local instance originalSwapPresheafSymmetric_bd3 {X : Scheme.{0}} : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.sheaf.obj)

/-- Actual sheafified tensor swap on the SAME original module sheaves. -/
def originalTensorSwapIso_bd3 {X : Scheme.{0}} (L N : X.Modules) : bundleTensor L N ≅ bundleTensor N L :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ L.val N.val)

/-- Ordinary first-power original sections, nonzero on ALL components, with no metric/period input. -/
theorem exists_originalSerreTwist_sections_bd3
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {A : X.Modules} (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ M : ℕ, 0 < M ∧ ∃ σ : Γ(bundleTensor L (bundleTensorPower A M), ⊤),
      ∃ τ : Γ(bundleTensorPower A M, ⊤),
        SectionNonzeroOnComponents f E σ ∧ SectionNonzeroOnComponents f E τ := by
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
  obtain ⟨s, hs⟩ := SGPT.BDivisor.BD3.exists_generatedSection_nonzeroOnComponents f E bT G
  obtain ⟨t, ht⟩ := SGPT.BDivisor.BD3.exists_generatedSection_nonzeroOnComponents f E bU J
  let M := P.power * D
  let eP : bundleTensorPower A M ≅ bundleTensorPower Q D :=
    nativeLineTensorPowerMulIso aA P.power D ≪≫ nativeLineTensorPowerIso P.iso D
  let eS : bundleTensor (bundleTensorPower Q D) L ≅ bundleTensor L (bundleTensorPower A M) :=
    bundleTensorIso eP.symm (Iso.refl L) ≪≫ originalTensorSwapIso_bd3 _ _
  let eT : bundleTensor (bundleTensorPower Q D) (SheafOfModules.unit X.ringCatSheaf) ≅ bundleTensorPower A M :=
    bundleTensorIso eP.symm (Iso.refl _) ≪≫ bundleTensorRightUnitIso _
  exact ⟨M, Nat.mul_pos P.power_pos (Nat.succ_pos _), eS.hom.val.app (.op ⊤) s,
    eT.hom.val.app (.op ⊤) t,
    originalSectionIso_nonzeroOnComponents f E eS s hs,
    originalSectionIso_nonzeroOnComponents f E eT t ht⟩

/-- SAME original E gives the genuine existing original hyperplane ample-polarization object. -/
def originalEmbeddingHyperplanePolarization_bd3 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) :
    SGPT.LineBundle.AmplePolarization f (hyperplaneBundle E) where
  power := 1
  power_pos := Nat.zero_lt_one
  ambientDimension := E.ambientDimension
  map := E.map
  isClosedImmersion := E.closedImmersion
  over_base := E.over_base
  iso := bundleTensorLeftUnitIso (hyperplaneBundle E)

/-- Literal book hyperplane powers give first-power presentations for ANY original line, on ALL components. -/
theorem exists_originalHyperplaneTwist_sections_bd3
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ M : ℕ, 0 < M ∧ ∃ σ : Γ(bundleTensor L (bundleTensorPower (hyperplaneBundle E) M), ⊤),
      ∃ τ : Γ(bundleTensorPower (hyperplaneBundle E) M, ⊤),
        SectionNonzeroOnComponents f E σ ∧ SectionNonzeroOnComponents f E τ :=
  exists_originalSerreTwist_sections_bd3 f E (hyperplaneAtlas E) (originalEmbeddingHyperplanePolarization_bd3 f E) a

end SGPT.Projective.NumEq.AlgebraicCurveDegree
