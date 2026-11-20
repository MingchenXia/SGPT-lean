import SGPT.Foundations.Schemes.PolynomialTwistedFiniteSpanSubsetComparison
import SGPT.Foundations.Schemes.NonemptySubsetCechComparison
import SGPT.Foundations.Schemes.SchemeModulePushforwardCech
import SGPT.Foundations.Schemes.NativeProjectiveFano

/-! # Actual global line sections from the genuine projective embedding

The finite graded module is constructed from true extended chart generators.
Its genuine nonempty-subset representation gives finite Čech cohomology;
native pushforward and structural-map composition transport the result to
the literal source section spaces. No section-finiteness premise is added
to the closed embedding or smooth Fano input.
-/

open CategoryTheory AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K] (n : ℕ)

/-- Actual finite quasicoherent chart modules produce finite genuine global sections. -/
theorem polynomialProjFiniteChartGlobalSections_finite
    (M : (polynomialProj K n).Modules)
    [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart M j, ⊤)]
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] :
    Module.Finite K (actualSchemeModuleBaseGlobalSections M
      (schemeConstantMap (polynomialProjStructureMap K n))) := by
  classical
  have hcover : iSup (polynomialProjCoordinateOpen K n) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates
  exact actualSchemeModuleNonemptyRepresentedGlobalSections_finite M
    (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))
    (polynomialProjTwistedFiniteSpanPiece K n M
      (polynomialProjFiniteChartGeneratorDegree K n M)
      (polynomialProjFiniteChartGeneratorTwist K n M)) hcover 0
    (polynomialProjChartGeneratedTwistedNonemptySubsetIso K n M)

/-- Genuine closed-immersion line geometry gives finite literal source sections. -/
theorem closedPolynomialProjLineGlobalSections_finite
    {X : Scheme} (i : X ⟶ polynomialProj K n) [IsClosedImmersion i]
    {L : X.Modules} (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule (actualPolynomialProjectivePullbackStructureMap i) L
    Module.Finite K (bundleSections L ⊤) := by
  let := schemeGlobalSectionModule (actualPolynomialProjectivePullbackStructureMap i) L
  let M := (Scheme.Modules.pushforward i).obj L
  let : ∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart M j, ⊤) :=
    fun j => polynomialProjPushforwardChartSections_finite i a j
  let : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent :=
    fun j => polynomialProjPushforwardChart_isQuasicoherent i a j
  have := polynomialProjFiniteChartGlobalSections_finite K n M
  let e : actualSchemeModuleBaseGlobalSections M
      (schemeGlobalConstants (actualPolynomialProjectivePullbackStructureMap
        (𝟙 (polynomialProj K n)))) ≅
      actualSchemeModuleBaseGlobalSections M
        (schemeConstantMap (polynomialProjStructureMap K n)) :=
    eqToIso (congrArg (actualSchemeModuleBaseGlobalSections M)
      (polynomialProj_identityPullback_constants K n))
  have : Module.Finite K (actualSchemeModuleBaseGlobalSections M
      (schemeGlobalConstants (actualPolynomialProjectivePullbackStructureMap
        (𝟙 (polynomialProj K n))))) := by
    exact Module.Finite.equiv e.toLinearEquiv.symm
  exact Module.Finite.equiv
    (actualPolynomialProjectivePushforwardGlobalSectionsIso i L).toLinearEquiv

/-- The actual given structural map acts on finite sections of every true line tensor power. -/
theorem ClosedProjectiveEmbedding.powerGlobalSections_finite
    {X : Scheme} {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    Module.Finite ℂ (bundlePowerGlobalSections L m) := by
  have he : actualPolynomialProjectivePullbackStructureMap e.map = f := e.over_base
  rw [← he]
  exact closedPolynomialProjLineGlobalSections_finite ℂ e.ambientDimension e.map
    (a.tensorPower m)

/-- Smooth projective Fano geometry derives finite genuine anticanonical section spaces. -/
theorem SmoothProjectiveFano.anticanonicalPowerGlobalSections_finite
    {n : ℕ} (F : SmoothProjectiveFano n) (m : ℕ) :
    letI := schemeGlobalSectionModule F.structureMap
      (bundleTensorPower (anticanonicalLineSheaf F.structureMap n) m)
    Module.Finite ℂ (bundlePowerGlobalSections (anticanonicalLineSheaf F.structureMap n) m) :=
  F.projective.powerGlobalSections_finite (smoothAnticanonicalLineAtlas F.structureMap n) m

end

end SGPT.Foundations.Schemes
