import SGPT.Foundations.Schemes.PositiveProjectiveCechInputs
import SGPT.Foundations.Schemes.NativeProjectiveCechEuler
import SGPT.Foundations.Schemes.NativeProjectiveGlobalSectionsFiniteness

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (N : ℕ)
variable {X : Scheme} (f : X ⟶ polynomialProj K N) (L : IntrinsicLineBundle X)
    (q : ℕ) (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)

/-- The genuine once-chosen finite graded span already represents the actual
UNTWISTED ambient section diagram at degree zero, so every actual H is finite. -/
theorem polynomialProjActualCech_homology_finite (M : (polynomialProj K N).Modules)
    [∀ j, Module.Finite (polynomialProjCoordinateRing K N j)
      Γ(polynomialProjModuleChart M j, ⊤)]
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] (p : ℕ) :
    Module.Finite K ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M
      (polynomialProjCoordinateOpen K N) (schemeConstantMap (polynomialProjStructureMap K N)))).homology p) := by
  let D := homogeneousCoordinateSubsetDiagram
    (polynomialIntegralGrading (K := K) (I := Fin (N + 1)))
    (polynomialProjChartGeneratedTwistedPiece K N M)
    (fun j ↦ (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K)) polynomialCoordinate_X_degree (0 : ℤ)
  let : Module.Finite K ((subsetCechComplex D).homology p) :=
    finiteGradedPolynomialCoordinateCech_homology_finite (K := K) (I := Fin (N + 1))
      (polynomialProjChartGeneratedTwistedPiece K N M) (0 : ℤ) p
  exact Module.Finite.equiv (nonemptySubsetCechHomologyIso
    (polynomialProjChartGeneratedTwistedNonemptySubsetIso K N M) p).toLinearEquiv

/-- Actual closed-projective line geometry produces finite ORIGINAL source
Čech homology with its given original structural field action. -/
theorem closedPolynomialProjLineCech_homology_finite
    {Y : Scheme} (i : Y ⟶ polynomialProj K N) [IsClosedImmersion i]
    {B : Y.Modules} (a : LineBundleAtlas B) (p : Y ⟶ Spec (.of K))
    (hp : actualPolynomialProjectivePullbackStructureMap i = p) (j : ℕ) :
    Module.Finite K ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram B
      (actualPolynomialProjectivePullbackCoordinateOpens i) (schemeGlobalConstants p))).homology j) := by
  subst p
  let M := (Scheme.Modules.pushforward i).obj B
  have : ∀ k, Module.Finite (polynomialProjCoordinateRing K N k)
      Γ(polynomialProjModuleChart M k, ⊤) :=
    fun k ↦ polynomialProjPushforwardChartSections_finite i a k
  have : ∀ k, (polynomialProjModuleChart M k).IsQuasicoherent :=
    fun k ↦ polynomialProjPushforwardChart_isQuasicoherent i a k
  let c := schemeConstantMap (polynomialProjStructureMap K N)
  let U := polynomialProjCoordinateOpen K N
  let : Module.Finite K ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M U c)).homology j) :=
    polynomialProjActualCech_homology_finite K N M j
  have hsrc : Module.Finite K ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram B
      (fun k ↦ i ⁻¹ᵁ U k) (actualSchemePushforwardSourceConstants i c))).homology j) :=
    Module.Finite.equiv (actualSchemeModulePushforwardHomologyIso i B c U j).toLinearEquiv
  have hc := actualPolynomialProjectivePushforwardSourceConstants_eq i
  rw [polynomialProj_identityPullback_constants K N] at hc
  change Module.Finite K ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram B
    (fun k ↦ i ⁻¹ᵁ U k) (schemeGlobalConstants (actualPolynomialProjectivePullbackStructureMap i)))).homology j)
  rw [← hc]
  exact hsrc

/-- Genuine projective line geometry produces the finite neighboring groups,
so the actual LES yields finite quotient homology in every degree. -/
theorem nativePositiveProjectiveSectionZeroCech_quotient_homology_finite
    [IsIntegral X] [IsClosedImmersion f] (s : bundlePowerGlobalSections L.sheaf q)
    (hs : s ≠ 0) (p : X ⟶ Spec (.of K))
    (hp : actualPolynomialProjectivePullbackStructureMap f = p) (m j : ℕ) :
    Module.Finite K ((nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₃.homology j) := by
  let C := nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
    (schemeGlobalConstants p) m
  let : Module.Finite K (C.X₂.homology j) :=
    closedPolynomialProjLineCech_homology_finite K N f
      ((L.atlas.tensorPower q).tensorPower (m + 1)) p hp j
  let : Module.Finite K (C.X₁.homology (j + 1)) :=
    closedPolynomialProjLineCech_homology_finite K N f
      ((L.atlas.tensorPower q).tensorPower m) p hp (j + 1)
  exact nativeCochainHomology_finite_dimensionShift C
    (nativePositiveProjectiveSectionZeroCechShortComplex_shortExact K N f L q e s hs
      (schemeGlobalConstants p) m) j

/-- Actual closed-projective/positive geometry PRODUCES all frame and finite-H
inputs of the original chosen-cover Euler identity, retaining the original p. -/
theorem nativePositiveProjectiveSectionZeroCechEuler_additive
    [IsIntegral X] [IsClosedImmersion f] (s : bundlePowerGlobalSections L.sheaf q)
    (hs : s ≠ 0) (p : X ⟶ Spec (.of K))
    (hp : actualPolynomialProjectivePullbackStructureMap f = p) (m : ℕ) :
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₂.homologyEulerChar =
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₁.homologyEulerChar +
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₃.homologyEulerChar := by
  let C := nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
    (schemeGlobalConstants p) m
  let : ∀ j, Module.Finite K (C.X₁.homology j) := fun j ↦
    closedPolynomialProjLineCech_homology_finite K N f
      ((L.atlas.tensorPower q).tensorPower m) p hp j
  let : ∀ j, Module.Finite K (C.X₂.homology j) := fun j ↦
    closedPolynomialProjLineCech_homology_finite K N f
      ((L.atlas.tensorPower q).tensorPower (m + 1)) p hp j
  exact sectionZeroPowerCechEuler_additive (L.atlas.tensorPower q) s hs
    (actualPolynomialProjectivePullbackCoordinateOpens f)
    (fun S ↦ actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f S.val S.property)
    (nativePositiveProjectiveSubsetFrame K N f L q e) (schemeGlobalConstants p) m

/-- The actual original Fano section-zero complexes use original projective
coordinates and literal structural complex scalars. -/
abbrev SmoothProjectiveFano.nativeAnticanonicalSectionZeroCechShortComplex
    {n : ℕ} (F : SmoothProjectiveFano n)
    (s : bundlePowerGlobalSections (smoothAnticanonicalLineBundle F.structureMap n).sheaf
      F.anticanonicalPower) (m : ℕ) :=
  nativePositiveProjectiveSectionZeroCechShortComplex ℂ F.projective.ambientDimension
    F.projective.map (smoothAnticanonicalLineBundle F.structureMap n) F.anticanonicalPower
    F.positivityIso s (schemeGlobalConstants F.structureMap) m

/-- ORIGINAL Fano geometry produces the actual chosen-cover Euler difference,
with no affine-frame or finite-H certificate input. -/
theorem SmoothProjectiveFano.nativeAnticanonicalSectionZeroCechEuler_additive
    {n : ℕ} (F : SmoothProjectiveFano n)
    (s : bundlePowerGlobalSections (smoothAnticanonicalLineBundle F.structureMap n).sheaf
      F.anticanonicalPower) (hs : s ≠ 0) (m : ℕ) :
    (F.nativeAnticanonicalSectionZeroCechShortComplex s m).X₂.homologyEulerChar =
      (F.nativeAnticanonicalSectionZeroCechShortComplex s m).X₁.homologyEulerChar +
        (F.nativeAnticanonicalSectionZeroCechShortComplex s m).X₃.homologyEulerChar :=
  nativePositiveProjectiveSectionZeroCechEuler_additive ℂ F.projective.ambientDimension
    F.projective.map (smoothAnticanonicalLineBundle F.structureMap n) F.anticanonicalPower
    F.positivityIso s hs F.structureMap F.projective.over_base m

end
end SGPT.Foundations.Schemes
