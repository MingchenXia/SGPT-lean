import SGPT.Foundations.Schemes.ActualSectionDiagramIsomorphisms
import SGPT.Foundations.Schemes.NativePositiveLineRestrictionComparison
import SGPT.Foundations.Schemes.NativeProjectiveLineCechEuler

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (f : X ⟶ polynomialProj K N) (L : IntrinsicLineBundle X) (q : ℕ)
    (s : bundlePowerGlobalSections L.sheaf q) (p : X ⟶ Spec (.of K))
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL quotient complex on the actual source coordinate cover. -/
def nativePositiveSectionZeroQuotientCechComplex (m : ℕ) : CochainComplex (ModuleCat K) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
    (bundleTensor (bundleTensorPower (bundleTensorPower L.sheaf q) m)
      (sectionZeroPushforwardStructure (L.atlas.tensorPower q) s))
    (actualPolynomialProjectivePullbackCoordinateOpens f) (schemeGlobalConstants p))

/-- The ACTUAL geometric restriction complex on the actual divisor pullback
cover, with the genuine original structural composite ι then p. -/
def nativePositiveSectionZeroRestrictedCechComplex (m : ℕ) : CochainComplex (ModuleCat K) ℕ :=
  let g := sectionZeroι (L.atlas.tensorPower q) s
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
    ((Scheme.Modules.pullback g).obj (bundleTensorPower (bundleTensorPower L.sheaf q) m))
    (fun j ↦ g ⁻¹ᵁ actualPolynomialProjectivePullbackCoordinateOpens f j)
    (schemeGlobalConstants (g ≫ p)))

/-- The actual divisor coordinate family genuinely covers the actual zero scheme. -/
theorem nativePositiveSectionZeroRestrictedCover_covers :
    iSup (fun j ↦ sectionZeroι (L.atlas.tensorPower q) s ⁻¹ᵁ
      actualPolynomialProjectivePullbackCoordinateOpens f j) = ⊤ := by
  change iSup ((Opens.map (sectionZeroι (L.atlas.tensorPower q) s).base).obj ∘
    actualPolynomialProjectivePullbackCoordinateOpens f) = ⊤
  rw [← Opens.map_iSup, actualPolynomialProjectivePullbackCoordinateOpens_covers]
  rfl

variable (e : bundleTensorPower L.sheaf q ≅
  (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)

/-- Canonical actual quotient/restriction comparison and true pushforward
comparison produce the ORIGINAL base-linear divisor-cover complex iso. -/
def nativePositiveSectionZeroCechIso (m : ℕ) :
    nativePositiveSectionZeroQuotientCechComplex K N f L q s p m ≅
      nativePositiveSectionZeroRestrictedCechComplex K N f L q s p m := by
  let g := sectionZeroι (L.atlas.tensorPower q) s
  let B := bundleTensorPower (bundleTensorPower L.sheaf q) m
  let R := (Scheme.Modules.pullback g).obj B
  let U := actualPolynomialProjectivePullbackCoordinateOpens f
  let c := schemeGlobalConstants p
  let Φ := nativePositiveProjectiveIteratedPowerRestrictionIso K N f L q e g m
  let E := actualSchemeModuleBaseSubsetIso Φ U c
  let E' := nonemptySubsetCechComplexIso
    (Functor.isoWhiskerLeft (nonemptySubsetInclusion (Fin (N + 1))) E)
  let P := actualSchemeModulePushforwardCechIso g R c U
  let C (d : K →+* Γ(sectionZeroSubscheme (L.atlas.tensorPower q) s, ⊤)) :=
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram R (fun j ↦ g ⁻¹ᵁ U j) d)
  have hc := actualSchemePushforwardSourceConstants_schemeGlobalConstants g p
  exact E' ≪≫ P ≪≫ eqToIso (congrArg C hc)

/-- The actual composite closed embedding and actual pullback line atlas
produce finite divisor homology for EVERY m, including m=0 and empty D. -/
theorem nativePositiveSectionZeroRestrictedCech_homology_finite
    [IsClosedImmersion f] (hp : actualPolynomialProjectivePullbackStructureMap f = p)
    (m j : ℕ) :
    Module.Finite K ((nativePositiveSectionZeroRestrictedCechComplex K N f L q s p m).homology j) := by
  let g := sectionZeroι (L.atlas.tensorPower q) s
  have hcomp : actualPolynomialProjectivePullbackStructureMap (g ≫ f) = g ≫ p := by
    rw [← hp]
    simp only [actualPolynomialProjectivePullbackStructureMap, Category.assoc]
  exact closedPolynomialProjLineCech_homology_finite K N (g ≫ f)
    (LineBundleAtlas.nativePullback g ((L.atlas.tensorPower q).tensorPower m)) (g ≫ p) hcomp j

include e in
/-- Genuine divisor line cohomology and the ACTUAL complex iso produce finite
quotient homology in EVERY m, without extrapolating a degree-successor result. -/
theorem nativePositiveSectionZeroQuotientCech_homology_finite
    [IsClosedImmersion f] (hp : actualPolynomialProjectivePullbackStructureMap f = p)
    (m j : ℕ) :
    Module.Finite K ((nativePositiveSectionZeroQuotientCechComplex K N f L q s p m).homology j) := by
  let : Module.Finite K
      ((nativePositiveSectionZeroRestrictedCechComplex K N f L q s p m).homology j) :=
    nativePositiveSectionZeroRestrictedCech_homology_finite K N f L q s p hp m j
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso
    (nativePositiveSectionZeroCechIso K N f L q s p e m) j).toLinearEquiv.symm

include e in
/-- Raw Euler readback through the actual canonical divisor-cover complex
iso. Genuine projective finite-homology producers are separate theorems above. -/
theorem nativePositiveSectionZeroCechEuler_eq_restricted (m : ℕ) :
    (nativePositiveSectionZeroQuotientCechComplex K N f L q s p m).homologyEulerChar =
      (nativePositiveSectionZeroRestrictedCechComplex K N f L q s p m).homologyEulerChar :=
  cochain_homologyEulerChar_eq_of_iso (nativePositiveSectionZeroCechIso K N f L q s p e m)

/-- The ORIGINAL positive-section Euler difference has the actual geometric
restriction on the actual divisor cover as its right term. -/
theorem nativePositiveProjectiveSectionZeroCechEulerOnDivisor
    [IsIntegral X] [IsClosedImmersion f] (hs : s ≠ 0)
    (hp : actualPolynomialProjectivePullbackStructureMap f = p) (m : ℕ) :
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₂.homologyEulerChar =
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₁.homologyEulerChar +
    (nativePositiveSectionZeroRestrictedCechComplex K N f L q s p (m + 1)).homologyEulerChar := by
  let C := nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
    (schemeGlobalConstants p) m
  have h := nativePositiveProjectiveSectionZeroCechEuler_additive K N f L q e s hs p hp m
  have hQ := nativePositiveSectionZeroCechEuler_eq_restricted K N f L q s p e (m + 1)
  exact h.trans (congrArg (fun z : ℤ ↦ C.X₁.homologyEulerChar + z) hQ)

/-- The actual ORIGINAL Fano divisor-cover restriction complex, retaining its
original anticanonical tensor order and composed structural complex scalars. -/
abbrev SmoothProjectiveFano.nativeAnticanonicalSectionZeroRestrictedCechComplex
    {n : ℕ} (F : SmoothProjectiveFano n)
    (s : bundlePowerGlobalSections (smoothAnticanonicalLineBundle F.structureMap n).sheaf
      F.anticanonicalPower) (m : ℕ) :=
  nativePositiveSectionZeroRestrictedCechComplex ℂ F.projective.ambientDimension F.projective.map
    (smoothAnticanonicalLineBundle F.structureMap n) F.anticanonicalPower s F.structureMap m

/-- ORIGINAL Fano geometry now yields the Euler difference on the ACTUAL
zero subscheme pullback coordinate cover and literal restriction sheaf. -/
theorem SmoothProjectiveFano.nativeAnticanonicalSectionZeroCechEulerOnDivisor
    {n : ℕ} (F : SmoothProjectiveFano n)
    (s : bundlePowerGlobalSections (smoothAnticanonicalLineBundle F.structureMap n).sheaf
      F.anticanonicalPower) (hs : s ≠ 0) (m : ℕ) :
    (F.nativeAnticanonicalSectionZeroCechShortComplex s m).X₂.homologyEulerChar =
      (F.nativeAnticanonicalSectionZeroCechShortComplex s m).X₁.homologyEulerChar +
        (F.nativeAnticanonicalSectionZeroRestrictedCechComplex s (m + 1)).homologyEulerChar :=
  nativePositiveProjectiveSectionZeroCechEulerOnDivisor ℂ F.projective.ambientDimension
    F.projective.map (smoothAnticanonicalLineBundle F.structureMap n) F.anticanonicalPower
    s F.structureMap F.positivityIso hs F.projective.over_base m

end
end SGPT.Foundations.Schemes
