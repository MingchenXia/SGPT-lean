import SGPT.Projective.AlgebraicNativeCutDimension
import SGPT.Projective.ComplexHomeomorphInverse
import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The SAME whole cut point homeomorphism is biholomorphic for the
ORIGINAL scheme native TN charts and ACTUAL member submanifold charts.
Blueprint: algebraic-native-cut-charts.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance cutChartsPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance cutChartsPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance cutChartsPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable (hK : (H.curvature a).val.IsKahler)
  (D : NativeRegularCut (schemeNativePositiveLine f n E a H hK))
  (σ : bundlePowerGlobalSections L D.power)
  [SmoothOfRelativeDimension (n - 1) (sectionZeroι (a.tensorPower D.power) σ ≫ f)]

local instance cutChartsSourceTopology : TopologicalSpace
    (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
  schemeAnalyticPointTopology _
local instance cutChartsSourceCharts : ChartedSpace (ComplexModel (n - 1))
    (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
  schemeAnalyticTNChartedSpace _ _
local instance cutChartsSourceManifold : IsComplexManifold (n - 1)
    (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
  schemeAnalyticTN_isComplexManifold _ _

variable (hread : ∀ (j : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens j →
    sectionCoefficient
      (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)).val
        D.cuttingSection p =
      schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) p)
include hread

/-- The SAME actual whole point homeomorphism is holomorphic from the
ORIGINAL algebraic zero scheme native TN charts into actual member charts. -/
theorem regularCutPointHomeomorph_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel (n - 1)) ∞
      (regularCutPointHomeomorph f n E a H hK D σ hread) := by
  let i := sectionZeroι (a.tensorPower D.power) σ
  let e := regularCutPointHomeomorph f n E a H hK D σ hread
  have hrange : ∀ q : SchemeComplexPoint (i ≫ f),
      schemeComplexPointMap (i ≫ f) f i rfl q ∈ D.carrier := fun q => (e q).property
  have h := SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.sub_le n 1) D.regularAtDim
    (schemeComplexPointMap_contMDiff f i (n - 1) n ∞) hrange
  have heq : (fun q : SchemeComplexPoint (i ≫ f) =>
      (⟨schemeComplexPointMap (i ≫ f) f i rfl q, hrange q⟩ : D.carrier)) = e := by
    funext q
    apply Subtype.ext
    rfl
  exact heq ▸ h

/-- Tangent injection is DERIVED from the ACTUAL original algebraic closed
immersion and actual member inclusion chain rule, not assumed. -/
theorem regularCutPointHomeomorph_mfderiv_injective
    (q : SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel (n - 1))
      (regularCutPointHomeomorph f n E a H hK D σ hread) q) := by
  let i := sectionZeroι (a.tensorPower D.power) σ
  let e := regularCutPointHomeomorph f n E a H hK D σ hread
  have he := regularCutPointHomeomorph_contMDiff f n E a H hK D σ hread
  have hι := D.inclusion.contMDiff
  have hcomp : (Subtype.val : D.carrier → SchemeComplexPoint f) ∘ e =
      schemeComplexPointMap (i ≫ f) f i rfl := by funext q; rfl
  have hchain := mfderiv_comp q (hι.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))
  have hchain' : mfderiv 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel n)
      (schemeComplexPointMap (i ≫ f) f i rfl) q =
      (mfderiv 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel n)
        (Subtype.val : D.carrier → SchemeComplexPoint f) (e q)).comp
        (mfderiv 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel (n - 1)) e q) := by
    rw [← hcomp]
    exact hchain
  have hi := SGPT.NAPotential.NativeSchemeImmersion.closedImmersion_mfderiv_injective
    (i ≫ f) f i rfl (n - 1) n q
  intro v w hvw
  apply hi
  rw [hchain']
  exact congrArg (mfderiv 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel n)
    (Subtype.val : D.carrier → SchemeComplexPoint f) (e q)) hvw

/-- The LITERAL existing inverse is holomorphic for the actual member and
ORIGINAL algebraic native TN chart structures. -/
theorem regularCutPointHomeomorph_symm_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel (n - 1)) ∞
      (regularCutPointHomeomorph f n E a H hK D σ hread).symm :=
  homeomorph_symm_contMDiff_of_mfderiv_injective _
    (regularCutPointHomeomorph_contMDiff f n E a H hK D σ hread)
    (regularCutPointHomeomorph_mfderiv_injective f n E a H hK D σ hread)

/-- Genuine same whole-cut biholomorphism, retaining BOTH original native
chart structures and the actual original inclusion point function. -/
def regularCutNativeDiffeomorph :
    Diffeomorph 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel (n - 1))
      (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) D.carrier ∞ where
  toEquiv := (regularCutPointHomeomorph f n E a H hK D σ hread).toEquiv
  contMDiff_toFun := regularCutPointHomeomorph_contMDiff f n E a H hK D σ hread
  contMDiff_invFun := regularCutPointHomeomorph_symm_contMDiff f n E a H hK D σ hread

/-- The biholomorphic identification uses the ACTUAL original scheme
closed-immersion point map, not a newly chosen analytic substitute. -/
theorem regularCutNativeDiffeomorph_val
    (q : SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :
    (regularCutNativeDiffeomorph f n E a H hK D σ hread q).val =
      schemeComplexPointMap (sectionZeroι (a.tensorPower D.power) σ ≫ f) f
        (sectionZeroι (a.tensorPower D.power) σ) rfl q := rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
