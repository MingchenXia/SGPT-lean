import SGPT.Projective.AlgebraicNativeRegularCut
import SGPT.Projective.NativeCITower
import SGPT.LineBundle.AmplePositiveMetric

/-! The SAME original algebraic positive metric manufactures a genuine
whole native regular cut and its original algebraic section/ideal.
Blueprint: algebraic-native-cut-producer.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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
open SGPT.BDivisor.NSKodaira

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance algNativeCutPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance algNativeCutPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance algNativeCutPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Literal associated native positive bundle of the ORIGINAL physical
algebraic metric, with its actual original own Chern form. -/
def schemeNativePositiveLine (hK : (H.curvature a).val.IsKahler) :
    NativePositiveLine n (SchemeComplexPoint f) where
  bundle := schemeHermitianLineBundle f n E a H
  smooth := isSourceSmoothHermitianMetric_schemeHermitianLineBundle f n E a H
  curvature := H.curvature a
  own := isOwnFirstChernForm_schemeHermitianLineBundle f n E a H
  positive := hK

private theorem algCoef_degree_cast {r t : ℕ} (h : r = t)
    {U : X.Opens} (α : LocalBundleFrame L U) (σ : bundlePowerGlobalSections L r) :
    algCoef α t (h ▸ σ : bundlePowerGlobalSections L t) = algCoef α r σ := by
  cases h
  rfl

private theorem sectionZeroIdeal_degree_cast {r t : ℕ} (h : r = t)
    (σ : bundlePowerGlobalSections L r) :
    sectionZeroIdealSheaf (a.tensorPower t) (h ▸ σ : bundlePowerGlobalSections L t) =
      sectionZeroIdealSheaf (a.tensorPower r) σ := by
  cases h
  rfl

/-- Actual SAME original positive metric -> actual native regular cut ->
actual section of SAME original algebraic power with exact coefficient and
whole principal-ideal readback. No desired-output comparison is input. -/
theorem exists_same_algebraic_regular_cut (hn : 0 < n)
    (hK : (H.curvature a).val.IsKahler) :
    ∃ D : NativeRegularCut (schemeNativePositiveLine f n E a H hK),
      ∃ σ : bundlePowerGlobalSections L D.power,
        (∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
          sectionCoefficient
            (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
            (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) (D.power - 1)).val
              D.cuttingSection p =
            schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) D.power σ) p) ∧
        ∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
          (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower D.power) σ)).mem p g ↔
            (nativeSectionIdeal
              (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)) D.cuttingSection).mem p g := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨D⟩ := exists_nativeRegularCut hn (schemeNativePositiveLine f n E a H hK)
  obtain ⟨σ, hread, hideal⟩ := exists_algebraic_positivePower_section f n E a H
    (D.power - 1) D.cuttingSection
  have hq : D.power - 1 + 1 = D.power := Nat.sub_add_cancel (Nat.succ_le_of_lt D.power_pos)
  let σ' : bundlePowerGlobalSections L D.power := hq ▸ σ
  refine ⟨D, σ', ?_, ?_⟩
  · intro i p hp
    change _ = schemeOpenRegularFunction f n E (a.opens i)
      (algCoef (a.frame i) D.power (hq ▸ σ : bundlePowerGlobalSections L D.power)) p
    rw [algCoef_degree_cast]
    exact hread i p hp
  · intro p g
    change (analytificationIdeal f n E
      (sectionZeroIdealSheaf (a.tensorPower D.power) (hq ▸ σ : bundlePowerGlobalSections L D.power))).mem p g ↔ _
    rw [sectionZeroIdeal_degree_cast]
    exact hideal p g

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
