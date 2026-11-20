import SGPT.Projective.AlgebraicNativeCutSmooth

/-! The ENTIRE actual original algebraic regular cut and the SAME native
regular member, through the actual original inclusion point map.
Blueprint: algebraic-native-whole-cut.tex. -/
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
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance wholeCutPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance wholeCutPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance wholeCutPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

section SameCut
variable (hK : (H.curvature a).val.IsKahler)
  (D : NativeRegularCut (schemeNativePositiveLine f n E a H hK))
  (σ : bundlePowerGlobalSections L D.power)
  (hread : ∀ (j : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens j →
    sectionCoefficient
      (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)).val
        D.cuttingSection p =
      schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) p)
include hread

/-- Literal original zero support equals the SAME entire actual regular
member, using the proved original same-section coefficient readers. -/
theorem regularCut_support_iff_member (p : SchemeComplexPoint f) :
    schemeComplexPointImage f p ∈ (sectionZeroIdealSheaf (a.tensorPower D.power) σ).support ↔
      p ∈ D.carrier := by
  obtain ⟨j, hj⟩ := a.covers (schemeComplexPointImage f p)
  have hsupport := sectionZero_support_iff_coefficient_zero f n E (a.tensorPower D.power) σ
    ((a.frame j).tensorPower D.power) p hj
  let B := positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hj _
  have hzero : sectionCoefficient B.Fiber e.val D.cuttingSection p = 0 ↔ D.cuttingSection p = 0 :=
    (e.val.linearEquivAt ℂ p he).map_eq_zero_iff
  have hcoeff : sectionCoefficient B.Fiber e.val D.cuttingSection p =
      schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) p := hread j p hj
  rw [hcoeff] at hzero
  exact hsupport.trans (hzero.trans (linearSection_zero_iff B D.sections D.generated D.hyperplane p))

/-- The ACTUAL original closed-immersion point map has exactly the SAME
whole native regular member as its range, with all components retained. -/
theorem regularCutPoint_range :
    Set.range (schemeComplexPointMap (sectionZeroι (a.tensorPower D.power) σ ≫ f) f
      (sectionZeroι (a.tensorPower D.power) σ) rfl) = D.carrier := by
  rw [closedImmersionComplexPointMap_range]
  change {p : SchemeComplexPoint f | schemeComplexPointImage f p ∈
    Set.range (sectionZeroIdealSheaf (a.tensorPower D.power) σ).subschemeι} = D.carrier
  rw [Scheme.IdealSheafData.range_subschemeι]
  ext p
  exact regularCut_support_iff_member f n E a H hK D σ hread p

/-- Genuine WHOLE same-cut homeomorphism; its map is the actual original
algebraic closed immersion point map. No native member is replaced. -/
def regularCutPointHomeomorph :
    letI : TopologicalSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
      schemeAnalyticPointTopology (sectionZeroι (a.tensorPower D.power) σ ≫ f)
    SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f) ≃ₜ D.carrier := by
  let := schemeAnalyticPointTopology (sectionZeroι (a.tensorPower D.power) σ ≫ f)
  exact (closedImmersionComplexPointMap_isClosedEmbedding f
    (sectionZeroι (a.tensorPower D.power) σ)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (regularCutPoint_range f n E a H hK D σ hread))

/-- The same-cut homeomorphism retains the ACTUAL original point map. -/
theorem regularCutPointHomeomorph_val
    (q : SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :
    (regularCutPointHomeomorph f n E a H hK D σ hread q).val =
      schemeComplexPointMap (sectionZeroι (a.tensorPower D.power) σ ≫ f) f
        (sectionZeroι (a.tensorPower D.power) σ) rfl q := rfl
end SameCut

/-- Unconditional original positive-metric producer of the SAME D, sigma,
smooth actual original algebraic zero scheme and entire actual native
point homeomorphism, with actual original point map retained. -/
theorem exists_same_algebraic_regular_cut_whole (hn : 0 < n)
    (hK : (H.curvature a).val.IsKahler) :
    ∃ D : NativeRegularCut (schemeNativePositiveLine f n E a H hK),
      ∃ σ : bundlePowerGlobalSections L D.power,
        (∀ (j : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens j →
          sectionCoefficient
            (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
            (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)).val
              D.cuttingSection p =
            schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) p) ∧
        (∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
          (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower D.power) σ)).mem p g ↔
            (nativeSectionIdeal
              (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)) D.cuttingSection).mem p g) ∧
        Smooth (sectionZeroι (a.tensorPower D.power) σ ≫ f) ∧
        (letI : TopologicalSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
          schemeAnalyticPointTopology (sectionZeroι (a.tensorPower D.power) σ ≫ f)
        ∃ e : SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f) ≃ₜ D.carrier,
          ∀ q, (e q).val = schemeComplexPointMap (sectionZeroι (a.tensorPower D.power) σ ≫ f) f
            (sectionZeroι (a.tensorPower D.power) σ) rfl q) := by
  obtain ⟨D, σ, hread, hideal, hsmooth⟩ := exists_same_algebraic_regular_cut_smooth f n E a H hn hK
  exact ⟨D, σ, hread, hideal, hsmooth,
    regularCutPointHomeomorph f n E a H hK D σ hread,
    regularCutPointHomeomorph_val f n E a H hK D σ hread⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
