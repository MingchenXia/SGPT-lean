import SGPT.Projective.NativeRightUnitSections
import SGPT.GAGA.H0LSections
import SGPT.NAPotential.GAGAMult2SectionIdeal
import SGPT.Bergman.SiuNativeSectionCartier

/-! GAGA preserves the SAME actual native positive-power section and its
ENTIRE original principal ideal. Blueprint: algebraic-native-ci-cuts.tex. -/
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

local instance nativeCIPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance nativeCIPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance nativeCIPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- EVERY section in the SAME literal native positive power algebraizes
in the SAME original sheaf tensor power. The coefficient AND full original
section-zero germ ideal identities are proved, not certificate inputs. -/
theorem exists_algebraic_positivePower_section (k : ℕ)
    (s : HolomorphicSections (n := n)
      (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber) :
    ∃ σ : bundlePowerGlobalSections L (k + 1),
      (∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
        sectionCoefficient (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber
          (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val s p =
            schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) (k + 1) σ) p) ∧
      ∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
        (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower (k + 1)) σ)).mem p g ↔
          (nativeSectionIdeal (positivePower (schemeHermitianLineBundle f n E a H) k) s).mem p g := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let B := schemeHermitianLineBundle f n E a H
  let T := positivePower B k
  let t : twistedSections B unit (k + 1) := rightUnitSectionInv T s
  obtain ⟨σ, hσ⟩ := SGPT.GAGA.H0L.exists_isAnalytificationOf a H t
  have hread (i : a.I) (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ a.opens i) :
      sectionCoefficient T.Fiber
        (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val s p =
          schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) (k + 1) σ) p := by
    let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
    have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hp k
    have hc := hσ i p hp
    change ((tensorAtlasFrame e unitAtlasFrame).val.continuousLinearMapAt ℂ p)
      (rightUnitSectionInv T s p) = _ at hc
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℂ
      (tensorAtlasFrame e unitAtlasFrame).val ⟨he, Set.mem_univ p⟩] at hc
    exact (rightUnitSectionInv_coordinate T s e he).symm.trans hc
  refine ⟨σ, hread, ?_⟩
  intro p g
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
  rw [analytificationIdeal_sectionZeroIdealSheaf_iff f n E a (k + 1) σ i hi g,
    nativeSectionIdeal_frame T s e he g]
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
    (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  constructor
  · intro hg
    apply SGPT.NAPotential.GAGAMult.IsInSpanAt.of_eventuallyEq hg
    rintro _ rfl
    refine ⟨sectionCoefficient T.Fiber e.val s, rfl, ?_⟩
    filter_upwards [hO.mem_nhds hi] with y hy
    exact (hread i y hy).symm
  · intro hg
    apply SGPT.NAPotential.GAGAMult.IsInSpanAt.of_eventuallyEq hg
    rintro _ rfl
    refine ⟨schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) (k + 1) σ), rfl, ?_⟩
    filter_upwards [hO.mem_nhds hi] with y hy
    exact hread i y hy

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
