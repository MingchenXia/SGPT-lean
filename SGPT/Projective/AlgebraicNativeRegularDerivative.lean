import SGPT.Projective.AlgebraicNativeStalkDerivation
import SGPT.Projective.AlgebraicNativeCutProducer
import SGPT.Projective.NativeRegularSectionMultiplicity

/-! Actual nonzero original algebraic normal derivatives of the SAME
manufactured native regular cut. Blueprint: algebraic-native-regular-derivative.tex. -/
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
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira

section Charts
variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Nonvanishing of the actual holomorphic derivative transports through
the genuine chart overlap, without identifying independently chosen charts. -/
theorem chart_derivative_ne_zero_transport (g : Y → ℂ) (x : Y)
    (hg : HolomorphicAt n g x) (c d : ComplexChart n Y)
    (hc : x ∈ c.val.source) (hd : x ∈ d.val.source)
    (hD : fderiv ℂ (g ∘ c.val.symm) (c.val x) ≠ 0) :
    fderiv ℂ (g ∘ d.val.symm) (d.val x) ≠ 0 := by
  have hz : c.val x ∈ coordinateDomain (id : Y → Y) c d := mem_coordinateDomain hc hd
  have hT : DifferentiableAt ℂ (coordinateMap (id : Y → Y) c d) (c.val x) :=
    (coordinateMap_contDiffAt contMDiff_id c d hz).differentiableAt (by simp)
  have hF : DifferentiableAt ℂ (g ∘ d.val.symm) (d.val x) :=
    (DerivativeIdeal.eventually_differentiableAt_comp_symm d hd hg).self_of_nhds
  have heq : (g ∘ d.val.symm) ∘ coordinateMap (id : Y → Y) c d =ᶠ[𝓝 (c.val x)]
      g ∘ c.val.symm := by
    filter_upwards [(coordinateDomain_isOpen contMDiff_id c d).mem_nhds hz] with z hz
    change g (d.val.symm (d.val (c.val.symm z))) = g (c.val.symm z)
    have hzd : c.val.symm z ∈ d.val.source := hz.2
    exact congrArg g (d.val.left_inv hzd)
  have hTval : coordinateMap (id : Y → Y) c d (c.val x) = d.val x := coordinateMap_at hc
  intro hzero
  apply hD
  have hF' : DifferentiableAt ℂ (g ∘ d.val.symm)
      (coordinateMap (id : Y → Y) c d (c.val x)) := hTval.symm ▸ hF
  rw [← heq.fderiv_eq, fderiv_comp (c.val x) hF' hT, hTval, hzero]
  exact ContinuousLinearMap.zero_comp _

/-- The actual regular member's SAME coefficient has nonzero derivative
in any prescribed genuine chart at the same point. -/
theorem regularSection_chart_derivative_ne_zero {N : ℕ}
    (L : HermitianHolomorphicLineBundle.{0,0} n Y)
    (s : Fin (N + 1) → HolomorphicSections (n := n) L.Fiber)
    (hgen : ∀ y, ∃ i, s i y ≠ 0) (l : HyperplaneSpace N)
    (hl : IsSmoothHypersurfaceMember n (sourceNativeFiniteSectionProjectiveMap L s hgen) l)
    (e : AtlasFrame L) (x : Y) (he : x ∈ e.val.baseSet)
    (hx : x ∈ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l)
    (d : ComplexChart n Y) (hd : x ∈ d.val.source) :
    fderiv ℂ (sectionCoefficient L.Fiber e.val (linearSection L s l) ∘ d.val.symm)
      (d.val x) ≠ 0 := by
  obtain ⟨c, hc, hD⟩ := exists_chart_coefficient_derivative_ne_zero L s hgen l hl e x he hx
  exact chart_derivative_ne_zero_transport _ x
    (nativeSectionCoefficient_holomorphicAt L (linearSection L s l) e he) c d hc hd hD
end Charts

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance regularDerivativePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance regularDerivativePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance regularDerivativePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance regularDerivativeStalkAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) :=
  stalkComplexAlgebra f (schemeComplexPointImage f p)
local instance regularDerivativePointAlgebra (p : SchemeComplexPoint f) :
    Algebra (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ :=
  (schemeComplexPointStalkEval f p).toAlgebra

/-- SAME original algebraic positive metric manufactures a full actual
regular cut, its SAME original algebraic power section and genuinely
nonzero original-stalk derivations at EVERY member point/frame. -/
theorem exists_same_algebraic_regular_cut_derivations (hn : 0 < n)
    (hK : (H.curvature a).val.IsKahler) :
    ∃ D : NativeRegularCut (schemeNativePositiveLine f n E a H hK),
      ∃ σ : bundlePowerGlobalSections L D.power,
        (∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
          sectionCoefficient
            (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
            (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) (D.power - 1)).val
              D.cuttingSection p =
            schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) D.power σ) p) ∧
        (∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
          (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower D.power) σ)).mem p g ↔
            (nativeSectionIdeal
              (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)) D.cuttingSection).mem p g) ∧
        ∀ (i : a.I) (p : SchemeComplexPoint f)
          (hp : schemeComplexPointImage f p ∈ a.opens i), p ∈ D.carrier →
          ∃ δ : Derivation ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ,
            δ (X.presheaf.germ (a.opens i) (schemeComplexPointImage f p) hp
              (algCoef (a.frame i) D.power σ)) ≠ 0 := by
  obtain ⟨D, σ, hread, hideal⟩ := exists_same_algebraic_regular_cut f n E a H hn hK
  refine ⟨D, σ, hread, hideal, ?_⟩
  intro i p hp hx
  let B := positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) (D.power - 1)
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hp _
  let c := complexChartAt (n := n) p
  have hc : p ∈ c.val.source := mem_complexChartAt_source p
  have hD := regularSection_chart_derivative_ne_zero B D.sections D.generated D.hyperplane
    D.regular e p he hx c hc
  let U : Set (SchemeComplexPoint f) := schemeComplexPointImage f ⁻¹' (a.opens i : Set X)
  have hU : IsOpen U := (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  have hsymm : ContinuousAt c.val.symm (c.val p) := c.val.continuousAt_symm (c.val.map_source hc)
  have heq : (sectionCoefficient B.Fiber e.val D.cuttingSection ∘ c.val.symm) =ᶠ[𝓝 (c.val p)]
      (schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) D.power σ) ∘ c.val.symm) := by
    have hpU : c.val.symm (c.val p) ∈ U := by rwa [c.val.left_inv hc]
    filter_upwards [hsymm.preimage_mem_nhds (hU.mem_nhds hpU)] with z hz
    exact hread i (c.val.symm z) hz
  apply exists_nativeStalkDerivation_regular_ne_zero f n E (a.opens i)
    (algCoef (a.frame i) D.power σ) p hp
  rw [← heq.fderiv_eq]
  exact hD

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
