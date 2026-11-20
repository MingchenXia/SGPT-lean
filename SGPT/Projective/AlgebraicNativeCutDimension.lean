import SGPT.Projective.AlgebraicNativeWholeCut
import SGPT.Projective.PrincipalCotangentRank
import SGPT.Projective.AlgebraicRelativeDimensionCriterion

/-! The ACTUAL original same algebraic regular cut has genuine relative
dimension n−1. Blueprint: algebraic-native-cut-dimension.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Module
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance cutDimensionPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance cutDimensionPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance cutDimensionPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance cutDimensionStalkAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) :=
  stalkComplexAlgebra f (schemeComplexPointImage f p)
local instance cutDimensionPointAlgebra (p : SchemeComplexPoint f) :
    Algebra (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ :=
  (schemeComplexPointStalkEval f p).toAlgebra

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

/-- For ANY fixed SAME actual regular cut, its original algebraic section
reader and genuine regularity manufacture actual nonzero stalk derivatives.
No independently chosen cut or chart is identified. -/
theorem regularCut_stalk_derivation (j : a.I) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ a.opens j) (hx : p ∈ D.carrier) :
    ∃ δ : Derivation ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ,
      δ (X.presheaf.germ (a.opens j) (schemeComplexPointImage f p) hp
        (algCoef (a.frame j) D.power σ)) ≠ 0 := by
  let B := positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hp _
  let c := complexChartAt (n := n) p
  have hc : p ∈ c.val.source := mem_complexChartAt_source p
  have hD := regularSection_chart_derivative_ne_zero B D.sections D.generated D.hyperplane
    D.regular e p he hx c hc
  let U : Set (SchemeComplexPoint f) := schemeComplexPointImage f ⁻¹' (a.opens j : Set X)
  have hU : IsOpen U := (a.opens j).isOpen.preimage (schemeComplexPointImage_continuous f)
  have hsymm : ContinuousAt c.val.symm (c.val p) := c.val.continuousAt_symm (c.val.map_source hc)
  have heq : (sectionCoefficient B.Fiber e.val D.cuttingSection ∘ c.val.symm) =ᶠ[𝓝 (c.val p)]
      (schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) ∘ c.val.symm) := by
    have hpU : c.val.symm (c.val p) ∈ U := by rwa [c.val.left_inv hc]
    filter_upwards [hsymm.preimage_mem_nhds (hU.mem_nhds hpU)] with z hz
    exact hread j (c.val.symm z) hz
  apply exists_nativeStalkDerivation_regular_ne_zero f n E (a.opens j)
    (algCoef (a.frame j) D.power σ) p hp
  rw [← heq.fderiv_eq]
  exact hD

/-- The ACTUAL same original zero-stalk cotangent rank is n−1, from the
genuine original principal relation and actual nonzero derivative. -/
theorem regularCutPoint_cotangent_finrank
    [Smooth (sectionZeroι (a.tensorPower D.power) σ ≫ f)]
    (q : SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :
    letI := stalkComplexAlgebra (sectionZeroι (a.tensorPower D.power) σ ≫ f)
      (schemeComplexPointImage (sectionZeroι (a.tensorPower D.power) σ ≫ f) q)
    finrank ((sectionZeroSubscheme (a.tensorPower D.power) σ).presheaf.stalk
      (schemeComplexPointImage (sectionZeroι (a.tensorPower D.power) σ ≫ f) q))
      Ω[(sectionZeroSubscheme (a.tensorPower D.power) σ).presheaf.stalk
        (schemeComplexPointImage (sectionZeroι (a.tensorPower D.power) σ ≫ f) q)⁄ℂ] = n - 1 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let i := sectionZeroι (a.tensorPower D.power) σ
  let z := schemeComplexPointImage (i ≫ f) q
  let p := schemeComplexPointMap (i ≫ f) f i rfl q
  have hpimage : schemeComplexPointImage f p = i z := rfl
  obtain ⟨j, hj⟩ := a.covers (schemeComplexPointImage f p)
  have hsupp : schemeComplexPointImage f p ∈ (sectionZeroIdealSheaf (a.tensorPower D.power) σ).support := by
    have hz : i z ∈ (sectionZeroIdealSheaf (a.tensorPower D.power) σ).support := z.property
    exact hpimage.symm ▸ hz
  have hx : p ∈ D.carrier := (regularCut_support_iff_member f n E a H hK D σ hread p).mp hsupp
  let A := X.presheaf.stalk (schemeComplexPointImage f p)
  let B := (sectionZeroSubscheme (a.tensorPower D.power) σ).presheaf.stalk z
  let := stalkComplexAlgebra f (schemeComplexPointImage f p)
  let := stalkComplexAlgebra (i ≫ f) z
  let tau : A →+* B := (i.stalkMap z).hom
  let : Algebra A B := tau.toAlgebra
  let : Algebra A ℂ := (schemeComplexPointStalkEval f p).toAlgebra
  let : Algebra B ℂ := (schemeComplexPointStalkEval (i ≫ f) q).toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c =>
    (originalStalk_algebraMap_comp f i z c).symm
  have heval : schemeComplexPointStalkEval f p =
      (schemeComplexPointStalkEval (i ≫ f) q).comp tau :=
    schemeComplexPointStalkEval_comp (i ≫ f) f i rfl q
  let : IsScalarTower A B ℂ := IsScalarTower.of_algebraMap_eq fun r => RingHom.congr_fun heval r
  let : IsScalarTower ℂ A ℂ := originalPointStalk_scalarTower f n p
  obtain ⟨_, _, hfin, hfree⟩ := originalSmoothStalk_differentials f (schemeComplexPointImage f p)
  let : Module.Finite A Ω[A⁄ℂ] := hfin
  let : Module.Free A Ω[A⁄ℂ] := hfree
  obtain ⟨_, _, hfinB, hfreeB⟩ := originalSmoothStalk_differentials (i ≫ f) z
  let : Module.Finite B Ω[B⁄ℂ] := hfinB
  let : Module.Free B Ω[B⁄ℂ] := hfreeB
  let g : A := X.presheaf.germ (a.opens j) (schemeComplexPointImage f p) hj
    (algCoef (a.frame j) D.power σ)
  have hker : RingHom.ker tau = Ideal.span {g} := sectionZero_stalk_kernel (a.tensorPower D.power) σ z j hj
  obtain ⟨δ, hδ⟩ := regularCut_stalk_derivation f n E a H hK D σ hread j p hj hx
  have hdim := PrincipalCotangentRank.principal_quotient_cotangent_finrank
    (i.stalkMap_surjective z) g hker δ hδ
  rw [Module.finrank_baseChange, originalStalk_cotangent_finrank f n (schemeComplexPointImage f p)] at hdim
  exact hdim
end SameCut

/-- Actual positive original metric -> SAME algebraic/native whole cut,
with genuine original zero-scheme smooth relative dimension n−1. -/
theorem exists_same_algebraic_regular_cut_dimension (hn : 0 < n)
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
        SmoothOfRelativeDimension (n - 1) (sectionZeroι (a.tensorPower D.power) σ ≫ f) ∧
        (letI : TopologicalSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f)) :=
          schemeAnalyticPointTopology (sectionZeroι (a.tensorPower D.power) σ ≫ f)
        ∃ e : SchemeComplexPoint (sectionZeroι (a.tensorPower D.power) σ ≫ f) ≃ₜ D.carrier,
          ∀ q, (e q).val = schemeComplexPointMap (sectionZeroι (a.tensorPower D.power) σ ≫ f) f
            (sectionZeroι (a.tensorPower D.power) σ) rfl q) := by
  obtain ⟨D, σ, hread, hideal, hsmooth, hwhole⟩ :=
    exists_same_algebraic_regular_cut_whole f n E a H hn hK
  let : Smooth (sectionZeroι (a.tensorPower D.power) σ ≫ f) := hsmooth
  refine ⟨D, σ, hread, hideal, ?_, hwhole⟩
  exact smoothOfRelativeDimension_of_complexPoint_cotangent_finrank
    (sectionZeroι (a.tensorPower D.power) σ ≫ f) (n - 1)
      (regularCutPoint_cotangent_finrank f n E a H hK D σ hread)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
