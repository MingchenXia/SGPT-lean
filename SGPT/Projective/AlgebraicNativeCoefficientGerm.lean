import SGPT.Projective.AlgebraicNativeSectionForward
import SGPT.Projective.AlgebraicCurveSectionLength

/-! Exact SAME physical native coefficient/original algebraic germ readback.
Blueprint: algebraic-native-coefficient-germ.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult
open SGPT.BDivisor.NSKodaira
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped Topology Manifold

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
local instance nativeGermPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance nativeGermPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance nativeGermPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The literal physical coefficient germ of the SAME manufactured native section. -/
def algebraicNativeCoefficientGerm (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i : a.I) (p : SchemeComplexPoint f) (hi : schemeComplexPointImage f p ∈ a.opens i) :
    NativeHolGerm n (SchemeComplexPoint f) p :=
  NativeHolGerm.mk
    (sectionCoefficient (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val
      (nativeSectionOfAlgebraicPositivePower f n E a H k σ))
    (nativeSectionCoefficient_holomorphicAt _ _ _ (mem_positivePowerAtlasFrame_baseSet _ hi k))

/-- Whole physical coefficient germ equals the SAME original coefficient stalk image. -/
theorem algebraicNativeCoefficientGerm_eq (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i : a.I) (p : SchemeComplexPoint f) (hi : schemeComplexPointImage f p ∈ a.opens i) :
    algebraicNativeCoefficientGerm f n E a H k σ i p hi =
      schemeNativeStalkGerm f n p
        (sectionStalkCoefficient (a.tensorPower (k + 1)) σ i (schemeComplexPointImage f p) hi) := by
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
    (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  have hEq : sectionCoefficient (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val
      (nativeSectionOfAlgebraicPositivePower f n E a H k σ) =ᶠ[𝓝 p]
      schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) (k + 1) σ) := by
    filter_upwards [hO.mem_nhds hi] with y hy
    exact nativeSectionOfAlgebraicPositivePower_frame f n E a H k σ i hy
  have hG : algebraicNativeCoefficientGerm f n E a H k σ i p hi =
      NativeHolGerm.mk (schemeOpenRegularFunction f n E (a.opens i)
        (algCoef (a.frame i) (k + 1) σ))
        (schemeOpenRegularFunction_holomorphicAt f n E (a.opens i)
          (algCoef (a.frame i) (k + 1) σ) p hi) :=
    NativeHolGerm.mk_eq_mk_iff.mpr hEq
  exact hG.trans (schemeOpenRegularFunction_germ f n E (a.opens i)
    (algCoef (a.frame i) (k + 1) σ) p hi)

/-- SAME preferred native-chart model germ of the actual physical coefficient. -/
theorem algebraicNativeCoefficientGerm_model (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i : a.I) (p : SchemeComplexPoint f) (hi : schemeComplexPointImage f p ∈ a.opens i) :
    NativeHolGerm.chartEquiv p (algebraicNativeCoefficientGerm f n E a H k σ i p hi) =
      stalkToModel f n p
        (sectionStalkCoefficient (a.tensorPower (k + 1)) σ i (schemeComplexPointImage f p) hi) := by
  rw [algebraicNativeCoefficientGerm_eq]
  rfl

/-- Genuine original integrality and nonzero section imply actual physical germ nonzero. -/
theorem algebraicNativeCoefficientGerm_ne_zero [IsIntegral X]
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0)
    (i : a.I) (p : SchemeComplexPoint f) (hi : schemeComplexPointImage f p ∈ a.opens i) :
    algebraicNativeCoefficientGerm f n E a H k σ i p hi ≠ 0 := by
  rw [algebraicNativeCoefficientGerm_eq]
  exact (map_ne_zero_iff _ (schemeNativeStalkGerm_injective f n p)).mpr
    (sectionStalkCoefficient_ne_zero (a.tensorPower (k + 1)) σ hσ i _ hi)

/-- EVERY nonempty actual original open contains a nonzero value of the SAME native section. -/
theorem nativeSectionOfAlgebraicPositivePower_dense [IsIntegral X]
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0) :
    ∀ U : Set (SchemeComplexPoint f), IsOpen U → U.Nonempty →
      ∃ y ∈ U, nativeSectionOfAlgebraicPositivePower f n E a H k σ y ≠ 0 := by
  intro U hU hUne
  obtain ⟨p, hp⟩ := hUne
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  by_contra h
  push Not at h
  apply algebraicNativeCoefficientGerm_ne_zero f n E a H k σ hσ i p hi
  change NativeHolGerm.mk _ _ =
    NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0)
  apply NativeHolGerm.mk_eq_mk_iff.mpr
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
    (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hU.mem_nhds hp, hO.mem_nhds hi] with y hyU hyi
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
  have he : y ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hyi k
  change e.val.linearEquivAt ℂ y he
    (nativeSectionOfAlgebraicPositivePower f n E a H k σ y) = 0
  rw [h y hyU, map_zero]

end SGPT.Projective.NumEq.AlgebraicCurveDegree
