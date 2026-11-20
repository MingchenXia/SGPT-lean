import SGPT.Projective.AlgebraicNativeSectionForward

/-! Full ideal, literal GAGA reader and faithfulness of the ACTUAL fixed
original algebraic section's manufactured native section.
Blueprint: algebraic-native-section-readback.tex. -/
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
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich SGPT.GAGA.H0L
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.BDivisor.NSKodaira

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance readbackPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance readbackPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance readbackPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The original GAGA reader is PROVED for the SAME manufactured native
section, never supplied as a certificate input. -/
theorem nativeSectionOfAlgebraicPositivePower_isAnalytificationOf
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) :
    IsAnalytificationOf f n E a H (j := k + 1)
      (rightUnitSectionInv (positivePower (schemeHermitianLineBundle f n E a H) k)
        (nativeSectionOfAlgebraicPositivePower f n E a H k σ)) σ := by
  intro i p hp
  let B := positivePower (schemeHermitianLineBundle f n E a H) k
  let s := nativeSectionOfAlgebraicPositivePower f n E a H k σ
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hp k
  change ((tensorAtlasFrame e unitAtlasFrame).val.continuousLinearMapAt ℂ p)
    (rightUnitSectionInv B s p) = _
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℂ
    (tensorAtlasFrame e unitAtlasFrame).val ⟨he, Set.mem_univ p⟩]
  exact (rightUnitSectionInv_coordinate B s e he).trans
    (nativeSectionOfAlgebraicPositivePower_frame f n E a H k σ i hp)

/-- FULL unchanged original algebraic section-zero ideal equals the actual
native physical section ideal at EVERY original point and germ. -/
theorem nativeSectionOfAlgebraicPositivePower_ideal
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ) :
    (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower (k + 1)) σ)).mem p g ↔
      (nativeSectionIdeal (positivePower (schemeHermitianLineBundle f n E a H) k)
        (nativeSectionOfAlgebraicPositivePower f n E a H k σ)).mem p g := by
  let B := positivePower (schemeHermitianLineBundle f n E a H) k
  let s := nativeSectionOfAlgebraicPositivePower f n E a H k σ
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
  rw [analytificationIdeal_sectionZeroIdealSheaf_iff f n E a (k + 1) σ i hi g,
    nativeSectionIdeal_frame B s e he g]
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
    (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  constructor
  · intro hg
    apply SGPT.NAPotential.GAGAMult.IsInSpanAt.of_eventuallyEq hg
    rintro _ rfl
    refine ⟨sectionCoefficient B.Fiber e.val s, rfl, ?_⟩
    filter_upwards [hO.mem_nhds hi] with y hy
    exact (nativeSectionOfAlgebraicPositivePower_frame f n E a H k σ i hy).symm
  · intro hg
    apply SGPT.NAPotential.GAGAMult.IsInSpanAt.of_eventuallyEq hg
    rintro _ rfl
    refine ⟨algebraicPowerCoefficient f n E a k σ i, rfl, ?_⟩
    filter_upwards [hO.mem_nhds hi] with y hy
    exact nativeSectionOfAlgebraicPositivePower_frame f n E a H k σ i hy

/-- The manufactured native section faithfully retains the SAME original
algebraic section. This is proved by actual original coefficient faithfulness. -/
theorem nativeSectionOfAlgebraicPositivePower_injective (k : ℕ) :
    Function.Injective (nativeSectionOfAlgebraicPositivePower f n E a H k) := by
  intro σ τ h
  apply atlasPowerGlobalCoefficients_ext a (k + 1)
  intro i
  apply eq_of_schemeOpenRegularFunction_eq f E n _ _
  intro p hp
  exact (nativeSectionOfAlgebraicPositivePower_frame f n E a H k σ i hp).symm.trans
    ((congrArg (fun s => sectionCoefficient
      (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val s p) h).trans
        (nativeSectionOfAlgebraicPositivePower_frame f n E a H k τ i hp))

/-- The original algebraic zero section manufactures the actual native zero section. -/
theorem nativeSectionOfAlgebraicPositivePower_zero (k : ℕ) :
    nativeSectionOfAlgebraicPositivePower f n E a H k (0 : bundlePowerGlobalSections L (k + 1)) = 0 := by
  ext p
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  let B := positivePower (schemeHermitianLineBundle f n E a H) k
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
  apply (e.val.linearEquivAt ℂ p he).injective
  have hc := nativeSectionOfAlgebraicPositivePower_frame f n E a H k 0 i hi
  simp only [algebraicPowerCoefficient, algCoef, map_zero, schemeOpenRegularFunction, dif_pos hi] at hc
  exact hc.trans (map_zero _).symm

/-- Nonzero ORIGINAL algebraic sections yield nonzero ACTUAL native sections. -/
theorem nativeSectionOfAlgebraicPositivePower_ne_zero_iff
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) :
    nativeSectionOfAlgebraicPositivePower f n E a H k σ ≠ 0 ↔ σ ≠ 0 := by
  rw [← nativeSectionOfAlgebraicPositivePower_zero f n E a H k]
  exact (nativeSectionOfAlgebraicPositivePower_injective f n E a H k).ne_iff

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
