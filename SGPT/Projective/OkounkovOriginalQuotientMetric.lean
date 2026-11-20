import SGPT.Projective.OriginalAtlasWeightedMetric
import SGPT.IGood.DXMainTensorMetric
import SGPT.Okounkov.ValGen2Dual

/-! A genuine physical metric on L' tensor dual L, with its actual original Chern difference.
Blueprint: okounkov-original-quotient-metric.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalDifference
open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.ValGen2
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} {L L' : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas L')

/-- Actual original restricted quotient frames on the LITERAL original sheaf. -/
def originalDifferenceAtlas : LineBundleAtlas (bundleTensor L' (bundleDual L)) where
  I := a.I × b.I
  opens ij := a.opens ij.1 ⊓ b.opens ij.2
  covers x := by
    obtain ⟨i,hi⟩ := a.covers x
    obtain ⟨j,hj⟩ := b.covers x
    exact ⟨(i,j),hi,hj⟩
  frame ij := (rightRestrictedFrame a b ij).tensor (leftRestrictedFrame a b ij).dual

variable (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (H : SchemeLineBundleMetric f n E L) (K : SchemeLineBundleMetric f n E L')

local instance differenceMetricTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance differenceMetricCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance differenceMetricManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

private theorem schemeTransition_dual {M : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame M U) (g : LocalBundleFrame M V) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) (hq : schemeComplexPointImage f p ∈ V) :
    schemeFrameTransition f n E e.dual g.dual p = (schemeFrameTransition f n E e g p)⁻¹ := by
  have hpq : schemeComplexPointImage f p ∈ U ⊓ V := ⟨hp,hq⟩
  simp only [schemeFrameTransition,localBundleFrameTransition_dual,schemeOpenRegularFunction,dif_pos hpq]
  let τ := localBundleFrameTransition e g (homOfLE inf_le_left) (homOfLE inf_le_right)
  let F : X.sheaf.obj.obj (.op (U ⊓ V)) →+* ℂ := NativeHolGerm.eval.comp
    ((schemeNativeStalkGerm f n p).comp
      (X.presheaf.germ (U ⊓ V) (schemeComplexPointImage f p) hpq).hom)
  change F ((τ⁻¹).val) = (F τ.val)⁻¹
  exact map_units_inv F τ

private def differenceWeights (ij : a.I × b.I) (p : SchemeComplexPoint f) : ℝ :=
  K.frameNormSq (rightRestrictedFrame a b ij) p / H.frameNormSq (leftRestrictedFrame a b ij) p

omit [IsSeparated f] [QuasiCompact f] in
private theorem differenceWeights_smooth (ij : a.I × b.I) (c : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℝ ∞ (fun z => differenceWeights a b f n E H K ij (c.val.symm z))
      (c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' (originalDifferenceAtlas a b).opens ij)) :=
  (K.smooth (rightRestrictedFrame a b ij) c).div (H.smooth (leftRestrictedFrame a b ij) c)
    (fun _ hz => (H.positive (leftRestrictedFrame a b ij) _ hz.2).ne')

omit [IsSeparated f] [QuasiCompact f] in
private theorem differenceWeights_positive (ij : a.I × b.I) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ (originalDifferenceAtlas a b).opens ij) :
    0 < differenceWeights a b f n E H K ij p :=
  div_pos (K.positive (rightRestrictedFrame a b ij) p hp) (H.positive (leftRestrictedFrame a b ij) p hp)

private theorem differenceWeights_transition (i j : a.I × b.I) (p : SchemeComplexPoint f)
    (hi : schemeComplexPointImage f p ∈ (originalDifferenceAtlas a b).opens i)
    (hj : schemeComplexPointImage f p ∈ (originalDifferenceAtlas a b).opens j) :
    differenceWeights a b f n E H K i p =
      Complex.normSq (schemeFrameTransition f n E ((originalDifferenceAtlas a b).frame i)
        ((originalDifferenceAtlas a b).frame j) p) * differenceWeights a b f n E H K j p := by
  dsimp only [differenceWeights,originalDifferenceAtlas]
  rw [SGPT.IGood.DXMain.schemeFrameTransition_tensor f n E _ _ _ _ p hi hj,
    schemeTransition_dual f n E _ _ p hi hj,Complex.normSq_mul,Complex.normSq_inv,
    K.transition (rightRestrictedFrame a b i) (rightRestrictedFrame a b j) p hi hj,
    H.transition (leftRestrictedFrame a b i) (leftRestrictedFrame a b j) p hi hj]
  field_simp

/-- The partition and genuine physical quotient metric are MANUFACTURED on the SAME original difference sheaf. -/
def originalDifferenceMetric : SchemeLineBundleMetric f n E (bundleTensor L' (bundleDual L)) :=
  atlasWeightedMetric f n E (originalDifferenceAtlas a b) (differenceWeights a b f n E H K)
    (differenceWeights_smooth a b f n E H K) (differenceWeights_positive a b f n E H K)

/-- EXACT actual physical norm ratio in EVERY genuine original quotient-atlas frame. -/
theorem originalDifferenceMetric_frame (ij : a.I × b.I) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ (originalDifferenceAtlas a b).opens ij) :
    (originalDifferenceMetric a b f n E H K).frameNormSq ((originalDifferenceAtlas a b).frame ij) p =
      K.frameNormSq (rightRestrictedFrame a b ij) p / H.frameNormSq (leftRestrictedFrame a b ij) p :=
  atlasWeightedMetric_frame f n E (originalDifferenceAtlas a b) (differenceWeights a b f n E H K)
    (differenceWeights_smooth a b f n E H K) (differenceWeights_positive a b f n E H K)
    (differenceWeights_transition a b f n E H K) ij p hp

/-- Actual original Chern coefficients are the genuine original metric difference, on EVERY chart target. -/
theorem originalDifferenceMetric_curvature :
    ((originalDifferenceMetric a b f n E H K).curvature (originalDifferenceAtlas a b)).val.GeometricallyEq
      (K.curvature b + -(H.curvature a)).val := by
  intro c z hz
  obtain ⟨ij,hij⟩ := (originalDifferenceAtlas a b).covers (schemeComplexPointImage f (c.val.symm z))
  let U := (originalDifferenceAtlas a b).opens ij
  let e := leftRestrictedFrame a b ij
  let g := rightRestrictedFrame a b ij
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    c.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hlogH := (H.smooth e c).log (fun _ hy => (H.positive e _ hy.2).ne')
  have hlogK := (K.smooth g c).log (fun _ hy => (K.positive g _ hy.2).ne')
  rw [ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_neg,
    (originalDifferenceMetric a b f n E H K).curvature_coeff_frame (originalDifferenceAtlas a b)
      ((originalDifferenceAtlas a b).frame ij) c hz hij,
    K.curvature_coeff_frame b g c hz hij,H.curvature_coeff_frame a e c hz hij]
  have heq : (fun w => -Real.log ((originalDifferenceMetric a b f n E H K).frameNormSq
      ((originalDifferenceAtlas a b).frame ij) (c.val.symm w))) =ᶠ[𝓝 z]
      fun w => -Real.log (K.frameNormSq g (c.val.symm w)) - (-Real.log (H.frameNormSq e (c.val.symm w))) := by
    filter_upwards [hO.mem_nhds ⟨hz,hij⟩] with w hw
    rw [originalDifferenceMetric_frame a b f n E H K ij _ hw.2,
      Real.log_div (K.positive g _ hw.2).ne' (H.positive e _ hw.2).ne']
    ring
  exact (smoothDDC_congr heq).trans (smoothDDC_sub hO hlogK.neg hlogH.neg ⟨hz,hij⟩)

/-- Equal ORIGINAL classes manufacture ZERO class of the actual original difference sheaf metric. -/
theorem originalDifferenceMetric_class_zero
    (hclass : RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b)) :
    RealBottChern.ofRepresentative ((originalDifferenceMetric a b f n E H K).curvature
      (originalDifferenceAtlas a b)) = 0 := by
  rw [RealBottChern.ofRepresentative_eq_of_geometricallyEq (originalDifferenceMetric_curvature a b f n E H K),
    RealBottChern.ofRepresentative_add,RealBottChern.ofRepresentative_neg,← hclass,add_neg_cancel]

end SGPT.Okounkov.OriginalDifference
