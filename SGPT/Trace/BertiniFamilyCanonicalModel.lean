import SGPT.Trace.BertiniPencilFamily
import SGPT.Trace.BertiniLocalOriginalChartNormal
import SGPT.Bergman.SourceNativeTensorSmoothMetric

/-! Actual physical canonical MODEL over the original full noncompact family.
Its actual top-covector/volume identification is a further proved producer. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeKodairaPullback SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))

def familyNativeXMap :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (familyIncidence p i a v U) X ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact ⟨fun q => q.val.2, (contMDiff_snd (n := 1) (m := n) (X := U) (Y := X)).comp
    (contMDiff_familyInclusion p i a v U p.contMDiff hsm)⟩

variable [CompactSpace X]

def familyNativeCanonicalModel :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    HermitianHolomorphicLineBundle n (familyIncidence p i a v U) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact nativeHolomorphicPullbackBundle
    (tensor (nativeCanonicalBundle (n := n) (X := X)) (nativeBertiniHyperplaneBundle p))
    (familyNativeXMap p i a v U hsm)

theorem familyNativeCanonicalModel_smooth :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    IsSourceSmoothHermitianMetric (familyNativeCanonicalModel p i a v U hsm) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  have hP : IsSourceSmoothHermitianMetric (nativeBertiniHyperplaneBundle p) :=
    nativeHolomorphicPullback_smooth (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  exact nativeHolomorphicPullback_smooth _ (familyNativeXMap p i a v U hsm)
    (sourceNativeTensor_smooth _ _ nativeCanonicalBundle_smooth hP)

def familyNativePhysicalModel (L : HermitianHolomorphicLineBundle n X) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    HermitianHolomorphicLineBundle n (familyIncidence p i a v U) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact tensor (familyNativeCanonicalModel p i a v U hsm)
    (nativeHolomorphicPullbackBundle L (familyNativeXMap p i a v U hsm))

theorem familyNativePhysicalModel_smooth (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    IsSourceSmoothHermitianMetric (familyNativePhysicalModel p i a v U hsm L) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact sourceNativeTensor_smooth _ _ (familyNativeCanonicalModel_smooth p i a v U hsm)
    (nativeHolomorphicPullback_smooth L (familyNativeXMap p i a v U hsm) hL)

include hsm in
omit [CompactSpace X] in
theorem exists_familyPreferredVerticalNormal
    (q : familyIncidence p i a v U) (j : Fin (N + 1))
    (hqj : p q.val.2 ∈ (affineChart j).source) :
    ∃ (m : Fin n),
      chartDeriv
        (productComplexChart (complexChartAt (n := 1) q.val.1) (complexChartAt (n := n) q.val.2))
        (prodModelEquiv 1 n (0,
          (chartDeriv (complexChartAt (n := n) q.val.2) (EuclideanSpace.single m 1)
            (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2)⁻¹ •
            EuclideanSpace.single m 1))
        (pencilLocalEquation p i a v U j) q.val = 1 := by
  let eX := complexChartAt (n := n) q.val.2
  let eT := complexChartAt (n := 1) q.val.1
  have hx : q.val.2 ∈ eX.val.source := mem_complexChartAt_source q.val.2
  have ht : q.val.1 ∈ eT.val.source := mem_complexChartAt_source q.val.1
  obtain ⟨m, hm⟩ := exists_nativeBertiniChartPartial_ne_zero p i (a - q.val.1.val 0 • v)
    j eX q.val.2 hx hqj q.property (hsm q.val.1)
  refine ⟨m, ?_⟩
  rw [chartDeriv_product_vertical eT eX ht hx
    (holomorphicAt_pencilLocalEquation p i a v U p.contMDiff j hqj)]
  let gm := chartDeriv eX (EuclideanSpace.single m 1)
    (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2
  change fderiv ℂ ((nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) ∘ eX.val.symm)
    (eX.val q.val.2) (gm⁻¹ • EuclideanSpace.single m 1) = 1
  rw [map_smul]
  change gm⁻¹ * gm = 1
  exact inv_mul_cancel₀ hm

end SGPT.Trace.BertiniFamilyCanonical
