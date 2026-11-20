import SGPT.Okounkov.AlgebraicBodyOperations
import SGPT.Okounkov.SchemeLineBundleMetricGeometry

/-!
# Tensor products of smooth Hermitian metrics on line bundles (algebraic setting)

Infrastructure for the twisted asymptotic Riemann–Roch formula `thm:DXmain1` (blueprint
`claude-dxmain:tensor-metric`): for smooth Hermitian metrics `h_T` on `T` and `h_M` on `M`, the
product metric `h_T ⊗ h_M` on `T ⊗ M` (`|e ⊗ g|² = |e|²_{h_T} |g|²_{h_M}` for local frames `e`, `g`
of `T`, `M` on a common open), and its Chern form `c₁(T ⊗ M, h_T ⊗ h_M) = c₁(T, h_T) + c₁(M, h_M)`.

Setting: `X` a complex scheme smooth of relative dimension `n` with a closed projective embedding
`E`, line bundles with rank-one atlases, `SchemeLineBundleMetric` the structural metrics,
`bundleTensor T M` the tensor product with the atlas `pairwiseTensorAtlas` of frames
`e|_{U ∩ V} ⊗ g|_{U ∩ V}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov
open scoped Topology ContDiff Manifold

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance dxTensorTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxTensorCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dxTensorManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {T M : X.Modules}

namespace SGPT.IGood.DXMain

/-- Transitions of tensor frames are products of transitions. -/
theorem schemeFrameTransition_tensor {U V : X.Opens}
    (e : LocalBundleFrame T U) (g : LocalBundleFrame M U)
    (e' : LocalBundleFrame T V) (g' : LocalBundleFrame M V)
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    schemeFrameTransition f n E (e.tensor g) (e'.tensor g') p =
      schemeFrameTransition f n E e e' p * schemeFrameTransition f n E g g' p := by
  let := E.isSeparated
  let := E.quasiCompact
  have hp : schemeComplexPointImage f p ∈ U ⊓ V := ⟨hpU, hpV⟩
  simp only [schemeFrameTransition, localBundleFrameTransition_tensor,
    schemeOpenRegularFunction, dif_pos hp, Units.val_mul, map_mul]

end SGPT.IGood.DXMain

namespace SGPT.Okounkov.SchemeLineBundleMetric

open SGPT.IGood.DXMain

variable {f n E} (HT : SchemeLineBundleMetric f n E T) (HM : SchemeLineBundleMetric f n E M)
  (aT : LineBundleAtlas T) (aM : LineBundleAtlas M)

/-- The weight of an arbitrary frame of `T ⊗ M` under `h_T ⊗ h_M`, read through the pairwise
tensor frame at the point. -/
def tensorProductFrameNormSq {U : X.Opens} (γ : LocalBundleFrame (bundleTensor T M) U)
    (p : SchemeComplexPoint f) : ℝ :=
  let c := pairwiseTensorAtlas aT aM
  let ij := (schemeLineBundleCore f n E c).indexAt p
  Complex.normSq (schemeFrameTransition f n E γ (c.frame ij) p) *
    (HT.frameNormSq (leftRestrictedFrame aT aM ij) p *
      HM.frameNormSq (rightRestrictedFrame aT aM ij) p)

/-- The weight in every frame `γ` through `p`, computed with any frames `e`, `g` of `T`, `M` on a
common open through `p`. -/
theorem tensorProductFrameNormSq_eq {U V : X.Opens} (γ : LocalBundleFrame (bundleTensor T M) U)
    (e : LocalBundleFrame T V) (g : LocalBundleFrame M V) (p : SchemeComplexPoint f)
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    HT.tensorProductFrameNormSq HM aT aM γ p =
      Complex.normSq (schemeFrameTransition f n E γ (e.tensor g) p) *
        (HT.frameNormSq e p * HM.frameNormSq g p) := by
  let c := pairwiseTensorAtlas aT aM
  let Z := schemeLineBundleCore f n E c
  let ij := Z.indexAt p
  have hpW : schemeComplexPointImage f p ∈ c.opens ij := Z.mem_baseSet_at p
  change Complex.normSq (schemeFrameTransition f n E γ
      ((leftRestrictedFrame aT aM ij).tensor (rightRestrictedFrame aT aM ij)) p) *
    (HT.frameNormSq (leftRestrictedFrame aT aM ij) p *
      HM.frameNormSq (rightRestrictedFrame aT aM ij) p) = _
  rw [HT.transition (leftRestrictedFrame aT aM ij) e p hpW hpV,
    HM.transition (rightRestrictedFrame aT aM ij) g p hpW hpV,
    schemeFrameTransition_cocycle f n E γ
      ((leftRestrictedFrame aT aM ij).tensor (rightRestrictedFrame aT aM ij)) (e.tensor g) p
      hpU hpW hpV,
    schemeFrameTransition_tensor f n E (leftRestrictedFrame aT aM ij)
      (rightRestrictedFrame aT aM ij) e g p hpW hpV,
    Complex.normSq_mul, Complex.normSq_mul]
  ring

/-- **The product metric `h_T ⊗ h_M` on `T ⊗ M`.** -/
def tensorProduct : SchemeLineBundleMetric f n E (bundleTensor T M) where
  frameNormSq := HT.tensorProductFrameNormSq HM aT aM
  positive := by
    intro U γ p hp
    let c := pairwiseTensorAtlas aT aM
    let Z := schemeLineBundleCore f n E c
    let ij := Z.indexAt p
    have hpW : schemeComplexPointImage f p ∈ c.opens ij := Z.mem_baseSet_at p
    change 0 < Complex.normSq (schemeFrameTransition f n E γ (c.frame ij) p) *
      (HT.frameNormSq (leftRestrictedFrame aT aM ij) p *
        HM.frameNormSq (rightRestrictedFrame aT aM ij) p)
    exact mul_pos (Complex.normSq_pos.mpr
      (schemeFrameTransition_ne_zero f n E γ (c.frame ij) p hp hpW))
      (mul_pos (HT.positive _ p hpW) (HM.positive _ p hpW))
  transition := by
    intro U V α β p hpU hpV
    let c := pairwiseTensorAtlas aT aM
    let Z := schemeLineBundleCore f n E c
    let ij := Z.indexAt p
    have hpW : schemeComplexPointImage f p ∈ c.opens ij := Z.mem_baseSet_at p
    change Complex.normSq (schemeFrameTransition f n E α (c.frame ij) p) * _ =
      Complex.normSq (schemeFrameTransition f n E α β p) *
        (Complex.normSq (schemeFrameTransition f n E β (c.frame ij) p) * _)
    rw [schemeFrameTransition_cocycle f n E α β (c.frame ij) p hpU hpV hpW, Complex.normSq_mul]
    ring
  smooth := by
    intro U γ e u hu
    let := E.isSeparated
    let := E.quasiCompact
    let c := pairwiseTensorAtlas aT aM
    let Z := schemeLineBundleCore f n E c
    let ij := Z.indexAt (e.val.symm u)
    let V := c.opens ij
    let lf := leftRestrictedFrame aT aM ij
    let rf := rightRestrictedFrame aT aM ij
    have hpV : schemeComplexPointImage f (e.val.symm u) ∈ V := Z.mem_baseSet_at _
    let D := e.val.target ∩ e.val.symm ⁻¹'
      ((schemeComplexPointImage f ⁻¹' U) ∩ (schemeComplexPointImage f ⁻¹' V))
    have hD : IsOpen D := e.val.isOpen_inter_preimage_symm
      ((U.isOpen.preimage (schemeComplexPointImage_continuous f)).inter
        (V.isOpen.preimage (schemeComplexPointImage_continuous f)))
    have huD : u ∈ D := ⟨hu.1, hu.2, hpV⟩
    have hVD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' V)) :=
      e.val.isOpen_inter_preimage_symm (V.isOpen.preimage (schemeComplexPointImage_continuous f))
    have hnorm : ContDiffAt ℝ ∞ (fun z => Complex.normSq
        (schemeFrameTransition f n E γ (lf.tensor rf) (e.val.symm z))) u := by
      apply BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [hD.mem_nhds huD] with z hz
      exact FactorizedWeightForm.differentiableAt_comp_chart_symm e hz.1
        (schemeFrameTransition_holomorphicAt f n E γ (lf.tensor rf) _
          hz.2.1 hz.2.2).mdifferentiableAt
    have hT : ContDiffAt ℝ ∞ (fun z => HT.frameNormSq lf (e.val.symm z)) u :=
      (HT.smooth lf e).contDiffAt (hVD.mem_nhds ⟨hu.1, hpV⟩)
    have hM : ContDiffAt ℝ ∞ (fun z => HM.frameNormSq rf (e.val.symm z)) u :=
      (HM.smooth rf e).contDiffAt (hVD.mem_nhds ⟨hu.1, hpV⟩)
    have heq : (fun z => HT.tensorProductFrameNormSq HM aT aM γ (e.val.symm z)) =ᶠ[𝓝 u]
        fun z => Complex.normSq (schemeFrameTransition f n E γ (lf.tensor rf) (e.val.symm z)) *
          (HT.frameNormSq lf (e.val.symm z) * HM.frameNormSq rf (e.val.symm z)) := by
      filter_upwards [hD.mem_nhds huD] with z hz
      exact HT.tensorProductFrameNormSq_eq HM aT aM γ lf rf _ hz.2.1 hz.2.2
    exact ((hnorm.mul (hT.mul hM)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- `|e ⊗ g|²_{h_T ⊗ h_M} = |e|²_{h_T} |g|²_{h_M}`. -/
theorem tensorProduct_frame {V : X.Opens} (e : LocalBundleFrame T V) (g : LocalBundleFrame M V)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ V) :
    (HT.tensorProduct HM aT aM).frameNormSq (e.tensor g) p =
      HT.frameNormSq e p * HM.frameNormSq g p := by
  change HT.tensorProductFrameNormSq HM aT aM (e.tensor g) p = _
  rw [HT.tensorProductFrameNormSq_eq HM aT aM (e.tensor g) e g p hp hp,
    schemeFrameTransition_self f n E (e.tensor g) p hp, Complex.normSq_one, one_mul]

/-- **`c₁(T ⊗ M, h_T ⊗ h_M) = c₁(T, h_T) + c₁(M, h_M)`** on every chart target, for every atlas
`b` of `T ⊗ M`. -/
theorem curvature_tensorProduct (b : LineBundleAtlas (bundleTensor T M)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ((HT.tensorProduct HM aT aM).curvature b).val.GeometricallyEq
      (HT.curvature aT + HM.curvature aM).val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e u hu
  let c := pairwiseTensorAtlas aT aM
  let Z := schemeLineBundleCore f n E c
  let ij := Z.indexAt (e.val.symm u)
  let V := c.opens ij
  let lf := leftRestrictedFrame aT aM ij
  let rf := rightRestrictedFrame aT aM ij
  have hp : schemeComplexPointImage f (e.val.symm u) ∈ V := Z.mem_baseSet_at _
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' V)) :=
    e.val.isOpen_inter_preimage_symm (V.isOpen.preimage (schemeComplexPointImage_continuous f))
  rw [ClosedRealOneOneForm.coeff_add]
  change ((HT.tensorProduct HM aT aM).curvature b).val.coeff e u =
    (HT.curvature aT).val.coeff e u + (HM.curvature aM).val.coeff e u
  rw [(HT.tensorProduct HM aT aM).curvature_coeff_frame b (lf.tensor rf) e hu hp,
    HT.curvature_coeff_frame aT lf e hu hp, HM.curvature_coeff_frame aM rf e hu hp]
  have hTs : ContDiffOn ℝ ∞ (fun z => Real.log (HT.frameNormSq lf (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' V)) :=
    (HT.smooth lf e).log fun _ hz => (HT.positive lf _ hz.2).ne'
  have hMs : ContDiffOn ℝ ∞ (fun z => Real.log (HM.frameNormSq rf (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' V)) :=
    (HM.smooth rf e).log fun _ hz => (HM.positive rf _ hz.2).ne'
  have heq : (fun z => -Real.log ((HT.tensorProduct HM aT aM).frameNormSq
      (lf.tensor rf) (e.val.symm z))) =ᶠ[𝓝 u]
      fun z => -Real.log (HT.frameNormSq lf (e.val.symm z)) +
        -Real.log (HM.frameNormSq rf (e.val.symm z)) := by
    filter_upwards [hD.mem_nhds ⟨hu, hp⟩] with z hz
    rw [HT.tensorProduct_frame HM aT aM lf rf _ hz.2,
      Real.log_mul (HT.positive lf _ hz.2).ne' (HM.positive rf _ hz.2).ne']
    ring
  exact (smoothDDC_congr heq).trans (smoothDDC_add hD hTs.neg hMs.neg ⟨hu, hp⟩)

end SGPT.Okounkov.SchemeLineBundleMetric
