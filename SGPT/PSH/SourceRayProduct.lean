import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.SingularSubgeodesicProductLocalPsh
import SGPT.Foundations.Analysis.Pending.OpensRestriction
import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open FirstPass.HolomorphicMaps FirstPass.LocalPotentialPullback
open ProductComplexManifold
open scoped Topology Manifold ContDiff ProductComplexManifold

/-- The genuine complex-linear identification of one Euclidean coordinate with
the original complex time; no real-valued time proxy is used. -/
def sourceRayTimeModelEquiv : ComplexModel 1 ≃L[ℂ] ℂ :=
  PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 ↦ ℂ)

/-- The actual original strip, expressed in the linearly identical one-coordinate model. -/
def sourceRayTimeStrip : Opens (ComplexModel 1) :=
  ⟨sourceRayTimeModelEquiv ⁻¹' complexTimeStrip,
    isOpen_complexTimeStrip.preimage sourceRayTimeModelEquiv.continuous⟩

def sourceRayTime (z : sourceRayTimeStrip) : ℂ := sourceRayTimeModelEquiv z.1

def sourceRayTimePoint : sourceRayTimeStrip :=
  ⟨sourceRayTimeModelEquiv.symm ((1 / 2 : ℝ) : ℂ), by
    change sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm _) ∈ complexTimeStrip
    norm_num [complexTimeStrip]⟩

/-- The time model is homeomorphic to the literal source complex strip. -/
def sourceRayTimeEquiv : sourceRayTimeStrip ≃ₜ {z : ℂ // z ∈ complexTimeStrip} where
  toFun z := ⟨sourceRayTime z, z.2⟩
  invFun z := ⟨sourceRayTimeModelEquiv.symm z.1, by
    change sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm z.1) ∈ complexTimeStrip
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using z.2⟩
  left_inv z := Subtype.ext (sourceRayTimeModelEquiv.symm_apply_apply z.1)
  right_inv z := Subtype.ext (sourceRayTimeModelEquiv.apply_symm_apply z.1)
  continuous_toFun := (sourceRayTimeModelEquiv.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (sourceRayTimeModelEquiv.symm.continuous.comp continuous_subtype_val).subtype_mk
    (fun z ↦ by
      change sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm z.1) ∈ complexTimeStrip
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using z.2)

def sourceRayTimeChart : ComplexChart 1 sourceRayTimeStrip := complexChartAt sourceRayTimePoint

theorem sourceRayTimeChart_apply (b : ComplexChart 1 sourceRayTimeStrip)
    (z : sourceRayTimeStrip) : b.val z = z.1 := by
  obtain ⟨x, hx⟩ := Opens.chart_eq (show Nonempty sourceRayTimeStrip from ⟨sourceRayTimePoint⟩)
    b.property
  rw [hx]
  rfl

theorem sourceRayTimeChart_symm_coe (b : ComplexChart 1 sourceRayTimeStrip)
    {z : ComplexModel 1} (hz : z ∈ b.val.target) :
    (b.val.symm z : ComplexModel 1) = z := by
  have h := b.val.right_inv hz
  rwa [sourceRayTimeChart_apply] at h

theorem sourceRayTimeChart_source : sourceRayTimeChart.val.source = univ := by
  change ((chartAt (ComplexModel 1) (sourceRayTimePoint : ComplexModel 1)).subtypeRestr
    (show Nonempty sourceRayTimeStrip from ⟨sourceRayTimePoint⟩)).source = univ
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  change (Subtype.val ⁻¹' (Set.univ : Set (ComplexModel 1))) = univ
  rfl

theorem sourceRayTimeChart_target : sourceRayTimeChart.val.target = sourceRayTimeStrip := by
  ext z
  constructor
  · intro hz
    have h := (sourceRayTimeChart.val.symm z).2
    rwa [sourceRayTimeChart_symm_coe sourceRayTimeChart hz] at h
  · intro hz
    have h := sourceRayTimeChart.val.map_source
      (show (⟨z, hz⟩ : sourceRayTimeStrip) ∈ sourceRayTimeChart.val.source by
        rw [sourceRayTimeChart_source]; trivial)
    rwa [sourceRayTimeChart_apply] at h

theorem sourceRayTime_chart_holomorphic (b : ComplexChart 1 sourceRayTimeStrip) :
    DifferentiableOn ℂ (sourceRayTime ∘ b.val.symm) b.val.target := by
  apply sourceRayTimeModelEquiv.differentiable.differentiableOn.congr
  intro z hz
  change sourceRayTimeModelEquiv (b.val.symm z : ComplexModel 1) = sourceRayTimeModelEquiv z
  rw [sourceRayTimeChart_symm_coe b hz]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual first-projection pullback of the entire original background. -/
def sourceRayProductBackground (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    AtlasClosedRealOneOneForm (ofFixedModel (n + 1) (M × sourceRayTimeStrip)) :=
  nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback
    (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)) (atlasClosedFormToNative θ))

/-- The full original universal local-potential condition on the actual complex
product. The genuine source theta-PSH definition supplies every corrected PSH
test and nondegeneracy, not an abstract joint-PSH certificate. -/
def SourceJointThetaPSH (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (curve : ℝ → M → EReal) : Prop :=
  (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH (sourceRayProductBackground θ)
    (fun p ↦ curve (sourceRayTime p.2).re p.1)

/-- Every product neighborhood has a non-pole point from the genuine slice at
the same original complex time. No joint nondegeneracy premise is requested. -/
theorem sourceRay_joint_locallyNondegenerate
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (hcurve : IsSubgeodesicInterior θ curve) :
    LocallyNondegenerate (fun p : M × sourceRayTimeStrip ↦ curve (sourceRayTime p.2).re p.1) := by
  intro p O hO hp
  let V : Set M := (fun x : M ↦ (x, p.2)) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_id.prodMk continuous_const)
  have hslice := hcurve.thetaPshPotential (show (sourceRayTime p.2).re ∈ Ioo (0 : ℝ) 1 from p.2.2)
  obtain ⟨y, hy, hny⟩ := hslice.2 p.1 V hV hp
  exact ⟨(y, p.2), hy, hny⟩

/-- The actual native joint complexification transports to every product chart,
and slice-produced nondegeneracy gives the FULL original all-local-potential
theta-PSH condition on the actual first-projection background. -/
theorem sourceJointThetaPSH_of_nativeInterior
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (hcurve : IsSubgeodesicInterior (atlasClosedFormToNative θ).val curve) :
    SourceJointThetaPSH θ curve := by
  have hraw := SingularSubgeodesicProductLocalPsh.thetaPlurisubharmonicOn_product_time_pullback
    (T := sourceRayTimeStrip) hcurve (V := univ) isOpen_univ
    (τ := sourceRayTime)
    (fun b ↦ (sourceRayTime_chart_holomorphic b).mono inter_subset_left)
    (fun y _ ↦ y.2)
  have hnative : IsThetaPshPotential
      (SmoothRealForm.pullback (ProductComplexManifold.contMDiff_fst (n := n) (m := 1))
        (atlasClosedFormToNative θ).val)
      (fun p : M × sourceRayTimeStrip ↦ curve (sourceRayTime p.2).re p.1) :=
    ⟨fun e z hz ↦ hraw e z hz (by simp), sourceRay_joint_locallyNondegenerate hcurve⟩
  apply (isThetaPSH_iff_nativeThetaPotential (sourceRayProductBackground θ) _).mpr
  exact hnative

/-- The actual complex linear product coordinates retain the original complex time. -/
def sourceRayProductModel (n : ℕ) : (ComplexModel n × ℂ) ≃L[ℂ] ComplexModel (n + 1) :=
  ((ContinuousLinearEquiv.refl ℂ (ComplexModel n)).prodCongr sourceRayTimeModelEquiv.symm).trans
    (prodModelEquiv n 1)

theorem sourceRayProductModel_split (p : ComplexModel n × ℂ) :
    (prodModelEquiv n 1).symm (sourceRayProductModel n p) =
      (p.1, sourceRayTimeModelEquiv.symm p.2) := by
  simp [sourceRayProductModel]

def sourceRayProductChart (e : ComplexChart n M) :
    ComplexChart (n + 1) (M × sourceRayTimeStrip) :=
  ⟨prodChart e.val sourceRayTimeChart.val, mem_image2_of_mem e.property sourceRayTimeChart.property⟩

omit [IsComplexManifold n M] in
/-- The exact entire product chart and full local-potential domain, with its
original spatial and complex-time inverse equations. -/
theorem sourceRayProductChart_read (e : ComplexChart n M)
    {W : Set (ComplexModel n)} (hWe : W ⊆ e.val.target)
    {p : ComplexModel n × ℂ} (hp : p ∈ geodesicChartDomain W) :
    sourceRayProductModel n p ∈ potentialDomain (Prod.fst : M × sourceRayTimeStrip → M)
      (sourceRayProductChart e) e W ∧
    coordinateMap (Prod.fst : M × sourceRayTimeStrip → M) (sourceRayProductChart e) e
      (sourceRayProductModel n p) = p.1 ∧
    ((sourceRayProductChart e).val.symm (sourceRayProductModel n p)).1 = e.val.symm p.1 ∧
    sourceRayTime ((sourceRayProductChart e).val.symm (sourceRayProductModel n p)).2 = p.2 := by
  have htime : sourceRayTimeModelEquiv.symm p.2 ∈ sourceRayTimeChart.val.target := by
    rw [sourceRayTimeChart_target]
    change sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm p.2) ∈ complexTimeStrip
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp.2
  have htarget : sourceRayProductModel n p ∈ (sourceRayProductChart e).val.target := by
    change sourceRayProductModel n p ∈ (prodChart e.val sourceRayTimeChart.val).target
    rw [prodChart_target]
    change (prodModelEquiv n 1).symm (sourceRayProductModel n p) ∈
      e.val.target ×ˢ sourceRayTimeChart.val.target
    rw [sourceRayProductModel_split]
    exact ⟨hWe hp.1, htime⟩
  have hspace : ((sourceRayProductChart e).val.symm (sourceRayProductModel n p)).1 =
      e.val.symm p.1 := by
    change e.val.symm ((prodModelEquiv n 1).symm (sourceRayProductModel n p)).1 = e.val.symm p.1
    rw [sourceRayProductModel_split]
  have hcoord : coordinateMap (Prod.fst : M × sourceRayTimeStrip → M)
      (sourceRayProductChart e) e (sourceRayProductModel n p) = p.1 := by
    change e.val (((sourceRayProductChart e).val.symm (sourceRayProductModel n p)).1) = p.1
    rw [hspace, e.val.right_inv (hWe hp.1)]
  refine ⟨⟨⟨htarget, ?_⟩, ?_⟩, hcoord, hspace, ?_⟩
  · change ((sourceRayProductChart e).val.symm (sourceRayProductModel n p)).1 ∈ e.val.source
    rw [hspace]
    exact e.val.map_target (hWe hp.1)
  · change coordinateMap _ _ _ _ ∈ W
    rw [hcoord]
    exact hp.1
  · change sourceRayTimeModelEquiv (sourceRayTimeChart.val.symm
      ((prodModelEquiv n 1).symm (sourceRayProductModel n p)).2 : ComplexModel 1) = p.2
    rw [sourceRayProductModel_split, sourceRayTimeChart_symm_coe sourceRayTimeChart htime]
    exact sourceRayTimeModelEquiv.apply_symm_apply p.2

/-- The FULL original product theta-PSH test yields the native corrected joint
function for every genuine base local potential, on its entire domain × strip. -/
theorem sourceJointThetaPSH_corrected
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (hjoint : SourceJointThetaPSH θ curve) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ρ) :
    PlurisubharmonicOn (subgeodesicChartFunction curve e ρ) (geodesicChartDomain W) := by
  have hnative := (isThetaPSH_iff_nativeThetaPotential (sourceRayProductBackground θ)
    (fun p : M × sourceRayTimeStrip ↦ curve (sourceRayTime p.2).re p.1)).mp hjoint
  let d := sourceRayProductChart e
  have hρd := isSmoothLocalPotential_pullback
    (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := M) (Y := sourceRayTimeStrip)) d hρ
  have hpsh := ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
    hnative.1 d hρd
  have hpull := hpsh.comp_continuousLinearMap (sourceRayProductModel n).toContinuousLinearMap
  intro p hp
  apply (hpull p (sourceRayProductChart_read e hρ.2.1 hp).1).congr
  filter_upwards [(isOpen_geodesicChartDomain hρ.1).mem_nhds hp] with q hq
  obtain ⟨_, hcoord, hspace, htime⟩ := sourceRayProductChart_read e hρ.2.1 hq
  change curve (sourceRayTime ((sourceRayProductChart e).val.symm
      (sourceRayProductModel n q)).2).re
      ((sourceRayProductChart e).val.symm (sourceRayProductModel n q)).1 +
        (ρ (coordinateMap (Prod.fst : M × sourceRayTimeStrip → M)
          (sourceRayProductChart e) e (sourceRayProductModel n q)) : EReal) =
    curve q.2.re (e.val.symm q.1) + (ρ q.1 : EReal)
  rw [hcoord, hspace, htime]

/-- The source interior predicate keeps genuine original slices separately from
the full universal product theta-PSH condition, as in the printed definition. -/
def SourceSubgeodesicInterior (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (curve : ℝ → M → EReal) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) 1, (ofFixedModel n M).IsThetaPSH θ (curve t)) ∧
    SourceJointThetaPSH θ curve

/-- Exact whole interior dictionary: actual source slices, full actual product,
and all original local potentials. -/
theorem sourceInterior_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (curve : ℝ → M → EReal) :
    SourceSubgeodesicInterior θ curve ↔ IsSubgeodesicInterior (atlasClosedFormToNative θ).val curve := by
  constructor
  · rintro ⟨hslices, hjoint⟩
    refine ⟨fun t ht ↦ (isThetaPSH_iff_nativeThetaPotential θ (curve t)).mp (hslices t ht), ?_⟩
    intro e z hz
    obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_chart_local_potential θ e hz
    have hpotential : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ρ :=
      ⟨hW, hWe, hρ, heq⟩
    exact ⟨W, ρ, hzW, hpotential, sourceJointThetaPSH_corrected hjoint e hpotential⟩
  · intro h
    exact ⟨fun t ht ↦ (isThetaPSH_iff_nativeThetaPotential θ (curve t)).mpr
      (h.thetaPshPotential ht), sourceJointThetaPSH_of_nativeInterior h⟩

end SGPT.PSH.VariableComplexAtlas
