import SGPT.Trace.BertiniFamilyCanonicalHolomorphic

/-! Actual coordinate canonical unit and its matched physical density. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyCanonicalCoordinateEquiv :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source), (familyNativeCanonicalModel p i a v U hsm).Fiber q ≃ₗ[ℂ] ℂ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  let F := familyNativeCanonicalFiberEquiv p i a v U hsm q
  let A := nativeOriginalChartTangentEquiv e q hq
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.map A.symm
  apply LinearEquiv.ofBijective (familyCanonicalCoordinateValue p i a v U hsm e q hq)
  constructor
  · intro u w huw
    apply F.injective
    have h := (F u).eq_smul_basis_det b
    have h' := (F w).eq_smul_basis_det b
    change (F u) b = (F w) b at huw
    rw [huw] at h
    exact h.trans h'.symm
  · intro c
    refine ⟨F.symm (c • b.det), ?_⟩
    change F (F.symm (c • b.det)) b = c
    rw [F.apply_symm_apply, AlternatingMap.smul_apply, Module.Basis.det_self]
    exact mul_one c

theorem familyCanonicalCoordinateEquiv_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (s : (familyNativeCanonicalModel p i a v U hsm).Fiber q),
      familyCanonicalCoordinateEquiv p i a v U hsm e q hq s =
        familyCanonicalCoordinateValue p i a v U hsm e q hq s := by
  intros
  rfl

def familyCoordinateCanonicalUnit :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source), (familyNativeCanonicalModel p i a v U hsm).Fiber q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  exact (familyCanonicalCoordinateEquiv p i a v U hsm e q hq).symm 1

theorem familyCoordinateCanonicalUnit_value :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source), familyCanonicalCoordinateValue p i a v U hsm e q hq
        (familyCoordinateCanonicalUnit p i a v U hsm e q hq) = 1 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  exact (familyCanonicalCoordinateEquiv p i a v U hsm e q hq).apply_symm_apply 1

theorem familyCoordinateCanonicalUnit_ne_zero :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source), familyCoordinateCanonicalUnit p i a v U hsm e q hq ≠ 0 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq hz
  have h := familyCoordinateCanonicalUnit_value p i a v U hsm e q hq
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem familyCoordinateCanonicalUnit_in_frame :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (x₀ : X)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (_hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hP : q.val.2 ∈ eP.val.baseSet),
      familyCoordinateCanonicalUnit p i a v U hsm e q hq =
        (familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q)⁻¹ •
          (familyCanonicalModelFrame p i a v U hsm x₀ eP).val.symm q 1 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e x₀ eP q hq hx hP
  apply (familyCanonicalCoordinateEquiv p i a v U hsm e q hq).injective
  rw [familyCanonicalCoordinateEquiv_apply, familyCoordinateCanonicalUnit_value,
    familyCanonicalCoordinateEquiv_apply, map_smul]
  change 1 = (familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q)⁻¹ * _
  have hc : familyCanonicalCoordinateValue p i a v U hsm e q hq
      ((familyCanonicalModelFrame p i a v U hsm x₀ eP).val.symm q 1) =
      familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q := by
    unfold familyModelCanonicalFrameCoefficient
    rw [dif_pos hq]
  rw [hc, inv_mul_cancel₀ (familyModelCanonicalFrameCoefficient_ne_zero p i a v U hsm e x₀ eP q hq hx hP)]

def familyMatchedChartDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source), ℝ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  exact (‖familyCoordinateCanonicalUnit p i a v U hsm e q hq‖ ^ 2)⁻¹

theorem familyMatchedChartDensity_pos :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source), 0 < familyMatchedChartDensity p i a v U hsm e q hq := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  exact inv_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr
    (familyCoordinateCanonicalUnit_ne_zero p i a v U hsm e q hq)))

theorem familyMatchedChartDensity_in_frame :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (x₀ : X)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (_hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hP : q.val.2 ∈ eP.val.baseSet), familyMatchedChartDensity p i a v U hsm e q hq =
        ‖familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q‖ ^ 2 /
          ‖(familyCanonicalModelFrame p i a v U hsm x₀ eP).val.symm q 1‖ ^ 2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e x₀ eP q hq hx hP
  unfold familyMatchedChartDensity
  rw [familyCoordinateCanonicalUnit_in_frame p i a v U hsm e x₀ eP q hq hx hP,
    norm_smul, mul_pow, norm_inv, inv_pow, mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]

def familyMatchedCoordinateDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) → ComplexModel (d + 1) → ℝ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun e z => if hz : z ∈ e.val.target then
    familyMatchedChartDensity p i a v U hsm e (e.val.symm z) (e.val.map_target hz) else 0

theorem familyMatchedCoordinateDensity_pos :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (z : ComplexModel (d + 1))
      (_hz : z ∈ e.val.target), 0 < familyMatchedCoordinateDensity p i a v U hsm e z := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e z hz
  unfold familyMatchedCoordinateDensity
  rw [dif_pos hz]
  exact familyMatchedChartDensity_pos p i a v U hsm e _ _

theorem familyMatchedCoordinateDensity_smooth :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)),
      ContDiffOn ℝ ∞ (familyMatchedCoordinateDensity p i a v U hsm e) e.val.target := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e z hz
  let q := e.val.symm z
  have hq : q ∈ e.val.source := e.val.map_target hz
  let x₀ := q.val.2
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) :=
    ⟨trivializationAt ℂ (nativeBertiniHyperplaneBundle p).Fiber x₀, inferInstance⟩
  have hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source := mem_complexChartAt_source _
  have hP : q.val.2 ∈ eP.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  let f := familyCanonicalModelFrame p i a v U hsm x₀ eP
  have hf : q ∈ f.val.baseSet := ⟨hx, hP⟩
  let k := familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP
  have hk := contMDiffAt_familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q hq hx hP
  have hks : ContDiffAt ℂ ∞ (fun w => k (e.val.symm w)) z :=
    contMDiffAt_iff_contDiffAt.mp (hk.comp z
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hz))
  have hkn : ContDiffAt ℝ ∞ (fun w => ‖k (e.val.symm w)‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt.comp z (hks.restrict_scalars ℝ)
  have hfn : ContDiffAt ℝ ∞ (fun w => ‖f.val.symm (e.val.symm w) 1‖ ^ 2) z :=
    (familyNativeCanonicalModel_smooth p i a v U hsm e f).contDiffAt
      ((e.val.isOpen_inter_preimage_symm f.val.open_baseSet).mem_nhds ⟨hz, hf⟩)
  have hfn0 : ‖f.val.symm q 1‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr
      (SGPT.Bergman.NativeHermitianMetric.sourceAtlasFrame_ne_zero _ f hf)))
  have hr := hkn.div hfn hfn0
  apply (hr.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hnear := e.val.continuousOn_symm.continuousAt (e.val.open_target.mem_nhds hz)
  have hnearX := ((familyNativeXMap p i a v U hsm).contMDiff.continuous.continuousAt.comp
    hnear).eventually ((complexChartAt (n := d + 1) x₀).val.open_source.mem_nhds hx)
  have hnearP := ((familyNativeXMap p i a v U hsm).contMDiff.continuous.continuousAt.comp
    hnear).eventually (eP.val.open_baseSet.mem_nhds hP)
  filter_upwards [e.val.open_target.mem_nhds hz, hnearX, hnearP] with w hw hxw hPw
  unfold familyMatchedCoordinateDensity
  rw [dif_pos hw]
  exact familyMatchedChartDensity_in_frame p i a v U hsm e x₀ eP _ _ hxw hPw

end SGPT.Trace.BertiniFamilyCanonical
