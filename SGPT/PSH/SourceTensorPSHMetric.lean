import SGPT.PSH.BookLineBundleMetrics
import SGPT.Bergman.SourceTensorDictionary
import SGPT.Foundations.Analysis.Pending.BlanchardWeight
import SGPT.PSH.BookPSHMetrics
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-! Complete original def:tensorprodpshmetric, source69360cfd
chapter_pshfunctions.tex1858–1865. Genuine native tensor bundle and smooth
reference constructed internally; every vector, zero/poles and n=0 retained.
Private consolidation: exact checked component bodies; imports consolidated
and each anonymous noncomputable section explicitly closed. -/

-- BEGIN CHECKED COMPONENT CompatibleFiberNorm
/-! Actual compatible auxiliary fibre norm/inner product, pulled back from
an ORIGINAL continuous linear frame. The ORIGINAL topology, vector
operations and bundle data remain definitionally retained. Complete source
blueprint source-tensor-psh:compatible-norms preceded this implementation. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceTensorMetricDraft
open Bundle Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

section Fiber
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- An actual original frame supplies a compatible norm with the EXACT
original fibre topology; no norm/topology witness is assumed by the caller. -/
@[instance_reducible] def compatibleNormedFiber (e : V ≃L[ℂ] ℂ) : NormedAddCommGroup V := by
  let G : NormedAddCommGroup V := NormedAddCommGroup.induced V ℂ e.toLinearEquiv e.injective
  have hT : (inferInstance : TopologicalSpace V)=G.toMetricSpace.toUniformSpace.toTopologicalSpace := by
    exact e.toHomeomorph.isInducing.eq_induced
  exact { G with toMetricSpace := G.toMetricSpace.replaceTopology hT }

/-- The compatible auxiliary norm is literally the modulus of the original
frame coordinate, and its topology is still the original one. -/
theorem compatibleNormedFiber_norm (e : V ≃L[ℂ] ℂ) (v : V) :
    letI := compatibleNormedFiber e
    ‖v‖=‖e v‖ := rfl

/-- The actual original frame also supplies the compatible Hermitian inner
product. This is not the input PSH metric or its smooth reference metric. -/
@[instance_reducible] def compatibleHermitianFiber (e : V ≃L[ℂ] ℂ) :
    letI := compatibleNormedFiber e
    InnerProductSpace ℂ V := by
  letI := compatibleNormedFiber e
  letI : NormedSpace ℂ V :=
    { (inferInstance : Module ℂ V) with
      norm_smul_le := by
        intro c x
        change ‖e (c • x)‖ ≤ ‖c‖*‖e x‖
        rw [map_smul,norm_smul] }
  exact
    { (inferInstance : NormedSpace ℂ V) with
      inner := fun x y => inner ℂ (e x) (e y)
      conj_inner_symm := fun x y => inner_conj_symm (e x) (e y)
      add_left := by intro x y z; rw [map_add,inner_add_left]
      smul_left := by intro x y c; rw [map_smul,inner_smul_left]
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner (e x) }

end Fiber

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (L : X → Type*) [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- Actual original native line-bundle frames produce compatible auxiliary
normed structures on EVERY fibre, without changing the original topology. -/
@[instance_reducible] def originalNormedFibers : ∀ x, NormedAddCommGroup (L x) := fun x =>
  compatibleNormedFiber ((trivializationAt ℂ L x).continuousLinearEquivAt ℂ x
    (FiberBundle.mem_baseSet_trivializationAt' x))

/-- Every original fibre receives an actual auxiliary Hermitian structure,
constructed internally from its actual original frame. -/
@[instance_reducible] def originalHermitianFibers :
    letI := originalNormedFibers L
    ∀ x, InnerProductSpace ℂ (L x) := fun x =>
  compatibleHermitianFiber ((trivializationAt ℂ L x).continuousLinearEquivAt ℂ x
    (FiberBundle.mem_baseSet_trivializationAt' x))

end SGPT.PSH.SourceTensorMetricDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT CompatibleFiberNorm

-- BEGIN CHECKED COMPONENT NativeTensorBundle
/-! Actual original tensor line-bundle structures constructed from native
holomorphic bundles, with NO auxiliary norm supplied by the caller.
The internally constructed compatible norms preserve the original topology.
The topology and holomorphic atlas use ALL original atlas pairs. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceTensorMetricDraft
open Bundle Set
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (L₁ L₂ : X → Type*)
  [∀ x, AddCommGroup (L₁ x)] [∀ x, Module ℂ (L₁ x)] [∀ x, TopologicalSpace (L₁ x)]
  [TopologicalSpace (TotalSpace ℂ L₁)] [FiberBundle ℂ L₁] [VectorBundle ℂ ℂ L₁]
  [ContMDiffVectorBundle ∞ ℂ L₁ 𝓘(ℂ, ComplexModel n)]
  [∀ x, AddCommGroup (L₂ x)] [∀ x, Module ℂ (L₂ x)] [∀ x, TopologicalSpace (L₂ x)]
  [TopologicalSpace (TotalSpace ℂ L₂)] [FiberBundle ℂ L₂] [VectorBundle ℂ ℂ L₂]
  [ContMDiffVectorBundle ∞ ℂ L₂ 𝓘(ℂ, ComplexModel n)]

local instance norm₁ : ∀ x, NormedAddCommGroup (L₁ x) := originalNormedFibers L₁
local instance inner₁ : ∀ x, InnerProductSpace ℂ (L₁ x) := originalHermitianFibers L₁
local instance norm₂ : ∀ x, NormedAddCommGroup (L₂ x) := originalNormedFibers L₂
local instance inner₂ : ∀ x, InnerProductSpace ℂ (L₂ x) := originalHermitianFibers L₂

/-- Actual tensor total-space topology, constructed from all original
holomorphic bundle charts and the internally compatible fibre norms. -/
@[instance_reducible] def nativeTensorTotalSpaceTopology :
    TopologicalSpace (TotalSpace ℂ (TensorFiber L₁ L₂)) :=
  tensorTotalSpaceTopology L₁ L₂

/-- The original tensor fibres form a genuine line bundle, with actual
all-pair product frames and no supplied output-bundle witness. -/
@[instance_reducible] def nativeTensorFiberBundle : FiberBundle ℂ (TensorFiber L₁ L₂) :=
  tensorFiberBundle L₁ L₂

/-- The actual tensor atlas is a complex vector-bundle atlas. -/
theorem nativeTensorVectorBundle : VectorBundle ℂ ℂ (TensorFiber L₁ L₂) :=
  tensorVectorBundle L₁ L₂

/-- The actual all-pair tensor transitions are holomorphic, on the literal
original tensor fibres, without assuming auxiliary normed input bundles. -/
theorem nativeTensorHolomorphicBundle :
    ContMDiffVectorBundle ∞ ℂ (TensorFiber L₁ L₂) 𝓘(ℂ, ComplexModel n) :=
  tensorHolomorphicBundle L₁ L₂

end SGPT.PSH.SourceTensorMetricDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT NativeTensorBundle

-- BEGIN CHECKED COMPONENT SmoothTensorMetric
/-! Genuine smooth Hermitian tensor reference for arbitrary ORIGINAL
native holomorphic line bundles. Every local holomorphic section is
covered, and no smoothness/curvature output witness is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceTensorMetricDraft
open Bundle Set Filter
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.PSH.LineBundleMetric
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (L₁ L₂ : X → Type*)
  [∀ x, AddCommGroup (L₁ x)] [∀ x, Module ℂ (L₁ x)] [∀ x, TopologicalSpace (L₁ x)]
  [TopologicalSpace (TotalSpace ℂ L₁)] [FiberBundle ℂ L₁] [VectorBundle ℂ ℂ L₁]
  [ContMDiffVectorBundle ∞ ℂ L₁ 𝓘(ℂ, ComplexModel n)]
  [∀ x, AddCommGroup (L₂ x)] [∀ x, Module ℂ (L₂ x)] [∀ x, TopologicalSpace (L₂ x)]
  [TopologicalSpace (TotalSpace ℂ L₂)] [FiberBundle ℂ L₂] [VectorBundle ℂ ℂ L₂]
  [ContMDiffVectorBundle ∞ ℂ L₂ 𝓘(ℂ, ComplexModel n)]
local instance smoothNorm₁ : ∀ x, NormedAddCommGroup (L₁ x) := originalNormedFibers L₁
local instance smoothInner₁ : ∀ x, InnerProductSpace ℂ (L₁ x) := originalHermitianFibers L₁
local instance smoothNorm₂ : ∀ x, NormedAddCommGroup (L₂ x) := originalNormedFibers L₂
local instance smoothInner₂ : ∀ x, InnerProductSpace ℂ (L₂ x) := originalHermitianFibers L₂

/-- Literal tensor of the two ORIGINAL frames. -/
def tensorFrame (p : X) (x : X) : TensorFiber L₁ L₂ x :=
  frame L₁ p x ⊗ₜ[ℂ] frame L₂ p x
abbrev tensorFrameDomain (p : X) : Set X := frameDomain L₁ p ∩ frameDomain L₂ p

theorem tensorFrame_holomorphic (p : X) :
    IsHolomorphicSectionOn (n := n) (TensorFiber L₁ L₂) (tensorFrame L₁ L₂ p)
      (tensorFrameDomain L₁ L₂ p) := by
  let et := tensorTrivialization L₁ L₂ (trivializationAt ℂ L₁ p) (trivializationAt ℂ L₂ p)
  change MDifferentiableOn _ _ _ et.baseSet
  rw [et.mdifferentiableOn_section_baseSet_iff]
  apply (mdifferentiableOn_const (c := (1 : ℂ))).congr
  intro x hx
  have h := et.apply_mk_symm hx (1 : ℂ)
  have hi : et.symm x 1 = tensorFrame L₁ L₂ p x := by
    change (tensorTrivialization L₁ L₂ (trivializationAt ℂ L₁ p)
      (trivializationAt ℂ L₂ p)).symm x 1 = _
    rw [tensorTrivialization_symm L₁ L₂ (trivializationAt ℂ L₁ p)
      (trivializationAt ℂ L₂ p) hx (1 : ℂ),one_smul]
    rfl
  rw [hi] at h
  exact congrArg Prod.snd h

/-- The actual form tensor of the ORIGINAL smooth reference metrics is
smooth for EVERY local holomorphic section of the actual tensor bundle. -/
def smoothTensorMetric (h₁ : HermitianMetric (n := n) L₁)
    (h₂ : HermitianMetric (n := n) L₂) : HermitianMetric (n := n) (TensorFiber L₁ L₂) where
  form := fun x => HermitianForm.tensor (finrank_fiber (L := L₁) x)
    (finrank_fiber (L := L₂) x) (h₁.form x) (h₂.form x)
  smooth := by
    intro s U hU hs e z hz
    let p := e.val.symm z
    let et := tensorTrivialization L₁ L₂ (trivializationAt ℂ L₁ p) (trivializationAt ℂ L₂ p)
    let W := U ∩ tensorFrameDomain L₁ L₂ p
    have hW : IsOpen W := hU.inter ((isOpen_frameDomain (L := L₁) p).inter
      (isOpen_frameDomain (L := L₂) p))
    have hp : p ∈ W := ⟨hz.2,mem_frameDomain (L := L₁) p,mem_frameDomain (L := L₂) p⟩
    let S := e.val.target ∩ e.val.symm ⁻¹' W
    have hS : IsOpen S := e.val.isOpen_inter_preimage_symm hW
    have hzS : z ∈ S := ⟨hz.1,hp⟩
    let g : X → ℂ := fun x => (et (TotalSpace.mk' ℂ x (s x))).2
    have hg : MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) g W :=
      (et.mdifferentiableOn_section_iff (IB := 𝓘(ℂ,ComplexModel n))
        (s := s) hW inter_subset_right).mp (hs.mono inter_subset_left)
    have hnorm : ContDiffAt ℝ ∞ (fun w => Complex.normSq (g (e.val.symm w))) z := by
      apply SGPT.Foundations.Analysis.Pending.BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [hS.mem_nhds hzS] with w hw
      exact differentiableAt_comp_chart_symm e hw.1
        ((hg _ hw.2).mdifferentiableAt (hW.mem_nhds hw.2))
    have hsm₁ := (h₁.smooth (frame L₁ p) (frameDomain L₁ p)
      (isOpen_frameDomain p) (frame_holomorphic p) e).contDiffAt
      ((e.val.isOpen_inter_preimage_symm (isOpen_frameDomain (L := L₁) p)).mem_nhds
        ⟨hz.1,hp.2.1⟩)
    have hsm₂ := (h₂.smooth (frame L₂ p) (frameDomain L₂ p)
      (isOpen_frameDomain p) (frame_holomorphic p) e).contDiffAt
      ((e.val.isOpen_inter_preimage_symm (isOpen_frameDomain (L := L₂) p)).mem_nhds
        ⟨hz.1,hp.2.2⟩)
    have heq : (fun w => (HermitianForm.tensor (finrank_fiber (L := L₁) (e.val.symm w))
        (finrank_fiber (L := L₂) (e.val.symm w)) (h₁.form (e.val.symm w))
        (h₂.form (e.val.symm w))).normSq (s (e.val.symm w))) =ᶠ[𝓝 z]
        fun w => Complex.normSq (g (e.val.symm w)) *
          ((h₁.form (e.val.symm w)).normSq (frame L₁ p (e.val.symm w)) *
          (h₂.form (e.val.symm w)).normSq (frame L₂ p (e.val.symm w))) := by
      filter_upwards [hS.mem_nhds hzS] with w hw
      have hrep : s (e.val.symm w) = g (e.val.symm w) • tensorFrame L₁ L₂ p (e.val.symm w) := by
        have h := et.symm_apply_apply_mk hw.2.2 (s (e.val.symm w))
        rw [tensorTrivialization_symm L₁ L₂ (trivializationAt ℂ L₁ p)
          (trivializationAt ℂ L₂ p) hw.2.2] at h
        exact h.symm
      rw [hrep,HermitianForm.normSq_smul]
      simp only [tensorFrame]
      rw [HermitianForm.normSq_tensor_tmul]
      rw [Complex.normSq_eq_norm_sq]
    exact ((hnorm.mul (hsm₁.mul hsm₂)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- Product formula in the ORIGINAL fibres, with the ORIGINAL reference forms. -/
theorem smoothTensorMetric_tmul (h₁ : HermitianMetric (n := n) L₁)
    (h₂ : HermitianMetric (n := n) L₂) (x : X) (v₁ : L₁ x) (v₂ : L₂ x) :
    ((smoothTensorMetric L₁ L₂ h₁ h₂).form x).normSq (v₁ ⊗ₜ[ℂ] v₂) =
      (h₁.form x).normSq v₁*(h₂.form x).normSq v₂ :=
  HermitianForm.normSq_tensor_tmul (finrank_fiber (L := L₁) x)
    (finrank_fiber (L := L₂) x) (h₁.form x) (h₂.form x) v₁ v₂

end SGPT.PSH.SourceTensorMetricDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT SmoothTensorMetric

-- BEGIN CHECKED COMPONENT TensorCurvature
/-! Actual first Chern comparison in every ORIGINAL chart, obtained from
the internally constructed smooth metric, not assumed. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceTensorMetricDraft
open Bundle Set Filter
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.PSH.LineBundleMetric
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (L₁ L₂ : X → Type*)
  [∀ x, AddCommGroup (L₁ x)] [∀ x, Module ℂ (L₁ x)] [∀ x, TopologicalSpace (L₁ x)]
  [TopologicalSpace (TotalSpace ℂ L₁)] [FiberBundle ℂ L₁] [VectorBundle ℂ ℂ L₁]
  [ContMDiffVectorBundle ∞ ℂ L₁ 𝓘(ℂ, ComplexModel n)]
  [∀ x, AddCommGroup (L₂ x)] [∀ x, Module ℂ (L₂ x)] [∀ x, TopologicalSpace (L₂ x)]
  [TopologicalSpace (TotalSpace ℂ L₂)] [FiberBundle ℂ L₂] [VectorBundle ℂ ℂ L₂]
  [ContMDiffVectorBundle ∞ ℂ L₂ 𝓘(ℂ, ComplexModel n)]
local instance chernNorm₁ : ∀ x, NormedAddCommGroup (L₁ x) := originalNormedFibers L₁
local instance chernInner₁ : ∀ x, InnerProductSpace ℂ (L₁ x) := originalHermitianFibers L₁
local instance chernNorm₂ : ∀ x, NormedAddCommGroup (L₂ x) := originalNormedFibers L₂
local instance chernInner₂ : ∀ x, InnerProductSpace ℂ (L₂ x) := originalHermitianFibers L₂

/-- The actual tensor of nonzero original frames never vanishes. -/
theorem tensorFrame_ne_zero (p : X) {x : X}
    (hx : x ∈ tensorFrameDomain L₁ L₂ p) : tensorFrame L₁ L₂ p x ≠ 0 := by
  let et := tensorTrivialization L₁ L₂ (trivializationAt ℂ L₁ p) (trivializationAt ℂ L₂ p)
  have hi : et.symm x 1 = tensorFrame L₁ L₂ p x := by
    simpa only [one_smul,tensorFrame,frame,et] using
      tensorTrivialization_symm L₁ L₂ (trivializationAt ℂ L₁ p) (trivializationAt ℂ L₂ p) hx 1
  intro h0
  have h1 := congrArg Prod.snd (et.apply_mk_symm hx (1 : ℂ))
  rw [hi,h0] at h1
  have hz : (et (TotalSpace.mk' ℂ x (0 : TensorFiber L₁ L₂ x))).2 = 0 :=
    (et.continuousLinearEquivAt ℂ x hx).map_zero
  rw [hz] at h1
  exact zero_ne_one h1

/-- The genuine Chern form of the genuine smooth tensor metric is the sum
of the ORIGINAL Chern forms, on every chart target, in every dimension. -/
theorem smoothTensorMetric_chern_coeff
    (h₁ : HermitianMetric (n := n) L₁) (h₂ : HermitianMetric (n := n) L₂)
    (e : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (firstChernForm (smoothTensorMetric L₁ L₂ h₁ h₂)).val.coeff e z =
      (firstChernForm h₁).val.coeff e z + (firstChernForm h₂).val.coeff e z := by
  let p := e.val.symm z
  let U := tensorFrameDomain L₁ L₂ p
  have hU : IsOpen U := (isOpen_frameDomain (L := L₁) p).inter (isOpen_frameDomain (L := L₂) p)
  have hp : p ∈ U := ⟨mem_frameDomain (L := L₁) p,mem_frameDomain (L := L₂) p⟩
  let S := e.val.target ∩ e.val.symm ⁻¹' U
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm hU
  have hzS : z ∈ S := ⟨hz,hp⟩
  rw [isFirstChernForm_firstChernForm (smoothTensorMetric L₁ L₂ h₁ h₂)
    (tensorFrame L₁ L₂ p) U hU (tensorFrame_holomorphic L₁ L₂ p)
    (fun x hx => tensorFrame_ne_zero L₁ L₂ p hx) e z hz hp,
    isFirstChernForm_firstChernForm h₁ (frame L₁ p) (frameDomain L₁ p)
      (isOpen_frameDomain p) (frame_holomorphic p) (fun x hx => frame_ne_zero hx) e z hz hp.1,
    isFirstChernForm_firstChernForm h₂ (frame L₂ p) (frameDomain L₂ p)
      (isOpen_frameDomain p) (frame_holomorphic p) (fun x hx => frame_ne_zero hx) e z hz hp.2]
  have hsm₁ := (chartSmooth_localWeight h₁ (isOpen_frameDomain p)
    (frame_holomorphic p) (fun x hx => frame_ne_zero hx) e).mono
      (fun w (hw : w ∈ S) => ⟨hw.1,hw.2.1⟩)
  have hsm₂ := (chartSmooth_localWeight h₂ (isOpen_frameDomain p)
    (frame_holomorphic p) (fun x hx => frame_ne_zero hx) e).mono
      (fun w (hw : w ∈ S) => ⟨hw.1,hw.2.2⟩)
  have heq : localWeight (smoothTensorMetric L₁ L₂ h₁ h₂) (tensorFrame L₁ L₂ p) e =ᶠ[𝓝 z]
      fun w => localWeight h₁ (frame L₁ p) e w+localWeight h₂ (frame L₂ p) e w := by
    filter_upwards [hS.mem_nhds hzS] with w hw
    simp only [localWeight,tensorFrame]
    rw [smoothTensorMetric_tmul,Real.log_mul
      ((h₁.form _).normSq_pos (frame_ne_zero hw.2.1)).ne'
      ((h₂.form _).normSq_pos (frame_ne_zero hw.2.2)).ne']
    ring
  exact (smoothDDC_congr heq).trans (smoothDDC_add hS hsm₁ hsm₂ hzS)

end SGPT.PSH.SourceTensorMetricDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT TensorCurvature

-- BEGIN CHECKED COMPONENT ThetaPshSum
/-! Genuine original theta-PSH sum, including actual local nondegeneracy,
all original poles and n=0. Full source-tensor-psh:theta-sum blueprint
preceded this proof. No positive mass/Kähler/certificate hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceTensorMetricDraft
open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Sum in DIFFERENT original backgrounds, with genuine theta-PSH
nondegeneracy produced from actual original pluripolar pole sets. -/
theorem thetaPsh_sum {θ₁ θ₂ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ₁ u) (hv : IsThetaPshPotential θ₂ v) :
    IsThetaPshPotential (θ₁+θ₂) (fun x => u x+v x) := by
  constructor
  · intro e z hz
    obtain ⟨W₁,ρ₁,hz₁,hρ₁,hpsh₁⟩ := hu.1 e z hz
    obtain ⟨W₂,ρ₂,hz₂,hρ₂,hpsh₂⟩ := hv.1 e z hz
    refine ⟨W₁∩W₂,fun y => ρ₁ y+ρ₂ y,⟨hz₁,hz₂⟩,?_,?_⟩
    · refine ⟨hρ₁.1.inter hρ₂.1,inter_subset_left.trans hρ₁.2.1,
        (hρ₁.2.2.1.mono inter_subset_left).add (hρ₂.2.2.1.mono inter_subset_right),?_⟩
      intro y hy
      rw [smoothDDC_add (hρ₁.1.inter hρ₂.1)
        (hρ₁.2.2.1.mono inter_subset_left) (hρ₂.2.2.1.mono inter_subset_right) hy,
        hρ₁.2.2.2 hy.1,hρ₂.2.2.2 hy.2]
      rfl
    · have heq : (fun y => chartFunction (fun x => u x+v x) e y+((ρ₁ y+ρ₂ y : ℝ):EReal)) =
          (fun y => (chartFunction u e y+(ρ₁ y:EReal))+(chartFunction v e y+(ρ₂ y:EReal))) := by
        funext y
        rw [EReal.coe_add]
        simp only [chartFunction]
        abel
      rw [heq]
      exact (hpsh₁.mono inter_subset_left).add (hpsh₂.mono inter_subset_right)
  · apply ThetaPshConvexCombination.locallyNondegenerate_of_poles_pluripolar (n := n)
    exact (manifoldLocallyPluripolar_union
      (quasiPsh_poles_manifoldLocallyPluripolar hu.quasiPshPotential)
      (quasiPsh_poles_manifoldLocallyPluripolar hv.quasiPshPotential)).mono
      (fun x hx => EReal.add_eq_bot_iff.mp hx)

end SGPT.PSH.SourceTensorMetricDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT ThetaPshSum

-- BEGIN CHECKED COMPONENT TensorPSHMetric
/-! Whole original def:tensorprodpshmetric: actual original tensor bundle,
actual fibrewise product, full PSH metric including zero/polar fibres. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceTensorMetricDraft
open Bundle Set Filter
open scoped Topology Manifold ContDiff TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.PSH.LineBundleMetric
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (L₁ L₂ : X → Type*)
  [∀ x, AddCommGroup (L₁ x)] [∀ x, Module ℂ (L₁ x)] [∀ x, TopologicalSpace (L₁ x)]
  [TopologicalSpace (TotalSpace ℂ L₁)] [FiberBundle ℂ L₁] [VectorBundle ℂ ℂ L₁]
  [ContMDiffVectorBundle ∞ ℂ L₁ 𝓘(ℂ, ComplexModel n)]
  [∀ x, AddCommGroup (L₂ x)] [∀ x, Module ℂ (L₂ x)] [∀ x, TopologicalSpace (L₂ x)]
  [TopologicalSpace (TotalSpace ℂ L₂)] [FiberBundle ℂ L₂] [VectorBundle ℂ ℂ L₂]
  [ContMDiffVectorBundle ∞ ℂ L₂ 𝓘(ℂ, ComplexModel n)]
local instance finalNorm₁ : ∀ x, NormedAddCommGroup (L₁ x) := originalNormedFibers L₁
local instance finalInner₁ : ∀ x, InnerProductSpace ℂ (L₁ x) := originalHermitianFibers L₁
local instance finalNorm₂ : ∀ x, NormedAddCommGroup (L₂ x) := originalNormedFibers L₂
local instance finalInner₂ : ∀ x, InnerProductSpace ℂ (L₂ x) := originalHermitianFibers L₂

/-- Literal singular tensor twisting identity on actual pure tensors,
including BOTH zero factors and ALL genuine polar cases. -/
theorem twistedForm_tensor_tmul (h₁ : HermitianMetric (n := n) L₁)
    (h₂ : HermitianMetric (n := n) L₂) (u v : X → EReal)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤)
    (x : X) (v₁ : L₁ x) (v₂ : L₂ x) :
    tensorMetric (twistedForm h₁ u) (twistedForm h₂ v) x (v₁ ⊗ₜ[ℂ] v₂) =
      twistedForm (smoothTensorMetric L₁ L₂ h₁ h₂) (fun y => u y+v y) x (v₁ ⊗ₜ[ℂ] v₂) := by
  classical
  have hformula := lineFormTensor_tmul (finrank_fiber (L := L₁) x)
    (finrank_fiber (L := L₂) x) (isHermitianOrSingular_twistedForm h₁ hu x)
    (isHermitianOrSingular_twistedForm h₂ hv x) v₁ v₂
  change tensorMetric _ _ _ _ = _ at hformula
  rw [hformula]
  by_cases hv₁ : v₁ = 0
  · subst v₁
    simp [twistedForm]
  by_cases hv₂ : v₂ = 0
  · subst v₂
    simp [twistedForm]
  have htensor : v₁ ⊗ₜ[ℂ] v₂ ≠ 0 := by
    intro h0
    have hpos := mul_pos ((h₁.form x).normSq_pos hv₁) ((h₂.form x).normSq_pos hv₂)
    have hh := smoothTensorMetric_tmul L₁ L₂ h₁ h₂ x v₁ v₂
    rw [h0,HermitianForm.normSq_zero] at hh
    exact hpos.ne' hh.symm
  simp only [twistedForm,if_neg hv₁,if_neg hv₂,if_neg htensor]
  rw [smoothTensorMetric_tmul,ENNReal.ofReal_mul ((h₁.form x).normSq_nonneg v₁),
    EReal.neg_add (Or.inr (hv x)) (Or.inl (hu x)),sub_eq_add_neg,EReal.exp_add]
  ac_rfl

/-- The literal ORIGINAL tensor metric is represented by the true smooth
reference tensor metric and the ORIGINAL potential sum, on EVERY vector. -/
theorem twistedForm_tensor (h₁ : HermitianMetric (n := n) L₁)
    (h₂ : HermitianMetric (n := n) L₂) (u v : X → EReal)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤) (x : X) (w : TensorFiber L₁ L₂ x) :
    tensorMetric (twistedForm h₁ u) (twistedForm h₂ v) x w =
      twistedForm (smoothTensorMetric L₁ L₂ h₁ h₂) (fun y => u y+v y) x w := by
  let A := tensorCoordinateEquiv L₁ L₂ (trivializationAt ℂ L₁ x) (trivializationAt ℂ L₂ x)
    x (mem_frameDomain (L := L₁) x) (mem_frameDomain (L := L₂) x)
  have hrep : w = (A w • frame L₁ x x) ⊗ₜ[ℂ] frame L₂ x x := by
    have hh := tensorCoordinateEquiv_symm_apply L₁ L₂ (trivializationAt ℂ L₁ x)
      (trivializationAt ℂ L₂ x) x (mem_frameDomain (L := L₁) x)
      (mem_frameDomain (L := L₂) x) (A w)
    change A.symm (A w) = _ at hh
    rw [A.symm_apply_apply] at hh
    simpa only [frame,TensorProduct.smul_tmul'] using hh
  rw [hrep]
  exact twistedForm_tensor_tmul L₁ L₂ h₁ h₂ u v hu hv x _ _

/-- Full original tensor-product PSH metric on the internally constructed
actual holomorphic tensor line bundle. No compactness, mass, auxiliary
norms, tensor atlas, smooth tensor metric or curvature equality is an input. -/
theorem tensorMetric_isPSH
    {q₁ : (x : X) → L₁ x → ℝ≥0∞} {q₂ : (x : X) → L₂ x → ℝ≥0∞}
    (h₁ : IsPSHMetric (n := n) L₁ q₁) (h₂ : IsPSHMetric (n := n) L₂ q₂) :
    IsPSHMetric (n := n) (TensorFiber L₁ L₂) (tensorMetric q₁ q₂) := by
  obtain ⟨h₀₁,u,hu⟩ := h₁.twist
  obtain ⟨h₀₂,v,hv⟩ := h₂.twist
  apply IsPSHMetric.of_with (h₀ := smoothTensorMetric L₁ L₂ h₀₁ h₀₂)
    (φ := fun x => u x+v x)
  constructor
  · have hsum := thetaPsh_sum hu.thetaPsh hv.thetaPsh
    have hcoeff : (firstChernForm (smoothTensorMetric L₁ L₂ h₀₁ h₀₂)).val.GeometricallyEq
        ((firstChernForm h₀₁).val+(firstChernForm h₀₂).val) := by
      intro e z hz
      exact smoothTensorMetric_chern_coeff L₁ L₂ h₀₁ h₀₂ e hz
    exact (hcoeff.thetaPshPotential_iff _).mpr hsum
  · intro x w
    have hq₁ : q₁ = twistedForm h₀₁ u := by funext y a; exact hu.eq_twisted y a
    have hq₂ : q₂ = twistedForm h₀₂ v := by funext y a; exact hv.eq_twisted y a
    rw [hq₁,hq₂]
    exact twistedForm_tensor L₁ L₂ h₀₁ h₀₂ u v
      (fun y => hu.thetaPsh.1.quasiPlurisubharmonic.ne_top y)
      (fun y => hv.thetaPsh.1.quasiPlurisubharmonic.ne_top y) x w

end SGPT.PSH.SourceTensorMetricDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT TensorPSHMetric
