import SGPT.Trace.BertiniDefiningSectionCoordinates
import SGPT.LineBundle.TMetricExists
import SGPT.PSH.GlobalL2CoverSystem
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The actual intrinsic native line-valued differential at an original zero.

Original native section coefficients and their actual transitions produce
frame independence by the product rule and actual section vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.LineBundle.TMetric
open SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (E : HermitianHolomorphicLineBundle.{0,0} n X)

/-- Actual physical section coefficients obey the actual original native
frame transition, without an assumed scalar-transition dictionary. -/
theorem nativeSectionCoefficient_transition
    (S : HolomorphicSections (n := n) E.Fiber) (e f : AtlasFrame E) {x : X}
    (hx : x ∈ e.val.baseSet ∩ f.val.baseSet) :
    sectionCoefficient E.Fiber f.val S x =
      frameTransition e f x * sectionCoefficient E.Fiber e.val S x := by
  let := e.property
  let := f.property
  have hrep := trivialization_eq_coef_smul_frame e.val hx.1 (S x)
  have hcoef : f.val.continuousLinearMapAt ℂ x (e.val.symm x 1) = frameTransition e f x := by
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) f.val hx.2]
    exact (Trivialization.coordChangeL_apply e.val f.val hx 1).symm
  unfold sectionCoefficient
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) f.val hx.2]
  conv_lhs => rw [hrep]
  rw [map_smul, hcoef, smul_eq_mul, mul_comm]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hx.1]

/-- The actual line-fibre-valued native derivative in a given original frame. -/
def nativeSectionFrameDifferential (S : HolomorphicSections (n := n) E.Fiber)
    (e : AtlasFrame E) (x : X) : TangentSpace 𝓘(ℂ, ComplexModel n) x →ₗ[ℂ] E.Fiber x where
  toFun v := (show ℂ from mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
    (sectionCoefficient E.Fiber e.val S) x v) • e.val.symm x 1
  map_add' u v := by rw [map_add, add_smul]
  map_smul' a v := by rw [map_smul, smul_smul]; rfl

/-- At an actual original section zero, the genuine original product rule
cancels the transition derivative and gives intrinsic frame independence. -/
theorem nativeSectionFrameDifferential_independent
    (S : HolomorphicSections (n := n) E.Fiber) (e f : AtlasFrame E) {x : X}
    (hx : x ∈ e.val.baseSet ∩ f.val.baseSet) (hS : S x = 0) :
    nativeSectionFrameDifferential E S e x = nativeSectionFrameDifferential E S f x := by
  let := e.property
  let := f.property
  have he : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (sectionCoefficient E.Fiber e.val S) x :=
    ((e.val.contMDiffAt_section_iff hx.1).mp (S.contMDiff x)).mdifferentiableAt (by simp)
  have hg := frameTransition_mdifferentiableAt e f hx
  have hz : sectionCoefficient E.Fiber e.val S x = 0 := by
    change (e.val.linearEquivAt ℂ x hx.1) (S x) = 0
    rw [hS, map_zero]
  have heq : sectionCoefficient E.Fiber f.val S =ᶠ[𝓝 x]
      (fun y => frameTransition e f y * sectionCoefficient E.Fiber e.val S y) := by
    filter_upwards [(e.val.open_baseSet.inter f.val.open_baseSet).mem_nhds hx] with y hy
    exact nativeSectionCoefficient_transition E S e f hy
  have hprod := (hg.hasMFDerivAt.mul he.hasMFDerivAt).congr_of_eventuallyEq heq
  let De : TangentSpace 𝓘(ℂ, ComplexModel n) x →L[ℂ] ℂ :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (sectionCoefficient E.Fiber e.val S) x
  let Df : TangentSpace 𝓘(ℂ, ComplexModel n) x →L[ℂ] ℂ :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (sectionCoefficient E.Fiber f.val S) x
  let Dg : TangentSpace 𝓘(ℂ, ComplexModel n) x →L[ℂ] ℂ :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (frameTransition e f) x
  have hd (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
      Df v = frameTransition e f x * De v := by
    have h := DFunLike.congr_fun hprod.mfderiv v
    change Df v = frameTransition e f x * De v + sectionCoefficient E.Fiber e.val S x * Dg v at h
    rwa [hz, zero_mul, add_zero] at h
  apply LinearMap.ext
  intro v
  change De v • e.val.symm x 1 = Df v • f.val.symm x 1
  rw [hd v, frame_eq_smul e f hx, smul_smul]
  rw [mul_comm]

/-- The actual original section produces its actual intrinsic line-valued
differential at its original zero, without a connection or conormal input. -/
def nativeSectionDifferentialAtZero (S : HolomorphicSections (n := n) E.Fiber)
    (x : X) (_hS : S x = 0) : TangentSpace 𝓘(ℂ, ComplexModel n) x →ₗ[ℂ] E.Fiber x :=
  nativeSectionFrameDifferential E S ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩ x

theorem nativeSectionDifferentialAtZero_in_frame (S : HolomorphicSections (n := n) E.Fiber)
    (x : X) (hS : S x = 0) (e : AtlasFrame E) (hx : x ∈ e.val.baseSet) :
    nativeSectionDifferentialAtZero E S x hS = nativeSectionFrameDifferential E S e x :=
  nativeSectionFrameDifferential_independent E S _ e
    ⟨mem_baseSet_trivializationAt ℂ E.Fiber x, hx⟩ hS

end SGPT.Trace.Bertini
