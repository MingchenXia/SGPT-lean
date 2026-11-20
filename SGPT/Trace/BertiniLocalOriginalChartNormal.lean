import SGPT.Trace.BertiniGlobalOriginalNormal

/-! Actual fixed-chart local normals and holomorphic original denominators.
Nonzero partials are produced from the original smooth member; no normal,
gradient-nonvanishing or metric certificate is supplied to that producer. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N) (j : Fin (N + 1))

def nativeBertiniChartEquation (e : ComplexChart n X) (z : ComplexModel n) : ℂ :=
  pairing (affineLift i ζ) (chartLift p e j z)

theorem nativeBertiniScalarDifferential_in_chart (e : ComplexChart n X) (x : X)
    (hex : x ∈ e.val.source) (hpx : p x ∈ (affineChart j).source)
    (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    nativeScalarDifferential (nativeBertiniLocalEquation p i ζ j) x v =
      fderiv ℂ (nativeBertiniChartEquation p i ζ j e) (e.val x)
        (nativeOriginalChartTangentEquiv e x hex v) := by
  have heq : nativeBertiniLocalEquation p i ζ j =ᶠ[𝓝 x]
      (nativeBertiniChartEquation p i ζ j e ∘ e.val) := by
    filter_upwards [e.val.open_source.mem_nhds hex] with y hy
    change pairing (affineLift i ζ) (affineLift j (affineChart j (p y))) =
      pairing (affineLift i ζ) (chartLift p e j (e.val y))
    rw [chartLift_chart p hy]
  have hG : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (nativeBertiniChartEquation p i ζ j e) (e.val x) :=
    (hasFDerivAt_pairing_chartLift p p.contMDiff ((mem_chartLiftDomain_iff p hex).mpr hpx)
      (affineLift i ζ)).differentiableAt.mdifferentiableAt
  have he := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hex
  have hcomp := mfderiv_comp x hG he
  rw [mfderiv_eq_fderiv] at hcomp
  rw [nativeOriginalChartTangentEquiv_apply]
  unfold nativeScalarDifferential
  rw [heq.mfderiv_eq, hcomp]
  rfl

def nativeBertiniLocalChartNormal (e : ComplexChart n X) (m : Fin n) (x : X)
    (hex : x ∈ e.val.source) : TangentSpace 𝓘(ℂ, ComplexModel n) x :=
  (nativeOriginalChartTangentEquiv e x hex).symm
    ((chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) x)⁻¹ •
      EuclideanSpace.single m 1)

theorem nativeBertiniLocalChartNormal_spec (e : ComplexChart n X) (m : Fin n) (x : X)
    (hex : x ∈ e.val.source) (hpx : p x ∈ (affineChart j).source)
    (hx : x ∈ member p (affinePoint i ζ))
    (hm : chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) x ≠ 0) :
    nativeBertiniIntrinsicConormal p i ζ x hx (nativeBertiniLocalChartNormal p i ζ j e m x hex) =
      nativeBertiniCoordinateSection p j x := by
  unfold nativeBertiniIntrinsicConormal
  rw [nativeBertiniSectionDifferentialAtZero p i ζ j x hpx hx,
    nativeBertiniScalarDifferential_in_chart p i ζ j e x hex hpx]
  unfold nativeBertiniLocalChartNormal
  rw [LinearEquiv.apply_symm_apply, map_smul]
  change ((chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) x)⁻¹ *
    chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) x) • _ = _
  rw [inv_mul_cancel₀ hm, one_smul]

theorem exists_nativeBertiniChartPartial_ne_zero (e : ComplexChart n X) (x : X)
    (hex : x ∈ e.val.source) (hpx : p x ∈ (affineChart j).source)
    (hx : x ∈ member p (affinePoint i ζ))
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    ∃ m : Fin n, chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) x ≠ 0 := by
  let s := nativeBertiniCoordinateSection p j x
  let ν := nativeBertiniNormalLift p i ζ x hx hsm s
  let C := nativeBertiniCoordinateFiberEquiv p j x hpx
  have hs : C s = 1 := nativeBertiniCoordinateFiberEquiv_coordinate p j x hpx
  have hnorm := nativeBertiniNormalLift_spec p i ζ x hx hsm s
  unfold nativeBertiniIntrinsicConormal at hnorm
  rw [nativeBertiniSectionDifferentialAtZero p i ζ j x hpx hx] at hnorm
  have hg : nativeScalarDifferential (nativeBertiniLocalEquation p i ζ j) x ν = 1 := by
    have h := congrArg C hnorm
    change C (nativeScalarDifferential (nativeBertiniLocalEquation p i ζ j) x ν • s) = C s at h
    rw [map_smul, hs, smul_eq_mul, mul_one] at h
    exact h
  rw [nativeBertiniScalarDifferential_in_chart p i ζ j e x hex hpx] at hg
  by_contra hn
  push Not at hn
  have hD : (fderiv ℂ (nativeBertiniChartEquation p i ζ j e) (e.val x)).toLinearMap = 0 := by
    apply (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.ext
    intro k
    have hk := hn k
    change fderiv ℂ (nativeBertiniChartEquation p i ζ j e) (e.val x) (EuclideanSpace.single k 1) = 0 at hk
    change fderiv ℂ (nativeBertiniChartEquation p i ζ j e) (e.val x)
      ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis k) = 0
    change fderiv ℂ (nativeBertiniChartEquation p i ζ j e) (e.val x)
      (EuclideanSpace.basisFun (Fin n) ℂ k) = 0
    rw [EuclideanSpace.basisFun_apply]
    exact hk
  have hzero := DFunLike.congr_fun hD (nativeOriginalChartTangentEquiv e x hex ν)
  change fderiv ℂ (nativeBertiniChartEquation p i ζ j e) (e.val x)
    (nativeOriginalChartTangentEquiv e x hex ν) = 0 at hzero
  exact one_ne_zero (hg.symm.trans hzero)

omit [IsComplexManifold n X] in
theorem nativeBertiniLocalEquation_holomorphicAt (x : X)
    (hpx : p x ∈ (affineChart j).source) :
    HolomorphicAt n (nativeBertiniLocalEquation p i ζ j) x := by
  filter_upwards [p.contMDiff.continuous.continuousAt.eventually
    ((affineChart j).open_source.mem_nhds hpx)] with y hy
  exact nativeBertiniLocalEquation_mdifferentiableAt p i ζ j y hy

theorem nativeBertiniChartPartial_holomorphicAt (e : ComplexChart n X) (m : Fin n) (x : X)
    (hex : x ∈ e.val.source) (hpx : p x ∈ (affineChart j).source) :
    HolomorphicAt n (chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j)) x :=
  holomorphicAt_chartDeriv hex (nativeBertiniLocalEquation_holomorphicAt p i ζ j x hpx)

end SGPT.Trace.Bertini
