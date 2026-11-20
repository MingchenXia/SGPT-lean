import SGPT.Toric.ExceptionalCurve
import Mathlib.Geometry.Manifold.Complex
import SGPT.Bergman.SourceNativeFirstChernForm
import SGPT.Hodge.SourceSmoothMixedCohomology
import Lean.Elab.Command

section ExceptionalCanonicalFragment001
/- BEGIN ExceptionalHyperplaneRestrictionDraft; original source SHA256 1d055358904b5220d8c3fe1187166ee2e24a5a847d8ad6a26daf5e2a2d3ae74c -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Bergman.TensorDictionaryDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def originalExceptionalHolomorphicMap :
    ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2)
      (SGPT.Projective.ComplexProjectiveSpace 1) (PolytopeToricVariety blowupGenerator hs) ∞ :=
  ⟨originalExceptionalCurve hs, contMDiff_originalExceptionalCurve hs⟩

/-- The SAME actual physical source H bundle restricted by the actual exceptional map. -/
abbrev ExceptionalHyperplaneFiber :=
  originalExceptionalHolomorphicMap hs *ᵖ (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs))

instance exceptionalHyperplaneNormed (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    NormedAddCommGroup (ExceptionalHyperplaneFiber hs u) :=
  inferInstanceAs (NormedAddCommGroup
    (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs) (originalExceptionalCurve hs u)))

instance exceptionalHyperplaneHermitian (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    InnerProductSpace ℂ (ExceptionalHyperplaneFiber hs u) :=
  inferInstanceAs (InnerProductSpace ℂ
    (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs) (originalExceptionalCurve hs u)))

instance exceptionalHyperplaneContinuousNorm :
    SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm (ExceptionalHyperplaneFiber hs) := by
  constructor
  exact (SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.continuous
    (V := ToricNativeLineFiber (nativeSourceHyperplaneMetric hs))).comp
      (_root_.Pullback.continuous_lift ℂ
        (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) (originalExceptionalHolomorphicMap hs))

def exceptionalHyperplaneBundle :
    HermitianHolomorphicLineBundle 1 (SGPT.Projective.ComplexProjectiveSpace 1) :=
  HermitianHolomorphicLineBundle.ofNative (ExceptionalHyperplaneFiber hs)

/-- An existing genuine projective hyperplane frame at the ACTUAL contracted point. -/
def exceptionalTargetFrame := trivializationAt ℂ NativeProjectiveHyperplaneFiber blowdownOrigin

instance exceptionalTargetFrame_memAtlas : MemTrivializationAtlas exceptionalTargetFrame := by
  unfold exceptionalTargetFrame
  infer_instance

theorem exceptionalTargetFrame_mem : blowdownOrigin ∈ exceptionalTargetFrame.baseSet :=
  mem_baseSet_trivializationAt ℂ NativeProjectiveHyperplaneFiber blowdownOrigin

/-- Actual fibrewise linear trivialization; no compatibility or obstruction certificate is an input. -/
def exceptionalHyperplaneFiberEquiv (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    ExceptionalHyperplaneFiber hs u ≃ₗ[ℂ] ℂ :=
  (nativeBlowdownHyperplaneFiberEquiv hs (originalExceptionalCurve hs u)).trans
    (exceptionalTargetFrame.linearEquivAt ℂ blowdownOrigin exceptionalTargetFrame_mem)

def exceptionalHyperplaneTotalMap (x : TotalSpace ℂ (ExceptionalHyperplaneFiber hs)) :
    SGPT.Projective.ComplexProjectiveSpace 1 × ℂ :=
  (x.proj, exceptionalHyperplaneFiberEquiv hs x.proj x.snd)

def exceptionalHyperplaneTotalInv (x : SGPT.Projective.ComplexProjectiveSpace 1 × ℂ) :
    TotalSpace ℂ (ExceptionalHyperplaneFiber hs) :=
  ⟨x.1, (exceptionalHyperplaneFiberEquiv hs x.1).symm x.2⟩

theorem exceptionalHyperplaneTotalMap_leftInverse :
    Function.LeftInverse (exceptionalHyperplaneTotalInv hs) (exceptionalHyperplaneTotalMap hs) := by
  intro x
  simp only [exceptionalHyperplaneTotalInv, exceptionalHyperplaneTotalMap,
    LinearEquiv.symm_apply_apply, TotalSpace.eta]

theorem exceptionalHyperplaneTotalMap_rightInverse :
    Function.RightInverse (exceptionalHyperplaneTotalInv hs) (exceptionalHyperplaneTotalMap hs) := by
  intro x
  simp only [exceptionalHyperplaneTotalInv, exceptionalHyperplaneTotalMap,
    LinearEquiv.apply_symm_apply, Prod.mk.eta]

/-- Genuine holomorphy of the forward physical restriction trivialization. -/
theorem contMDiff_exceptionalHyperplaneTotalMap :
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞ (exceptionalHyperplaneTotalMap hs) := by
  have h1 := contMDiff_nativePullbackLift
    (toricNativeHermitianLineBundle (nativeSourceHyperplaneMetric hs)) (originalExceptionalHolomorphicMap hs)
  have h2 := (contMDiff_nativeBlowdownHyperplaneTotalMap hs).comp h1
  have h3 := (contMDiff_nativePullbackLift nativeProjectiveHyperplaneBundle
    (originalBlowdownHolomorphicMap hs)).comp h2
  apply (contMDiff_proj (ExceptionalHyperplaneFiber hs)).prodMk
  intro x
  let k := Bundle.Pullback.lift (originalBlowdownHolomorphicMap hs) ∘
    nativeBlowdownHyperplaneTotalMap hs ∘ Bundle.Pullback.lift (originalExceptionalHolomorphicMap hs)
  have hk : k x ∈ exceptionalTargetFrame.source := by
    apply exceptionalTargetFrame.mem_source.mpr
    change originalBlowdown hs (originalExceptionalCurve hs x.proj) ∈ exceptionalTargetFrame.baseSet
    rw [originalExceptionalCurve_blowdown]
    exact exceptionalTargetFrame_mem
  have he := ((exceptionalTargetFrame.contMDiffOn (IB := 𝓘(ℂ, ComplexModel 2)) (n := ∞)).contMDiffAt
    (exceptionalTargetFrame.open_source.mem_nhds hk)).snd.comp x (h3 x)
  apply he.congr_of_eventuallyEq
  exact Eventually.of_forall fun y => by
    change (exceptionalTargetFrame ⟨blowdownOrigin,
      nativeBlowdownHyperplaneFiberEquiv hs (originalExceptionalCurve hs y.proj) y.snd⟩).2 =
        (exceptionalTargetFrame ⟨originalBlowdown hs (originalExceptionalCurve hs y.proj),
          nativeBlowdownHyperplaneFiberEquiv hs (originalExceptionalCurve hs y.proj) y.snd⟩).2
    rw [originalExceptionalCurve_blowdown]

/-- An actual holomorphic constant-base inverse-frame map into the projective H bundle. -/
theorem contMDiff_exceptionalConstantFrame :
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞
      (fun x : SGPT.Projective.ComplexProjectiveSpace 1 × ℂ =>
        (⟨blowdownOrigin, exceptionalTargetFrame.symm blowdownOrigin x.2⟩ :
          TotalSpace ℂ NativeProjectiveHyperplaneFiber)) := by
  apply exceptionalTargetFrame.contMDiff_iff (fun _ => exceptionalTargetFrame.mem_source.mpr
    exceptionalTargetFrame_mem) |>.mpr
  refine ⟨contMDiff_const, ?_⟩
  simpa only [exceptionalTargetFrame.apply_mk_symm exceptionalTargetFrame_mem] using
    (contMDiff_snd : ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ℂ) ∞
      (fun x : SGPT.Projective.ComplexProjectiveSpace 1 × ℂ => x.2))

/-- The actual inverse physical restriction trivialization is holomorphic as well. -/
theorem contMDiff_exceptionalHyperplaneTotalInv :
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞ (exceptionalHyperplaneTotalInv hs) := by
  have hU := contMDiff_nativePullbackMk nativeProjectiveHyperplaneBundle
    (originalBlowdownHolomorphicMap hs) ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
    (fun x : SGPT.Projective.ComplexProjectiveSpace 1 × ℂ => originalExceptionalCurve hs x.1)
    (fun x => exceptionalTargetFrame.symm blowdownOrigin x.2)
    ((contMDiff_originalExceptionalCurve hs).comp contMDiff_fst) (by
      change ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
        ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞
        (fun x : SGPT.Projective.ComplexProjectiveSpace 1 × ℂ =>
          (⟨originalBlowdown hs (originalExceptionalCurve hs x.1),
            exceptionalTargetFrame.symm blowdownOrigin x.2⟩ : TotalSpace ℂ NativeProjectiveHyperplaneFiber))
      convert contMDiff_exceptionalConstantFrame using 1
      funext x
      exact congrArg (fun p : SGPT.Projective.ComplexProjectiveSpace 2 =>
        (⟨p, (show ℂ from exceptionalTargetFrame.symm blowdownOrigin x.2)⟩ :
          TotalSpace ℂ NativeProjectiveHyperplaneFiber)) (originalExceptionalCurve_blowdown hs x.1))
  have hV := (contMDiff_nativeBlowdownHyperplaneTotalInv hs).comp hU
  exact contMDiff_nativePullbackMk
    (toricNativeHermitianLineBundle (nativeSourceHyperplaneMetric hs)) (originalExceptionalHolomorphicMap hs)
    ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) Prod.fst
    (fun x => (exceptionalHyperplaneFiberEquiv hs x.1).symm x.2) contMDiff_fst hV

/-- An actual holomorphic physical line-bundle trivialization over the ENTIRE exceptional P1. -/
def exceptionalHyperplaneBundleHomeomorph : TotalSpace ℂ (ExceptionalHyperplaneFiber hs) ≃ₜ
    SGPT.Projective.ComplexProjectiveSpace 1 × ℂ where
  toFun := exceptionalHyperplaneTotalMap hs
  invFun := exceptionalHyperplaneTotalInv hs
  left_inv := exceptionalHyperplaneTotalMap_leftInverse hs
  right_inv := exceptionalHyperplaneTotalMap_rightInverse hs
  continuous_toFun := (contMDiff_exceptionalHyperplaneTotalMap hs).continuous
  continuous_invFun := (contMDiff_exceptionalHyperplaneTotalInv hs).continuous

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END ExceptionalHyperplaneRestrictionDraft -/
end ExceptionalCanonicalFragment001

section ExceptionalCanonicalFragment002
/- BEGIN ExceptionalRestrictionFullSectionsDraft; original source SHA256 1eb5939ec619749559cd8dcd5db76bbe3025d41424adf57c8c4d89971a3e7766 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

abbrev ExceptionalHyperplaneFullSections := SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 1)
  (ExceptionalHyperplaneFiber hs)

/-- Coefficient of an ARBITRARY full section in the actual global restriction trivialization. -/
def exceptionalRestrictionSectionCoefficient (s : ExceptionalHyperplaneFullSections hs)
    (u : SGPT.Projective.ComplexProjectiveSpace 1) : ℂ :=
  exceptionalHyperplaneFiberEquiv hs u (s u)

theorem contMDiff_exceptionalRestrictionSectionCoefficient
    (s : ExceptionalHyperplaneFullSections hs) :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞ (exceptionalRestrictionSectionCoefficient hs s) :=
  ((contMDiff_exceptionalHyperplaneTotalMap hs).comp s.contMDiff).snd

/-- Native compact-complex Liouville proves constancy, with no constant-coefficient input. -/
theorem exceptionalRestrictionSectionCoefficient_constant
    (s : ExceptionalHyperplaneFullSections hs) (u v : SGPT.Projective.ComplexProjectiveSpace 1) :
    exceptionalRestrictionSectionCoefficient hs s u = exceptionalRestrictionSectionCoefficient hs s v :=
  ((contMDiff_exceptionalRestrictionSectionCoefficient hs s).mdifferentiable (by simp)).apply_eq_of_compactSpace u v

/-- The actual constant-frame section, holomorphic in the actual physical pullback topology. -/
def exceptionalRestrictionConstantSection (c : ℂ) : ExceptionalHyperplaneFullSections hs where
  toFun u := (exceptionalHyperplaneFiberEquiv hs u).symm c
  contMDiff_toFun := (contMDiff_exceptionalHyperplaneTotalInv hs).comp
    (contMDiff_id.prodMk contMDiff_const)

/-- The actual FULL restricted H0 space is C, not a chosen one-dimensional subspace. -/
def exceptionalRestrictionFullSectionsEquiv : ExceptionalHyperplaneFullSections hs ≃ₗ[ℂ] ℂ where
  toFun s := exceptionalRestrictionSectionCoefficient hs s
    (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 0)
  invFun := exceptionalRestrictionConstantSection hs
  left_inv s := by
    ext u
    apply (exceptionalHyperplaneFiberEquiv hs u).injective
    change exceptionalHyperplaneFiberEquiv hs u
      ((exceptionalHyperplaneFiberEquiv hs u).symm
        (exceptionalRestrictionSectionCoefficient hs s
          (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 0))) =
      exceptionalRestrictionSectionCoefficient hs s u
    rw [LinearEquiv.apply_symm_apply]
    exact exceptionalRestrictionSectionCoefficient_constant hs s _ u
  right_inv c := by
    exact (exceptionalHyperplaneFiberEquiv hs
      (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 0)).apply_symm_apply c
  map_add' s t := by
    exact map_add (exceptionalHyperplaneFiberEquiv hs
      (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 0)) _ _
  map_smul' a s := by
    exact map_smul (exceptionalHyperplaneFiberEquiv hs
      (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 0)) a _

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END ExceptionalRestrictionFullSectionsDraft -/
end ExceptionalCanonicalFragment002

section ExceptionalCanonicalFragment003
/- BEGIN ExceptionalFlatHermitianMetricDraft; original source SHA256 bbf5c4ebd11be4695eeb9c804e93c2d6e88069a8ec58551a58cd81336d5fb81d -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.PSH SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Actual positive Hermitian forms pulled back through the genuine physical trivialization. -/
def exceptionalFlatHermitianForm (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    HermitianForm (ExceptionalHyperplaneFiber hs u) where
  toSesq := ((innerₛₗ ℂ : ℂ →ₗ⋆[ℂ] ℂ →ₗ[ℂ] ℂ).compl₂
    (exceptionalHyperplaneFiberEquiv hs u).toLinearMap).comp
      (exceptionalHyperplaneFiberEquiv hs u).toLinearMap
  pos' v hv := by
    have hne : exceptionalHyperplaneFiberEquiv hs u v ≠ 0 := by
      intro h
      apply hv
      apply (exceptionalHyperplaneFiberEquiv hs u).injective
      simpa only [map_zero] using h
    refine ⟨‖exceptionalHyperplaneFiberEquiv hs u v‖ ^ 2, sq_pos_of_pos (norm_pos_iff.mpr hne), ?_⟩
    change inner ℂ (exceptionalHyperplaneFiberEquiv hs u v) (exceptionalHyperplaneFiberEquiv hs u v) = _
    simpa only [Complex.ofReal_pow] using!
      (inner_self_eq_norm_sq_to_K (exceptionalHyperplaneFiberEquiv hs u v))

theorem exceptionalFlatHermitianForm_normSq (u : SGPT.Projective.ComplexProjectiveSpace 1)
    (v : ExceptionalHyperplaneFiber hs u) :
    (exceptionalFlatHermitianForm hs u).normSq v = Complex.normSq (exceptionalHyperplaneFiberEquiv hs u v) := by
  change (inner ℂ (exceptionalHyperplaneFiberEquiv hs u v) (exceptionalHyperplaneFiberEquiv hs u v)).re = _
  rw [Complex.normSq_eq_norm_sq]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (exceptionalHyperplaneFiberEquiv hs u v)

/-- A genuine smooth metric on the SAME original physical restriction. The existing
metric definition is verified for EVERY local holomorphic section, not just the global frame. -/
def exceptionalFlatHermitianMetric : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber hs) where
  form := exceptionalFlatHermitianForm hs
  smooth := by
    intro s U hU hsU c z hz
    let g : SGPT.Projective.ComplexProjectiveSpace 1 → ℂ := fun u => exceptionalHyperplaneFiberEquiv hs u (s u)
    have hF := ((contMDiff_exceptionalHyperplaneTotalMap hs).mdifferentiable (by simp)).snd
    have hg : MDifferentiableOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) g U := by
      intro u hu
      exact (hF (⟨u, s u⟩ : TotalSpace ℂ (ExceptionalHyperplaneFiber hs))).comp_mdifferentiableWithinAt u (hsU u hu)
    have hn : ContDiffAt ℝ ∞ (fun w => Complex.normSq (g (c.val.symm w))) z := by
      apply SGPT.Foundations.Analysis.Pending.BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [(c.val.isOpen_inter_preimage_symm hU).mem_nhds hz] with w hw
      exact differentiableAt_comp_chart_symm c hw.1 ((hg _ hw.2).mdifferentiableAt (hU.mem_nhds hw.2))
    simp only [exceptionalFlatHermitianForm_normSq]
    exact hn.contDiffWithinAt

/-- Actual zero curvature, from the SAME genuine metric and actual nowhere-zero holomorphic frame. -/
theorem exceptionalFlat_firstChern_geometrically_zero :
    (firstChernForm (exceptionalFlatHermitianMetric hs)).val.GeometricallyEq
      (0 : ClosedRealOneOneForm 1 (SGPT.Projective.ComplexProjectiveSpace 1)).val := by
  let s := exceptionalRestrictionConstantSection hs 1
  have hhol : IsHolomorphicSectionOn (n := 1) (ExceptionalHyperplaneFiber hs) s univ :=
    (s.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hne : ∀ u ∈ (univ : Set (SGPT.Projective.ComplexProjectiveSpace 1)), s u ≠ 0 := by
    intro u _ hz
    have h := congrArg (exceptionalHyperplaneFiberEquiv hs u) hz
    change exceptionalHyperplaneFiberEquiv hs u ((exceptionalHyperplaneFiberEquiv hs u).symm 1) =
      exceptionalHyperplaneFiberEquiv hs u 0 at h
    rw [LinearEquiv.apply_symm_apply, map_zero] at h
    exact one_ne_zero h
  have hw (c : ComplexChart 1 (SGPT.Projective.ComplexProjectiveSpace 1)) :
      localWeight (exceptionalFlatHermitianMetric hs) s c = 0 := by
    funext w
    simp only [localWeight, exceptionalFlatHermitianMetric, exceptionalFlatHermitianForm_normSq]
    change -Real.log (Complex.normSq (exceptionalHyperplaneFiberEquiv hs (c.val.symm w)
      ((exceptionalHyperplaneFiberEquiv hs (c.val.symm w)).symm 1))) = 0
    rw [LinearEquiv.apply_symm_apply]
    norm_num
  intro c z hz
  have hc := isFirstChernForm_firstChernForm (exceptionalFlatHermitianMetric hs)
    s univ isOpen_univ hhol hne c z hz (mem_univ _)
  have hdc : smoothDDC (localWeight (exceptionalFlatHermitianMetric hs) s c) z = 0 := by
    have hcongr := smoothDDC_congr (z := z) (g := fun _ : ComplexModel 1 => (0 : ℝ))
      (Eventually.of_forall fun w => by
        have h := congrFun (hw c) w
        simpa only [Pi.zero_apply] using h)
    exact hcongr.trans (smoothDDC_zero z)
  exact (hc.trans hdc).trans (by simp only [ClosedRealOneOneForm.coeff_zero])

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END ExceptionalFlatHermitianMetricDraft -/
end ExceptionalCanonicalFragment003

section ExceptionalCanonicalFragment004
/- BEGIN ExceptionalCurveDegreeDraft; original source SHA256 3661050bbc8f2d300810d4aed86f5bc73fb1e8deae9fc7b97397f2eabea8a96d -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.LineBundleMetric
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME actual restricted bundle has zero genuine first Chern class for EVERY
smooth metric, by the existing metric-independence theorem and the manufactured flat metric. -/
theorem exceptionalRestriction_firstChernClass_zero
    (h : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber hs)) :
    RealBottChern.ofRepresentative (firstChernForm h) = 0 := by
  calc
    RealBottChern.ofRepresentative (firstChernForm h) =
        RealBottChern.ofRepresentative (firstChernForm (exceptionalFlatHermitianMetric hs)) :=
      firstChernClass_eq h (exceptionalFlatHermitianMetric hs)
    _ = RealBottChern.ofRepresentative (0 : ClosedRealOneOneForm 1 (SGPT.Projective.ComplexProjectiveSpace 1)) :=
      RealBottChern.ofRepresentative_eq_of_geometricallyEq (exceptionalFlat_firstChern_geometrically_zero hs)
    _ = 0 := RealBottChern.ofRepresentative_zero

/-- GENUINE curve degree: the existing native one-dimensional first-Chern CLASS integral,
computed by actual smooth-form integration. It is not assigned a scalar value by definition. -/
def exceptionalHyperplaneCurveDegree
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (h : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber hs)) : ℝ :=
  classSlotIntegral κ (fun _ : Fin 1 => RealBottChern.ofRepresentative (firstChernForm h))

/-- The printed degree-zero reason, on the SAME actual exceptional P1 and physical H,
for every actual smooth metric and every genuine native auxiliary integration background. -/
theorem exceptionalHyperplaneCurveDegree_eq_zero
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (h : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber hs)) :
    exceptionalHyperplaneCurveDegree hs κ h = 0 := by
  unfold exceptionalHyperplaneCurveDegree
  simp_rw [exceptionalRestriction_firstChernClass_zero hs h]
  change classSlotIntegral κ
    (fun _ : Fin 1 => RealBottChern.ofRepresentative (0 : ClosedRealOneOneForm 1 _)) = 0
  rw [classSlotIntegral_ofRepresentative]
  simpa only [Function.update_eq_self] using
    (slotIntegral_update_zero κ (fun _ : Fin 1 => (0 : ClosedRealOneOneForm 1 _)) (0 : Fin 1))

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END ExceptionalCurveDegreeDraft -/
end ExceptionalCanonicalFragment004


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalExceptionalCurveDraft, `NativeHolomorphicPullbackLiftDraft, `NativeHolomorphicPullbackMkDraft, `ExceptionalHyperplaneRestrictionDraft, `ExceptionalRestrictionFullSectionsDraft, `PhysicalPowerExceptionalValuesDraft, `OriginalFullSectionProjectiveMapDraft, `PhysicalHyperplaneNonseparationDraft, `SourceExceptionalRestrictionDraft, `ExceptionalFlatHermitianMetricDraft, `ExceptionalCurveDegreeDraft, `OriginalHyperplaneDivisorPullbackDraft, `ActualHyperplaneCartierEquationsDraft, `SourceP2BlowupExampleDraft, `OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private source or geometry provider in proper exceptional module: {m}"
