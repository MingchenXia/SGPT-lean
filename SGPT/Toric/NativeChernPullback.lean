import SGPT.Bergman.SourceNativeFirstChernForm
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.BDivisor.ClassPullback
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN NativeHolomorphicMetricPullbackDraft; original source SHA256 0549e7a9add11ca78b53eb415907b8b567df3e1c0715fe62d61bf19200f36ee4 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff

variable {n k : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]

abbrev NativeHolomorphicPullbackFiber (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) := f *ᵖ L.Fiber

instance nativeHolomorphicPullbackNormed (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) (y : Y) :
    NormedAddCommGroup (NativeHolomorphicPullbackFiber L f y) := inferInstanceAs (NormedAddCommGroup (L.Fiber (f y)))

instance nativeHolomorphicPullbackHermitian (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) (y : Y) :
    InnerProductSpace ℂ (NativeHolomorphicPullbackFiber L f y) := inferInstanceAs (InnerProductSpace ℂ (L.Fiber (f y)))

instance nativeHolomorphicPullbackTotalTopology (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    TopologicalSpace (TotalSpace ℂ (NativeHolomorphicPullbackFiber L f)) :=
  _root_.Pullback.TotalSpace.topologicalSpace ℂ L.Fiber (f : Y → X)

instance nativeHolomorphicPullbackFiberBundle (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    FiberBundle ℂ (NativeHolomorphicPullbackFiber L f) :=
  FiberBundle.pullback (E := L.Fiber) (F := ℂ) f

instance nativeHolomorphicPullbackVectorBundle (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    VectorBundle ℂ ℂ (NativeHolomorphicPullbackFiber L f) :=
  VectorBundle.pullback (E := L.Fiber) (F := ℂ) (𝕜 := ℂ) f

instance nativeHolomorphicPullbackHoloBundle (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    ContMDiffVectorBundle ∞ ℂ (NativeHolomorphicPullbackFiber L f) 𝓘(ℂ, ComplexModel k) :=
  ContMDiffVectorBundle.pullback ℂ L.Fiber 𝓘(ℂ, ComplexModel k) f

instance nativeHolomorphicPullbackContinuousNorm (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    ContinuousFiberNorm (NativeHolomorphicPullbackFiber L f) := by
  constructor
  exact (ContinuousFiberNorm.continuous (V := L.Fiber)).comp (_root_.Pullback.continuous_lift ℂ L.Fiber f)

def nativeHolomorphicPullbackBundle (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    HermitianHolomorphicLineBundle k Y :=
  HermitianHolomorphicLineBundle.ofNative (NativeHolomorphicPullbackFiber L f)

omit [IsComplexManifold k Y] in
/-- Literal frame inverse in the actual native pullback, on its genuine original base open. -/
theorem nativeHolomorphicPullbackFrame_symm (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → X))
    {y : Y} (hy : f y ∈ e.baseSet) (a : ℂ) :
    (e.pullback f).symm y a = e.symm (f y) a := by
  have h := (e.pullback f).mk_symm hy a
  change (⟨y, (e.pullback f).symm y a⟩ : TotalSpace ℂ (NativeHolomorphicPullbackFiber L f)) =
    ⟨y, e.symm (f y) a⟩ at h
  simpa only [TotalSpace.mk_inj] using h

/-- The SAME inherited physical fibre norm has genuinely smooth frame norms after actual
holomorphic pullback; both manifold dimensions are arbitrary. -/
theorem nativeHolomorphicPullback_smooth (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (hL : IsSourceSmoothHermitianMetric L) :
    IsSourceSmoothHermitianMetric (nativeHolomorphicPullbackBundle L f) := by
  intro c e z hz
  have he := e.property.out
  change ∃ (e0 : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → X))
    (_ : MemTrivializationAtlas e0), e.val = e0.pullback f at he
  obtain ⟨e0, he0, hdef⟩ := he
  let E : AtlasFrame L := ⟨e0, he0⟩
  let d := complexChartAt (n := n) (f (c.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f c d := ⟨hz.1, mem_complexChartAt_source _⟩
  have hframe : f (c.val.symm z) ∈ e0.baseSet := by
    have h := hz.2
    rw [hdef] at h
    exact h
  have hF := HolomorphicMaps.coordinateMap_contDiffAt_real f.contMDiff c d hzd
  have hn := (hL d E).contDiffAt
    ((d.val.isOpen_inter_preimage_symm e0.open_baseSet).mem_nhds
      (show HolomorphicMaps.coordinateMap f c d z ∈ d.val.target ∩ d.val.symm ⁻¹' e0.baseSet from
        ⟨HolomorphicMaps.coordinateMap_mem_target hzd, by
          change d.val.symm (d.val (f (c.val.symm z))) ∈ e0.baseSet
          rw [d.val.left_inv hzd.2]
          exact hframe⟩))
  have hcomp := hn.comp z hF
  have hEq : (fun w => ‖e.val.symm (c.val.symm w) 1‖ ^ 2) =ᶠ[𝓝 z]
      fun w => ‖e0.symm (d.val.symm (HolomorphicMaps.coordinateMap f c d w)) 1‖ ^ 2 := by
    have hUE := c.val.isOpen_inter_preimage_symm (e0.open_baseSet.preimage f.contMDiff.continuous)
    filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen f.contMDiff c d).mem_nhds hzd,
      hUE.mem_nhds (show z ∈ c.val.target ∩ c.val.symm ⁻¹' (f ⁻¹' e0.baseSet) from ⟨hz.1, hframe⟩)] with w hw hwE
    rw [hdef, nativeHolomorphicPullbackFrame_symm L f e0 hwE.2]
    change _ = ‖e0.symm (d.val.symm (d.val (f (c.val.symm w)))) 1‖ ^ 2
    rw [d.val.left_inv hw.2]
  exact (hcomp.congr_of_eventuallyEq hEq).contDiffWithinAt

end SGPT.Toric.F1IntersectionDraft

end
/- END NativeHolomorphicMetricPullbackDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN NativeHolomorphicChernPullbackDraft; original source SHA256 7ef95d10ff5b3a167df1976e58fcedcdb62a8b574bdcf63f721948e2bd954df1 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH SGPT.PSH.LineBundleMetric
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff

variable {n k : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]

/-- The actual native Chern form of the SAME physically pulled-back bundle is the
actual holomorphic two-form pullback, in arbitrary source/target dimensions.
The original OWN first-Chern reader is the ordinary curvature datum, not an input
pullback/comparison output; toric source consumers manufacture it internally. -/
theorem nativeHolomorphicPullback_firstChern_geometrically
    (L : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (hL : IsSourceSmoothHermitianMetric L) (θ : ClosedRealOneOneForm n X)
    (hθ : SGPT.PSH.GlobalL2.IsOwnFirstChernForm L θ) :
    (sourceNativeFirstChernForm (nativeHolomorphicPullbackBundle L f)
      (nativeHolomorphicPullback_smooth L f hL)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback f.contMDiff θ).val := by
  intro c z hz
  let x := f (c.val.symm z)
  let E : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  let EP : AtlasFrame (nativeHolomorphicPullbackBundle L f) :=
    ⟨E.val.pullback f, ⟨E.val, E.property, rfl⟩⟩
  let d := complexChartAt (n := n) x
  let F := HolomorphicMaps.coordinateMap f c d
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f c d := ⟨hz, mem_complexChartAt_source _⟩
  have hxE : f (c.val.symm z) ∈ E.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hzD := HolomorphicMaps.coordinateMap_mem_target hzd
  have hDE : d.val.symm (F z) ∈ E.val.baseSet := by
    change d.val.symm (d.val (f (c.val.symm z))) ∈ E.val.baseSet
    rw [d.val.left_inv hzd.2]
    exact hxE
  let T := d.val.target ∩ d.val.symm ⁻¹' E.val.baseSet
  have hT : IsOpen T := d.val.isOpen_inter_preimage_symm E.val.open_baseSet
  let S := HolomorphicMaps.coordinateDomain f c d ∩
    (c.val.target ∩ c.val.symm ⁻¹' (f ⁻¹' E.val.baseSet))
  have hS : IsOpen S := (HolomorphicMaps.coordinateDomain_isOpen f.contMDiff c d).inter
    (c.val.isOpen_inter_preimage_symm (E.val.open_baseSet.preimage f.contMDiff.continuous))
  have hzS : z ∈ S := ⟨hzd, hz, hxE⟩
  let W := fun w : ComplexModel n => -Real.log (‖E.val.symm (d.val.symm w) 1‖ ^ 2)
  have hW : ContDiffOn ℝ ∞ W T := by
    have h := chartSmooth_localWeight (sourceNativeHermitianMetric L hL) E.val.open_baseSet
      (sourceAtlasFrame_holomorphic L E) (fun _ hu => sourceAtlasFrame_ne_zero L E hu) d
    have hEq : localWeight (sourceNativeHermitianMetric L hL) (fun y => E.val.symm y 1) d = W := by
      funext w
      simp only [localWeight, sourceNativeHermitianMetric_normSq]
      rfl
    rw [hEq] at h
    exact h
  have hmap : MapsTo F S T := by
    intro w hw
    refine ⟨HolomorphicMaps.coordinateMap_mem_target hw.1, ?_⟩
    change d.val.symm (d.val (f (c.val.symm w))) ∈ E.val.baseSet
    rw [d.val.left_inv hw.1.2]
    exact hw.2.2
  have hchain := HolomorphicDDC.smoothDDC_comp hS hT
    ((HolomorphicMaps.coordinateMap_contDiffOn f.contMDiff c d).mono inter_subset_left)
    hW hmap hzS
  have hweight : (fun w => -Real.log (‖EP.val.symm (c.val.symm w) 1‖ ^ 2)) =ᶠ[𝓝 z]
      (fun w => W (F w)) := by
    filter_upwards [hS.mem_nhds hzS] with w hw
    change -Real.log (‖(E.val.pullback f).symm (c.val.symm w) 1‖ ^ 2) = _
    rw [nativeHolomorphicPullbackFrame_symm L f E.val hw.2.2]
    change _ = -Real.log (‖E.val.symm (d.val.symm (d.val (f (c.val.symm w)))) 1‖ ^ 2)
    rw [d.val.left_inv hw.1.2]
  have hown := hθ d E (F z) hzD hDE
  have hownW : θ.val.coeff d (F z) = smoothDDC W (F z) := hown
  rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff f.contMDiff θ.val c d hzd]
  have hpull := sourceNativeFirstChernForm_isOwn (nativeHolomorphicPullbackBundle L f)
    (nativeHolomorphicPullback_smooth L f hL) c EP z hz hxE
  exact hpull.trans ((smoothDDC_congr hweight).trans
    (hchain.trans (congrArg (fun a => a.compContinuousLinearMap (fderiv ℝ F z)) hownW.symm)))

end SGPT.Toric.F1IntersectionDraft

end
/- END NativeHolomorphicChernPullbackDraft -/
end F1CanonicalFragment002

section F1CanonicalFragment003
/- BEGIN NativeNefCurvePullbackDraft; original source SHA256 7ebe098bbf349ecf3e363b69b6b56c004fda9d35d9fb8a2bb1f304c21b67f538 -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff

variable {k n : ℕ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]

/-- The existing actual chart-smooth composition proof, in arbitrary source/target dimensions. -/
theorem chartSmooth_comp_anyDimension {g : Y → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {h : X → ℝ}
    (hh : ChartSmooth (n := n) h) : ChartSmooth (n := k) (fun z => h (g z)) := by
  intro e u hu
  set d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hu, mem_complexChartAt_source _⟩
  have h1 := HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hud
  have h2 := (hh d).contDiffAt
    (d.val.open_target.mem_nhds (HolomorphicMaps.coordinateMap_mem_target hud))
  have h3 := ContDiffAt.comp (g := fun z => h (d.val.symm z)) u h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hg e d).mem_nhds hud] with u' hu'
  show h (g (e.val.symm u')) = h (d.val.symm (d.val (g (e.val.symm u'))))
  rw [d.val.left_inv hu'.2]


/-- The actual full dd^c chain rule in arbitrary source/target dimensions. -/
theorem smoothDDC_comp_chart_anyDimension {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {h : X → ℝ} (hh : ChartSmooth (n := n) h) (e : ComplexChart k Y) (d : ComplexChart n X)
    {z : ComplexModel k} (hzd : z ∈ HolomorphicMaps.coordinateDomain f e d) :
    smoothDDC (fun y => h (f (e.val.symm y))) z =
      (smoothDDC (fun w => h (d.val.symm w)) (HolomorphicMaps.coordinateMap f e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap f e d) z) := by
  have hD := HolomorphicMaps.coordinateDomain_isOpen hf e d
  rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
    (HolomorphicMaps.coordinateMap_contDiffOn hf e d) (hh d)
    (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
  apply smoothDDC_congr
  filter_upwards [hD.mem_nhds hzd] with y hy
  show h (f (e.val.symm y)) = h (d.val.symm (d.val (f (e.val.symm y))))
  rw [d.val.left_inv hy.2]


/-- Native nefness pulls back along EVERY actual holomorphic map from a compact Kähler source,
including the original exceptional P1 into the original surface. -/
theorem nefWithRespectTo_holomorphicPullbackAnyDimension [CompactSpace Y] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (omega : KahlerBackground n X) (omegaY : KahlerBackground k Y)
    {θ : ClosedRealOneOneForm n X} (hθ : NefWithRespectTo omega θ) :
    NefWithRespectTo omegaY (ClosedRealOneOneForm.pullback hf θ) := by
  obtain ⟨A, hA, hdom⟩ := Pending.KahlerDomination.exists_pos_isSemipositive_add_smul omegaY
    (-ClosedRealOneOneForm.pullback hf omega.form)
  intro ε hε
  obtain ⟨h, hh, hpos⟩ := hθ (ε / A) (div_pos hε hA)
  refine ⟨fun y => h (f y), chartSmooth_comp_anyDimension hf hh, ?_⟩
  intro e z hz v
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  set F := HolomorphicMaps.coordinateMap f e d
  set L := fderiv ℝ F z
  have hFz : F z ∈ d.val.target := HolomorphicMaps.coordinateMap_mem_target hzd
  have hvec (u w : ComplexModel k) : L ∘ ![u, w] = ![L u, L w] := by
    funext i
    fin_cases i <;> rfl
  have hLI : L (Complex.I • v) = Complex.I • L v :=
    HolomorphicMaps.coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  -- the pulled-back positivity of `θ + ddᶜ h + (ε / A) ω`
  have h1 := hpos d (F z) hFz (L v)
  -- the domination `-f^*ω + A ω_Y ≥ 0`
  have h2 := hdom e z hz v
  have hθc : (ClosedRealOneOneForm.pullback hf θ).val.coeff e z ![v, Complex.I • v] =
      θ.val.coeff d (F z) ![L v, Complex.I • L v] := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hLI]
  have hωc : (ClosedRealOneOneForm.pullback hf omega.form).val.coeff e z ![v, Complex.I • v] =
      omega.form.val.coeff d (F z) ![L v, Complex.I • L v] := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hLI]
  have hddc : smoothDDC (fun y => h (f (e.val.symm y))) z ![v, Complex.I • v] =
      smoothDDC (fun w => h (d.val.symm w)) (F z) ![L v, Complex.I • L v] := by
    rw [smoothDDC_comp_chart_anyDimension hf hh e d hzd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hLI]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at h2
  rw [hθc, hddc]
  rw [hωc] at h2
  have h3 : 0 ≤ (ε / A) * (-omega.form.val.coeff d (F z) ![L v, Complex.I • L v] +
      A * omegaY.form.val.coeff e z ![v, Complex.I • v]) :=
    mul_nonneg (div_pos hε hA).le h2
  have hkey : (ε / A) * (-omega.form.val.coeff d (F z) ![L v, Complex.I • L v] +
      A * omegaY.form.val.coeff e z ![v, Complex.I • v]) =
      -(ε / A * omega.form.val.coeff d (F z) ![L v, Complex.I • L v]) +
        ε * omegaY.form.val.coeff e z ![v, Complex.I • v] := by
    field_simp
  linarith [h1, h3, hkey]


end SGPT.Toric.F1IntersectionDraft

end
/- END NativeNefCurvePullbackDraft -/
end F1CanonicalFragment003


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"
