import SGPT.Trace.BertiniFamilyPhysicalDensity
import SGPT.Bergman.SourceNativeTensorChern
import SGPT.Trace.OTExt5Ricci

/-! Actual canonical matched-volume curvature cancels in EVERY original
physical frame and EVERY genuine density of the produced family measure. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.NativeHermitianMetric SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.TwistedL2

private theorem actualFrameWeight_levi {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (B : HermitianHolomorphicLineBundle n Y) (hB : IsSourceSmoothHermitianMetric B)
    (c : ComplexChart n Y) (e : AtlasFrame B) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain B c e) (w : ComplexModel n) :
    leviForm (fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z w =
      Real.pi * (sourceNativeFirstChernForm B hB).val.coeff c z ![w,Complex.I • w] := by
  have hn := (hB c e).contDiffAt ((isOpen_chartFrameDomain B c e).mem_nhds hz)
  have hweight : ContDiffAt ℝ 2 (fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z :=
    (hn.log (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero B e hz.2))).ne').neg.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have h := smoothDDC_complexDiagonal_eq_leviForm hweight w
  rw [← sourceNativeFirstChernForm_isOwn B hB c e z hz.1 hz.2] at h
  rw [h, mul_div_cancel₀ _ Real.pi_ne_zero]

private theorem actualLocalWeight_levi {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (B : HermitianHolomorphicLineBundle n Y) (hB : IsSourceSmoothHermitianMetric B)
    (c : ComplexChart n Y) (e : AtlasFrame B) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain B c e) {ρ : ComplexModel n → ℝ}
    (hρ : ContDiffAt ℝ ∞ ρ z) (hρ0 : 0 < ρ z) (w : ComplexModel n) :
    leviForm (SGPT.Trace.TwistedL2.localWeight B c e ρ (fun _ => 0)) z w =
      Real.pi * (sourceNativeFirstChernForm B hB).val.coeff c z ![w,Complex.I • w] -
        leviForm (fun y => Real.log (ρ y)) z w := by
  have hn := (hB c e).contDiffAt ((isOpen_chartFrameDomain B c e).mem_nhds hz)
  have hweight : ContDiffAt ℝ 2 (fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z :=
    (hn.log (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero B e hz.2))).ne').neg.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hlog : ContDiffAt ℝ 2 (fun y => Real.log (ρ y)) z :=
    (hρ.log hρ0.ne').of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : SGPT.Trace.TwistedL2.localWeight B c e ρ (fun _ => 0) =
      fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2) + -Real.log (ρ y) := by
    funext y
    simp only [SGPT.Trace.TwistedL2.localWeight, frameNormSq, add_zero, sub_eq_add_neg]
  rw [heq]
  change leviForm ((fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) +
    (fun y => -Real.log (ρ y))) z w = _
  have hneg : leviForm (fun y => -Real.log (ρ y)) z w =
      -leviForm (fun y => Real.log (ρ y)) z w := leviForm_neg (fun y => Real.log (ρ y)) z w
  rw [leviForm_add hweight hlog.neg, hneg, actualFrameWeight_levi B hB c e hz w]
  rfl

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem familyMatchedDensity_unique :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (c : ComplexChart (d + 1) (familyIncidence p i a v U)) (ρ : ComplexModel (d + 1) → ℝ),
      IsChartDensity (familyMatchedVolume p i a v U hsm) c ρ →
      ∀ z ∈ c.val.target, ρ z = familyMatchedCoordinateDensity p i a v U hsm c z := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro c ρ hρ z hz
  have hs := familyMatchedCoordinateDensity_smooth p i a v U hsm c
  have hp := familyMatchedCoordinateDensity_pos p i a v U hsm c
  have hm := hρ.2.2.symm.trans (familyMatchedVolume_chart p i a v U hsm c)
  have hρe := ENNReal.continuous_ofReal.comp_continuousOn hρ.1.continuousOn
  have hse := ENNReal.continuous_ofReal.comp_continuousOn hs.continuousOn
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (hρe.aemeasurable c.val.open_target.measurableSet)
    (hse.aemeasurable c.val.open_target.measurableSet)).mp hm
  have heq := Measure.eqOn_open_of_ae_eq hae c.val.open_target hρe hse
  exact (ENNReal.ofReal_eq_ofReal_iff (hρ.2.1 z hz).le (hp z hz).le).mp (heq hz)

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyMatchedDensity_log_levi :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (c : ComplexChart (d + 1) (familyIncidence p i a v U)) (z : ComplexModel (d + 1)),
      z ∈ c.val.target → ∀ w : ComplexModel (d + 1),
      leviForm (fun y => Real.log (familyMatchedCoordinateDensity p i a v U hsm c y)) z w =
        Real.pi * (sourceNativeFirstChernForm (familyNativeCanonicalModel p i a v U hsm)
          (familyNativeCanonicalModel_smooth p i a v U hsm)).val.coeff c z ![w,Complex.I • w] := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro c z hz w
  let q := c.val.symm z
  let x₀ := q.val.2
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) :=
    ⟨trivializationAt ℂ (nativeBertiniHyperplaneBundle p).Fiber x₀,inferInstance⟩
  let K := familyNativeCanonicalModel p i a v U hsm
  let f := familyCanonicalModelFrame p i a v U hsm x₀ eP
  let k := familyModelCanonicalFrameCoefficient p i a v U hsm c x₀ eP
  have hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source := mem_complexChartAt_source _
  have hP : q.val.2 ∈ eP.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hf : q ∈ f.val.baseSet := ⟨hx,hP⟩
  have hzf : z ∈ chartFrameDomain K c f := ⟨hz,hf⟩
  have hnear := (isOpen_chartFrameDomain K c f).mem_nhds hzf
  have hk := contMDiffAt_familyModelCanonicalFrameCoefficient p i a v U hsm c x₀ eP q
    (c.val.map_target hz) hx hP
  have hks : ContDiffAt ℂ ∞ (fun y => k (c.val.symm y)) z :=
    contMDiffAt_iff_contDiffAt.mp (hk.comp z
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas c.property) hz))
  have hkn := (contDiff_norm_sq ℝ).contDiffAt.comp z (hks.restrict_scalars ℝ)
  have hk0 : k q ≠ 0 := familyModelCanonicalFrameCoefficient_ne_zero p i a v U hsm c x₀ eP q
    (c.val.map_target hz) hx hP
  have hlogk : ContDiffAt ℝ 2 (fun y => Real.log (‖k (c.val.symm y)‖ ^ 2)) z :=
    (hkn.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hk0))).of_le (WithTop.coe_le_coe.mpr le_top)
  have hfn := (familyNativeCanonicalModel_smooth p i a v U hsm c f).contDiffAt hnear
  have hlogf : ContDiffAt ℝ 2 (fun y => -Real.log (‖f.val.symm (c.val.symm y) 1‖ ^ 2)) z :=
    (hfn.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sourceAtlasFrame_ne_zero K f hf)))).neg.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have heq : (fun y => Real.log (familyMatchedCoordinateDensity p i a v U hsm c y)) =ᶠ[𝓝 z]
      fun y => Real.log (‖k (c.val.symm y)‖ ^ 2) + -Real.log (‖f.val.symm (c.val.symm y) 1‖ ^ 2) := by
    filter_upwards [hnear] with y hy
    have hyX : (c.val.symm y).val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source := hy.2.1
    have hyP : (c.val.symm y).val.2 ∈ eP.val.baseSet := hy.2.2
    have hky := familyModelCanonicalFrameCoefficient_ne_zero p i a v U hsm c x₀ eP _
      (c.val.map_target hy.1) hyX hyP
    have hfy := sourceAtlasFrame_ne_zero K f hy.2
    unfold familyMatchedCoordinateDensity
    rw [dif_pos hy.1, familyMatchedChartDensity_in_frame p i a v U hsm c x₀ eP _ _ hyX hyP,
      Real.log_div (pow_ne_zero 2 (norm_ne_zero_iff.mpr hky))
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr hfy))]
    rfl
  have hJ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (fun s => k (c.val.symm s)) y := by
    filter_upwards [hnear] with y hy
    have hky := contMDiffAt_familyModelCanonicalFrameCoefficient p i a v U hsm c x₀ eP
      (c.val.symm y) (c.val.map_target hy.1) hy.2.1 hy.2.2
    exact (contMDiffAt_iff_contDiffAt.mp (hky.comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas c.property) hy.1))).differentiableAt
        (by simp)
  rw [leviForm_congr_ev heq w]
  change leviForm ((fun y => Real.log (‖k (c.val.symm y)‖ ^ 2)) +
    (fun y => -Real.log (‖f.val.symm (c.val.symm y) 1‖ ^ 2))) z w = _
  rw [leviForm_add hlogk hlogf,
    SGPT.Trace.OTExt5.leviForm_log_norm_sq_eq_zero hJ hk0 w, zero_add]
  exact actualFrameWeight_levi K (familyNativeCanonicalModel_smooth p i a v U hsm) c f hzf w

theorem familyPhysical_localWeight_levi
    (L : HermitianHolomorphicLineBundle (d + 1) X) (hL : IsSourceSmoothHermitianMetric L) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (c : ComplexChart (d + 1) (familyIncidence p i a v U))
      (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L)) (ρ : ComplexModel (d + 1) → ℝ),
      IsChartDensity (familyMatchedVolume p i a v U hsm) c ρ →
      ∀ z ∈ chartFrameDomain (familyNativePhysicalModel p i a v U hsm L) c e,
      ∀ w : ComplexModel (d + 1),
      leviForm (SGPT.Trace.TwistedL2.localWeight (familyNativePhysicalModel p i a v U hsm L)
        c e ρ (fun _ => 0)) z w =
      Real.pi * (sourceNativeFirstChernForm (nativeHolomorphicPullbackBundle L
        (familyNativeXMap p i a v U hsm))
        (nativeHolomorphicPullback_smooth L (familyNativeXMap p i a v U hsm) hL)).val.coeff c z
          ![w,Complex.I • w] := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro c e ρ hρ z hz w
  have heq : (fun y => Real.log (ρ y)) =ᶠ[𝓝 z]
      fun y => Real.log (familyMatchedCoordinateDensity p i a v U hsm c y) := by
    filter_upwards [c.val.open_target.mem_nhds hz.1] with y hy
    rw [familyMatchedDensity_unique p i a v U hsm c ρ hρ y hy]
  rw [actualLocalWeight_levi _ (familyNativePhysicalModel_smooth p i a v U hsm L hL) c e hz
    (hρ.1.contDiffAt (c.val.open_target.mem_nhds hz.1)) (hρ.2.1 z hz.1) w,
    leviForm_congr_ev heq w, familyMatchedDensity_log_levi p i a v U hsm c z hz.1 w]
  have ht := congrArg (fun A => A ![w,Complex.I • w])
    (sourceNativeTensor_chern_coeff (familyNativeCanonicalModel p i a v U hsm)
      (nativeHolomorphicPullbackBundle L (familyNativeXMap p i a v U hsm))
      (familyNativeCanonicalModel_smooth p i a v U hsm)
      (nativeHolomorphicPullback_smooth L (familyNativeXMap p i a v U hsm) hL) c hz.1)
  simp only [ContinuousAlternatingMap.add_apply] at ht
  change (sourceNativeFirstChernForm (familyNativePhysicalModel p i a v U hsm L)
    (familyNativePhysicalModel_smooth p i a v U hsm L hL)).val.coeff c z ![w,Complex.I • w] = _ at ht
  rw [ht]
  ring

theorem familyPhysical_localWeight_levi_originalChern
    (L : HermitianHolomorphicLineBundle (d + 1) X) (hL : IsSourceSmoothHermitianMetric L) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (c : ComplexChart (d + 1) (familyIncidence p i a v U))
      (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L)) (ρ : ComplexModel (d + 1) → ℝ),
      IsChartDensity (familyMatchedVolume p i a v U hsm) c ρ →
      ∀ z ∈ chartFrameDomain (familyNativePhysicalModel p i a v U hsm L) c e,
      ∀ w : ComplexModel (d + 1),
      leviForm (SGPT.Trace.TwistedL2.localWeight (familyNativePhysicalModel p i a v U hsm L)
        c e ρ (fun _ => 0)) z w =
      Real.pi * (ClosedRealOneOneForm.pullback (familyNativeXMap p i a v U hsm).contMDiff
        (sourceNativeFirstChernForm L hL)).val.coeff c z ![w,Complex.I • w] := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro c e ρ hρ z hz w
  rw [familyPhysical_localWeight_levi p i a v U hsm L hL c e ρ hρ z hz w]
  have hpull := nativeHolomorphicPullback_firstChern_geometrically L (familyNativeXMap p i a v U hsm)
    hL (sourceNativeFirstChernForm L hL) (sourceNativeFirstChernForm_isOwn L hL) c hz.1
  rw [hpull]

end SGPT.Trace.BertiniFamilyCanonical
