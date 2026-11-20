import SGPT.Trace.BertiniNativeMemberPoleType

/-! Actual full original Cartier ideal and SAME physical pole gentle on the IDENTITY. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniNativeSectionPole
open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Okounkov.TranscendentalPole

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ))

include hsm in
theorem nativeBertini_vanishingIdeal_invertible :
    (vanishingIdeal (n := n) (member p (affinePoint i ζ))).IsInvertible := by
  intro x
  obtain ⟨U,g,A,hU,hxU,hg,hgen,_,_,hfactor,_⟩ := exists_nativeBertini_pole_local_data p i ζ hsm x
  refine ⟨U,hU,hxU,g,(fun y hy => (hg y hy).self_of_nhds.mdifferentiableWithinAt),?_,hgen⟩
  intro W hW hWU hWne
  obtain ⟨y,hy,hsy⟩ := nativeBertiniAffineSection_dense_nonzero p i ζ hsm W hW hWne
  refine ⟨y,hy,fun hgy => ?_⟩
  have hz : poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ) y = 0 := by
    rw [hfactor y (hWU hy),hgy,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul]
  exact hsy ((poleWeight_zero_iff _ _ y).mp hz)

def nativeBertiniMemberDivisor : EffectiveDivisor n X where
  ideal := vanishingIdeal (n := n) (member p (affinePoint i ζ))
  isInvertible := nativeBertini_vanishingIdeal_invertible p i ζ hsm

omit [CompactSpace X] in
private theorem actualIdentityModification :
    AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) (id : X → X) := by
  refine ⟨contMDiff_id,isProperMap_id,∅,∅,id,
    isClosed_empty,isComplexAnalyticSubset_empty,?_,
    isClosed_empty,isComplexAnalyticSubset_empty,?_,?_,
    contMDiff_id.contMDiffOn,fun _ _ => rfl,fun _ _ => rfl⟩ <;> simp

include hsm in
theorem nativeBertini_pole_sourceGentle (omega : KahlerBackground n X) {c : ℚ} (hc : 0 < c) :
    SGPT.PSH.SourceGentleAnalyticSingularities (n := n)
      (fun x => ((c : ℝ) : EReal) * SGPT.Trace.OTExt2.logPole
        (poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ)) x) c
      (vanishingIdeal (n := n) (member p (affinePoint i ζ))) := by
  let P := nativeBertiniHyperplaneBundle p
  let s := nativeBertiniAffineSection p i ζ
  let F := SGPT.Trace.OTExt2.logPole (poleWeight P s)
  have hP : IsSourceSmoothHermitianMetric P :=
    SGPT.Toric.F1IntersectionDraft.nativeHolomorphicPullback_smooth
      (SGPT.Bergman.NativeKodairaPullback.sourceProjectiveHyperplaneBundle N) p
      (SGPT.Bergman.NativeKodairaPullback.sourceProjectiveHyperplaneBundle_sourceSmooth N)
  obtain ⟨C,_,htheta⟩ := exists_uniform_nativeBertini_pole_thetaPsh omega p
  have hpsh := htheta i ζ hsm
  have hcR : (0 : ℝ) < c := Rat.cast_pos.mpr hc
  have hcpsh := PotentialMassComparison.isThetaPshPotential_smul hpsh hcR
  have hinv (x : X) : (((c : ℝ)⁻¹ : ℝ) : EReal) * (((c : ℝ) : EReal) * F x) = F x := by
    rw [← mul_assoc,← EReal.coe_mul,inv_mul_cancel₀ hcR.ne',EReal.coe_one,one_mul]
  refine ⟨⟨_,hcpsh⟩,hcpsh.quasiPshPotential,?_,?_,?_,X,inferInstance,inferInstance,
    inferInstance,id,nativeBertiniMemberDivisor p i ζ hsm,actualIdentityModification,⟨omega⟩,?_⟩
  · obtain ⟨_,hcoh,hloc⟩ := nativeBertini_pole_analyticType p i ζ hsm
    refine ⟨hc,hcoh,fun x => ?_⟩
    obtain ⟨U,hU,hxU,N,g,hg,hgen,R,B,hB,heq⟩ := hloc x
    refine ⟨U,hU,hxU,N,g,hg,hgen,fun y => (c : ℝ)*R y,(c : ℝ)*B,?_,?_⟩
    · intro y hy
      rw [abs_mul,abs_of_pos hcR]
      exact mul_le_mul_of_nonneg_left (hB y hy) hcR.le
    · intro y hy
      change ((c : ℝ) : EReal) * F y = _
      dsimp only [F,P,s]
      rw [heq y hy,EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le)
        (EReal.coe_ne_top _)]
      norm_num
  · intro x
    rw [hinv]
    simpa only [F,SGPT.Trace.OTExt2.logPole,ENNReal.exp_log] using
      (ENNReal.ofReal_ne_top (r := poleWeight P s x))
  · have heq : (fun x => (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) *
        (((c : ℝ) : EReal) * F x))).toReal) = fun x => (EReal.exp (F x)).toReal := by
      funext x
      rw [hinv]
    rw [heq]
    exact nativePole_chartSmooth_exp P s hP
  · intro y
    obtain ⟨U,g,A,hU,hyU,hg,hgen,hA,hApos,hfactor,hlog⟩ :=
      exists_nativeBertini_pole_local_data p i ζ hsm y
    have hgnon : ∀ W : Set X, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0 := by
      intro W hW hWU hWne
      obtain ⟨t,ht,hst⟩ := nativeBertiniAffineSection_dense_nonzero p i ζ hsm W hW hWne
      refine ⟨t,ht,fun hgt => ?_⟩
      apply hst
      apply (poleWeight_zero_iff P s t).mp
      rw [hfactor t (hWU ht),hgt,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul]
    let e := complexChartAt (n := n) y
    have hyt : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
    have hey : e.val.symm (e.val y) = y := e.val.left_inv (mem_complexChartAt_source y)
    have hT : Tendsto (fun w : ComplexModel n => e.val.symm (w + e.val y)) (𝓝 0) (𝓝 y) := by
      have h1 : Tendsto (fun w : ComplexModel n => w + e.val y) (𝓝 0) (𝓝 (e.val y)) := by
        simpa only [zero_add] using (continuous_add_const (e.val y)).tendsto (0 : ComplexModel n)
      have h2 := (e.val.continuousAt_symm hyt).tendsto.comp h1
      rwa [hey] at h2
    have hev : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w + e.val y ∈ e.val.target ∧
        e.val.symm (w + e.val y) ∈ U := by
      have h1 : Tendsto (fun w : ComplexModel n => w + e.val y) (𝓝 0) (𝓝 (e.val y)) := by
        simpa only [zero_add] using (continuous_add_const (e.val y)).tendsto (0 : ComplexModel n)
      exact (h1.eventually (e.val.open_target.mem_nhds hyt)).and (hT.eventually (hU.mem_nhds hyU))
    obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨U,hU,hyU,g,(fun z hz => (hg z hz).self_of_nhds.mdifferentiableWithinAt),hgnon,hgen,
      centeredChart y,subset_rfl,sub_self _,fun w => (c : ℝ)*Real.log (A (e.val.symm (w+e.val y))),
      r,hr,(fun w hw => (hball w hw).1),?_,?_⟩
    · have hmaps : MapsTo (fun w : ComplexModel n => w+e.val y) (ball 0 r)
          (e.val.target ∩ e.val.symm ⁻¹' U) := fun w hw => hball w hw
      have hlogA : ContDiffOn ℝ ∞ (fun w => Real.log (A (e.val.symm w)))
          (e.val.target ∩ e.val.symm ⁻¹' U) :=
        ((hA e).mono inter_subset_left).log (fun w hw => (hApos _ hw.2).ne')
      exact contDiffOn_const.mul (hlogA.comp ((contDiff_id.add contDiff_const).contDiffOn) hmaps)
    · intro w hw
      refine ⟨(hball w hw).2,?_⟩
      change ((c : ℝ) : EReal)*F (e.val.symm (w+e.val y)) =
        ((c : ℝ) : EReal)*ENNReal.log (ENNReal.ofReal (‖g (e.val.symm (w+e.val y))‖^2)) +
          (((c : ℝ)*Real.log (A (e.val.symm (w+e.val y))) : ℝ) : EReal)
      dsimp only [F,P,s]
      rw [hlog _ (hball w hw).2,EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr hcR.le) (EReal.coe_ne_top _),← EReal.coe_mul]

end SGPT.Trace.BertiniNativeSectionPole
