import SGPT.Trace.BertiniNativeMemberPoleLocal

/-! SAME original physical pole: genuine analytic type and exact basic pole properties. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniNativeSectionPole
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Toric.F1IntersectionDraft SGPT.Bergman.NativeKodairaPullback

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

omit [CompactSpace X] in
private theorem actualChartSmooth_continuous {A : X → ℝ} (hA : ChartSmooth (n := n) A) :
    Continuous A := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn isOpen_univ
    (fun c => by simpa only [Set.preimage_univ,Set.inter_univ] using hA c) (mem_univ x)

theorem nativeBertini_pole_analyticType
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    HasAnalyticSingularitiesOfType (n := n)
      (SGPT.Trace.OTExt2.logPole (poleWeight (nativeBertiniHyperplaneBundle p)
        (nativeBertiniAffineSection p i ζ))) 1 (vanishingIdeal (n := n) (member p (affinePoint i ζ))) := by
  refine ⟨one_pos,VanishingIdealCoherent.isCoherent_vanishingIdeal
    (isClosedSubmanifold_member p p.contMDiff hsm),fun x => ?_⟩
  obtain ⟨U,g,A,hU,hxU,hg,hgen,hA,hApos,_,hlog⟩ :=
    exists_nativeBertini_pole_local_data p i ζ hsm x
  have hcont : ContinuousAt (fun y => |Real.log (A y)|) x :=
    ((actualChartSmooth_continuous hA).continuousAt.log (hApos x hxU).ne').abs
  have hbd : ∀ᶠ y in 𝓝 x, |Real.log (A y)| < |Real.log (A x)| + 1 :=
    hcont.eventually (isOpen_Iio.mem_nhds (lt_add_one _))
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ |Real.log (A y)| < |Real.log (A x)| + 1 := by
    filter_upwards [hU.mem_nhds hxU,hbd] with y hy hyb
    exact ⟨hy,hyb⟩
  obtain ⟨V,hVsub,hV,hxV⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨V,hV,hxV,1,fun _ => g,?_,?_,fun y => Real.log (A y),|Real.log (A x)|+1,
    fun y hy => (hVsub hy).2.le,?_⟩
  · intro _ y hy
    exact (hg y (hVsub hy).1).self_of_nhds.mdifferentiableWithinAt
  · intro y hy f
    simpa only [Set.range_const,Set.mem_singleton_iff] using hgen y (hVsub hy).1 f
  · intro y hy
    norm_num only [Rat.cast_one,EReal.coe_one,one_mul]
    rw [generatorLog_eq_log_sum,Fin.sum_univ_one]
    exact hlog y (hVsub hy).1

variable (P : HermitianHolomorphicLineBundle.{0,0} n X)
  (s : HolomorphicSections (n := n) P.Fiber)

theorem nativePole_ne_top (x : X) : SGPT.Trace.OTExt2.logPole (poleWeight P s) x ≠ ⊤ :=
  fun h => ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h)

theorem nativePole_continuous : Continuous (SGPT.Trace.OTExt2.logPole (poleWeight P s)) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp
    ((sectionNormMap P.Fiber (poleSection P s)).continuous.pow 2))

theorem nativePole_chartSmooth_exp (hP : IsSourceSmoothHermitianMetric P) :
    ChartSmooth (n := n) (fun x => (EReal.exp (SGPT.Trace.OTExt2.logPole (poleWeight P s) x)).toReal) := by
  have heq : (fun x => (EReal.exp (SGPT.Trace.OTExt2.logPole (poleWeight P s) x)).toReal) =
      poleWeight P s := by
    funext x
    rw [SGPT.Trace.OTExt2.logPole,ENNReal.exp_log,ENNReal.toReal_ofReal (poleWeight_nonneg P s x)]
  rw [heq]
  exact poleWeight_chartSmooth P s hP

variable
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)

theorem nativeBertini_pole_eq_bot_iff (x : X) :
    SGPT.Trace.OTExt2.logPole (poleWeight (nativeBertiniHyperplaneBundle p)
      (nativeBertiniAffineSection p i ζ)) x = ⊥ ↔ x ∈ member p (affinePoint i ζ) := by
  change ENNReal.log (ENNReal.ofReal _) = ⊥ ↔ _
  rw [ENNReal.log_eq_bot_iff,ENNReal.ofReal_eq_zero]
  have hz : poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ) x ≤ 0 ↔
      poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ) x = 0 :=
    ⟨fun h => le_antisymm h (poleWeight_nonneg _ _ x),fun h => h.le⟩
  rw [hz,poleWeight_zero_iff,nativeBertiniAffineSection_zero_iff]

theorem nativeBertini_pole_smoothOn_compl (e : ComplexChart n X) :
    ContDiffOn ℝ ∞ (fun z =>
      (SGPT.Trace.OTExt2.logPole (poleWeight (nativeBertiniHyperplaneBundle p)
        (nativeBertiniAffineSection p i ζ)) (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹' (member p (affinePoint i ζ))ᶜ) := by
  let P := nativeBertiniHyperplaneBundle p
  let s := nativeBertiniAffineSection p i ζ
  have hP : IsSourceSmoothHermitianMetric P :=
    nativeHolomorphicPullback_smooth
      (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  have hpos (z : ComplexModel n) (hz : z ∈ e.val.target ∩ e.val.symm ⁻¹' (member p (affinePoint i ζ))ᶜ) :
      0 < poleWeight P s (e.val.symm z) := by
    have hne : s (e.val.symm z) ≠ 0 := by
      intro h
      exact hz.2 ((nativeBertiniAffineSection_zero_iff p i ζ (e.val.symm z)).mp h)
    rw [poleWeight_eq]
    exact mul_pos (poleScale_pos P s) (sq_pos_of_pos (norm_pos_iff.mpr hne))
  have hlog := ((poleWeight_chartSmooth P s hP e).mono inter_subset_left).log
    (fun z hz => (hpos z hz).ne')
  apply hlog.congr
  intro z hz
  rw [SGPT.Trace.OTExt2.logPole,ENNReal.log_ofReal_of_pos (hpos z hz),EReal.toReal_coe]

end SGPT.Trace.BertiniNativeSectionPole
