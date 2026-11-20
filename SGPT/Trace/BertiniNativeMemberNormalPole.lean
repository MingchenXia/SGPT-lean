import SGPT.Trace.BertiniNativeMemberPoleGentle
import SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus

/-! The SAME physical original section norm is the FULL normal pole, uniformly in H. -/
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
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
open SGPT.Foundations.Analysis.Pending.IdealWeightComparison
open SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient
open SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Okounkov.TranscendentalPole SGPT.Toric.F1IntersectionDraft

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ))

include hsm in
theorem nativeBertini_pole_localForm (x : X) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ : IsFlatteningOf (member p (affinePoint i ζ)) Φ k) :
    ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, y ∉ member p (affinePoint i ζ) →
      |(SGPT.Trace.OTExt2.logPole (poleWeight (nativeBertiniHyperplaneBundle p)
        (nativeBertiniAffineSection p i ζ)) y).toReal - Real.log (flatNormalWeight Φ k y)| ≤ C := by
  obtain ⟨U,g,A,hU,hxU,hg,hgen,hA,hApos,hfactor,hlog⟩ :=
    exists_nativeBertini_pole_local_data p i ζ hsm x
  have hgm : (vanishingIdeal (n := n) (member p (affinePoint i ζ))).mem x g :=
    (hgen x hxU g).mpr (isInSpanAt_self rfl (hg x hxU))
  obtain ⟨D,hD,hGflat⟩ := exists_nhds_norm_sq_le_of_isInSpanAt ((flatGen_generates hΦ g).mp hgm)
  have hflats : ∀ j : Fin n, IsInSpanAt (n := n) (· ∈ range (fun _ : Fin 1 => g)) x (flatGen Φ k j) := by
    intro j
    have hm := (flatGen_generates hΦ (flatGen Φ k j)).mpr
      (isInSpanAt_self ⟨j,rfl⟩ (holomorphicAt_flatGen Φ k j))
    simpa only [Set.range_const,Set.mem_singleton_iff] using (hgen x hxU _).mp hm
  obtain ⟨B,hB,hflatG⟩ := exists_nhds_generatorNormSq_le_of_forall_isInSpanAt hflats
  simp only [generatorNormSq,Fin.sum_univ_one] at hflatG
  have hAc : ContinuousAt A x := MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn isOpen_univ
    (fun c => by simpa only [Set.preimage_univ,Set.inter_univ] using hA c) (mem_univ x)
  have hbd : ∀ᶠ y in 𝓝 x, |Real.log (A y)| < |Real.log (A x)|+1 :=
    (hAc.log (hApos x hxU).ne').abs.eventually (isOpen_Iio.mem_nhds (lt_add_one _))
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      generatorNormSq (flatGen Φ k) y ≤ B*‖g y‖^2 ∧
      ‖g y‖^2 ≤ D*generatorNormSq (flatGen Φ k) y ∧ |Real.log (A y)| < |Real.log (A x)|+1 := by
    filter_upwards [hU.mem_nhds hxU,hflatG,hGflat,hbd] with y hy hyB hyD hyA
    exact ⟨hy,hyB,hyD,hyA⟩
  refine ⟨_,hev,max |Real.log (1/B)| |Real.log D|+(|Real.log (A x)|+1),?_⟩
  intro y hy hyH
  have hgne : g y ≠ 0 := by
    intro hgy
    apply hyH
    apply (nativeBertiniAffineSection_zero_iff p i ζ y).mp
    apply (poleWeight_zero_iff _ _ y).mp
    rw [hfactor y hy.1,hgy,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul]
  have hGpos : 0 < ‖g y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hgne)
  have hflatpos : 0 < generatorNormSq (flatGen Φ k) y := by
    by_contra h
    have h0 : generatorNormSq (flatGen Φ k) y = 0 :=
      le_antisymm (le_of_not_gt h) (generatorNormSq_nonneg _ _)
    have hh := hy.2.2.1
    rw [h0,mul_zero] at hh
    exact not_le_of_gt hGpos hh
  have hlow : (1/B)*generatorNormSq (flatGen Φ k) y ≤ ‖g y‖^2 := by
    have h := (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hy.2.1)
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using h
  have hab := abs_log_sub_log_le (show 0 < 1/B by positivity) hD hflatpos hlow hy.2.2.1
  rw [hlog y hy.1,ENNReal.log_ofReal_of_pos hGpos,← EReal.coe_add,EReal.toReal_coe,
    flatNormalWeight_eq_generatorNormSq]
  calc
    _ = |(Real.log (‖g y‖^2)-Real.log (generatorNormSq (flatGen Φ k) y))+Real.log (A y)| := by
      congr 1
      ring
    _ ≤ |Real.log (‖g y‖^2)-Real.log (generatorNormSq (flatGen Φ k) y)|+|Real.log (A y)| := abs_add_le _ _
    _ ≤ _ := add_le_add hab hy.2.2.2.le

include hsm in
theorem nativeBertini_pole_blowup_factor {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    (blowupMap : Z → X) (hblowupMap : IsBlowupAlong n (member p (affinePoint i ζ)) blowupMap) (z : Z) :
    ∃ (S : Set Z) (h : Z → ℂ) (R : Z → ℝ), IsOpen S ∧ z ∈ S ∧
      (∀ y ∈ S, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h y) ∧
      (∀ y ∈ S, ∀ a : Z → ℂ,
        (exceptionalDivisor hblowupMap).ideal.mem y a ↔ IsInSpanAt (n := n) (· = h) y a) ∧
      (∀ e : ComplexChart n Z,
        ContDiffOn ℝ ∞ (fun w => R (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      ∀ y ∈ S, SGPT.Trace.OTExt2.logPole (poleWeight (nativeBertiniHyperplaneBundle p)
        (nativeBertiniAffineSection p i ζ)) (blowupMap y) =
          ENNReal.log (ENNReal.ofReal (‖h y‖^2))+(R y : EReal) := by
  obtain ⟨U,g,A,hU,hxU,hg,hgen,hA,hApos,_,hlog⟩ := exists_nativeBertini_pole_local_data p i ζ hsm (blowupMap z)
  have hblowupMaps := hblowupMap.contMDiff
  let S := blowupMap ⁻¹' U
  have hS : IsOpen S := hU.preimage hblowupMaps.continuous
  have hgblowupMap (y : Z) (hy : y ∈ S) : HolomorphicAt n (g ∘ blowupMap) y :=
    (hg (blowupMap y) hy).comp_contMDiff (Eventually.of_forall fun _ => hblowupMaps.contMDiffAt)
  refine ⟨S,g ∘ blowupMap,fun y => Real.log (A (blowupMap y)),hS,hxU,
    (fun y hy => (hgblowupMap y hy).self_of_nhds),?_,?_,fun y hy => hlog (blowupMap y) hy⟩
  · intro y hy a
    rw [exceptionalDivisor_ideal,RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff]
    constructor
    · intro ha
      apply RelativePrincipalizationSpan.IsInSpanAt.trans (fun t ht => ?_) ha
      obtain ⟨b,hb,rfl⟩ := ht
      apply IsInSpanAt.mono (fun t ht => ?_)
        (GermIdealPullbackCalculus.isInSpanAt_comp hblowupMaps ((hgen (blowupMap y) hy b).mp hb))
      obtain ⟨b,hbg,rfl⟩ := ht
      rw [hbg]
    · intro ha
      apply IsInSpanAt.mono (fun t ht => ?_) ha
      rw [ht]
      exact ⟨g,(hgen (blowupMap y) hy g).mpr (isInSpanAt_self rfl (hg (blowupMap y) hy)),rfl⟩
  · intro e
    have hcomp := BlanchardForm.contDiffOn_chartSmooth_comp hblowupMaps hA e
    exact (hcomp.mono inter_subset_left).log (fun w hw => (hApos _ hw.2).ne')

theorem exists_uniform_nativeBertini_isGlobalNormalPole (omega : KahlerBackground n X) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (j : Fin (N + 1)) (eta : ComplexModel N),
      IsSmoothHypersurfaceMember n p (affinePoint j eta) →
      let R := poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p j eta)
      SGPT.Trace.OTExt2.IsGlobalNormalPole omega (member p (affinePoint j eta)) R ∧
      (∀ eps : ℝ, 0 < eps → ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        0 ≤ leviForm (fun y => Real.log (R (c.val.symm y)+eps)) z v / Real.pi +
          b*SGPT.Trace.TwistedL2.kahlerQuad omega c z v) ∧
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) → ∀ v : ComplexModel n,
        0 ≤ leviForm (fun y => Real.log (R (c.val.symm y))) z v / Real.pi +
          b*SGPT.Trace.TwistedL2.kahlerQuad omega c z v) := by
  let P := nativeBertiniHyperplaneBundle p
  have hP : IsSourceSmoothHermitianMetric P := nativeHolomorphicPullback_smooth
    (sourceProjectiveHyperplaneBundle N) p (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  obtain ⟨b,hb,hAll⟩ := exists_uniform_poleWeight_levi_bound omega P hP
  refine ⟨b,hb,fun j eta hreg => ?_⟩
  let s := nativeBertiniAffineSection p j eta
  let R := poleWeight P s
  have hlev := hAll s
  have hPole : IsSubmanifoldPole omega (member p (affinePoint j eta)) (SGPT.Trace.OTExt2.logPole R) :=
    { exists_thetaPsh := by
        obtain ⟨C,hC,hCtheta⟩ := exists_uniform_nativeBertini_pole_thetaPsh omega p
        exact ⟨C,hC,hCtheta j eta hreg⟩
      eq_bot_iff := nativeBertini_pole_eq_bot_iff p j eta
      ne_top := nativePole_ne_top P s
      continuous := nativePole_continuous P s
      smoothOn_compl := nativeBertini_pole_smoothOn_compl p j eta
      chartSmooth_exp := nativePole_chartSmooth_exp P s hP
      localForm := fun x _ k Phi hPhi => nativeBertini_pole_localForm p j eta hreg x k Phi hPhi
      analyticType := nativeBertini_pole_analyticType p j eta hreg
      blowup := fun f hf z => nativeBertini_pole_blowup_factor p j eta hreg f hf z
      gentle := fun c hc => nativeBertini_pole_sourceGentle p j eta hreg omega hc }
  refine ⟨{ smooth := poleWeight_chartSmooth P s hP
            nonneg := poleWeight_nonneg P s
            lt_exp := poleWeight_lt_exp P s
            pole := hPole
            levi := ⟨b,hb,hlev⟩ },hlev⟩

end SGPT.Trace.BertiniNativeSectionPole
