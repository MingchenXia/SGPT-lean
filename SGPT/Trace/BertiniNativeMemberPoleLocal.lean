import SGPT.Trace.BertiniNativeSectionPoleLevi
import SGPT.Trace.BertiniGlobalSectionDivision
import SGPT.Bergman.SourceNativeTensorSmoothMetric

/-! Actual original regular member principal ideal and SAME physical pole local factor. -/
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
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Toric.F1IntersectionDraft SGPT.PSH.LineBundleMetric

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

theorem exists_nativeBertini_pole_local_data
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) (x : X) :
    ∃ (U : Set X) (g : X → ℂ) (A : X → ℝ), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, HolomorphicAt n g y) ∧
      (∀ y ∈ U, ∀ f : X → ℂ,
        (vanishingIdeal (n := n) (member p (affinePoint i ζ))).mem y f ↔
          IsInSpanAt (n := n) (· = g) y f) ∧
      ChartSmooth (n := n) A ∧ (∀ y ∈ U, 0 < A y) ∧
      (∀ y ∈ U, poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ) y =
        ‖g y‖ ^ 2 * A y) ∧
      ∀ y ∈ U,
        SGPT.Trace.OTExt2.logPole (poleWeight (nativeBertiniHyperplaneBundle p)
          (nativeBertiniAffineSection p i ζ)) y =
        ENNReal.log (ENNReal.ofReal (‖g y‖ ^ 2)) + (Real.log (A y) : EReal) := by
  let P := nativeBertiniHyperplaneBundle p
  let s := nativeBertiniAffineSection p i ζ
  let j := chartIndex (p x)
  let U : Set X := p ⁻¹' (affineChart j).source
  let g := nativeBertiniLocalEquation p i ζ j
  let A : X → ℝ := fun y => poleScale P s * ‖nativeBertiniCoordinateSection p j y‖ ^ 2
  have hU : IsOpen U := (affineChart j).open_source.preimage p.contMDiff.continuous
  have hxU : x ∈ U := mem_affineChart_chartIndex (p x)
  have hg (y : X) (hy : y ∈ U) : HolomorphicAt n g y :=
    nativeBertiniLocalEquation_holomorphicAt p i ζ j y hy
  have hmem (y : X) (hy : y ∈ U) : y ∈ member p (affinePoint i ζ) ↔ g y = 0 := by
    rw [← nativeBertiniAffineSection_zero_iff p i ζ y,
      nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j y hy]
    change g y • nativeBertiniCoordinateSection p j y = 0 ↔ g y = 0
    rw [smul_eq_zero]
    simp only [nativeBertiniCoordinateSection_ne_zero p j y hy,or_false]
  have hreg (y : X) (hy : y ∈ U) (hgy : g y = 0) :
      ∃ (a : ComplexChart n X) (v : ComplexModel n), y ∈ a.val.source ∧ chartDeriv a v g y ≠ 0 := by
    obtain ⟨m,hm⟩ := exists_nativeBertiniChartPartial_ne_zero p i ζ j (complexChartAt (n := n) y) y
      (mem_complexChartAt_source y) hy ((hmem y hy).mpr hgy) hsm
    exact ⟨complexChartAt (n := n) y,EuclideanSpace.single m 1,mem_complexChartAt_source y,hm⟩
  have hgen (y : X) (hy : y ∈ U) (f : X → ℂ) :
      (vanishingIdeal (n := n) (member p (affinePoint i ζ))).mem y f ↔
        IsInSpanAt (n := n) (· = g) y f := by
    rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff hU hg hreg hy f]
    constructor
    · rintro ⟨hf,hzero⟩
      refine ⟨hf,?_⟩
      filter_upwards [hzero] with z hz
      intro hzZ
      exact hz ((hmem z hzZ.2).mpr hzZ.1)
    · rintro ⟨hf,hzero⟩
      refine ⟨hf,?_⟩
      filter_upwards [hU.mem_nhds hy,hzero] with z hzU hz
      intro hzH
      exact hz ⟨(hmem z hzU).mp hzH,hzU⟩
  have hP : IsSourceSmoothHermitianMetric P :=
    nativeHolomorphicPullback_smooth (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  have hA : ChartSmooth (n := n) A := by
    have hs : IsHolomorphicSectionOn P.Fiber (nativeBertiniCoordinateSection p j) univ :=
      (nativeBertiniCoordinateSection p j).mdifferentiable.mdifferentiableOn
    have h := (sourceNativeHermitianMetric P hP).smooth _ univ isOpen_univ hs
    intro c
    simpa only [A,sourceNativeHermitianMetric_normSq,Set.preimage_univ,Set.inter_univ] using
      contDiffOn_const.mul (h c)
  have hApos (y : X) (hy : y ∈ U) : 0 < A y :=
    mul_pos (poleScale_pos P s) (sq_pos_of_pos
      (norm_pos_iff.mpr (nativeBertiniCoordinateSection_ne_zero p j y hy)))
  have hfactor (y : X) (hy : y ∈ U) : poleWeight P s y = ‖g y‖ ^ 2 * A y := by
    rw [poleWeight_eq,nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j y hy,
      norm_smul,mul_pow]
    change poleScale P s * (‖g y‖ ^ 2 * ‖nativeBertiniCoordinateSection p j y‖ ^ 2) = _
    dsimp only [A]
    ring
  refine ⟨U,g,A,hU,hxU,hg,hgen,hA,hApos,hfactor,?_⟩
  intro y hy
  unfold SGPT.Trace.OTExt2.logPole
  rw [hfactor y hy,ENNReal.ofReal_mul (sq_nonneg _),ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos (hApos y hy)]

/- Original regularity forces the SAME actual defining section to be densely
nonzero on every open set, even when X or its member is disconnected or empty. -/
omit [CompactSpace X] in
theorem nativeBertiniAffineSection_dense_nonzero
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, nativeBertiniAffineSection p i ζ y ≠ 0 := by
  intro U hU hUne
  by_contra h
  push Not at h
  have hsub (y : X) (hy : y ∈ U) : y ∈ member p (affinePoint i ζ) :=
    (nativeBertiniAffineSection_zero_iff p i ζ y).mp (h y hy)
  obtain ⟨x,hx⟩ := hUne
  let j := chartIndex (p x)
  have hxj : p x ∈ (affineChart j).source := mem_affineChart_chartIndex (p x)
  obtain ⟨e,v,hex,hv⟩ := hsm x (hsub x hx) j hxj
  have hJ : IsOpen (p ⁻¹' (affineChart j).source) :=
    (affineChart j).open_source.preimage p.contMDiff.continuous
  have heq : memberEquation p (affinePoint i ζ) j =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hx,hJ.mem_nhds hxj] with y hy hyj
    exact (mem_member_iff_memberEquation p (affinePoint i ζ) j hyj).mp (hsub y hy)
  apply hv
  rw [(chartDeriv_congr (v := v) hex heq).self_of_nhds]
  change fderiv ℂ (fun _ : ComplexModel n => (0 : ℂ)) (e.val x) v = 0
  have hzero : HasFDerivAt (fun _ : ComplexModel n => (0 : ℂ))
      (0 : ComplexModel n →L[ℂ] ℂ) (e.val x) := hasFDerivAt_const (0 : ℂ) (e.val x)
  rw [hzero.fderiv]
  rfl

theorem nativeBertini_pole_locallyNondegenerate
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    LocallyNondegenerate (SGPT.Trace.OTExt2.logPole
      (poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ))) := by
  intro x U hU hx
  obtain ⟨y,hy,hsy⟩ := nativeBertiniAffineSection_dense_nonzero p i ζ hsm U hU ⟨x,hx⟩
  have hpos : 0 < poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ) y := by
    rw [poleWeight_eq]
    exact mul_pos (poleScale_pos _ _) (sq_pos_of_pos (norm_pos_iff.mpr hsy))
  refine ⟨y,hy,?_⟩
  change ENNReal.log (ENNReal.ofReal _) ≠ ⊥
  rw [ENNReal.log_ofReal_of_pos hpos]
  exact EReal.coe_ne_bot _

theorem exists_uniform_nativeBertini_pole_thetaPsh
    (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n X)
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin (N + 1)) (ζ : ComplexModel N),
      IsSmoothHypersurfaceMember n p (affinePoint i ζ) →
      IsThetaPshPotential (C • omega.form).val (SGPT.Trace.OTExt2.logPole
        (poleWeight (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ))) := by
  let P := nativeBertiniHyperplaneBundle p
  have hP : IsSourceSmoothHermitianMetric P :=
    nativeHolomorphicPullback_smooth (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  let θ := sourceNativeFirstChernForm P hP
  obtain ⟨C,hC,hbound⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  refine ⟨C,hC.le,fun i ζ hsm => ?_⟩
  have htheta : IsThetaPshPotential θ.val (SGPT.Trace.OTExt2.logPole
      (poleWeight P (nativeBertiniAffineSection p i ζ))) :=
    ⟨poleWeight_log_thetaPlurisubharmonic P _ hP,nativeBertini_pole_locallyNondegenerate p i ζ hsm⟩
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive htheta hbound
  have heq : θ + (-θ + C • omega.form) = C • omega.form := by module
  rwa [heq] at h

end SGPT.Trace.BertiniNativeSectionPole
