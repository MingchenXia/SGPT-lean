import SGPT.Trace.BertiniHodgeFinite

/-! Actual raw zero-dimensional multiplier stalk/coherence and COMPLETE
all-dimensional intrinsic/member Hodge finite-energy original H0 reader. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

private theorem actualModelZero_integrable_finite
    (φ : ComplexModel 0 → EReal) (f : ComplexModel 0 → ℂ) (z : ComplexModel 0)
    {c : ℝ} (hc : 0 < c) (hbot : φ z ≠ ⊥) (htop : φ z ≠ ⊤) :
    MultiplierIntegrableAt φ c f z volume := by
  have hval : ∀ y, φ y = ((φ z).toReal : EReal) := by
    intro y
    rw [Subsingleton.elim y z]
    exact (EReal.coe_toReal htop hbot).symm
  have hf : f = fun _ => f z := funext fun y => congrArg f (Subsingleton.elim y z)
  have hdens : multiplierDensity φ c f = fun _ =>
      ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal (Real.exp (-(c * (φ z).toReal))) := by
    funext y
    have hfy : f y = f z := congrArg f (Subsingleton.elim y z)
    simp only [multiplierDensity,hval y,hfy,multiplierWeight_coe]
  refine ⟨hc,ball z 1,isOpen_ball,mem_ball_self one_pos,?_,?_,?_⟩
  · rw [hf]
    exact differentiableOn_const (f z)
  · rw [hdens]
    exact aemeasurable_const
  · rw [hdens,lintegral_const,Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) measure_ball_lt_top

private theorem actualModelZero_integrable_iff
    (φ : ComplexModel 0 → EReal) (f : ComplexModel 0 → ℂ) (z : ComplexModel 0)
    {c : ℝ} (hc : 0 < c) (htop : φ z ≠ ⊤) :
    MultiplierIntegrableAt φ c f z volume ↔ (φ z = ⊥ → f z = 0) := by
  by_cases hb : φ z = ⊥
  · constructor
    · intro h _
      by_contra hf
      obtain ⟨_hc,U,hU,hz,_hhol,_hm,hfin⟩ := h
      have hdens : multiplierDensity φ c f = fun _ => ⊤ := by
        funext y
        rw [Subsingleton.elim y z]
        unfold multiplierDensity
        rw [hb,multiplierWeight_bot hc,
          ENNReal.mul_top (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hf))).ne']
      have hpos : 0 < volume U := hU.measure_pos volume ⟨z,hz⟩
      rw [hdens,lintegral_const,Measure.restrict_apply_univ,ENNReal.top_mul hpos.ne'] at hfin
      exact (lt_irrefl _ hfin)
    · intro h
      have hz : f z = 0 := h hb
      have hf : f = fun _ => 0 := funext fun y => (congrArg f (Subsingleton.elim y z)).trans hz
      rw [hf]
      have hzero : multiplierDensity φ c (fun _ : ComplexModel 0 => 0) = fun _ => 0 :=
        funext (multiplierDensity_zero φ c)
      refine ⟨hc,ball z 1,isOpen_ball,mem_ball_self one_pos,differentiableOn_const 0,?_,?_⟩
      · simpa only [hzero] using (aemeasurable_const :
          AEMeasurable (fun _ : ComplexModel 0 => (0 : ℝ≥0∞)) (volume.restrict (ball z 1)))
      · simp only [multiplierDensity_zero,lintegral_zero,ENNReal.zero_lt_top]
  · exact ⟨fun _ h => (hb h).elim,fun _ => actualModelZero_integrable_finite φ f z hc hb htop⟩

section ZeroDimensional
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]

omit [IsComplexManifold 0 X] in
theorem rawZeroDimensional_multiplier_mem_iff {φ : X → EReal}
    (hφtop : ∀ x, φ x ≠ ⊤) {c : ℝ} (hc : 0 < c) (x : X) (F : X → ℂ) :
    (multiplierIdeal (n := 0) c φ).mem x F ↔
      HolomorphicAt 0 F x ∧ (φ x = ⊥ → F x = 0) := by
  let e := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source _
  have htop : chartFunction φ e (e.val x) ≠ ⊤ := by
    simpa only [chartFunction,e.val.left_inv hx] using hφtop x
  have h := actualModelZero_integrable_iff (chartFunction φ e)
    (fun z => F (e.val.symm z)) (e.val x) hc htop
  simp only [chartFunction,e.val.left_inv hx] at h
  exact and_congr_right fun _ => h

omit [IsComplexManifold 0 X] in
theorem rawZeroDimensional_multiplier_isCoherent {φ : X → EReal}
    (hφtop : ∀ x, φ x ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := 0) c φ).IsCoherent := by
  classical
  intro x
  let e := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source _
  have hyx : ∀ y ∈ e.val.source, y = x :=
    fun y hy => e.val.injOn hy hx (Subsingleton.elim _ _)
  by_cases hb : φ x = ⊥
  · refine ⟨e.val.source,e.val.open_source,hx,1,fun _ _ => 0,
      fun _ => mdifferentiableOn_const,?_⟩
    intro y hy F
    have hxy := hyx y hy
    subst y
    rw [rawZeroDimensional_multiplier_mem_iff hφtop hc]
    constructor
    · rintro ⟨hF,hpole⟩
      have hF0 := hpole hb
      refine ⟨hF,0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,
        fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_⟩
      filter_upwards [e.val.open_source.mem_nhds hx] with z hz
      have hzx := hyx z hz
      simp [hzx,hF0]
    · rintro ⟨hF,N,s,a,hs,_ha,heq⟩
      refine ⟨hF,fun _ => ?_⟩
      have h := heq.self_of_nhds
      calc
        F x = ∑ i, a i x * s i x := h
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          obtain ⟨j,hj⟩ := hs i
          have hi : s i x = 0 := congrFun hj.symm x
          rw [hi,mul_zero]
  · refine ⟨e.val.source,e.val.open_source,hx,1,fun _ _ => 1,
      fun _ => mdifferentiableOn_const,?_⟩
    intro y hy F
    have hxy := hyx y hy
    subst y
    rw [rawZeroDimensional_multiplier_mem_iff hφtop hc]
    constructor
    · rintro ⟨hF,_hpole⟩
      refine ⟨hF,1,fun _ _ => 1,fun _ => F,fun _ => ⟨0,rfl⟩,fun _ => hF,?_⟩
      exact Eventually.of_forall fun z => by simp
    · intro hF
      exact ⟨hF.1,fun h => (hb h).elim⟩
end ZeroDimensional

theorem raw_qpsh_multiplier_isCoherent_allDimensions {n : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    {c : ℝ} (hc : 0 < c) : (multiplierIdeal (n := n) c φ).IsCoherent := by
  cases n with
  | zero => exact rawZeroDimensional_multiplier_isCoherent (fun x => hφ.ne_top x) hc
  | succ m =>
    exact SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      (Nat.zero_lt_succ m) hφ hc

section General
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X)

theorem nativePhysicalHodgeEnergy_finite_iff_full_originalIdeal_allDimensions
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber) :
    S ∈ fullHolomorphicIdealSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber
      (sourceDegreeMultiplierIdeal (n := n) 1 φ) ↔
      nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x)) < ⊤ := by
  classical
  let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
  let I := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hIeq : I = multiplierIdeal (n := n) 1 φ := by
    simpa only [I,Nat.cast_one] using (sourceDegreeMultiplierIdeal_pos (n := n) 1 one_pos φ)
  have hI : I.IsCoherent := by
    rw [hIeq]
    exact raw_qpsh_multiplier_isCoherent_allDimensions hφ one_pos
  rw [nativePhysicalHodgeEnergy_finite_iff_multiplierGerms L S φ hφ.upperSemicontinuous.measurable]
  constructor
  · intro hS x
    let q := nativePreferredPhysicalFrame L x
    have hq : x ∈ q.val.baseSet := ⟨mem_complexChartAt_source _,mem_baseSet_trivializationAt ℂ _ _⟩
    change globalSectionSheafEquiv (n := n) B.Fiber S ∈ idealOpenSectionSubmodule (n := n) B.Fiber I ⊤ at hS
    have h := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) B.Fiber I hI q S hq).mp
      (hS q ⟨x,mem_univ x⟩ hq)
    rw [hIeq] at h
    exact h
  · intro hpoint
    change globalSectionSheafEquiv (n := n) B.Fiber S ∈ idealOpenSectionSubmodule (n := n) B.Fiber I ⊤
    intro e x hxe
    let q := nativePreferredPhysicalFrame L x.val
    have hq : x.val ∈ q.val.baseSet := ⟨mem_complexChartAt_source _,mem_baseSet_trivializationAt ℂ _ _⟩
    apply (localFrameCoefficientGerm_mem_iff (n := n) B.Fiber I ⊤ e q
      (globalSectionSheafEquiv (n := n) B.Fiber S) x hxe hq).mpr
    apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) B.Fiber I hI q S hq).mpr
    rw [hIeq]
    exact hpoint x.val
end General

theorem nativeBertiniMemberHodgeEnergy_finite_iff_full_originalIdeal_allDimensions {d N : ℕ}
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d + 1)) Y]
    [IsComplexManifold (d + 1) Y] [CompactSpace Y]
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) Y) {φ : Y → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ S : HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber,
      S ∈ fullHolomorphicIdealSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
        (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val)) ↔
      nativeBertiniMemberHodgeEnergy p i ζ hsm L φ S < ⊤ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  intro S
  exact nativePhysicalHodgeEnergy_finite_iff_full_originalIdeal_allDimensions _
    (SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (nativeBertiniMemberInclusionMap p i ζ hsm).contMDiff hφ) S

end SGPT.Trace.Bertini
