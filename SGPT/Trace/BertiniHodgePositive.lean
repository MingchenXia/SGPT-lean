import SGPT.Trace.BertiniHodgeLocalCoefficient
import SGPT.Trace.BertiniHodgeChartMass
import SGPT.Trace.BertiniMemberHodgeEnergy
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

/-! Genuine intrinsic physical Hodge positivity for every nonzero original
section, with raw quasi-psh weights and true minus-infinity pole components. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

section General
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

theorem exists_raw_qpsh_nonneg_upper_bound {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, φ x ≤ (M : EReal) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨0,le_rfl,fun x => isEmptyElim x⟩
  obtain ⟨x₀,-,hx₀⟩ := (hφ.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
    univ_nonempty isCompact_univ
  refine ⟨max (φ x₀).toReal 0,le_max_right _ _,fun x => (hx₀ (mem_univ x)).trans ?_⟩
  by_cases hb : φ x₀ = ⊥
  · rw [hb]
    exact bot_le
  · rw [← EReal.coe_toReal (hφ.ne_top x₀) hb]
    exact EReal.coe_le_coe_iff.mpr (by rw [EReal.toReal_coe]; exact le_max_left _ _)

variable [MeasurableSpace X] [BorelSpace X]

theorem nativePhysicalHodgeEnergy_pos
    (L : HermitianHolomorphicLineBundle n X)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (hS : S ≠ 0) :
    0 < nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x)) := by
  classical
  have hxS : ∃ x : X, S x ≠ 0 := by
    by_contra h
    push Not at h
    apply hS
    ext x
    exact h x
  obtain ⟨x₀,hS₀⟩ := hxS
  obtain ⟨M,-,hM⟩ := exists_raw_qpsh_nonneg_upper_bound hφ
  let c := complexChartAt (n := n) x₀
  let z₀ := c.val x₀
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀,inferInstance⟩
  let eK := nativeCanonicalFrame (n := n) x₀
  let q := tensorAtlasFrame eK e
  let := e.property
  let := eK.property
  let := q.property
  have hx : x₀ ∈ c.val.source := mem_complexChartAt_source _
  have hz₀ : z₀ ∈ c.val.target := c.val.map_source hx
  have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : x₀ ∈ q.val.baseSet := ⟨hx,he⟩
  have hinv : c.val.symm z₀ = x₀ := c.val.left_inv hx
  let C : X → ℂ := fun x => (q.val ⟨x,S x⟩).2
  have hC₀ : C x₀ ≠ 0 := by
    intro hz
    apply hS₀
    apply (q.val.linearEquivAt ℂ x₀ hq).injective
    exact hz.trans (map_zero _).symm
  have hC : ContinuousAt C x₀ :=
    ((q.val.contMDiffAt_section_iff hq).mp (S.contMDiff x₀)).continuousAt
  have hE : ContinuousAt (fun x => ‖e.val.symm x 1‖) x₀ :=
    (frameNorm_continuousOn L.Fiber e.val).continuousAt (e.val.open_baseSet.mem_nhds he)
  have hcinv := c.val.continuousAt_symm hz₀
  have hC' : ContinuousAt C (c.val.symm z₀) := by simpa only [hinv] using hC
  have hE' : ContinuousAt (fun x => ‖e.val.symm x 1‖) (c.val.symm z₀) := by simpa only [hinv] using hE
  let N : ComplexModel n → ℝ := fun z => ‖C (c.val.symm z)‖ ^ 2 * ‖e.val.symm (c.val.symm z) 1‖ ^ 2
  have hNc : ContinuousAt N z₀ := ((hC'.comp hcinv).norm.pow 2).mul ((hE'.comp hcinv).pow 2)
  have hN₀ : 0 < N z₀ := by
    dsimp only [N]
    rw [hinv]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hC₀))
      (sq_pos_of_pos (frameNorm_pos L.Fiber e.val he))
  have hframe : ∀ᶠ z in 𝓝 z₀, c.val.symm z ∈ e.val.baseSet := by
    apply hcinv.eventually
    rw [hinv]
    exact e.val.open_baseSet.mem_nhds he
  have hnear : ∀ᶠ z in 𝓝 z₀,
      z ∈ c.val.target ∧ c.val.symm z ∈ e.val.baseSet ∧ N z₀ / 2 ≤ N z := by
    filter_upwards [c.val.open_target.mem_nhds hz₀,hframe,
      hNc.eventually (lt_mem_nhds (half_lt_self hN₀))] with z hzt hze hNz
    exact ⟨hzt,hze,hNz.le⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let D := nativeCanonicalPhysicalCoordinateDensity L S (fun x => multiplierWeight 1 (φ x)) c
  have hD (z : ComplexModel n) (hz : z ∈ ball z₀ r) :
      D z = ENNReal.ofReal (N z) * multiplierWeight 1 (φ (c.val.symm z)) := by
    change nativeCanonicalPhysicalCoordinateDensity L S (fun x => multiplierWeight 1 (φ x))
      (complexChartAt (n := n) x₀) z = _
    rw [nativePhysicalPreferredCoordinateDensity_eq_multiplier L S φ x₀ e z
      (hball hz).1 (hball hz).2.1]
    unfold multiplierDensity chartFunction
    change ENNReal.ofReal (‖e.val.symm (c.val.symm z) 1‖ ^ 2) *
      (ENNReal.ofReal (‖C (c.val.symm z)‖ ^ 2) * multiplierWeight 1 (φ (c.val.symm z))) =
      ENNReal.ofReal (‖C (c.val.symm z)‖ ^ 2 * ‖e.val.symm (c.val.symm z) 1‖ ^ 2) *
        multiplierWeight 1 (φ (c.val.symm z))
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_assoc]
    exact mul_left_comm _ _ _
  have hw₀ : 0 < multiplierWeight 1 (M : EReal) := by
    rw [multiplierWeight_coe]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  let β := ENNReal.ofReal (N z₀ / 2) * multiplierWeight 1 (M : EReal)
  have hβ : 0 < β := ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (half_pos hN₀),hw₀⟩
  have hconst : 0 < (∫⁻ _z : ComplexModel n in ball z₀ r, β) := by
    simpa using ENNReal.mul_pos_iff.mpr ⟨hβ,measure_ball_pos volume z₀ hr⟩
  have hbound : (∫⁻ _z : ComplexModel n in ball z₀ r, β) ≤ ∫⁻ z in ball z₀ r, D z := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    rw [hD z hz]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hball hz).2.2)
      (multiplierWeight_antitone (c := 1) zero_le_one (hM (c.val.symm z)))
  let W := c.val.source ∩ c.val ⁻¹' ball z₀ r
  have hW : IsOpen W := c.val.isOpen_inter_preimage isOpen_ball
  have himage : c.val '' W = ball z₀ r := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx.2
    · intro hz
      have hzt := (hball hz).1
      refine ⟨c.val.symm z,⟨c.val.map_target hzt,?_⟩,c.val.right_inv hzt⟩
      change c.val (c.val.symm z) ∈ ball z₀ r
      rwa [c.val.right_inv hzt]
  have hglobal := nativePhysicalHodgeEnergy_ge_chartSubset L S
    (fun x => multiplierWeight 1 (φ x)) c W hW.measurableSet inter_subset_left
  rw [himage] at hglobal
  exact (hconst.trans_le hbound).trans_le hglobal

end General

theorem nativeBertiniMemberHodgeEnergy_pos {d N : ℕ}
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d + 1)) Y]
    [IsComplexManifold (d + 1) Y] [CompactSpace Y]
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) Y) {φ : Y → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ S : HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber,
      S ≠ 0 → 0 < nativeBertiniMemberHodgeEnergy p i ζ hsm L φ S := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  intro S hS
  exact nativePhysicalHodgeEnergy_pos _
    (SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (nativeBertiniMemberInclusionMap p i ζ hsm).contMDiff hφ) S hS

end SGPT.Trace.Bertini
