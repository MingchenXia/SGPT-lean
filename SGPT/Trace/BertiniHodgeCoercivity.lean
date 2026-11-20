import SGPT.Trace.BertiniHodgeSemicontinuity

/-! Original fixed-member Hodge energy controls the SAME native section
supremum norm; genuine finite-energy sublevels are compact. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

section General
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X)

theorem exists_nativePhysicalHodgeEnergy_uniform_lower_bound
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber,
        ENNReal.ofReal (c * ‖S‖ ^ 2) ≤
          nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x)) := by
  classical
  let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
  let H := HolomorphicSections (n := n) B.Fiber
  let E (S : H) := nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x))
  let := holomorphicSections_finiteDimensional (n := n) B.Fiber
  let := FiniteDimensional.proper ℂ H
  by_cases hne : (sphere (0 : H) 1).Nonempty
  · have hlsc : LowerSemicontinuous E := nativePhysicalHodgeEnergy_lowerSemicontinuous L _
      ((measurable_originalMultiplierWeight measurable_id 1).comp hφ.upperSemicontinuous.measurable)
    obtain ⟨S₀,hS₀,hmin⟩ := (hlsc.lowerSemicontinuousOn (sphere (0 : H) 1)).exists_isMinOn hne
      (isCompact_sphere (0 : H) 1)
    have hnS₀ : ‖S₀‖ = 1 := mem_sphere_zero_iff_norm.mp hS₀
    have hS₀ne : S₀ ≠ 0 := by
      intro h
      rw [h,norm_zero] at hnS₀
      exact zero_ne_one hnS₀
    have hpos : 0 < E S₀ := nativePhysicalHodgeEnergy_pos L hφ S₀ hS₀ne
    have hreal : ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c ≤ E S₀ := by
      by_cases htop : E S₀ = ⊤
      · exact ⟨1,one_pos,htop ▸ le_top⟩
      · exact ⟨(E S₀).toReal,ENNReal.toReal_pos hpos.ne' htop,ENNReal.ofReal_toReal_le⟩
    obtain ⟨c,hc,hcE⟩ := hreal
    refine ⟨c,hc,?_⟩
    intro S
    by_cases hS : S = 0
    · subst S
      simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,ENNReal.ofReal_zero,zero_le]
    · let T : H := (‖S‖⁻¹ : ℂ) • S
      have hT : T ∈ sphere (0 : H) 1 :=
        mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hS)
      have hnorm : (‖S‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hS)
      have hST : S = (‖S‖ : ℂ) • T := by
        dsimp only [T]
        rw [smul_smul,mul_inv_cancel₀ hnorm,one_smul]
      have hET : ENNReal.ofReal c ≤ E T := hcE.trans (hmin hT)
      have hscale : E S = ENNReal.ofReal (‖S‖ ^ 2) * E T := by
        calc
          E S = E ((‖S‖ : ℂ) • T) := congrArg E hST
          _ = ENNReal.ofReal (‖S‖ ^ 2) * E T := by
            change nativePhysicalHodgeEnergy L ((‖S‖ : ℂ) •
              (T : ∀ x, B.Fiber x)) _ = _
            rw [nativePhysicalHodgeEnergy_smul]
            rw [Complex.norm_real,Real.norm_of_nonneg (norm_nonneg S)]
      calc
        ENNReal.ofReal (c * ‖S‖ ^ 2) = ENNReal.ofReal (‖S‖ ^ 2) * ENNReal.ofReal c := by
          rw [ENNReal.ofReal_mul hc.le,mul_comm]
        _ ≤ ENNReal.ofReal (‖S‖ ^ 2) * E T := mul_le_mul' le_rfl hET
        _ = E S := hscale.symm
  · refine ⟨1,one_pos,?_⟩
    intro S
    have hS : S = 0 := by
      by_contra hs
      exact hne ⟨(‖S‖⁻¹ : ℂ) • S,mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hs)⟩
    subst S
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,ENNReal.ofReal_zero,zero_le]

theorem isCompact_nativePhysicalHodgeEnergy_sublevel
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {S : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber |
        nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x)) ≤ ENNReal.ofReal R} := by
  classical
  let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
  let H := HolomorphicSections (n := n) B.Fiber
  let E (S : H) := nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x))
  obtain ⟨c,hc,hbound⟩ := exists_nativePhysicalHodgeEnergy_uniform_lower_bound L hφ
  have hlsc : LowerSemicontinuous E := nativePhysicalHodgeEnergy_lowerSemicontinuous L _
    ((measurable_originalMultiplierWeight measurable_id 1).comp hφ.upperSemicontinuous.measurable)
  have hclosed : IsClosed {S : H | E S ≤ ENNReal.ofReal R} := hlsc.isClosed_preimage _
  have hsub : {S : H | E S ≤ ENNReal.ofReal R} ⊆ closedBall (0 : H) (1 + R / c) := by
    intro S hS
    have he := (ENNReal.ofReal_le_ofReal_iff hR).mp ((hbound S).trans hS)
    have hsq : ‖S‖ ^ 2 ≤ R / c := (le_div_iff₀ hc).mpr (by nlinarith [he])
    have hRc : 0 ≤ R / c := div_nonneg hR hc.le
    rw [mem_closedBall_zero_iff]
    by_contra! hn
    nlinarith [sq_nonneg (‖S‖ - 1)]
  exact (isCompact_section_closedBall B.Fiber (0 : H) (1 + R / c)).of_isClosed_subset hclosed hsub
end General

section Member
variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y] [CompactSpace Y]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) Y) {φ : Y → EReal}
  (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ)

include hφ in
theorem exists_nativeBertiniMemberHodgeEnergy_uniform_lower_bound :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∃ c : ℝ, 0 < c ∧ ∀ S : HolomorphicSections (n := d)
      (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber,
      ENNReal.ofReal (c * ‖S‖ ^ 2) ≤ nativeBertiniMemberHodgeEnergy p i ζ hsm L φ S := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  exact exists_nativePhysicalHodgeEnergy_uniform_lower_bound _
    (SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (nativeBertiniMemberInclusionMap p i ζ hsm).contMDiff hφ)

include hφ in
theorem isCompact_nativeBertiniMemberHodgeEnergy_sublevel (R : ℝ) (hR : 0 ≤ R) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    IsCompact {S : HolomorphicSections (n := d)
      (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber |
      nativeBertiniMemberHodgeEnergy p i ζ hsm L φ S ≤ ENNReal.ofReal R} := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  exact isCompact_nativePhysicalHodgeEnergy_sublevel _
    (SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (nativeBertiniMemberInclusionMap p i ζ hsm).contMDiff hφ) R hR
end Member
end SGPT.Trace.Bertini
