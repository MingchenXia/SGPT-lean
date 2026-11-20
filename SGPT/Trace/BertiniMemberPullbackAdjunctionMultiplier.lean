import SGPT.Trace.BertiniMemberPullbackAdjunctionInverse
import SGPT.Trace.BertiniHodgeRawZeroDimensional

/-! Actual native member adjunction preserves the SAME original intrinsic
multiplier ideal on ENTIRE genuine native H0, in both directions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf
open SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

theorem nativeContMDiffAt_holomorphicGerm {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {C : Y → ℂ} {y : Y}
    (hC : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ C y) :
    HolomorphicAt n C y := by
  have hC1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) 1 C y := hC.of_le (by simp)
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp hC1
  exact hnear.mono fun z hz => hz.mdifferentiableAt (by simp)

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

theorem nativeBertiniMemberPullbackAdjunction_mem_originalIdeal_iff :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (ψ : member p (affinePoint i ζ) → EReal), ManifoldQuasiPlurisubharmonic (n := d) ψ →
    ∀ S : HolomorphicSections (n := d) (nativeHolomorphicPullbackBundle
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
      (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber,
      S ∈ fullHolomorphicIdealSections (n := d) (nativeHolomorphicPullbackBundle
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
        (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber (sourceDegreeMultiplierIdeal (n := d) 1 ψ) ↔
      nativeBertiniMemberPullbackAdjunctionSection p i ζ hsm L S ∈
        fullHolomorphicIdealSections (n := d)
          (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
            (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
          (sourceDegreeMultiplierIdeal (n := d) 1 ψ) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro ψ hψ S
  let B := nativeHolomorphicPullbackBundle
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
    (nativeBertiniMemberInclusionMap p i ζ hsm)
  let D := tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))
  let R := nativeBertiniMemberPullbackAdjunctionSection p i ζ hsm L S
  let I := sourceDegreeMultiplierIdeal (n := d) 1 ψ
  have hIeq : I = multiplierIdeal (n := d) 1 ψ := by
    simpa only [I,Nat.cast_one] using (sourceDegreeMultiplierIdeal_pos (n := d) 1 one_pos ψ)
  have hI : I.IsCoherent := by
    rw [hIeq]
    exact raw_qpsh_multiplier_isCoherent_allDimensions hψ one_pos
  change (globalSectionSheafEquiv (n := d) B.Fiber S ∈ idealOpenSectionSubmodule (n := d) B.Fiber I ⊤) ↔
    (globalSectionSheafEquiv (n := d) D.Fiber R ∈ idealOpenSectionSubmodule (n := d) D.Fiber I ⊤)
  constructor
  · intro hS g y hyg
    obtain ⟨e,f,he,hf,C,hC,hCne,hread⟩ := exists_nativeBertiniPhysicalAdjunction_local_unit p i ζ hsm L y.val
    apply (localFrameCoefficientGerm_mem_iff (n := d) D.Fiber I ⊤ g f
      (globalSectionSheafEquiv (n := d) D.Fiber R) y hyg hf).mpr
    apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := d) D.Fiber I hI f R hf).mpr
    have hcoeff := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := d) B.Fiber I hI e S he).mp
      (hS e y he)
    rw [hIeq] at hcoeff ⊢
    apply mem_multiplierIdeal_congr
      (mem_multiplierIdeal_holomorphic_mul (nativeContMDiffAt_holomorphicGerm hC) hcoeff)
    filter_upwards [hread] with z hz
    exact (mul_comm (C z) ((e.val ⟨z,S z⟩).2)).trans (hz (S z)).symm
  · intro hR g y hyg
    obtain ⟨e,f,he,hf,C,hC,hCne,hread⟩ := exists_nativeBertiniPhysicalAdjunction_local_unit p i ζ hsm L y.val
    apply (localFrameCoefficientGerm_mem_iff (n := d) B.Fiber I ⊤ g e
      (globalSectionSheafEquiv (n := d) B.Fiber S) y hyg he).mpr
    apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := d) B.Fiber I hI e S he).mpr
    have hcoeff := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := d) D.Fiber I hI f R hf).mp
      (hR f y hf)
    rw [hIeq] at hcoeff ⊢
    apply mem_multiplierIdeal_congr
      (mem_multiplierIdeal_holomorphic_mul (nativeContMDiffAt_holomorphicGerm (hC.inv₀ hCne)) hcoeff)
    filter_upwards [hread,hC.continuousAt.eventually_ne hCne] with z hz hCz
    change (C z)⁻¹ * (f.val ⟨z,nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L z (S z)⟩).2 =
      (e.val ⟨z,S z⟩).2
    rw [hz (S z)]
    calc
      (C z)⁻¹ * ((e.val ⟨z,S z⟩).2 * C z) = ((e.val ⟨z,S z⟩).2) * ((C z)⁻¹ * C z) := by ring
      _ = (e.val ⟨z,S z⟩).2 := by rw [inv_mul_cancel₀ hCz,mul_one]

def nativeBertiniMemberMultiplierAdjunctionEquiv :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (ψ : member p (affinePoint i ζ) → EReal), ManifoldQuasiPlurisubharmonic (n := d) ψ →
    nativeMultiplierSections (nativeHolomorphicPullbackBundle
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
      (nativeBertiniMemberInclusionMap p i ζ hsm)) ψ ≃ₗ[ℂ]
    nativeMultiplierSections (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))) ψ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro ψ hψ
  let J := nativeBertiniMemberPullbackAdjunctionEquiv p i ζ hsm L
  have hmem := nativeBertiniMemberPullbackAdjunction_mem_originalIdeal_iff p i ζ hsm L ψ hψ
  exact {
    toFun := fun S => ⟨J S.val,(hmem S.val).mp S.property⟩
    invFun := fun R => ⟨J.symm R.val,by
      apply (hmem (J.symm R.val)).mpr
      change J (J.symm R.val) ∈ _
      rw [J.apply_symm_apply]
      exact R.property⟩
    left_inv := by
      intro S
      apply Subtype.ext
      exact J.symm_apply_apply S.val
    right_inv := by
      intro R
      apply Subtype.ext
      exact J.apply_symm_apply R.val
    map_add' := by
      intro S T
      apply Subtype.ext
      exact J.map_add S.val T.val
    map_smul' := by
      intro c S
      apply Subtype.ext
      exact J.map_smul c S.val }

end SGPT.Trace.Bertini
