import SGPT.Trace.BertiniNativeMemberImageTrace

/-! Internally produced SAME-small-domain holomorphic coefficients, true energy and interpolation. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d+1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N+1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d+1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ)

theorem exists_native_small_coefficient_energy_dictionary (t₀ : U)
    (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (b : ∀ t : U, Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i (a-t.val 0 • v) L hφ))
    (hb : ∀ (t : U) (j : Fin r), b t j =
      (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ (S j))
    (hInj : ∀ t : U,
      letI := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsm t)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
      Function.Injective (nativeBertiniPhysicalQuotientRestriction p i (a-t.val 0 • v) (hsm t) L hφ)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    let T := fun j => nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
    ∃ (W : TopologicalSpace.Opens (ComplexModel 1)) (hWU : W ≤ U), t₀.val ∈ W ∧
      ∀ (V : TopologicalSpace.Opens (ComplexModel 1)) (hVW : V ≤ W),
      let hVU := hVW.trans hWU
      let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
      letI := familyChartedSpace p i a v V p.contMDiff hsV
      letI := isComplexManifold_family p i a v V p.contMDiff hsV
      ∃ C : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber →ₗ[ℂ]
          (V → Fin r → ℂ),
        (∀ F, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, Fin r → ℂ) ∞ (C F)) ∧
        (∀ (c : Fin r → ℂ) (t : V),
          C (familyPhysicalBaseRestriction p i a v U V hVU hsm L (∑ j, c j • T j)) t = c) ∧
        (∀ (F : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber) (t : V),
          letI := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsV t)
          letI := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsV t)
          letI := isCompact_iff_compactSpace.mp
            (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
          ∀ Tg : nativeMultiplierSections
            (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ,
            familyNativeMemberAdjunctionSection p i a v V hsV L t F =
              nativeBertiniPhysicalQuotientRestriction p i (a-t.val 0 • v) (hsV t) L hφ
                ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
                  (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ Tg) →
            nativeBertiniPhysicalQuotientHodgeEnergy p i (a-t.val 0 • v) (hsV t) L hφ
              (∑ j, (C F t) j • (nativeMultiplierSectionMap
                (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
                hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ (S j)) =
              familyNativeMemberHodgeEnergy p i a v V hsV L φ t F) ∧
        ∀ (F : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber)
          (t : V) (c : Fin r → ℂ),
          (∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
            F q = ∑ j, c j • T j (familyBaseInclusion p i a v U V hVU q)) → C F t = c := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a-t₀.val 0 • v) (hsm t₀)
  let := nativeBertiniMemberComplex p i (a-t₀.val 0 • v) (hsm t₀)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t₀.val 0 • v))).isCompact
  dsimp only
  obtain ⟨W,hWU,htW,hAll⟩ := exists_native_quotient_small_holomorphic_coefficient_extractor
    p i a v U hsm L hφ t₀ r S (b t₀) (hb t₀) (hInj t₀)
  refine ⟨W,hWU,htW,?_⟩
  intro V hVW
  let hVU := hVW.trans hWU
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  obtain ⟨C,hC,hNorm,hRead⟩ := hAll V hVW
  refine ⟨C,hC,hNorm,?_,?_⟩
  · intro F t
    let := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsV t)
    let := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsV t)
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
    intro Tg hImage
    obtain ⟨c,hTrace⟩ := exists_native_original_frame_trace_of_actual_quotient_image p i a v U hsm L V hVU hφ t
      r S (b ⟨t.val,hVU t.property⟩) (hb ⟨t.val,hVU t.property⟩) F Tg hImage
    have hRealTrace := hRead F t ⟨c,hTrace⟩
    exact nativeQuotientHodgeEnergy_eq_smallMember_of_trace p i a v U V hVU hsm L hφ t r S (C F t) F hRealTrace
  · intro F t c hTrace
    let := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsV t)
    let := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsV t)
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
    have hRealTrace := hRead F t ⟨c,hTrace⟩
    apply nativeQuotientCoefficients_eq_of_same_small_trace p i a v U V hVU hsm L hφ t r S
      (b ⟨t.val,hVU t.property⟩) (hb ⟨t.val,hVU t.property⟩) (hInj ⟨t.val,hVU t.property⟩) (C F t) c
    intro q hq
    exact (hRealTrace q hq).symm.trans (hTrace q hq)

end SGPT.Trace.BertiniFamilyCanonical
