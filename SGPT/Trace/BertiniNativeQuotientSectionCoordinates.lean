import SGPT.Trace.BertiniNativeSmallCoefficients

/-! Actual original native quotient restriction/section readback and holomorphic coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem nativeMultiplierFamilyPhysicalSectionMap_memberSection (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ S : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ,
      familyNativeMemberAdjunctionSection p i a v U hsm L t
        (nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ S) =
      nativeBertiniPhysicalQuotientRestriction p i (a - t.val 0 • v) (hsm t) L hφ
        ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ S) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S
  ext y
  rfl

theorem nativeMultiplierFamilyPhysicalSectionMap_memberSection_sum (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (c : Fin r → ℂ),
      familyNativeMemberAdjunctionSection p i a v U hsm L t
        (∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)) =
      nativeBertiniPhysicalQuotientRestriction p i (a - t.val 0 • v) (hsm t) L hφ
        (∑ j, c j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  classical
  intro r S c
  have h := nativeMultiplierFamilyPhysicalSectionMap_memberSection p i a v U hsm L hφ t (∑ j, c j • S j)
  simpa only [map_sum,map_smul] using h

theorem nativeMultiplierFamilyPhysicalSections_independent_of_quotientBasis (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i (a - t.val 0 • v) L hφ)),
      (∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) →
      Function.Injective (nativeBertiniPhysicalQuotientRestriction p i (a - t.val 0 • v) (hsm t) L hφ) →
      ∀ c : Fin r → ℂ, familyNativeMemberAdjunctionSection p i a v U hsm L t
        (∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)) = 0 → c = 0 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  classical
  intro r S b hb hInj c hc
  have hRzero := (nativeMultiplierFamilyPhysicalSectionMap_memberSection_sum p i a v U hsm L hφ t r S c).symm.trans hc
  have hQzero := hInj (hRzero.trans (map_zero _).symm)
  have hcomb : (∑ j, c j • (nativeMultiplierSectionMap
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
      hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) = b.equivFun.symm c := by
    rw [b.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb j]
  rw [hcomb] at hQzero
  apply b.equivFun.symm.injective
  exact hQzero.trans (map_zero _).symm

theorem exists_native_quotient_small_holomorphic_coefficient_extractor (t₀ : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t₀.val 0 • v) (hsm t₀)
    letI := nativeBertiniMemberComplex p i (a - t₀.val 0 • v) (hsm t₀)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t₀.val 0 • v))).isCompact
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i (a - t₀.val 0 • v) L hφ)),
      (∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t₀.val 0 • v))).range.mkQ (S j)) →
      Function.Injective (nativeBertiniPhysicalQuotientRestriction p i (a - t₀.val 0 • v) (hsm t₀) L hφ) →
      let T := fun j => nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
      ∃ (W : TopologicalSpace.Opens (ComplexModel 1)) (hWU : W ≤ U) (_ht₀ : t₀.val ∈ W),
        ∀ (V : TopologicalSpace.Opens (ComplexModel 1)) (hVW : V ≤ W),
        let hVU := hVW.trans hWU
        letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
        letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
        ∃ C : HolomorphicSections (n := d + 1)
            (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber →ₗ[ℂ]
            (V → Fin r → ℂ),
          (∀ F, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, Fin r → ℂ) ∞ (C F)) ∧
          (∀ (c : Fin r → ℂ) (t : V),
            C (familyPhysicalBaseRestriction p i a v U V hVU hsm L (∑ j, c j • T j)) t = c) ∧
          ∀ (F : HolomorphicSections (n := d + 1)
            (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
            (t : V),
            (∃ c : Fin r → ℂ, ∀ q : familyIncidence p i a v V,
              q.val.1.val = t.val → F q = ∑ j, c j • T j (familyBaseInclusion p i a v U V hVU q)) →
            ∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
              F q = ∑ j, (C F t) j • T j (familyBaseInclusion p i a v U V hVU q) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t₀.val 0 • v) (hsm t₀)
  let := nativeBertiniMemberComplex p i (a - t₀.val 0 • v) (hsm t₀)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t₀.val 0 • v))).isCompact
  intro r S b hb hInj
  have hInd := nativeMultiplierFamilyPhysicalSections_independent_of_quotientBasis
    p i a v U hsm L hφ t₀ r S b hb hInj
  exact exists_actual_small_member_holomorphic_coefficient_extractor p i a v U hsm L t₀ r
    (fun j => nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)) hInd

end SGPT.Trace.BertiniFamilyCanonical
