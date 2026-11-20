import SGPT.Trace.BertiniNativeQuotientSectionCoordinates
import SGPT.Trace.BertiniNativeQuotientEnergyField

/-! Exact SAME original quotient/small-member energy, and true fibre coefficient uniqueness. -/
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
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem nativeQuotientHodgeEnergy_eq_smallMember_of_trace (t : V) :
    let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff hsV
    letI := isComplexManifold_family p i a v V p.contMDiff hsV
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (c : Fin r → ℂ) (F : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V hsV L).Fiber),
      (∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
        F q = ∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
          (familyBaseInclusion p i a v U V hVU q)) →
      nativeBertiniPhysicalQuotientHodgeEnergy p i (a - t.val 0 • v) (hsV t) L hφ
        (∑ j, c j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) =
      familyNativeMemberHodgeEnergy p i a v V hsV L φ t F := by
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  classical
  dsimp only
  intro r S c F hTrace
  let T := ∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
  let R := familyPhysicalBaseRestriction p i a v U V hVU hsm L T
  have hFR : familyNativeMemberHodgeEnergy p i a v V hsV L φ t F =
      familyNativeMemberHodgeEnergy p i a v V hsV L φ t R := by
    apply familyNativeMemberHodgeEnergy_congr
    intro y
    have h := hTrace (⟨(t,y.val),y.property⟩ : familyIncidence p i a v V) rfl
    refine h.trans ?_
    symm
    change T (familyBaseInclusion p i a v U V hVU ⟨(t,y.val),y.property⟩) = _
    change ((ContMDiffSection.coeAddHom 𝓘(ℂ, ComplexModel (d + 1)) ℂ ∞
      (familyNativePhysicalModel p i a v U hsm L).Fiber) T) _ = _
    dsimp only [T]
    rw [map_sum]
    simp only [Finset.sum_apply,ContMDiffSection.coeAddHom_apply]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hR := familyPhysicalBaseRestriction_memberHodgeEnergy p i a v U V hVU hsm L φ t T
  have hQ := nativeMultiplierFamilyPhysicalSectionMap_memberHodgeEnergy_sum p i a v U hsm L hφ
    ⟨t.val,hVU t.property⟩ r S c
  exact hQ.trans (hR.symm.trans hFR.symm)

theorem nativeQuotientFrameEnergy_eq_smallMember_of_trace
    (B : TopologicalSpace.Opens (ComplexModel N))
    (hsB : ∀ ζ : B, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ.val))
    (t : V) (ht : a - t.val 0 • v ∈ B) :
    let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff hsV
    letI := isComplexManifold_family p i a v V p.contMDiff hsV
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (c : Fin r → ℂ) (F : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V hsV L).Fiber),
      (∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
        F q = ∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
          (familyBaseInclusion p i a v U V hVU q)) →
      nativeBertiniQuotientFrameEnergy p i B hsB L hφ S (a - t.val 0 • v) c =
      familyNativeMemberHodgeEnergy p i a v V hsV L φ t F := by
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  dsimp only
  intro r S c F hTrace
  rw [nativeBertiniQuotientFrameEnergy_apply p i B hsB L hφ S ⟨_,ht⟩ c]
  exact nativeQuotientHodgeEnergy_eq_smallMember_of_trace p i a v U V hVU hsm L hφ t r S c F hTrace

theorem nativeQuotientCoefficients_eq_of_same_small_trace (t : V) :
    let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff hsV
    letI := isComplexManifold_family p i a v V p.contMDiff hsV
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i (a - t.val 0 • v) L hφ)),
      (∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) →
      Function.Injective (nativeBertiniPhysicalQuotientRestriction p i (a - t.val 0 • v) (hsV t) L hφ) →
      ∀ c d : Fin r → ℂ,
        (∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
          (∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
            (familyBaseInclusion p i a v U V hVU q)) =
          (∑ j, d j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
            (familyBaseInclusion p i a v U V hVU q))) → c = d := by
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  classical
  dsimp only
  intro r S b hb hInj c w hTrace
  let T := fun j => nativeMultiplierFamilyPhysicalSectionMap p i a v V hsV L hφ (S j)
  have hzeroVal (q : familyIncidence p i a v V) (hq : q.val.1.val = t.val) :
      (∑ j, (c - w) j • T j) q = 0 := by
    have hsmall := hTrace q hq
    change (∑ j, c j • T j q) = (∑ j, w j • T j q) at hsmall
    have hsum : (∑ j, (c-w) j • T j) q = ∑ j, (c-w) j • T j q := by
      change ((ContMDiffSection.coeAddHom 𝓘(ℂ, ComplexModel (d + 1)) ℂ ∞
        (familyNativePhysicalModel p i a v V hsV L).Fiber) (∑ j, (c-w) j • T j)) q = _
      rw [map_sum]
      simp only [Finset.sum_apply,ContMDiffSection.coeAddHom_apply]
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [hsum]
    simpa only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib] using sub_eq_zero.mpr hsmall
  have hInd := nativeMultiplierFamilyPhysicalSections_independent_of_quotientBasis
    p i a v V hsV L hφ t r S b hb hInj
  have hcd : c - w = 0 := by
    apply hInd
    ext y
    rw [familyNativeMemberAdjunctionSection_apply,
      hzeroVal ⟨(t,y.val),y.property⟩ rfl,map_zero]
    rfl
  exact sub_eq_zero.mp hcd

end SGPT.Trace.BertiniFamilyCanonical
