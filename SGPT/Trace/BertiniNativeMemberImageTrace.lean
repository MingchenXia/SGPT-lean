import SGPT.Trace.BertiniNativeCoefficientEnergy

/-! Genuine member images recover the ENTIRE actual original physical fibre trace. -/
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

theorem familyNativeMemberAdjunctionSection_eq_iff_fibre (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
    ∀ F G : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
      familyNativeMemberAdjunctionSection p i a v U hsm L t F =
        familyNativeMemberAdjunctionSection p i a v U hsm L t G ↔
      ∀ q : familyIncidence p i a v U, q.val.1.val = t.val → F q = G q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
  intro F G
  constructor
  · intro h q hq
    rcases q with ⟨⟨u,x⟩,hx⟩
    change u.val = t.val at hq
    have hut : u = t := Subtype.ext hq
    subst u
    let y : member p (affinePoint i (a-t.val 0 • v)) := ⟨x,hx⟩
    apply (nativeBertiniPhysicalAdjunctionFiberEquiv p i (a-t.val 0 • v) (hsm t) L y).injective
    exact congrArg (fun S => S y) h
  · intro h
    apply familyNativeMemberAdjunctionSection_congr
    intro y
    exact h ⟨(t,y.val),y.property⟩ rfl

theorem exists_native_original_frame_trace_of_actual_quotient_image
    (V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ) (t : V) :
    let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff hsV
    letI := isComplexManifold_family p i a v V p.contMDiff hsV
    letI := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsV t)
    letI := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsV t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i (a-t.val 0 • v) L hφ)),
      (∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ (S j)) →
      ∀ (F : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber)
        (T : nativeMultiplierSections
          (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ),
        familyNativeMemberAdjunctionSection p i a v V hsV L t F =
          nativeBertiniPhysicalQuotientRestriction p i (a-t.val 0 • v) (hsV t) L hφ
            ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
              (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ T) →
        ∃ c : Fin r → ℂ, ∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
          F q = ∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
            (familyBaseInclusion p i a v U V hVU q) := by
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let := nativeBertiniMemberChartedSpace p i (a-t.val 0 • v) (hsV t)
  let := nativeBertiniMemberComplex p i (a-t.val 0 • v) (hsV t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • v))).isCompact
  dsimp only
  classical
  intro r S b hb F T hImage
  let M := nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
    (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))
  let c := b.equivFun (M.range.mkQ T)
  let Ts := fun j => nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
  let Rbig := ∑ j, c j • Ts j
  let R := familyPhysicalBaseRestriction p i a v U V hVU hsm L Rbig
  have hQ : M.range.mkQ T = ∑ j, c j • M.range.mkQ (S j) := by
    calc
      _ = b.equivFun.symm c := (b.equivFun.symm_apply_apply _).symm
      _ = ∑ j, c j • M.range.mkQ (S j) := by
        rw [b.equivFun_symm_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [hb j]
  have hSum := nativeMultiplierFamilyPhysicalSectionMap_memberSection_sum p i a v U hsm L hφ
    ⟨t.val,hVU t.property⟩ r S c
  have hBase := familyPhysicalBaseRestriction_member p i a v U V hVU hsm L t Rbig
  have hFR : familyNativeMemberAdjunctionSection p i a v V hsV L t F =
      familyNativeMemberAdjunctionSection p i a v V hsV L t R := by
    rw [hBase]
    rw [hSum]
    exact hImage.trans (congrArg (nativeBertiniPhysicalQuotientRestriction p i (a-t.val 0 • v) (hsV t) L hφ) hQ)
  have htrace := (familyNativeMemberAdjunctionSection_eq_iff_fibre p i a v V hsV L t F R).mp hFR
  refine ⟨c,fun q hq => (htrace q hq).trans ?_⟩
  change Rbig (familyBaseInclusion p i a v U V hVU q) = _
  change ((ContMDiffSection.coeAddHom 𝓘(ℂ, ComplexModel (d+1)) ℂ ∞
    (familyNativePhysicalModel p i a v U hsm L).Fiber) Rbig) _ = _
  dsimp only [Rbig]
  rw [map_sum]
  simp only [Finset.sum_apply,ContMDiffSection.coeAddHom_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

end SGPT.Trace.BertiniFamilyCanonical
