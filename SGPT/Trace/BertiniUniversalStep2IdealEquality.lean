import SGPT.Trace.BertiniUniversalStep2Generators
import SGPT.Trace.BertiniUniversalRegularOTStalk
import SGPT.Trace.BertiniFixedNativeMemberLift
import SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus

/-! Genuine book Step2: actual full multiplier-ideal equality at EVERY
original member stalk, with only clearly labelled all-high Step1.4 H0
image equality incoming. Actual generation, coefficients and local OT
are produced; no desired ideal/sheaf comparison certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology ENNReal TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft SGPT.Trace.Bertini SGPT.Trace.TwistedL2
open SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))

theorem book_multiplierIdeal_equality_of_all_high_physical_H0_images
    (G U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hU : IsSourceSmoothHermitianMetric U)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) (k₀ : ℕ) :
    let hk : d ≤ d + 1 := Nat.le_succ d
    let hreg := nativeBertiniMemberRegularity p i ζ hsm
    let hC : IsClosedSubmanifold (d + 1) (member p (affinePoint i ζ)) :=
      ⟨isClosed_member p p.contMDiff.continuous (affinePoint i ζ),fun x hx => ⟨d,hreg x hx⟩⟩
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (∀ k : ℕ, k₀ ≤ k → let L := twistedPower G U k
      (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ).range =
        fullHolomorphicIdealSections (n := d)
          (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
            (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
          (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val))) →
    ∀ y : member p (affinePoint i ζ),
      Ideal.comap (structureStalkEquiv hk hreg hC y)
        (stalkIdeal (multiplierIdeal (n := d) 1 (fun z : member p (affinePoint i ζ) => φ z.val)) y) =
      restStalk (multiplierIdeal (n := d + 1) 1 φ) (submanifoldSubspace hC) y.val := by
  intro hk hreg hC
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hStep14
  obtain ⟨k,hk₀,m,S,hRestr,hGen⟩ := exists_actual_multiplier_generators_restricting_intrinsic_of_step14
    p i ζ hsm G U hG hU hGpos φ hφ k₀ hStep14
  let V := twistedPower G
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) U) k
  let ι := nativeBertiniMemberInclusionMap p i ζ hsm
  let J := multiplierIdeal (n := d) 1 (fun z : member p (affinePoint i ζ) => φ z.val)
  have hφres := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp ι.contMDiff hφ.1
  have hJ : J.IsCoherent := raw_qpsh_multiplier_isCoherent_allDimensions hφres one_pos
  have hAlong (j : Fin m) := nativeRestrictedMultiplierSection_isAlong V ι.contMDiff φ hφ.1
    ⟨sourceNativeHolomorphicSectionPullback V ι (S j).val,hRestr j⟩
  have hFres (y : member p (affinePoint i ζ)) (F : X → ℂ)
      (hF : (multiplierIdeal (n := d + 1) 1 φ).mem y.val F) : J.mem y (F ∘ Subtype.val) := by
    let e : AtlasFrame V := ⟨trivializationAt ℂ V.Fiber y.val,inferInstance⟩
    have he : y.val ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
    have hSpan := hGen y.val e he F hF
    have hcomp := GermIdealPullbackCalculus.isInSpanAt_comp ι.contMDiff hSpan
    have hCoeff (j : Fin m) : J.mem y
        ((fun z => e.val.continuousLinearMapAt ℂ z ((S j).val z)) ∘ Subtype.val) := by
      have h := hAlong j y
      simp only [EReal.coe_one,one_mul] at h
      apply MultiplierIdealProductComparison.mem_multiplierIdeal_congr h
      filter_upwards [(e.val.open_baseSet.preimage ι.contMDiff.continuous).mem_nhds he] with z hz
      change (e.val ⟨z.val,(S j).val z.val⟩).2 =
        e.val.continuousLinearMapAt ℂ z.val ((S j).val z.val)
      exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hz _).symm
    obtain ⟨D,_hD,hyD,q,s,_hs,hJspan⟩ := hJ y
    apply (hJspan y hyD _).mpr
    apply IsInSpanAt.trans ?_ hcomp
    rintro g ⟨a,⟨j,rfl⟩,rfl⟩
    exact (hJspan y hyD _).mp (hCoeff j)
  intro y
  refine le_antisymm (regular_multiplierIdeal_restrict_le_restStalk
    (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)) hk hreg hφ.1 1 y) ?_
  unfold restStalk
  apply Ideal.map_le_iff_le_comap.mpr
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨F,hFhol,hF,rfl⟩
  change structureStalkEquiv hk hreg hC y
    (Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol)) ∈ stalkIdeal J y
  rw [structureStalkEquiv_mk,restrictGerm_mk]
  exact Ideal.subset_span ⟨F ∘ Subtype.val,holomorphicAt_comp_val hk hreg hFhol,hFres y F hF,rfl⟩

end SGPT.Trace.BertiniUniversal
