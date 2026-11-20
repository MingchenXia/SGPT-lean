import SGPT.Trace.BertiniUniversalIntrinsicLift
import SGPT.Trace.BertiniPhysicalQuotientRestriction

/-! Genuine original quotient image of EVERY finite intrinsic Hodge
section, at ONE twist threshold before all original smooth members. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology ENNReal TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft SGPT.Trace.Bertini

private theorem swapLastFiber_twice {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (E F G : HermitianHolomorphicLineBundle n Y) (x : Y)
    (v : (tensor (tensor E F) G).Fiber x) :
    NativeTensorSwap.swapLastFiber E G F x (NativeTensorSwap.swapLastFiber E F G x v) = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b =>
    induction a using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul,map_zero]
    | add u v hu hv => simp only [TensorProduct.add_tmul,map_add,hu,hv]
    | tmul u v => rfl

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

theorem exists_uniform_original_finiteHodge_quotient_lift
    (G : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
      (hU : IsSourceSmoothHermitianMetric U), (sourceNativeFirstChernForm U hU).val.IsSemipositive →
      ∀ k : ℕ, k₀ ≤ k → ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
        (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)),
      letI := nativeBertiniMemberChartedSpace p i ζ hsm
      letI := nativeBertiniMemberComplex p i ζ hsm
      letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
      let L := twistedPower G U k
      ∀ R : HolomorphicSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber,
      nativeBertiniMemberHodgeEnergy p i ζ hsm L φ R < ⊤ →
      ∃ T : nativeMultiplierSections
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ,
        nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
          ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
            (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range.mkQ T) = R := by
  obtain ⟨k₀,hk₀,hLift⟩ := exists_uniform_original_finiteHodge_canonical_lift p G hG hGpos φ hφ
  refine ⟨k₀,hk₀,?_⟩
  intro U hU hUpos k hk i ζ hsm
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro L R hR
  obtain ⟨T,hT⟩ := hLift U hU hUpos k hk i ζ hsm R hR
  let Tq := nativeMultiplierSwapLastSectionMap (nativeCanonicalBundle (n := d + 1) (X := X))
    (nativeBertiniHyperplaneBundle p) L hφ T
  refine ⟨Tq,?_⟩
  rw [nativeBertiniPhysicalQuotientRestriction_mk]
  have hswap : NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d + 1) (X := X)) L
      (nativeBertiniHyperplaneBundle p) Tq.val = T.val := by
    ext x
    exact swapLastFiber_twice _ _ _ x (T.val x)
  rw [hswap]
  exact hT

end SGPT.Trace.BertiniUniversal
