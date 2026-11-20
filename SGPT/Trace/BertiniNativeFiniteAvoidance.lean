import SGPT.Trace.BertiniNativeFiniteGermTests
import SGPT.Trace.BertiniGlobalSectionDivision
import SGPT.Trace.BertiniNativeQuotientHodge

/-! Actual native global multiplier cancellation and injectivity from PRODUCED finite avoidance. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
theorem originalCoherent_mem_unit_mul_iff (A : GermIdeal n X) (hA : A.IsCoherent)
    {x : X} {f : X → ℂ} (hf : HolomorphicAt n f x) (hfx : f x ≠ 0) (g : X → ℂ) :
    A.mem x (fun y => f y * g y) ↔ A.mem x g := by
  obtain ⟨U,_hU,hx,k,s,_hs,hspan⟩ := hA x
  rw [hspan x hx _,hspan x hx _]
  constructor
  · intro hfg
    have hi := RelativePrincipalizationSpan.holomorphicAt_inv hf hfx
    apply InvertibleIdealQuotient.IsInSpanAt.congr' (IsInSpanAt.mul_left hi hfg)
    filter_upwards [hf.continuousAt.eventually_ne hfx] with y hy
    simp only [← mul_assoc,inv_mul_cancel₀ hy,one_mul]
  · exact IsInSpanAt.mul_left hf

variable [CompactSpace X] (E : HermitianHolomorphicLineBundle.{0,0} n X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)

include hφ in
theorem exists_finite_nativeMultiplier_tensor_cancellation :
    ∃ F : Finset X, ∀ (P : HermitianHolomorphicLineBundle.{0,0} n X)
      (u : HolomorphicSections (n := n) E.Fiber) (s : HolomorphicSections (n := n) P.Fiber),
      (∀ x ∈ F, s x ≠ 0) →
      nativeTensorSection E P u s ∈ fullHolomorphicIdealSections (n := n) (tensor E P).Fiber
        (sourceDegreeMultiplierIdeal (n := n) 1 φ) →
      u ∈ fullHolomorphicIdealSections (n := n) E.Fiber (sourceDegreeMultiplierIdeal (n := n) 1 φ) := by
  classical
  obtain ⟨F,hF⟩ := exists_finite_nativeMultiplier_tests E hφ
  let A := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hA : A.IsCoherent := sourceDegreeMultiplierIdeal_isCoherent 1 hφ
  refine ⟨F,?_⟩
  intro P u s hnonzero hS
  apply (hF u).mpr
  intro x hx
  let e := preferredOriginalFrame E.Fiber x
  let f := preferredOriginalFrame P.Fiber x
  let q := tensorAtlasFrame e f
  let := e.property
  let := f.property
  let := q.property
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : x ∈ q.val.baseSet := ⟨he,hf⟩
  have hSM : A.mem x (sectionCoefficient (tensor E P).Fiber q.val (nativeTensorSection E P u s)) :=
    (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) (tensor E P).Fiber A hA q
      (nativeTensorSection E P u s) hq).mp (hS q ⟨x,mem_univ x⟩ hq)
  let a := sectionCoefficient P.Fiber f.val s
  let b := sectionCoefficient E.Fiber e.val u
  have ha : HolomorphicAt n a x := originalSectionCoefficient_holomorphicAt (n := n) P.Fiber f s hf
  have hax : a x ≠ 0 := by
    intro hz
    apply hnonzero x hx
    apply (f.val.linearEquivAt ℂ x hf).injective
    exact hz.trans (map_zero _).symm
  have hprod : A.mem x (fun y => a y * b y) := by
    obtain ⟨U,_hU,hxU,k,t,_ht,hspan⟩ := hA x
    apply (hspan x hxU _).mpr
    apply InvertibleIdealQuotient.IsInSpanAt.congr' ((hspan x hxU _).mp hSM)
    filter_upwards [e.val.open_baseSet.mem_nhds he,f.val.open_baseSet.mem_nhds hf] with y hyE hyP
    rw [nativeTensorSection_coefficient E P e f u s y hyE hyP]
    exact mul_comm _ _
  exact (originalCoherent_mem_unit_mul_iff A hA ha hax b).mp hprod

variable [ConnectedSpace X]

theorem exists_finite_nativeBertini_multiplier_division {N : ℕ}
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞) :
    ∃ F : Finset X, ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
      (_hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)),
      (∀ x ∈ F, x ∉ member p (affinePoint i ζ)) →
      ∀ S : nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ,
        (∀ x ∈ member p (affinePoint i ζ), S.val x = 0) →
        ∃ u : nativeMultiplierSections E φ,
          nativeMultiplierSectionMap E (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ) u = S := by
  classical
  obtain ⟨F,hF⟩ := exists_finite_nativeMultiplier_tensor_cancellation E hφ
  let x₀ : X := Classical.choice inferInstance
  refine ⟨insert x₀ F,?_⟩
  intro i ζ hsm havoid S hS
  have hproper : ∃ x : X, x ∉ member p (affinePoint i ζ) := ⟨x₀,havoid x₀ (Finset.mem_insert_self _ _)⟩
  obtain ⟨u,hu⟩ := exists_nativeBertini_global_section_division p i ζ hsm E S.val hS hproper
  have hnonzero (x : X) (hx : x ∈ F) : nativeBertiniAffineSection p i ζ x ≠ 0 := by
    intro hz
    exact havoid x (Finset.mem_insert_of_mem hx) ((nativeBertiniAffineSection_zero_iff p i ζ x).mp hz)
  have humem := hF (nativeBertiniHyperplaneBundle p) u (nativeBertiniAffineSection p i ζ) hnonzero
    (show nativeTensorSection E (nativeBertiniHyperplaneBundle p) u (nativeBertiniAffineSection p i ζ) ∈
      fullHolomorphicIdealSections (n := n) (tensor E (nativeBertiniHyperplaneBundle p)).Fiber
        (sourceDegreeMultiplierIdeal (n := n) 1 φ) from hu ▸ S.property)
  refine ⟨⟨u,humem⟩,?_⟩
  apply Subtype.ext
  exact hu

section Physical
variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y] [CompactSpace Y] [ConnectedSpace Y]
  (pM : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) Y)
  {ψ : Y → EReal} (hψ : IsGlobalQuasiPshPotential (n := d + 1) ψ)

theorem exists_finite_nativeBertini_quotient_restriction_injective :
    ∃ F : Finset Y, ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
      (hsm : IsSmoothHypersurfaceMember (d + 1) pM (affinePoint i ζ)),
      (∀ y ∈ F, y ∉ member pM (affinePoint i ζ)) →
      letI := nativeBertiniMemberChartedSpace pM i ζ hsm
      letI := nativeBertiniMemberComplex pM i ζ hsm
      letI := isCompact_iff_compactSpace.mp (isClosed_member pM pM.contMDiff.continuous (affinePoint i ζ)).isCompact
      Function.Injective (nativeBertiniPhysicalQuotientRestriction pM i ζ hsm L hψ) := by
  classical
  let K := nativeCanonicalBundle (n := d + 1) (X := Y)
  let E₀ := tensor K L
  let P := nativeBertiniHyperplaneBundle pM
  obtain ⟨F,hF⟩ := exists_finite_nativeBertini_multiplier_division E₀ hψ pM
  refine ⟨F,?_⟩
  intro i ζ hsm havoid
  let := nativeBertiniMemberChartedSpace pM i ζ hsm
  let := nativeBertiniMemberComplex pM i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member pM pM.contMDiff.continuous (affinePoint i ζ)).isCompact
  let R := nativeBertiniPhysicalQuotientRestriction pM i ζ hsm L hψ
  have hz (q : NativeBertiniMultiplierQuotient pM i ζ L hψ) (hq : R q = 0) : q = 0 := by
    revert hq
    refine Submodule.Quotient.induction_on
      (nativeMultiplierSectionMap E₀ P hψ (nativeBertiniAffineSection pM i ζ)).range q ?_
    intro S hS
    have hvanish (y : Y) (hy : y ∈ member pM (affinePoint i ζ)) : S.val y = 0 := by
      let yH : member pM (affinePoint i ζ) := ⟨y,hy⟩
      have hp := congrArg (fun T => T yH) hS
      change nativeBertiniPhysicalAdjunctionFiberEquiv pM i ζ hsm L yH
        (NativeTensorSwap.swapLastFiber K L P y (S.val y)) = 0 at hp
      apply (NativeTensorSwap.swapLastFiber K L P y).injective
      apply (nativeBertiniPhysicalAdjunctionFiberEquiv pM i ζ hsm L yH).injective
      simpa only [map_zero] using hp
    obtain ⟨u,hu⟩ := hF i ζ hsm havoid S hvanish
    apply (Submodule.Quotient.mk_eq_zero
      (nativeMultiplierSectionMap E₀ P hψ (nativeBertiniAffineSection pM i ζ)).range).mpr
    exact ⟨u,hu⟩
  intro q₁ q₂ hq
  apply sub_eq_zero.mp
  apply hz (q₁ - q₂)
  rw [map_sub,hq,sub_self]

end Physical
end SGPT.Trace.Bertini
