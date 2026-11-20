import SGPT.Checks.Comparison.TraceResolutionDivisorialCoherence

/-! The actual native prime-composition map is bijective and reflects
THE ORIGINAL common-resolution relation. Accepted common-model and embedded
resolution EXISTENCE APIs only; no Hironaka implementation development.
Blueprint: trace-prime-birational-dictionary.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff ENNReal

variable {k : ℕ} {V W Z : Type u} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel k) V] [ChartedSpace (ComplexModel k) W]
  [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k V] [IsComplexManifold k W] [IsComplexManifold k Z]
  {π : W → V} (hπ : IsAnalyticModification (n := k) π)

include hπ in
/-- Actual holomorphic lifts through an actual modification are unique
when their actual common composite is itself a modification. -/
theorem modification_lifts_eq {a b : Z → W}
    (ha : IsAnalyticModification (n := k) a)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ b)
    (he : π ∘ a = π ∘ b) : a = b := by
  obtain ⟨A,B,s,_hAc,_hAa,_hAi,_hBc,_hBa,hBi,hpre,_hs,_hright,hleft⟩ := hπ.2.2
  have hcomp := AnalyticModificationComposition.isAnalyticModification_comp hπ ha
  have hd : Dense ((π ∘ a) ⁻¹' Bᶜ) := by
    rw [preimage_compl]
    exact interior_eq_empty_iff_dense_compl.mp
      (AnalyticModelDomination.interior_preimage_eq_empty_of_isAnalyticModification hcomp hBi)
  apply Continuous.ext_on hd ha.1.continuous hb.continuous
  intro z hz
  have haA : a z ∉ A := by
    rw [← hpre]
    exact hz
  have hbA : b z ∉ A := by
    rw [← hpre]
    change (π ∘ b) z ∉ B
    rw [← congrFun he z]
    exact hz
  exact (hleft (a z) haA).symm.trans
    ((congrArg s (congrFun he z)).trans (hleft (b z) hbA))

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
/-- Reflection uses the SAME actual common model, both original
modifications and the original equal strict transforms. -/
theorem primePush_commonResolution_iff (p q : PrimePresentation k W) :
    commonResolutionRelation (primePush hπ p) (primePush hπ q) ↔ commonResolutionRelation p q := by
  constructor
  · rintro ⟨h⟩
    refine ⟨⟨h.model,h.left,h.right,h.left_modification,h.right_modification,?_,h.strict_equal⟩⟩
    exact modification_lifts_eq hπ
      (AnalyticModificationComposition.isAnalyticModification_comp p.modification h.left_modification)
      (q.modification.1.comp h.right_modification.1) h.over_base
  · exact primePush_commonResolution hπ

variable [CompactSpace V] [ConnectedSpace V] [CompactSpace W] [ConnectedSpace W]

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
/-- Injection on the ACTUAL original direct prime classes. -/
theorem directPrimePush_injective : Function.Injective (directPrimePush hπ) := by
  intro x y
  refine Quot.inductionOn x ?_
  intro p
  refine Quot.inductionOn y ?_
  intro q he
  exact (direct_mk_eq_iff p q).mpr ((primePush_commonResolution_iff hπ p q).mp
    ((direct_mk_eq_iff (primePush hπ p) (primePush hπ q)).mp he))

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]
  [CompactSpace W] [ConnectedSpace W] in
/-- Actual SAME-divisor lifting, constructed from original geometry.
The accepted embedded-resolution existence theorem is reused unchanged. -/
theorem exists_primePush_related (p : PrimePresentation k V) :
    ∃ q : PrimePresentation k W, commonResolutionRelation (primePush hπ q) p := by
  obtain ⟨Z,_,_,_,_,_,g₀,g₁,hg₀,hg₁,hover⟩ :=
    SGPT.PSH.CompactSmoothCommonModel.exists_actual_compact_smooth_common_model p.modification hπ
  obtain ⟨F,hF,hFd⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold p.smooth
  have hcodim : F.dim + 1 = k := by rw [hFd]; exact p.codimension_one
  obtain ⟨Ft,hFt,hFtd,_himage,_hreader⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hg₀ F hcodim
  obtain ⟨Z',_,_,_,μ,hμ,hres⟩ := EmbeddedResolution.exists_embeddedResolution Ft
  have hμmod := SGPT.Okounkov.isAnalyticModification_of_finiteBlowupSequence hμ
  let q : PrimePresentation k W :=
    { model := BlowupTowers.CMfd.of (n := k) Z'
      projection := g₁ ∘ μ
      modification := AnalyticModificationComposition.isAnalyticModification_comp hg₁ hμmod
      divisor := strictTransform k μ Ft.carrier
      divisorDimension := Ft.dim
      smooth := hres.2
      codimension_one := by rw [hFtd]; exact hcodim }
  refine ⟨q,⟨⟨q.model,id,g₀ ∘ μ,SGPT.Okounkov.isAnalyticModification_identity,
    AnalyticModificationComposition.isAnalyticModification_comp hg₀ hμmod,?_,?_⟩⟩⟩
  · funext z
    exact (congrFun hover (μ z)).symm
  · change strictTransform k id (strictTransform k μ Ft.carrier) =
      strictTransform k (g₀ ∘ μ) p.divisor
    rw [StrictTransformComposition.strictTransform_comp hg₀.1 hμmod.1]
    rw [← hF, ← hFt]
    simp only [strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,closure_closure]

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
/-- Every actual original prime class lifts across the actual modification. -/
theorem directPrimePush_surjective : Function.Surjective (directPrimePush hπ) := by
  intro x
  refine Quot.inductionOn x ?_
  intro p
  obtain ⟨q,hq⟩ := exists_primePush_related hπ p
  exact ⟨Quot.mk commonResolutionRelation q,(direct_mk_eq_iff _ _).mpr hq⟩

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
/-- The ACTUAL original prime quotient dictionary is a bijection. -/
theorem directPrimePush_bijective : Function.Bijective (directPrimePush hπ) :=
  ⟨directPrimePush_injective hπ,directPrimePush_surjective hπ⟩

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
/-- Actual bijection keeps EVERY same positive REAL weight and the trivial
point; it includes dimension zero, with its vacuous strict-prime branch. -/
theorem nativeDivisorialPush_bijective : Function.Bijective (nativeDivisorialPush hπ) := by
  constructor
  · intro x y h
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some cy =>
            change none = some (cy.1,directPrimePush hπ cy.2) at h
            cases h
    | some cx =>
        cases y with
        | none =>
            change some (cx.1,directPrimePush hπ cx.2) = none at h
            cases h
        | some cy =>
            rcases cx with ⟨c,p⟩
            rcases cy with ⟨d,q⟩
            change some (c,directPrimePush hπ p) = some (d,directPrimePush hπ q) at h
            have he := Option.some.inj h
            have hc : c = d := congrArg (fun z : {c : ℝ // 0 < c} × DirectPrimeOver k V => z.1) he
            have hp : p = q := directPrimePush_injective hπ
              (congrArg (fun z : {c : ℝ // 0 < c} × DirectPrimeOver k V => z.2) he)
            exact congrArg some (Prod.ext hc hp)
  · intro y
    cases y with
    | none => exact ⟨none,rfl⟩
    | some cy =>
        rcases cy with ⟨c,p⟩
        obtain ⟨q,hq⟩ := directPrimePush_surjective hπ p
        exact ⟨some (c,q),by change some (c,directPrimePush hπ q) = some (c,p); rw [hq]⟩

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
/-- The ACTUAL geometric native divisorial equivalence, from the proved
bijection of the literal same-prime composition map. -/
def nativeDivisorialEquiv : NativeDivisorialPoint k W ≃ NativeDivisorialPoint k V :=
  Equiv.ofBijective (nativeDivisorialPush hπ) (nativeDivisorialPush_bijective hπ)

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
theorem nativeDivisorialEquiv_apply (v : NativeDivisorialPoint k W) :
    nativeDivisorialEquiv hπ v = nativeDivisorialPush hπ v := rfl

omit [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] in
theorem nativeDivisorialEquiv_symm_trivial : (nativeDivisorialEquiv hπ).symm none = none := by
  apply (nativeDivisorialEquiv hπ).injective
  exact (nativeDivisorialEquiv hπ).apply_symm_apply none

end SGPT.NAPotential.TraceComparison
