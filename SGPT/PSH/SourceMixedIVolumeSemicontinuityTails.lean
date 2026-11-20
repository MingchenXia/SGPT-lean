import SGPT.PSH.CompactPrimeNumerical
import SGPT.PSH.SourceTestCurveModificationPullback
import SGPT.PSH.SourceThetaPSHCompactness
import SGPT.Foundations.Analysis.Pending.DivisorialFamilySupremumLelong

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.PSH.SourceUSCTailsDraft
open Set Filter
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
  SGPT.Foundations.Analysis.Pending.DivisorialFamilySupremumLelong
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  VariableComplexAtlas CompactPrimeOver CompactPrimeNumerical

private theorem sourceGenericLelong_eq_half_native
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
    (a : M → EReal) (E : Set M) :
    (ofFixedModel (m+1) M).sourceGenericLelong a E =
      (2 : ENNReal)⁻¹ * divisorialLelongNumber m a E := by
  simp only [sourceGenericLelong,sourceLelong_ofFixedModel_eq]
  rw [divisorialLelongNumber,iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  symm
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Every original actual prime model reads the literal regularized supremum
as the infimum of the same original source Lelong readers. No supplied
pullback/supremum commutation, compact model or flattening certificate. -/
theorem presentationReader_uscSup_eq_iInf {I : Type*} [Nonempty I]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : I → X → EReal)
    (hu : ∀ i, (ofFixedModel n X).IsThetaPSH θ (u i)) {B : ℝ}
    (hB : ∀ i x, u i x ≤ (B : EReal)) (p : PrimePresentation n X) :
    presentationReader (uscSup u) p = ⨅ i, presentationReader (u i) p := by
  cases n with
  | zero => have hp := p.dimension_pos; omega
  | succ m =>
    let : CompactSpace p.model := compactSpace_of_isAnalyticModification p.modification
    let θY := θ.nativeHolomorphicPullback p.modification.1
    have huY (i : I) : (ofFixedModel (m+1) p.model).IsThetaPSH θY (u i ∘ p.projection) :=
      (hu i).comp_native_analyticModification p.modification
    have hYsup : (ofFixedModel (m+1) p.model).IsThetaPSH θY
        (uscSup (fun i => u i ∘ p.projection)) :=
      isThetaPSH_uscSup_of_majorant huY upperSemicontinuous_const
        (fun _ => EReal.coe_ne_top B) (fun i y => hB i (p.projection y))
    have hcomp := uscSup_comp_modification p.modification θ u hYsup
    have hun (i : I) := (isThetaPSH_iff_nativeThetaPotential θY _).mp (huY i)
    have hflat (y : p.model) (hy : y ∈ p.divisor) :
        Nonempty (DivisorFlattening (m := m) p.divisor y) := by
      have hd : p.divisorDimension = m := by have h := p.codimension_one; omega
      apply DivisorFlattening.nonempty_of_regularAtDim
      simpa only [hd] using p.smooth.2.2 y hy
    have hν := divisorialLelongNumber_regularized_iSup_eq_iInf
      (fun i => (hun i).1) (fun i y => hB i (p.projection y)) hflat
    change (ofFixedModel (m+1) p.model).sourceGenericLelong
      (uscSup u ∘ p.projection) p.divisor = _
    rw [← hcomp]
    simp_rw [presentationReader,sourceGenericLelong_eq_half_native]
    change (2 : ENNReal)⁻¹ * divisorialLelongNumber m
      (uscRegularization (fun y => ⨆ i, (u i ∘ p.projection) y)) p.divisor = _
    rw [hν,ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]

/-- The literal spatial USC supremum of the original directed tail. -/
def tailSup {J : Type*} [Preorder J] (u : J → X → EReal) (j : J) : X → EReal :=
  uscSup (fun k : Ici j => u k.val)

omit [CompactSpace X] in
/-- Actual original theta-PSH membership of every whole tail. -/
theorem tailSup_thetaPSH {J : Type*} [Preorder J]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : J → X → EReal)
    (hu : ∀ j, (ofFixedModel n X).IsThetaPSH θ (u j)) {B : ℝ}
    (hB : ∀ j x, u j x ≤ (B : EReal)) (j : J) :
    (ofFixedModel n X).IsThetaPSH θ (tailSup u j) := by
  let : Nonempty (Ici j) := ⟨⟨j,le_rfl⟩⟩
  exact isThetaPSH_uscSup_of_majorant (fun k : Ici j => hu k.val)
    upperSemicontinuous_const (fun _ => EReal.coe_ne_top B)
    (fun k x => hB k.val x)

omit [CompactSpace X] in
/-- The actual bound and actual input member survive genuine tail closure. -/
theorem tailSup_bounds {J : Type*} [Preorder J] (u : J → X → EReal) {B : ℝ}
    (hB : ∀ j x, u j x ≤ (B : EReal)) (j : J) :
    u j ≤ tailSup u j ∧ tailSup u j ≤ fun _ => (B : EReal) := by
  constructor
  · intro x
    exact (le_iSup (fun k : Ici j => u k.val x) ⟨j,le_rfl⟩).trans
      (le_uscRegularization (fun y => ⨆ k : Ici j, u k.val y) x)
  · exact uscRegularization_le upperSemicontinuous_const
      (fun x => iSup_le fun k : Ici j => hB k.val x)

omit [CompactSpace X] in
/-- Tails decrease as ENTIRE original functions, without a cofinal sequence. -/
theorem tailSup_antitone {J : Type*} [Preorder J] (u : J → X → EReal) :
    Antitone (tailSup u) := by
  intro j k hjk
  apply uscRegularization_mono
  intro x
  exact iSup_le fun a : Ici k =>
    le_iSup (fun b : Ici j => u b.val x) ⟨a.val,hjk.trans a.property⟩

/-- Exact generic-Lelong reader on EVERY actual prime-over-X and original tail. -/
theorem presentationReader_tailSup {J : Type*} [Preorder J]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : J → X → EReal)
    (hu : ∀ j, (ofFixedModel n X).IsThetaPSH θ (u j)) {B : ℝ}
    (hB : ∀ j x, u j x ≤ (B : EReal)) (j : J) (p : PrimePresentation n X) :
    presentationReader (tailSup u j) p = ⨅ k : Ici j, presentationReader (u k.val) p := by
  let : Nonempty (Ici j) := ⟨⟨j,le_rfl⟩⟩
  exact presentationReader_uscSup_eq_iInf θ (fun k : Ici j => u k.val)
    (fun k => hu k.val) (fun k x => hB k.val x) p

/-- Incoming original divisorial convergence proves the ACTUAL target-to-tail
I-order, using all original proper prime tests, with no output comparison input. -/
theorem target_IOrder_tailSup {J : Type*} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : J → X → EReal)
    (v : X → EReal) (hu : ∀ j, (ofFixedModel n X).IsThetaPSH θ (u j))
    (hv : (ofFixedModel n X).IsThetaPSH θ v) {B : ℝ}
    (hB : ∀ j x, u j x ≤ (B : EReal))
    (hlim : ∀ p : PrimePresentation n X, Tendsto (fun j => presentationReader (u j) p)
      atTop (𝓝 (presentationReader v p))) (j : J) :
    sourceIOrder (ofFixedModel n X) v (tailSup u j) := by
  apply (sourceIOrder_iff_presentationComparison ⟨θ,hv⟩
    ⟨θ,tailSup_thetaPSH θ u hu hB j⟩).mpr
  intro p
  rw [presentationReader_tailSup θ u hu hB j p]
  apply ge_of_tendsto (hlim p)
  filter_upwards [eventually_ge_atTop j] with k hk
  exact iInf_le (fun a : Ici j => presentationReader (u a.val) p) ⟨k,hk⟩

/-- The original tail readers converge to the original target readers on
EVERY actual prime, for arbitrary directed nets, including infinite values. -/
theorem tendsto_presentationReader_tailSup {J : Type*} [Preorder J]
    [IsDirectedOrder J] [Nonempty J]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : J → X → EReal)
    (v : X → EReal) (hu : ∀ j, (ofFixedModel n X).IsThetaPSH θ (u j)) {B : ℝ}
    (hB : ∀ j x, u j x ≤ (B : EReal))
    (hlim : ∀ p : PrimePresentation n X, Tendsto (fun j => presentationReader (u j) p)
      atTop (𝓝 (presentationReader v p))) (p : PrimePresentation n X) :
    Tendsto (fun j => presentationReader (tailSup u j) p)
      atTop (𝓝 (presentationReader v p)) := by
  have hm : Monotone (fun j => ⨅ k : Ici j, presentationReader (u k.val) p) := by
    intro j k hjk
    apply le_iInf
    intro a
    exact iInf_le (fun b : Ici j => presentationReader (u b.val) p)
      ⟨a.val,hjk.trans a.property⟩
  have he : (⨆ j, ⨅ k : Ici j, presentationReader (u k.val) p) =
      presentationReader v p := by
    have h := (atTop_basis : (atTop : Filter J).HasBasis (fun _ => True) Ici).liminf_eq_iSup_iInf
      (u := fun j => presentationReader (u j) p)
    simpa only [iSup_true,iInf_subtype,mem_Ici] using h.symm.trans (hlim p).liminf_eq
  have ht := tendsto_atTop_iSup hm
  rw [he] at ht
  simpa only [presentationReader_tailSup θ u hu hB] using ht

end SGPT.PSH.SourceUSCTailsDraft
