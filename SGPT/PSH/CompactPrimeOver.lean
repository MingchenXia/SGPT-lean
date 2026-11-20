import SGPT.PSH.CompactSmoothCommonModel
import SGPT.Okounkov.NativeFlagBaseGeometry
import SGPT.PSH.SourceGenericLelong
import SGPT.Foundations.Analysis.Pending.AnalyticModelDomination
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition
import SGPT.Foundations.Analysis.Pending.RawCommonResolutionPrimeReader
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.CompactPrimeOver

universe u
open scoped Topology Manifold ContDiff

open Set
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy BlowupTowers
open VariableComplexAtlas SquaredLogLelongSourceNormalization

/-- Actual smooth-model geometry and the original connected regular hypersurface. -/
structure PrimePresentation (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] where
  model : CMfd.{u} n
  projection : model → X
  modification : IsAnalyticModification (n := n) projection
  divisor : Set model
  divisorDimension : ℕ
  smooth : IsClosedConnectedSubmanifold n divisor divisorDimension
  codimension_one : divisorDimension + 1 = n

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

theorem PrimePresentation.dimension_pos (p : PrimePresentation n X) : 0 < n := by
  have h := p.codimension_one
  omega

def presentationCenter (p : PrimePresentation n X) : Set X :=
  p.projection '' p.divisor

def presentationReader (φ : X → EReal) (p : PrimePresentation n X) : ℝ≥0∞ :=
  (ofFixedModel n p.model).sourceGenericLelong (φ ∘ p.projection) p.divisor

/-- Natural common-resolution data; the common strict carrier is not supplied
as an extra analytic or reader certificate. -/
structure CommonResolutionGeometry (p q : PrimePresentation n X) where
  model : CMfd.{u} n
  left : model → p.model
  right : model → q.model
  left_modification : IsAnalyticModification (n := n) left
  right_modification : IsAnalyticModification (n := n) right
  over_base : p.projection ∘ left = q.projection ∘ right
  strict_equal : strictTransform n left p.divisor = strictTransform n right q.divisor

def commonResolutionRelation (p q : PrimePresentation n X) : Prop :=
  Nonempty (CommonResolutionGeometry p q)

private theorem common_analytic_carriers {p q : PrimePresentation n X}
    (h : CommonResolutionGeometry p q) :
    ∃ (V₀ : ClosedIrreducibleAnalyticSubvariety n p.model)
      (V₁ : ClosedIrreducibleAnalyticSubvariety n q.model)
      (W : ClosedIrreducibleAnalyticSubvariety n h.model),
      V₀.carrier = p.divisor ∧ V₁.carrier = q.divisor ∧
      W.carrier = strictTransform n h.left V₀.carrier ∧
      W.carrier = strictTransform n h.right V₁.carrier := by
  obtain ⟨V₀, hV₀, hd₀⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold p.smooth
  obtain ⟨V₁, hV₁, _hd₁⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold q.smooth
  have hcodim : V₀.dim + 1 = n := by
    rw [hd₀]
    exact p.codimension_one
  obtain ⟨W, hW, _hdW, _himage, _hreader⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader
      h.left_modification V₀ hcodim
  have hstrict : strictTransform n h.left V₀.carrier =
      strictTransform n h.right V₁.carrier := by
    simpa only [hV₀, hV₁] using h.strict_equal
  exact ⟨V₀, V₁, W, hV₀, hV₁, hW, hW.trans hstrict⟩

/-- The literal source reader is invariant under each natural geometric
common-resolution witness, including infinite values. -/
theorem presentationReader_eq_of_commonResolution {p q : PrimePresentation n X}
    (h : CommonResolutionGeometry p q) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    presentationReader φ p = presentationReader φ q := by
  obtain ⟨V₀, V₁, W, hV₀, hV₁, hW₀, hW₁⟩ := common_analytic_carriers h
  have hraw := RawCommonResolutionPrimeReader.iInf_lelongNumber_eq_of_common_resolution
    p.modification q.modification h.left_modification h.right_modification
    h.over_base hφ V₀ V₁ W hW₀ hW₁
  have hn : n ≠ 0 := Nat.ne_of_gt p.dimension_pos
  simp only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← iInf_lelongNumber_eq_two_mul_squaredLog hn,
    ← iInf_lelongNumber_eq_two_mul_squaredLog hn]
  simpa only [hV₀, hV₁, Function.comp_def] using hraw

/-- The center is produced from the actual whole strict-transform images. -/
theorem presentationCenter_eq_of_commonResolution {p q : PrimePresentation n X}
    (h : CommonResolutionGeometry p q) : presentationCenter p = presentationCenter q := by
  obtain ⟨V₀, V₁, W, hV₀, hV₁, hW₀, hW₁⟩ := common_analytic_carriers h
  have himage₀ := RawProperStrictTransformLelongReader.image_eq_of_strictTransform
    h.left_modification.1 h.left_modification.2.1 V₀ W hW₀
  have himage₁ := RawProperStrictTransformLelongReader.image_eq_of_strictTransform
    h.right_modification.1 h.right_modification.2.1 V₁ W hW₁
  unfold presentationCenter
  rw [← hV₀, ← hV₁, ← himage₀, ← himage₁, image_image, image_image]
  exact congrArg (fun f : h.model → X => f '' W.carrier) h.over_base


/-- Literal smooth common-resolution projection and holomorphic domination maps.
No modification records for the two domination maps are supplied. -/
structure HolomorphicCommonResolutionGeometry (p q : PrimePresentation n X) where
  model : CMfd.{u} n
  projection : model → X
  modification : IsAnalyticModification (n := n) projection
  left : model → p.model
  right : model → q.model
  left_holomorphic : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ left
  right_holomorphic : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ right
  left_over_base : p.projection ∘ left = projection
  right_over_base : q.projection ∘ right = projection
  strict_equal : strictTransform n left p.divisor = strictTransform n right q.divisor

def holomorphicCommonResolutionRelation (p q : PrimePresentation n X) : Prop :=
  Nonempty (HolomorphicCommonResolutionGeometry p q)

/-- The actual common projection and genuine holomorphic domination dictionary
identify the exact two single-common-resolution witness descriptions. -/
theorem commonResolutionRelation_iff_holomorphicCommonResolutionRelation
    (p q : PrimePresentation n X) :
    commonResolutionRelation p q ↔ holomorphicCommonResolutionRelation p q := by
  constructor
  · rintro ⟨h⟩
    exact ⟨⟨h.model, p.projection ∘ h.left,
      AnalyticModificationComposition.isAnalyticModification_comp p.modification h.left_modification,
      h.left, h.right, h.left_modification.1, h.right_modification.1,
      rfl, h.over_base.symm, h.strict_equal⟩⟩
  · rintro ⟨h⟩
    exact ⟨⟨h.model, h.left, h.right,
      AnalyticModelDomination.isAnalyticModification_of_holomorphic_over
        p.modification h.modification h.left_holomorphic h.left_over_base,
      AnalyticModelDomination.isAnalyticModification_of_holomorphic_over
        q.modification h.modification h.right_holomorphic h.right_over_base,
      h.left_over_base.trans h.right_over_base.symm, h.strict_equal⟩⟩

theorem commonResolutionRelation_refl (p : PrimePresentation n X) :
    commonResolutionRelation p p := by
  exact ⟨⟨p.model, id, id, SGPT.Okounkov.isAnalyticModification_identity,
    SGPT.Okounkov.isAnalyticModification_identity, rfl, rfl⟩⟩

theorem commonResolutionRelation_symm {p q : PrimePresentation n X}
    (hpq : commonResolutionRelation p q) : commonResolutionRelation q p := by
  obtain ⟨h⟩ := hpq
  exact ⟨⟨h.model, h.right, h.left, h.right_modification, h.left_modification,
    h.over_base.symm, h.strict_equal.symm⟩⟩

section Compact

variable [ConnectedSpace X] [CompactSpace X]

/-- A SINGLE actual new witness is constructed by common refinement over the
middle model and literal holomorphic strict-transform composition. -/
theorem commonResolutionRelation_trans {p q r : PrimePresentation n X}
    (hpq : commonResolutionRelation p q) (hqr : commonResolutionRelation q r) :
    commonResolutionRelation p r := by
  obtain ⟨h₀⟩ := hpq
  obtain ⟨h₁⟩ := hqr
  let : CompactSpace q.model :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification q.modification
  let : ConnectedSpace q.model :=
    SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification q.modification
  obtain ⟨Z, instTop, instChart, instMfd, _instConn, _instCompact, a, b, ha, hb, hab⟩ :=
    SGPT.PSH.CompactSmoothCommonModel.exists_actual_compact_smooth_common_model
      h₀.right_modification h₁.left_modification
  refine ⟨⟨CMfd.of (n := n) Z, h₀.left ∘ a, h₁.right ∘ b,
    AnalyticModificationComposition.isAnalyticModification_comp h₀.left_modification ha,
    AnalyticModificationComposition.isAnalyticModification_comp h₁.right_modification hb,
    ?_, ?_⟩⟩
  · funext z
    change p.projection (h₀.left (a z)) = r.projection (h₁.right (b z))
    calc
      p.projection (h₀.left (a z)) = q.projection (h₀.right (a z)) :=
        congrFun h₀.over_base (a z)
      _ = q.projection (h₁.left (b z)) := congrArg q.projection (congrFun hab z)
      _ = r.projection (h₁.right (b z)) := congrFun h₁.over_base (b z)
  · rw [StrictTransformComposition.strictTransform_comp h₀.left_modification.1 ha.1,
      StrictTransformComposition.strictTransform_comp h₁.right_modification.1 hb.1]
    calc
      strictTransform n a (strictTransform n h₀.left p.divisor) =
          strictTransform n a (strictTransform n h₀.right q.divisor) :=
        congrArg (strictTransform n a) h₀.strict_equal
      _ = strictTransform n (h₀.right ∘ a) q.divisor :=
        (StrictTransformComposition.strictTransform_comp h₀.right_modification.1 ha.1 q.divisor).symm
      _ = strictTransform n (h₁.left ∘ b) q.divisor :=
        congrArg (fun f => strictTransform n f q.divisor) hab
      _ = strictTransform n b (strictTransform n h₁.left q.divisor) :=
        StrictTransformComposition.strictTransform_comp h₁.left_modification.1 hb.1 q.divisor
      _ = strictTransform n b (strictTransform n h₁.right r.divisor) :=
        congrArg (strictTransform n b) h₁.strict_equal

/-- The original SINGLE-common-resolution relation, with all three actual
proved equivalence laws. No equivalence-closure relation is substituted. -/
def directSetoid : Setoid (PrimePresentation n X) where
  r := commonResolutionRelation
  iseqv := ⟨commonResolutionRelation_refl, @commonResolutionRelation_symm n X _ _ _,
    @commonResolutionRelation_trans n X _ _ _ _ _⟩

variable (n X) in
/-- Quotient by the original direct relation after proving its actual equivalence laws. -/
def DirectPrimeOver : Type (u + 1) :=
  Quotient (directSetoid (n := n) (X := X))

variable (n X) in
/-- The original positive rational weights, paired with direct geometric classes. -/
def WeightedDirectPrimeOver : Type (u + 1) :=
  {c : ℚ // 0 < c} × DirectPrimeOver n X

/-- Class equality is EXACTLY the single actual common-resolution relation. -/
theorem direct_mk_eq_iff (p q : PrimePresentation n X) :
    (Quot.mk commonResolutionRelation p : DirectPrimeOver n X) =
      Quot.mk commonResolutionRelation q ↔ commonResolutionRelation p q := by
  constructor
  · exact Quotient.exact (s := directSetoid (n := n) (X := X)) (a := p) (b := q)
  · exact Quotient.sound (s := directSetoid (n := n) (X := X)) (a := p) (b := q)

def directCenter : DirectPrimeOver n X → Set X :=
  Quot.lift presentationCenter (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationCenter_eq_of_commonResolution h)

def directReader (φ : X → EReal)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) : DirectPrimeOver n X → ℝ≥0∞ :=
  Quot.lift (presentationReader φ) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationReader_eq_of_commonResolution h hφ)

theorem directCenter_mk (p : PrimePresentation n X) :
    directCenter (Quot.mk commonResolutionRelation p) = presentationCenter p := rfl

theorem directReader_mk (φ : X → EReal)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (p : PrimePresentation n X) :
    directReader φ hφ (Quot.mk commonResolutionRelation p) = presentationReader φ p := rfl

omit [ConnectedSpace X] [CompactSpace X] in
private theorem raw_of_sourcePSH {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsPSH φ) :
    ManifoldQuasiPlurisubharmonic (n := n) φ := by
  have hnative : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  intro e z hz
  exact (hnative.chartPlurisubharmonic e z hz).quasiPlurisubharmonicAt

/-- Original source PSH input manufactures the regularity needed for descent. -/
def directSourcePSHReader (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ) :
    DirectPrimeOver n X → ℝ≥0∞ := directReader φ (raw_of_sourcePSH hφ)

theorem directSourcePSHReader_mk (φ : X → EReal)
    (hφ : (ofFixedModel n X).IsPSH φ) (p : PrimePresentation n X) :
    directSourcePSHReader φ hφ (Quot.mk commonResolutionRelation p) =
      (ofFixedModel n p.model).sourceGenericLelong (φ ∘ p.projection) p.divisor := rfl

end Compact
end SGPT.PSH.CompactPrimeOver
