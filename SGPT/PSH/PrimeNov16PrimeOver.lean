import SGPT.PSH.PrimeNov16CommonModel
import SGPT.PSH.CompactPrimeMultiplierLimit

/-! The SINGLE common-resolution relation and genuine readers over arbitrary
noncompact smooth bases. Actual common models, not a generated relation, prove
transitivity. Singular original bases are not claimed here.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16PrimeOver
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.BlowupSequences AnalyticModificationLocalDiscrepancy CompactPrimeOver
  CompactPrimeMultiplierOrder CompactPrimeMultiplierLimit VariableComplexAtlas
  SquaredLogLelongSourceNormalization
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

theorem commonResolutionRelation_trans {p q r : PrimePresentation n X}
    (hpq : commonResolutionRelation p q) (hqr : commonResolutionRelation q r) :
    commonResolutionRelation p r := by
  obtain ⟨h₀⟩ := hpq
  obtain ⟨h₁⟩ := hqr
  obtain ⟨Z, a, b, ha, hb, hab⟩ :=
    PrimeNov16CommonModel.exists_actual_common_model h₀.right_modification h₁.left_modification
  refine ⟨⟨Z, h₀.left ∘ a, h₁.right ∘ b,
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
        (StrictTransformComposition.strictTransform_comp h₀.right_modification.1 ha.1
          q.divisor).symm
      _ = strictTransform n (h₁.left ∘ b) q.divisor :=
        congrArg (fun f => strictTransform n f q.divisor) hab
      _ = strictTransform n b (strictTransform n h₁.left q.divisor) :=
        StrictTransformComposition.strictTransform_comp h₁.left_modification.1 hb.1 q.divisor
      _ = strictTransform n b (strictTransform n h₁.right r.divisor) :=
        congrArg (strictTransform n b) h₁.strict_equal

def primeSetoid : Setoid (PrimePresentation n X) where
  r := commonResolutionRelation
  iseqv := ⟨commonResolutionRelation_refl, commonResolutionRelation_symm,
    commonResolutionRelation_trans⟩

variable (n X) in
def PrimeOver : Type 1 :=
  Quotient (primeSetoid (n := n) (X := X))

variable (n X) in
def WeightedPrimeOver : Type 1 :=
  {c : ℚ // 0 < c} × PrimeOver n X

theorem mk_eq_iff (p q : PrimePresentation n X) :
    (Quot.mk commonResolutionRelation p : PrimeOver n X) =
      Quot.mk commonResolutionRelation q ↔ commonResolutionRelation p q := by
  constructor
  · exact Quotient.exact (s := primeSetoid (n := n) (X := X)) (a := p) (b := q)
  · exact Quotient.sound (s := primeSetoid (n := n) (X := X)) (a := p) (b := q)

def center : PrimeOver n X → Set X :=
  Quot.lift presentationCenter (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationCenter_eq_of_commonResolution h)

theorem center_mk (p : PrimePresentation n X) :
    center (Quot.mk commonResolutionRelation p) = presentationCenter p := rfl

def reader (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    PrimeOver n X → ℝ≥0∞ :=
  Quot.lift (presentationReader φ) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationReader_eq_of_commonResolution h hφ)

theorem reader_mk (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (p : PrimePresentation n X) :
    reader φ hφ (Quot.mk commonResolutionRelation p) = presentationReader φ p := rfl

private theorem qpsh_of_sourcePSH {φ : X → EReal} (hφ : (ofFixedModel n X).IsPSH φ) :
    ManifoldQuasiPlurisubharmonic (n := n) φ := by
  have hnative : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  intro e z hz
  exact (hnative.chartPlurisubharmonic e z hz).quasiPlurisubharmonicAt

private theorem globalQPSH_of_sourcePSH {φ : X → EReal} (hφ : (ofFixedModel n X).IsPSH φ) :
    IsGlobalQuasiPshPotential (n := n) φ := by
  have hnative : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  exact ⟨qpsh_of_sourcePSH hφ, hnative.locallyNondegenerate⟩

def sourcePSHReader (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ) :
    PrimeOver n X → ℝ≥0∞ :=
  reader φ (qpsh_of_sourcePSH hφ)

theorem sourcePSHReader_mk (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ)
    (p : PrimePresentation n X) :
    sourcePSHReader φ hφ (Quot.mk commonResolutionRelation p) =
      (ofFixedModel n p.model).sourceGenericLelong (φ ∘ p.projection) p.divisor := rfl

def multiplierOrder {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ) {c : ℝ}
    (hc : 0 < c) : PrimeOver n X → ℕ :=
  Quot.lift (presentationMultiplierOrder hφ hc) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationMultiplierOrder_eq_of_commonResolution hφ hc h)

theorem multiplierOrder_mk {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    {c : ℝ} (hc : 0 < c) (p : PrimePresentation n X) :
    multiplierOrder hφ hc (Quot.mk commonResolutionRelation p) =
      presentationMultiplierOrder hφ hc p := rfl

theorem tendsto_multiplierOrder_ratio (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ)
    (E : PrimeOver n X) :
    Tendsto (fun k : ℕ =>
      (multiplierOrder (globalQPSH_of_sourcePSH hφ)
        (show (0 : ℝ) < (k + 1 : ℕ) by positivity) E : ℝ≥0∞) / (k + 1 : ℕ))
      atTop (𝓝 (sourcePSHReader φ hφ E)) := by
  refine Quot.inductionOn E ?_
  intro p
  exact tendsto_presentationMultiplierOrder_ratio (globalQPSH_of_sourcePSH hφ) p

theorem tendsto_multiplierOrder_ratio_of_qpsh {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (E : PrimeOver n X) :
    Tendsto (fun k : ℕ =>
      (multiplierOrder hφ (show (0 : ℝ) < (k + 1 : ℕ) by positivity) E : ℝ≥0∞) /
        (k + 1 : ℕ)) atTop (𝓝 (reader φ hφ.1 E)) := by
  refine Quot.inductionOn E ?_
  intro p
  exact tendsto_presentationMultiplierOrder_ratio hφ p

end SGPT.PSH.PrimeNov16PrimeOver
