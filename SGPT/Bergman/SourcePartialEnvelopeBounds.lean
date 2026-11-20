import SGPT.Bergman.SourcePartialEnvelopeConcavity

/-! # Original partial-envelope singularity types and uniform upper bounds

Faithful integration candidate: only the independently reviewed same8 and
uniform7 tails. The existing canonical partial-envelope and foundation modules
are imported. No old29/foundation5/concavity-consumer10 body is copied here.
This work file has not been compiled; ROOT owns canonical validation/adoption.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace SGPT.Bergman.PartialEnvelopeSameType

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeConcavity
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology Classical

universe u

private theorem uscSup_add_const {I : Type*} {X : Type*} [TopologicalSpace X]
    (v : I → X → EReal) (c : ℝ) :
    uscSup (fun i x => v i x + (c : EReal)) = fun x => uscSup v x + (c : EReal) := by
  have heq : (fun x => ⨆ i, v i x + (c : EReal)) =
      fun x => (⨆ i, v i x) + (c : EReal) := by
    funext x
    exact iSup_add_coe (fun i => v i x) c
  change uscRegularization (fun x => ⨆ i, v i x + (c : EReal)) = _
  rw [heq, uscRegularization_add_coe_const]
  rfl

private theorem ereal_move_finite {a b : EReal} (c : ℝ)
    (h : a + ((-c : ℝ) : EReal) ≤ b) : a ≤ b + (c : EReal) := by
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c))).mp
  simpa only [sub_eq_add_neg, EReal.coe_neg] using h

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Original positive reference and finite obstacle lower bound manufacture an
ACTUAL member of the literal positive ordinary partial subtype. -/
theorem positivePartialCompetitors_nonempty
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x) :
    Nonempty (positivePartialCompetitors θ φ K f) := by
  obtain ⟨A, hA⟩ := ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).exists_global_upper_bound
  obtain ⟨B, hB⟩ := hf
  let c : ℝ := B - A
  let χ : M → EReal := fun x => φ x + (c : EReal)
  have hχ := sourceThetaPSH_add_const hφ c
  have hχB (x : M) : χ x ≤ (B : EReal) := by
    calc
      χ x ≤ (A : EReal) + (c : EReal) := add_le_add (hA x) le_rfl
      _ = (B : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        dsimp only [c]
        ring
  have hχφ : SGPT.PSH.SingularityLE χ φ := ⟨c, fun _ _ => le_rfl⟩
  have hχpos : 0 < sourcePotentialNonPluripolarMeasure θ χ hχ univ :=
    hφpos.trans_eq (sourceAffine_mass_add_const hφ c).symm
  exact ⟨⟨⟨χ, hχ, partialObstacle_of_forall (fun x => (hχB x.val).trans (hB x)), hχφ⟩, hχpos⟩⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual nonPP/upper-obstacle data rule out the true top branch and supply
both a WHOLE-family bound and genuinely theta-PSH regularized supremum. -/
theorem boundedFamily_of_partialObstacle {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, f x ≤ (B : EReal))
    {v : I → M → EReal} (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i))
    (hvK : ∀ i, partialObstacle (n := n) K f (v i)) :
    ∃ C : ℝ, (∀ i x, v i x ≤ (C : EReal)) ∧
      (uscSup v ≤ fun _ => (C : EReal)) ∧ (ofFixedModel n M).IsThetaPSH θ (uscSup v) := by
  rcases uscSup_top_or_genuine hv with htop | hgood
  · exfalso
    obtain ⟨B, hB⟩ := hf
    have hret := partialObstacle_uscSup hK ⟨B, hB⟩ hv hvK
    obtain ⟨S, hS, hbound⟩ := (partialObstacle_iff_exists_pluripolar K f (uscSup v)).mp hret
    apply hK
    apply hS.mono
    intro x hxK
    by_contra hxS
    have htopB : (⊤ : EReal) ≤ (B : EReal) := by
      simpa only [htop] using (hbound ⟨x, hxK⟩ hxS).trans (hB ⟨x, hxK⟩)
    exact (not_le_of_gt (EReal.coe_lt_top B)) htopB
  · exact hgood

/-- BOTH literal full partial outputs become genuine and finitely upper bounded
from the original reference and lower/upper obstacle bounds, internally. -/
theorem partialEnvelopes_genuine_bounded
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    {f : K → EReal} (hlo : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x)
    (hup : ∃ B : ℝ, ∀ x : K, f x ≤ (B : EReal)) :
    ∃ C D : ℝ, (ofFixedModel n M).IsThetaPSH θ (partialEnvelope θ φ K f) ∧
      (ofFixedModel n M).IsThetaPSH θ (partialIEnvelope θ φ K f) ∧
        (partialEnvelope θ φ K f ≤ fun _ => (C : EReal)) ∧
        (partialIEnvelope θ φ K f ≤ fun _ => (D : EReal)) := by
  obtain ⟨w⟩ := positivePartialCompetitors_nonempty hφ hφpos hlo
  let : Nonempty (partialCompetitors θ φ K f) := ⟨w.val⟩
  let : Nonempty (partialICompetitors θ φ K f) := ⟨⟨w.val.val, w.val.property.1,
    w.val.property.2.1, sourceIOrder_of_singularityLE w.val.property.1 hφ w.val.property.2.2⟩⟩
  obtain ⟨C, _hCfamily, hC, hgP⟩ := boundedFamily_of_partialObstacle
    (v := fun v : partialCompetitors θ φ K f => v.val) hK hup
      (fun v => v.property.1) (fun v => v.property.2.1)
  obtain ⟨D, _hDfamily, hD, hgI⟩ := boundedFamily_of_partialObstacle
    (v := fun v : partialICompetitors θ φ K f => v.val) hK hup
      (fun v => v.property.1) (fun v => v.property.2.1)
  exact ⟨C, D, hgP, hgI, hC, hD⟩

/-- WHOLE ordinary part of lma:same_sing_type: original finite-additive type,
with no desired output bound or envelope membership supplied. -/
theorem partialEnvelope_same_singularity_type (_ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    (f : K → ℝ) (hf : ∃ R : ℝ, ∀ x : K, |f x| ≤ R) :
    SGPT.PSH.SingularityEquiv
      (partialEnvelope θ φ K (fun x => (f x : EReal))) (sourceSingularityEnvelope θ φ) := by
  obtain ⟨R, hR⟩ := hf
  let g : K → EReal := fun x => (f x : EReal)
  have hlo : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ g x :=
    ⟨-R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).1⟩
  have hup : ∃ B : ℝ, ∀ x : K, g x ≤ (B : EReal) :=
    ⟨R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).2⟩
  obtain ⟨C, _D, _hgP, _hgI, hC, _hD⟩ := partialEnvelopes_genuine_bounded hφ hφpos hK hlo hup
  let H := partialEnvelope θ φ K g
  have hlow : (fun x => sourceSingularityEnvelope θ φ x + ((-R : ℝ) : EReal)) ≤ H := by
    have hl : uscSup (fun v : sourceSingularityCompetitors θ φ => fun x => v.val x + ((-R : ℝ) : EReal)) ≤ H := by
      apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K g)
      intro x
      apply iSup_le
      intro v
      have hv := sourceThetaPSH_add_const v.property.1 (-R)
      have hvK : ∀ y : K, v.val y.val + ((-R : ℝ) : EReal) ≤ g y := by
        intro y
        have hl : v.val y.val + ((-R : ℝ) : EReal) ≤ ((-R : ℝ) : EReal) := by
          simpa only [Pi.zero_apply, zero_add] using add_le_add (v.property.2.1 y.val) (le_refl ((-R : ℝ) : EReal))
        exact hl.trans (EReal.coe_le_coe_iff.mpr (abs_le.mp (hR y)).1)
      have hvφ : SGPT.PSH.SingularityLE (fun y => v.val y + ((-R : ℝ) : EReal)) φ :=
        (show SGPT.PSH.SingularityLE (fun y => v.val y + ((-R : ℝ) : EReal)) v.val from
          ⟨-R, fun _ _ => le_rfl⟩).trans v.property.2.2
      exact le_partialEnvelope hv (partialObstacle_of_forall hvK) hvφ x
    rw [uscSup_add_const] at hl
    exact hl
  have hupper : H ≤ fun x => sourceSingularityEnvelope θ φ x + (C : EReal) := by
    apply uscRegularization_le
      (upperSemicontinuous_add_coe_const (upperSemicontinuous_sourceSingularityEnvelope θ φ) C)
    intro x
    apply iSup_le
    intro v
    have hv := sourceThetaPSH_add_const v.property.1 (-C)
    have hvbound : v.val ≤ fun _ => (C : EReal) :=
      (le_partialEnvelope v.property.1 v.property.2.1 v.property.2.2).trans hC
    have hv0 : (fun y => v.val y + ((-C : ℝ) : EReal)) ≤ 0 := by
      intro y
      simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero, Pi.zero_apply] using
        add_le_add (hvbound y) (le_refl ((-C : ℝ) : EReal))
    have hvφ : SGPT.PSH.SingularityLE (fun y => v.val y + ((-C : ℝ) : EReal)) φ :=
      (show SGPT.PSH.SingularityLE (fun y => v.val y + ((-C : ℝ) : EReal)) v.val from
        ⟨-C, fun _ _ => le_rfl⟩).trans v.property.2.2
    exact ereal_move_finite C (le_sourceSingularityEnvelope hv hv0 hvφ x)
  exact ⟨⟨C, fun x _ => hupper x⟩, ⟨R, fun x _ => ereal_move_finite R (hlow x)⟩⟩

/-- WHOLE ideal part of lma:same_sing_type in the original additive type,
using the true ALL normalized I-ORDER characterization, not assumed equivalence. -/
theorem partialIEnvelope_same_singularity_type (_ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    (f : K → ℝ) (hf : ∃ R : ℝ, ∀ x : K, |f x| ≤ R) :
    SGPT.PSH.SingularityEquiv
      (partialIEnvelope θ φ K (fun x => (f x : EReal))) (sourceIEnvelope θ φ) := by
  obtain ⟨R, hR⟩ := hf
  let g : K → EReal := fun x => (f x : EReal)
  have hlo : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ g x :=
    ⟨-R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).1⟩
  have hup : ∃ B : ℝ, ∀ x : K, g x ≤ (B : EReal) :=
    ⟨R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).2⟩
  obtain ⟨_C, D, _hgP, _hgI, _hC, hD⟩ := partialEnvelopes_genuine_bounded hφ hφpos hK hlo hup
  let H := partialIEnvelope θ φ K g
  have hlow : (fun x => sourceIEnvelope θ φ x + ((-R : ℝ) : EReal)) ≤ H := by
    have hl : uscSup (fun v : sourceICompetitors θ φ => fun x => v.val x + ((-R : ℝ) : EReal)) ≤ H := by
      apply uscRegularization_le (upperSemicontinuous_partialIEnvelope θ φ K g)
      intro x
      apply iSup_le
      intro v
      have hv := sourceThetaPSH_add_const v.property.1 (-R)
      have hvK : ∀ y : K, v.val y.val + ((-R : ℝ) : EReal) ≤ g y := by
        intro y
        have hl : v.val y.val + ((-R : ℝ) : EReal) ≤ ((-R : ℝ) : EReal) := by
          simpa only [Pi.zero_apply, zero_add] using add_le_add (v.property.2.1 y.val) (le_refl ((-R : ℝ) : EReal))
        exact hl.trans (EReal.coe_le_coe_iff.mpr (abs_le.mp (hR y)).1)
      have hvI : sourceIOrder (ofFixedModel n M) (fun y => v.val y + ((-R : ℝ) : EReal)) φ :=
        sourceIOrder_trans (sourceIOrder_of_singularityLE hv v.property.1
          ⟨-R, fun _ _ => le_rfl⟩) v.property.2.2.1
      exact le_partialIEnvelope hv (partialObstacle_of_forall hvK) hvI x
    rw [uscSup_add_const] at hl
    exact hl
  have hupper : H ≤ fun x => sourceIEnvelope θ φ x + (D : EReal) := by
    apply uscRegularization_le
      (upperSemicontinuous_add_coe_const (upperSemicontinuous_sourceIEnvelope θ φ) D)
    intro x
    apply iSup_le
    intro v
    have hv := sourceThetaPSH_add_const v.property.1 (-D)
    have hvbound : v.val ≤ fun _ => (D : EReal) :=
      (le_partialIEnvelope v.property.1 v.property.2.1 v.property.2.2).trans hD
    have hv0 : (fun y => v.val y + ((-D : ℝ) : EReal)) ≤ 0 := by
      intro y
      simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero, Pi.zero_apply] using
        add_le_add (hvbound y) (le_refl ((-D : ℝ) : EReal))
    have hvI : sourceIOrder (ofFixedModel n M) (fun y => v.val y + ((-D : ℝ) : EReal)) φ :=
      sourceIOrder_trans (sourceIOrder_of_singularityLE hv v.property.1
        ⟨-D, fun _ _ => le_rfl⟩) v.property.2.2
    have hvE : (fun y => v.val y + ((-D : ℝ) : EReal)) ≤ sourceIEnvelope θ φ := by
      rw [sourceIEnvelope_eq_sSup_sourceIOrder hφ]
      exact le_sSup ⟨hv, hv0, hvI⟩
    exact ereal_move_finite D (hvE x)
  exact ⟨⟨D, fun x _ => hupper x⟩, ⟨R, fun x _ => ereal_move_finite R (hlow x)⟩⟩

/-- WHOLE original lma:same_sing_type and eq:PthetaKvarphiv_singtype,
BOTH distinct partial/normalized operators with exact bounded real weight. -/
theorem partialEnvelopes_same_singularity_type (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    (f : K → ℝ) (hf : ∃ R : ℝ, ∀ x : K, |f x| ≤ R) :
    SGPT.PSH.SingularityEquiv
      (partialEnvelope θ φ K (fun x => (f x : EReal))) (sourceSingularityEnvelope θ φ) ∧
    SGPT.PSH.SingularityEquiv
      (partialIEnvelope θ φ K (fun x => (f x : EReal))) (sourceIEnvelope θ φ) :=
  ⟨partialEnvelope_same_singularity_type ω hφ hφpos hK f hf,
    partialIEnvelope_same_singularity_type ω hφ hφpos hK f hf⟩

end SGPT.Bergman.PartialEnvelopeSameType

namespace SGPT.Bergman.PartialEnvelopeUniformBound

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeSameType
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Classical

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The ENTIRE original QE upper-obstacle class for fixed theta/K/B.
No phi, general weight, singularity order or positive-mass restriction. -/
def universalObstacleCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (K : Set M) (B : ℝ) :=
  {η : M → EReal // (ofFixedModel n M).IsThetaPSH θ η ∧
    partialObstacle (n := n) K (fun _ => (B : EReal)) η}

variable [CompactSpace M] [ConnectedSpace M]

/-- Actual uniform class construction produces C BEFORE every original reference
and weight; empty indices are a genuine separate branch, not a certificate. -/
theorem exists_uniform_potential_bound
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : universalObstacleCompetitors θ K B,
      ∀ x : M, η.val x ≤ (C : EReal) := by
  by_cases hi : Nonempty (universalObstacleCompetitors θ K B)
  · let := hi
    obtain ⟨C₀, hC₀, _hOut, _hg⟩ := boundedFamily_of_partialObstacle
      (v := fun η : universalObstacleCompetitors θ K B => η.val)
      hK ⟨B, fun _ => le_rfl⟩ (fun η => η.property.1) (fun η => η.property.2)
    refine ⟨|C₀| + 1, by linarith [abs_nonneg C₀], ?_⟩
    have hC : C₀ ≤ |C₀| + 1 := by linarith [le_abs_self C₀]
    exact fun η x => (hC₀ η x).trans (EReal.coe_le_coe_iff.mpr hC)
  · exact ⟨1, zero_lt_one, fun η => False.elim (hi ⟨η⟩)⟩

/-- The actual fixed constant has ONLY theta/K/B/geometry arguments. In
particular no reference phi or entire obstacle f occurs in this definition. -/
noncomputable def uniformUpperBound
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) (B : ℝ) : ℝ :=
  Classical.choose (exists_uniform_potential_bound θ hK B)

theorem uniformUpperBound_pos
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) (B : ℝ) :
    0 < uniformUpperBound θ hK B :=
  (Classical.choose_spec (exists_uniform_potential_bound θ hK B)).1

theorem le_uniformUpperBound
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) (B : ℝ)
    {η : M → EReal} (hη : (ofFixedModel n M).IsThetaPSH θ η)
    (hηK : partialObstacle (n := n) K (fun _ => (B : EReal)) η) :
    η ≤ fun _ => (uniformUpperBound θ hK B : EReal) :=
  (Classical.choose_spec (exists_uniform_potential_bound θ hK B)).2 ⟨η, hη, hηK⟩

/-- SAME fixed C(theta,K,B) bounds BOTH original full partial operators for
EVERY reference and EVERY extended-real weight at most B. No output certificate. -/
theorem partialEnvelopes_le_uniformUpperBound
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) (B : ℝ)
    (φ : M → EReal) (f : K → EReal) (hf : ∀ x : K, f x ≤ (B : EReal)) :
    (partialEnvelope θ φ K f ≤ fun _ => (uniformUpperBound θ hK B : EReal)) ∧
      (partialIEnvelope θ φ K f ≤ fun _ => (uniformUpperBound θ hK B : EReal)) := by
  constructor
  · apply uscRegularization_le upperSemicontinuous_const
    intro x
    apply iSup_le
    intro v
    exact le_uniformUpperBound θ hK B v.property.1
      (partialObstacle_mono v.property.2.1 hf) x
  · apply uscRegularization_le upperSemicontinuous_const
    intro x
    apply iSup_le
    intro v
    exact le_uniformUpperBound θ hK B v.property.1
      (partialObstacle_mono v.property.2.1 hf) x

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- WHOLE original cor:Ppartbdd_bdabove, including the exact C(sup_K f,K,X)
uniformity at fixed theta: SAME positive C for ALL positive references. -/
theorem partialEnvelopes_uniform_bound_at_sup (_ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    (f : K → ℝ) (hf : ∃ R : ℝ, ∀ x : K, |f x| ≤ R) :
    0 < uniformUpperBound θ hK (sSup (range f)) ∧
      ∀ φ : M → EReal, ∀ hφ : (ofFixedModel n M).IsThetaPSH θ φ,
        0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ →
          (partialEnvelope θ φ K (fun x => (f x : EReal)) ≤
            fun _ => (uniformUpperBound θ hK (sSup (range f)) : EReal)) ∧
          (partialIEnvelope θ φ K (fun x => (f x : EReal)) ≤
            fun _ => (uniformUpperBound θ hK (sSup (range f)) : EReal)) := by
  obtain ⟨R, hR⟩ := hf
  have hb : BddAbove (range f) := ⟨R, by
    rintro y ⟨x, rfl⟩
    exact (abs_le.mp (hR x)).2⟩
  refine ⟨uniformUpperBound_pos θ hK _, ?_⟩
  intro φ _hφ _hφpos
  exact partialEnvelopes_le_uniformUpperBound θ hK (sSup (range f)) φ (fun x => (f x : EReal))
    (fun x => EReal.coe_le_coe_iff.mpr (le_csSup hb (mem_range_self x)))

end SGPT.Bergman.PartialEnvelopeUniformBound
