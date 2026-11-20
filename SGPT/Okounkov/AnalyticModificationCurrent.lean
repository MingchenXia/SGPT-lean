import SGPT.Okounkov.ThetaCurrentPullbackFunctorial
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
open NaturalThetaPshClosedCurrent

variable {m : ℕ} {X Y U : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]
  [TopologicalSpace U] [ChartedSpace (ComplexModel (m + 1)) U]
  [IsComplexManifold (m + 1) U]

/-- The literal full theta current on any genuine smooth modification;
no source flag on the input-current model is required. -/
def analyticModificationThetaCurrent {f : Y → X}
    (hf : IsAnalyticModification (n := m + 1) f)
    (θ : ClosedRealOneOneForm (m + 1) X) (v : X → EReal)
    (hv : IsThetaPshPotential θ.val v) :
    GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m)) :=
  thetaPotentialCurrent (ClosedRealOneOneForm.pullback hf.1 θ).val (v ∘ f)
    (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hf θ hv)

/-- Actual strong pullback and the existing theta-current producer provide
all supported closedness, type and full positivity data. -/
theorem analyticModificationThetaCurrent_closed_type_positive {f : Y → X}
    (hf : IsAnalyticModification (n := m + 1) f)
    (θ : ClosedRealOneOneForm (m + 1) X) (v : X → EReal)
    (hv : IsThetaPshPotential θ.val v) :
    (analyticModificationThetaCurrent hf θ v hv).IsClosed (canonicalBasis (m + 1)) ∧
    (analyticModificationThetaCurrent hf θ v hv).IsTypeOneOne
      (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    IsFullPositive (analyticModificationThetaCurrent hf θ v hv) :=
  thetaPotentialCurrent_closed_type_positive _ _ _

/-- Thin consumption of genuine whole-current representation independence,
including the exceptional support. -/
theorem analyticModificationThetaCurrent_eq_of_eq {f : Y → X}
    (hf : IsAnalyticModification (n := m + 1) f)
    {θ σ : ClosedRealOneOneForm (m + 1) X} {v w : X → EReal}
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential σ.val w)
    (heq : thetaPotentialCurrent θ.val v hv = thetaPotentialCurrent σ.val w hw) :
    analyticModificationThetaCurrent hf θ v hv =
      analyticModificationThetaCurrent hf σ w hw :=
  thetaPotentialCurrent_modification_pullback_eq_of_eq hf hv hw heq

/-- The original geometric form composition law supplies literal whole-current
composition on arbitrary genuine smooth models. -/
theorem analyticModificationThetaCurrent_comp {f : Y → X} {g : U → Y}
    (hf : IsAnalyticModification (n := m + 1) f)
    (hg : IsAnalyticModification (n := m + 1) g)
    (θ : ClosedRealOneOneForm (m + 1) X) (v : X → EReal)
    (hv : IsThetaPshPotential θ.val v) :
    analyticModificationThetaCurrent
      (AnalyticModificationComposition.isAnalyticModification_comp hf hg) θ v hv =
      analyticModificationThetaCurrent hg (ClosedRealOneOneForm.pullback hf.1 θ) (v ∘ f)
        (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
          hf θ hv) := by
  apply thetaPotentialCurrent_eq_of_geometricallyEq
  exact SmoothRealForm.pullback_comp_geometricallyEq hf.1 hg.1 θ.val

/-- An arbitrary original current on a compact smooth model internally supplies
its global representation and unique full pullback, without a source flag. -/
theorem exists_unique_compact_current_analyticModification_pullback [CompactSpace X]
    {f : Y → X} (hf : IsAnalyticModification (n := m + 1) f)
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃! R : GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m)),
      R.IsClosed (canonicalBasis (m + 1)) ∧
      R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive R ∧
      ∀ (θ : ClosedRealOneOneForm (m + 1) X) (v : X → EReal)
        (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
        R = analyticModificationThetaCurrent hf θ v hv := by
  obtain ⟨θ, v, hv, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hc h11 hT
  let R := analyticModificationThetaCurrent hf θ v hv
  have hp := analyticModificationThetaCurrent_closed_type_positive hf θ v hv
  refine ⟨R, ⟨hp.1, hp.2.1, hp.2.2, ?_⟩, ?_⟩
  · intro σ w hw hreadw
    exact analyticModificationThetaCurrent_eq_of_eq hf hv hw (hread.symm.trans hreadw)
  · intro S hS
    exact hS.2.2.2 θ v hv hread

/-- Genuine common-modification geometry produces one SAME entire upstairs
current from both routes and EVERY intermediate representation. -/
theorem exists_compact_current_commonModification_pullbacks
    {Y₀ Y₁ : Type u}
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel (m + 1)) Y₀]
    [IsComplexManifold (m + 1) Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (m + 1)) Y₁]
    [IsComplexManifold (m + 1) Y₁] [CompactSpace X]
    {f₀ : Y₀ → X} {f₁ : Y₁ → X} {g₀ : U → Y₀} {g₁ : U → Y₁}
    (hf₀ : IsAnalyticModification (n := m + 1) f₀)
    (hf₁ : IsAnalyticModification (n := m + 1) f₁)
    (hg₀ : IsAnalyticModification (n := m + 1) g₀)
    (hg₁ : IsAnalyticModification (n := m + 1) g₁)
    (hcomm : f₀ ∘ g₀ = f₁ ∘ g₁)
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (R₀ : GlobalCurrent (m + 1) Y₀ (degreeTwo (Nat.succ_pos m)))
      (R₁ : GlobalCurrent (m + 1) Y₁ (degreeTwo (Nat.succ_pos m)))
      (Q : GlobalCurrent (m + 1) U (degreeTwo (Nat.succ_pos m))),
      (R₀.IsClosed (canonicalBasis (m + 1)) ∧
        R₀.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive R₀) ∧
      (R₁.IsClosed (canonicalBasis (m + 1)) ∧
        R₁.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive R₁) ∧
      (Q.IsClosed (canonicalBasis (m + 1)) ∧
        Q.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive Q) ∧
      (∀ (θ : ClosedRealOneOneForm (m + 1) X) (v : X → EReal)
        (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
        R₀ = analyticModificationThetaCurrent hf₀ θ v hv ∧
        R₁ = analyticModificationThetaCurrent hf₁ θ v hv ∧
        Q = analyticModificationThetaCurrent
          (AnalyticModificationComposition.isAnalyticModification_comp hf₀ hg₀) θ v hv) ∧
      (∀ (σ : ClosedRealOneOneForm (m + 1) Y₀) (w : Y₀ → EReal)
        (hw : IsThetaPshPotential σ.val w), R₀ = thetaPotentialCurrent σ.val w hw →
        Q = analyticModificationThetaCurrent hg₀ σ w hw) ∧
      ∀ (σ : ClosedRealOneOneForm (m + 1) Y₁) (w : Y₁ → EReal)
        (hw : IsThetaPshPotential σ.val w), R₁ = thetaPotentialCurrent σ.val w hw →
        Q = analyticModificationThetaCurrent hg₁ σ w hw := by
  obtain ⟨R₀, hR₀, _huniq₀⟩ :=
    exists_unique_compact_current_analyticModification_pullback hf₀ T hc h11 hT
  obtain ⟨R₁, hR₁, _huniq₁⟩ :=
    exists_unique_compact_current_analyticModification_pullback hf₁ T hc h11 hT
  let hq₀ := AnalyticModificationComposition.isAnalyticModification_comp hf₀ hg₀
  obtain ⟨Q, hQ, _huniqQ⟩ :=
    exists_unique_compact_current_analyticModification_pullback hq₀ T hc h11 hT
  refine ⟨R₀, R₁, Q, ⟨hR₀.1, hR₀.2.1, hR₀.2.2.1⟩,
    ⟨hR₁.1, hR₁.2.1, hR₁.2.2.1⟩, ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩, ?_, ?_, ?_⟩
  · intro θ v hv hread
    exact ⟨hR₀.2.2.2 θ v hv hread, hR₁.2.2.2 θ v hv hread,
      hQ.2.2.2 θ v hv hread⟩
  · intro σ w hw hread₀
    obtain ⟨θ, v, hv, hread, _hchart⟩ :=
      OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
        T hc h11 hT
    let hv₀ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hf₀ θ hv
    have hrep : thetaPotentialCurrent (ClosedRealOneOneForm.pullback hf₀.1 θ).val
        (v ∘ f₀) hv₀ = thetaPotentialCurrent σ.val w hw :=
      (hR₀.2.2.2 θ v hv hread).symm.trans hread₀
    exact (hQ.2.2.2 θ v hv hread).trans
      ((analyticModificationThetaCurrent_comp hf₀ hg₀ θ v hv).trans
        (analyticModificationThetaCurrent_eq_of_eq hg₀ hv₀ hw hrep))
  · intro σ w hw hread₁
    obtain ⟨θ, v, hv, hread, _hchart⟩ :=
      OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
        T hc h11 hT
    let hv₁ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hf₁ θ hv
    have hrep : thetaPotentialCurrent (ClosedRealOneOneForm.pullback hf₁.1 θ).val
        (v ∘ f₁) hv₁ = thetaPotentialCurrent σ.val w hw :=
      (hR₁.2.2.2 θ v hv hread).symm.trans hread₁
    have hq₁ := AnalyticModificationComposition.isAnalyticModification_comp hf₁ hg₁
    have hreadQ : Q = analyticModificationThetaCurrent hq₁ θ v hv := by
      have he : (⟨f₀ ∘ g₀, hq₀⟩ :
          {q : U → X // IsAnalyticModification (n := m + 1) q}) =
          ⟨f₁ ∘ g₁, hq₁⟩ := Subtype.ext hcomm
      have hcurr := congrArg (fun q :
          {q : U → X // IsAnalyticModification (n := m + 1) q} =>
          analyticModificationThetaCurrent q.property θ v hv) he
      exact (hQ.2.2.2 θ v hv hread).trans hcurr
    exact hreadQ.trans ((analyticModificationThetaCurrent_comp hf₁ hg₁ θ v hv).trans
      (analyticModificationThetaCurrent_eq_of_eq hg₁ hv₁ hw hrep))

end SGPT.Okounkov
