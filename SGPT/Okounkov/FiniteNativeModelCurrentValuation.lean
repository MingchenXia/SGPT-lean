import SGPT.Okounkov.FiniteSmoothModelValuationChoice
import SGPT.Okounkov.SmoothModelBirationalChoice

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- The original signed model-current definition for an actual finite native
initial modification. Full native existence produces the adapted flag model
internally; whole-current choice and the original real correction are retained. -/
def finiteNativeModelCurrentFlagValuation {pi : Z → F.carrier}
    (hpi : IsBlowupSequence (m + 1) F.carrier Z pi)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) : Fin (m + 1) → ℝ :=
  letI : CompactSpace Z :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hpi).1
  let result := exists_flagLifting_dominating_finiteNativeModification F Z pi hpi
  let W := Classical.choose result
  let h := Classical.choose (Classical.choose_spec result)
  let hs := Classical.choose_spec (Classical.choose_spec result)
  smoothModelCurrentFlagChoice (W := W) (h := h)
    (isAnalyticModification_of_finiteBlowupSequence hpi) hs.1.contMDiff hs.2.2 T hc h11 hT

/-- Every actual finite adapted choice computes the literal internally defined
value. No supplied common model, square, upstairs current, or equality occurs. -/
theorem finiteNativeModelCurrentFlagValuation_eq_choice
    {W : OriginalFlagGeometry.{u} (m + 1)} {pi : Z → F.carrier}
    (hpi : IsBlowupSequence (m + 1) F.carrier Z pi)
    {h : W.carrier → Z} (hs : IsBlowupSequence (m + 1) Z W.carrier h)
    (hLift : IsFlagLifting F W (pi ∘ h))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    letI : CompactSpace Z :=
      (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hpi).1
    finiteNativeModelCurrentFlagValuation hpi T hc h11 hT =
      smoothModelCurrentFlagChoice (isAnalyticModification_of_finiteBlowupSequence hpi)
        hs.contMDiff hLift T hc h11 hT := by
  let : CompactSpace Z :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hpi).1
  let result := exists_flagLifting_dominating_finiteNativeModification F Z pi hpi
  let W0 := Classical.choose result
  let h0 := Classical.choose (Classical.choose_spec result)
  have hs0 := Classical.choose_spec (Classical.choose_spec result)
  exact smoothModelCurrentFlagChoice_eq_of_finiteModels
    (isAnalyticModification_of_finiteBlowupSequence hpi) hs0.1 hs hs0.2.2 hLift T hc h11 hT

/-- The definition outputs its actual model and whole-current readback,
retaining every original theta-potential representation and signed value. -/
theorem finiteNativeModelCurrentFlagValuation_spec {pi : Z → F.carrier}
    (hpi : IsBlowupSequence (m + 1) F.carrier Z pi)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (W : OriginalFlagGeometry.{u} (m + 1)) (h : W.carrier → Z)
      (_hs : IsBlowupSequence (m + 1) Z W.carrier h)
      (_hTotal : IsBlowupSequence (m + 1) F.carrier W.carrier (pi ∘ h))
      (hLift : IsFlagLifting F W (pi ∘ h))
      (hf : IsAnalyticModification (n := m + 1) h)
      (R : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m))),
      ∃ (hcR : R.IsClosed (canonicalBasis (m + 1)))
        (h11R : R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hR : IsFullPositive R),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          R = analyticModificationThetaCurrent hf θ v hv) ∧
        finiteNativeModelCurrentFlagValuation hpi T hc h11 hT =
          correctedModelCurrentFlagValuation hLift R hcR h11R hR := by
  let : CompactSpace Z :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hpi).1
  let result := exists_flagLifting_dominating_finiteNativeModification F Z pi hpi
  let W := Classical.choose result
  let h := Classical.choose (Classical.choose_spec result)
  have hs := Classical.choose_spec (Classical.choose_spec result)
  obtain ⟨hf, R, hcR, h11R, hR, hread, hvalue⟩ := smoothModelCurrentFlagChoice_spec
    (isAnalyticModification_of_finiteBlowupSequence hpi) hs.1.contMDiff hs.2.2 T hc h11 hT
  exact ⟨W, h, hs.1, hs.2.1, hs.2.2, hf, R, hcR, h11R, hR, hread, hvalue⟩

/-- A genuine finite further model produces its whole pullback current and
preserves the independently defined native function. The actual original flag
and same adapted model are produced internally on the literal composite. -/
theorem exists_finiteNativeModelCurrentFlagValuation_birational
    {Z' : Type u} [TopologicalSpace Z']
    [ChartedSpace (ComplexModel (m + 1)) Z'] [IsComplexManifold (m + 1) Z']
    {pi : Z → F.carrier} (hpi : IsBlowupSequence (m + 1) F.carrier Z pi)
    {p : Z' → Z} (hp : IsBlowupSequence (m + 1) Z Z' p)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (T' : GlobalCurrent (m + 1) Z' (degreeTwo (Nat.succ_pos m))),
      ∃ (hc' : T'.IsClosed (canonicalBasis (m + 1)))
        (h11' : T'.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hT' : IsFullPositive T'),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          T' = analyticModificationThetaCurrent
            (isAnalyticModification_of_finiteBlowupSequence hp) θ v hv) ∧
        finiteNativeModelCurrentFlagValuation (isBlowupSequence_comp_nativeFlag hpi hp)
          T' hc' h11' hT' = finiteNativeModelCurrentFlagValuation hpi T hc h11 hT := by
  let : CompactSpace Z :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hpi).1
  let hpiMod := isAnalyticModification_of_finiteBlowupSequence hpi
  let hpMod := isAnalyticModification_of_finiteBlowupSequence hp
  let : CompactSpace Z' :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpMod
  let hTotal := isBlowupSequence_comp_nativeFlag hpi hp
  obtain ⟨W, h, hs, _hsTotal, hLift⟩ :=
    exists_flagLifting_dominating_finiteNativeModification F Z' (pi ∘ p) hTotal
  obtain ⟨T', hc', h11', hT', hread, hvalue⟩ :=
    exists_smoothModelCurrentFlagChoice_birational hpiMod hpMod hs.contMDiff
      hLift T hc h11 hT
  refine ⟨T', hc', h11', hT', hread, ?_⟩
  have hUp := finiteNativeModelCurrentFlagValuation_eq_choice hTotal hs
    hLift T' hc' h11' hT'
  have hDown := finiteNativeModelCurrentFlagValuation_eq_choice hpi
    (isBlowupSequence_comp_nativeFlag hp hs) hLift T hc h11 hT
  exact hUp.trans (hvalue.trans hDown.symm)

end SGPT.Okounkov
