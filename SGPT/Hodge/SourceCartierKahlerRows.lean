import SGPT.Hodge.SourceCartierExactQEA
import SGPT.Hodge.SourceGCurrentSmoothShift
import SGPT.Hodge.SourceNefProjectiveEquiv

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
open scoped Topology

def reciprocalStep (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)

theorem reciprocalStep_pos (i : ℕ) : 0 < reciprocalStep i := by
  dsimp [reciprocalStep]
  positivity

theorem reciprocalStep_le_one (i : ℕ) : reciprocalStep i ≤ 1 := by
  dsimp [reciprocalStep]
  apply (div_le_one (by positivity)).mpr
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem reciprocalStep_antitone : Antitone reciprocalStep := by
  intro i j hij
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

theorem reciprocalStep_tendsto : Tendsto reciprocalStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual root trace, expressed in the original root class group. -/
def sourceRootClass (D : WeilFamilyAny (ModelSystem.blowup n X)) : RealBottChern n X :=
  D.val ModelSystem.Model.root

/-- Literal original current of the supplied genuine native presentation. -/
def representedCurrent (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) : ClosedPositive (n := n) (X := X) :=
  SourceDSDraft.sourcePotentialCurrentAny (nativeClosedFormToAtlas θ)
    ⟨u, (isThetaPSH_iff_nativeThetaPotential _ _).mpr hu⟩

omit [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem representedCurrent_isPresentation (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) : IsPresentationAny (representedCurrent θ u hu) θ u :=
  SourceDSDraft.sourcePotentialCurrentAny_isPresentation _ _

/-- Arbitrary original nef families INTERNALLY produce genuine Kähler
realizations of every reciprocal smooth shift. No realization, positive mass,
current presentation, Kähler margin or desired family certificate is supplied. -/
theorem exists_kahler_realization_rows (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D) :
    ∃ (θ : ℕ → ClosedRealOneOneForm n X) (u : ℕ → X → EReal)
      (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)),
      (∀ i, IsKahlerCurrentPotential (θ i) (u i)) ∧
      (∀ i, RealBottChern.ofRepresentative (θ i) =
        sourceRootClass D + reciprocalStep i • RealBottChern.ofRepresentative ω.form) ∧
      ∀ i, currentBDivisorAnyOn (ModelSystem.blowup n X)
        (representedCurrent (θ i) (u i) (hu i)) =
          D + reciprocalStep i • rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
  let κ : ℕ → KahlerBackground n X := fun i =>
    KahlerBackground.smul (half_pos (reciprocalStep_pos i)) ω
  let E : NefRoot (sourceRootClass D) := ⟨D,hD,rfl⟩
  let F (i : ℕ) := nefRootComponent ω (sourceRootClass D) E (sourceKahlerFormOfBackground (κ i))
  let T (i : ℕ) := (exists_gCurrent_realizing ω _ (F i)).choose
  have hfam (i : ℕ) : currentBDivisorAnyOn (ModelSystem.blowup n X) (T i).val =
      D + rootCartierAny (RealBottChern.ofRepresentative (κ i).form) :=
    (congrArg Subtype.val (exists_gCurrent_realizing ω _ (F i)).choose_spec).trans
      (congrArg (fun c => D + rootCartierAny c) (indexClass_ofBackground (κ i)))
  have hTclass (i : ℕ) : currentClassAny (T i).val =
      sourceRootClass D + RealBottChern.ofRepresentative (κ i).form :=
    (T i).property.1.trans (congrArg (fun c => sourceRootClass D+c) (indexClass_ofBackground (κ i)))
  let θ (i : ℕ) := atlasClosedFormToNative (currentPresentationBackground (T i).val) + (κ i).form
  let u (i : ℕ) := currentPresentationPotential (T i).val
  have hu (i : ℕ) : IsThetaPshPotential (θ i).val (u i) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive
      (currentPresentation_isPresentation (T i).val).choose (κ i).isSemipositive
  have hκclass (i : ℕ) : RealBottChern.ofRepresentative (κ i).form =
      (reciprocalStep i / 2) • RealBottChern.ofRepresentative ω.form :=
    RealBottChern.ofRepresentative_smul _ _
  have hκcartier (i : ℕ) : rootCartierAny (RealBottChern.ofRepresentative (κ i).form) =
      (reciprocalStep i / 2) • rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
    rw [hκclass, rootCartierAny_smul]
  refine ⟨θ, u, hu, ?_, ?_, ?_⟩
  · intro i
    refine ⟨κ i, ?_⟩
    change IsThetaPshPotential
      (atlasClosedFormToNative (currentPresentationBackground (T i).val) + (κ i).form - (κ i).form).val _
    rw [add_sub_cancel_right]
    exact (currentPresentation_isPresentation (T i).val).choose
  · intro i
    calc
      RealBottChern.ofRepresentative (θ i) =
          RealBottChern.ofRepresentative
            (atlasClosedFormToNative (currentPresentationBackground (T i).val)) +
              RealBottChern.ofRepresentative (κ i).form := RealBottChern.ofRepresentative_add _ _
      _ = currentClassAny (T i).val + RealBottChern.ofRepresentative (κ i).form :=
        congrArg (fun c => c + RealBottChern.ofRepresentative (κ i).form)
          (currentClassAny_eq_of_presentation _ _ _ (currentPresentation_isPresentation (T i).val)).symm
      _ = (sourceRootClass D + RealBottChern.ofRepresentative (κ i).form) +
          RealBottChern.ofRepresentative (κ i).form :=
        congrArg (fun c => c + RealBottChern.ofRepresentative (κ i).form) (hTclass i)
      _ = sourceRootClass D +
          reciprocalStep i • RealBottChern.ofRepresentative ω.form := by rw [hκclass]; module
  · intro i
    change currentBDivisorAnyOn (ModelSystem.blowup n X)
      (semipositiveShiftCurrent (T i).val (κ i).form (κ i).isSemipositive) = _
    calc
      _ = currentBDivisorAnyOn (ModelSystem.blowup n X) (T i).val +
          rootCartierAny (RealBottChern.ofRepresentative (κ i).form) :=
        semipositiveShiftCurrent_bdivisor _ _ _
      _ = (D + rootCartierAny (RealBottChern.ofRepresentative (κ i).form)) +
          rootCartierAny (RealBottChern.ofRepresentative (κ i).form) :=
        congrArg (fun E => E + rootCartierAny (RealBottChern.ofRepresentative (κ i).form)) (hfam i)
      _ = D + reciprocalStep i • rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
        rw [hκcartier]
        module

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
