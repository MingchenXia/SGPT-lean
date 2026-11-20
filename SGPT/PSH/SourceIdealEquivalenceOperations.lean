import SGPT.Envelopes.SourceIEnvelopeAlgebra
import SGPT.PSH.SourceGlobalOrderAddition
import SGPT.PSH.SourceGlobalOrderSupremum
import SGPT.PSH.AtlasQPSHScaling

/-! Full-source ideal-equivalence operations for original `prop:Iequivmax`.

The maximum inputs are arbitrary genuine QPSH potentials. Their common
background is produced internally. The family clause retains an arbitrary
nonempty index type and both original uniform real upper bounds.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem idealOperations_native_of_source {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

/-- Arbitrary positive real scaling preserves the genuine all-level source
ideal equivalence, with both scaled QPSH domains manufactured. -/
theorem sourceIEquivalent_pos_smul {u v : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (huv : sourceIEquivalent (ofFixedModel n M) u v) {c : ℝ} (hc : 0 < c) :
    sourceIEquivalent (ofFixedModel n M)
      (fun x => (c : EReal) * u x) (fun x => (c : EReal) * v x) := by
  have hI := (sourceIEquivalent_iff_native hu hv).mp huv
  apply (sourceIEquivalent_iff_native (hu.pos_smul hc) (hv.pos_smul hc)).mpr
  exact ⟨ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hI.1 hc,
    ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hI.2 hc⟩

section GlobalFinite

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

private theorem idealOperations_common_four_background (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b) :
    ∃ θ : AtlasClosedRealOneOneForm (ofFixedModel n M),
      (ofFixedModel n M).IsThetaPSH θ u ∧ (ofFixedModel n M).IsThetaPSH θ v ∧
      (ofFixedModel n M).IsThetaPSH θ a ∧ (ofFixedModel n M).IsThetaPSH θ b := by
  obtain ⟨C, hC, huC, haC, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      (idealOperations_native_of_source hu) (idealOperations_native_of_source ha)
  obtain ⟨D, hD, hvD, hbD, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      (idealOperations_native_of_source hv) (idealOperations_native_of_source hb)
  let Θ : ClosedRealOneOneForm n M := (C + D) • omega.form
  have hformC : C • omega.form + D • omega.form = Θ := by
    dsimp [Θ]
    module
  have hformD : D • omega.form + C • omega.form = Θ := by
    dsimp [Θ]
    module
  have liftC {q : M → EReal} (hq : IsThetaPshPotential (C • omega.form).val q) :
      IsThetaPshPotential Θ.val q := by
    simpa only [hformC] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hq
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hD.le)
  have liftD {q : M → EReal} (hq : IsThetaPshPotential (D • omega.form).val q) :
      IsThetaPshPotential Θ.val q := by
    simpa only [hformD] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hq
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hC.le)
  have source {q : M → EReal} (hq : IsThetaPshPotential Θ.val q) :
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas Θ) q := by
    apply (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas Θ) q).mpr
    simpa only [sourceNativeAtlasForm_roundTrip] using hq
  exact ⟨nativeClosedFormToAtlas Θ, source (liftC huC), source (liftD hvD),
    source (liftC haC), source (liftD hbD)⟩

/-- The maximum clause on the ENTIRE genuine source QPSH domain, without a
supplied common background for the four independent inputs. -/
theorem sourceIEquivalent_max_globalQPSH (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b)
    (hua : sourceIEquivalent (ofFixedModel n M) u a)
    (hvb : sourceIEquivalent (ofFixedModel n M) v b) :
    sourceIEquivalent (ofFixedModel n M)
      (fun x => max (u x) (v x)) (fun x => max (a x) (b x)) := by
  obtain ⟨θ, huθ, hvθ, haθ, hbθ⟩ :=
    idealOperations_common_four_background omega hu hv ha hb
  exact sourceIEquivalent_max huθ hvθ haθ hbθ hua hvb

/-- The first THREE printed clauses of original `prop:Iequivmax`, for
arbitrary QPSH inputs, literal extended addition, and positive real scaling. -/
theorem sourceIEquivalent_finite_operations (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b)
    (hua : sourceIEquivalent (ofFixedModel n M) u a)
    (hvb : sourceIEquivalent (ofFixedModel n M) v b) {c : ℝ} (hc : 0 < c) :
    sourceIEquivalent (ofFixedModel n M)
        (fun x => max (u x) (v x)) (fun x => max (a x) (b x)) ∧
      sourceIEquivalent (ofFixedModel n M)
        (fun x => u x + v x) (fun x => a x + b x) ∧
      sourceIEquivalent (ofFixedModel n M)
        (fun x => (c : EReal) * u x) (fun x => (c : EReal) * a x) := by
  refine ⟨sourceIEquivalent_max_globalQPSH omega hu hv ha hb hua hvb, ?_,
    sourceIEquivalent_pos_smul hu ha hua hc⟩
  exact ⟨GlobalOrderAddition.sourceIOrder_add omega hu hv ha hb hua.1 hvb.1,
    GlobalOrderAddition.sourceIOrder_add omega ha hb hu hv hua.2 hvb.2⟩

end GlobalFinite

section ArbitrarySupremum

variable [CompactSpace M] [Nonempty M]

/-- The FOURTH printed clause of original `prop:Iequivmax`: arbitrary
nonempty uniformly bounded same-background families, with both genuine
supremum domains produced by the all-level order theorem. -/
theorem sourceIEquivalent_uscSup {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : I → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i))
    (huBound : ∃ C : ℝ, ∀ i x, u i x ≤ (C : EReal))
    (hvBound : ∃ D : ℝ, ∀ i x, v i x ≤ (D : EReal))
    (huv : ∀ i, sourceIEquivalent (ofFixedModel n M) (u i) (v i)) :
    sourceIEquivalent (ofFixedModel n M) (uscSup u) (uscSup v) := by
  exact ⟨sourceIOrder_uscSup hu hv huBound hvBound (fun i => (huv i).1),
    sourceIOrder_uscSup hv hu hvBound huBound (fun i => (huv i).2)⟩

end ArbitrarySupremum
end SGPT.PSH.VariableComplexAtlas
