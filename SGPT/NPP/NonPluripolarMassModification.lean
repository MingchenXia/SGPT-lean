import SGPT.PSH.SourceBimeromorphicMixedIVolume
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-!
# Invariance of non-pluripolar masses under modifications

Source `prop:nppmassinv` (chapter `chapter_npp.tex`): for a proper bimeromorphic
morphism `π : Y → X` from a Kähler manifold `Y` and closed positive
`(1,1)`-currents `T_1, …, T_n` on `X`,

  `∫_Y π^*T_1 ∧ ⋯ ∧ π^*T_n = ∫_X T_1 ∧ ⋯ ∧ T_n`,

and the analogous identity for push-forwards of currents on `Y`.

Proved here (the first identity):
* `sourceMixedNonPluripolarMass_modification_pullback`: the potential form, in
  every dimension (including `0`): for `T_i = θ_i + dd^c φ_i`,
  `π^*T_i = π^*θ_i + dd^c (φ_i ∘ π)` (the source's definition of `π^*T_i`);
* `sourceCurrentNonPluripolarMass` (the non-pluripolar mass of a tuple of
  original closed positive `(1,1)`-currents, independent of the chosen
  presentations `T_i = θ_i + dd^c φ_i`) and
  `sourceCurrentNonPluripolarMass_modification_pullback`: the current form,
  with the original current pull-back `sourceCurrentModificationPullback`.

The push-forward identity is not formalized (push-forwards of currents along
modifications are not available).

`IsAnalyticModification` is the existing formalization of a proper bimeromorphic
morphism (proper holomorphic, with a holomorphic inverse off closed nowhere dense
analytic sets), already used for source `prop:biminv`.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NPP

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback
open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open SGPT.PSH.VariableComplexAtlas

section Potentials

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The pull-back `φ ∘ π` of a source `θ`-psh function is source `π^*θ`-psh. -/
theorem isThetaPSH_modification_pullback {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    (ofFixedModel n Y).IsThetaPSH
      (nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ)))
      (u ∘ π) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact isThetaPshPotential_comp_of_isAnalyticModification hπ _
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu)

/-- Source `prop:nppmassinv`, first identity, potential form: the total mixed
non-pluripolar mass of `π^*θ_i + dd^c(φ_i ∘ π)` on `Y` equals that of
`θ_i + dd^c φ_i` on `X`, in every dimension. -/
theorem sourceMixedNonPluripolarMass_modification_pullback {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : Fin n → X → EReal) (hu : ∀ i, (ofFixedModel n X).IsThetaPSH (θ i) (u i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    sourceMixedNonPluripolarMass
      (fun i => nativeClosedFormToAtlas
        (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (θ i))))
      (fun i => u i ∘ π) (fun i => isThetaPSH_modification_pullback hπ (hu i)) =
      sourceMixedNonPluripolarMass θ u hu := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  simp only [sourceMixedNonPluripolarMass_eq_native, sourceNativeAtlasForm_roundTrip]
  exact AnalyticModificationMixedMass.globalMixedMeasure_univ_pullback_of_isAnalyticModification
    hπ (θ := fun i => atlasClosedFormToNative (θ i))
    (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)).1)

end Potentials

section Currents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem singularityEquiv_sub_chartSmooth [CompactSpace M]
    {g : M → ℝ} (hg : ChartSmooth (n := m + 1) g) (u : M → EReal) :
    SGPT.PSH.SingularityEquiv u (fun x => u x - (g x : EReal)) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hbound : ∀ x, |g x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  refine ⟨⟨B, fun x _ => ?_⟩, ⟨B, fun x _ => ?_⟩⟩
  · have hh := add_le_add (le_refl (u x - (g x : EReal)))
      (EReal.coe_le_coe_iff.mpr (abs_le.mp (hbound x)).2)
    have heq : u x - (g x : EReal) + (g x : EReal) = u x := by
      simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
        neg_add_cancel, EReal.coe_zero, add_zero]
    rwa [heq] at hh
  · change u x + -(g x : EReal) ≤ u x + (B : EReal)
    have hb : -g x ≤ B := by linarith [(abs_le.mp (hbound x)).1]
    have hc : -(g x : EReal) ≤ (B : EReal) := by
      rw [← EReal.coe_neg]
      exact EReal.coe_le_coe_iff.mpr hb
    exact add_le_add le_rfl hc

/-- A genuine native presentation gives a source `θ`-psh function. -/
theorem isThetaPSH_nativeClosedFormToAtlas {θ : ClosedRealOneOneForm (m + 1) M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    (ofFixedModel (m + 1) M).IsThetaPSH (nativeClosedFormToAtlas θ) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  simpa only [sourceNativeAtlasForm_roundTrip] using hu

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The total mixed non-pluripolar mass depends only on the currents
`θ_i + dd^c u_i`, not on the chosen backgrounds and potentials. -/
theorem sourceMixedNonPluripolarMass_eq_of_thetaPotentialCurrent_eq
    (ω : KahlerBackground (m + 1) M)
    (θ η : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M))
    (u v : Fin (m + 1) → M → EReal)
    (hu : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (η i) (v i))
    (heq : ∀ i, thetaPotentialCurrent (atlasClosedFormToNative (θ i)).val (u i)
        ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) =
      thetaPotentialCurrent (atlasClosedFormToNative (η i)).val (v i)
        ((isThetaPSH_iff_nativeThetaPotential (η i) (v i)).mp (hv i))) :
    sourceMixedNonPluripolarMass θ u hu = sourceMixedNonPluripolarMass η v hv := by
  classical
  have hclass i := sourceThetaPotentialCurrent_class_eq (hu i) (hv i) (heq i)
  have hrel i : ClosedRealOneOneForm.BottChernRel
      (atlasClosedFormToNative (η i)) (atlasClosedFormToNative (θ i)) :=
    ((RealBottChern.ofRepresentative_eq_iff _ _).mp (hclass i)).symm
  choose g hg hηθ using hrel
  have hchange i : SourceSmoothBackgroundChange (η i) (θ i) (g i) :=
    (sourceSmoothBackgroundChange_iff_native _ _ _).mpr ⟨hg i, hηθ i⟩
  let v' : Fin (m + 1) → M → EReal := fun i x => v i x - (g i x : EReal)
  have hv' i : (ofFixedModel (m + 1) M).IsThetaPSH (θ i) (v' i) :=
    sourceThetaPSH_sub_smooth (hchange i) (hv i)
  have hsame i : SGPT.PSH.SingularityEquiv (u i) (v' i) :=
    SGPT.PSH.singularityEquiv_trans
      (SGPT.Okounkov.sameSingularity_of_thetaPotentialCurrent_eq _ _ (heq i))
      (singularityEquiv_sub_chartSmooth (hg i) (v i))
  calc
    sourceMixedNonPluripolarMass θ u hu = sourceMixedNonPluripolarMass θ v' hv' :=
      le_antisymm
        (sourceMixedNonPluripolarMass_mono ω hu hv' (fun i => (hsame i).1))
        (sourceMixedNonPluripolarMass_mono ω hv' hu (fun i => (hsame i).2))
    _ = sourceMixedNonPluripolarMass η v hv := by
      simp only [sourceMixedNonPluripolarMass_eq_native]
      exact congrArg (fun μ : Measure M => μ univ)
        (GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
          (θ := fun i => atlasClosedFormToNative (η i))
          (η := fun i => atlasClosedFormToNative (θ i)) (u := v) (f := g)
          (fun i => ((sourceSmoothBackgroundChange_iff_native _ _ _).mp (hchange i)).1)
          (fun i => ((sourceSmoothBackgroundChange_iff_native _ _ _).mp (hchange i)).2)
          (fun i => ((isThetaPSH_iff_nativeThetaPotential (η i) _).mp (hv i)).1))

omit [MeasurableSpace M] [BorelSpace M] in
/-- A chosen presentation `T_i = θ_i + dd^c u_i` of a tuple of original closed
positive `(1,1)`-currents. -/
theorem exists_currentTupleRepresentation
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    ∃ (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
      (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)),
      ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i) := by
  choose θ u hu hread _hchart using fun i =>
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  exact ⟨θ, u, hu, hread⟩

/-- The non-pluripolar mass `∫_X T_1 ∧ ⋯ ∧ T_n` of a tuple of original closed
positive `(1,1)`-currents (source `def:npp:L146` read at top degree on a compact
manifold): the mixed non-pluripolar mass of one presentation
`T_i = θ_i + dd^c u_i`; by `sourceCurrentNonPluripolarMass_eq_representation`
every presentation gives the same value. -/
def sourceCurrentNonPluripolarMass
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) : ℝ≥0∞ :=
  sourceMixedNonPluripolarMass
    (fun i => nativeClosedFormToAtlas (Classical.choose (exists_currentTupleRepresentation T hc h11 hp) i))
    (Classical.choose (Classical.choose_spec (exists_currentTupleRepresentation T hc h11 hp)))
    (fun i => isThetaPSH_nativeClosedFormToAtlas (Classical.choose (Classical.choose_spec
      (Classical.choose_spec (exists_currentTupleRepresentation T hc h11 hp))) i))

/-- Every presentation `T_i = θ_i + dd^c u_i` computes the current mass. -/
theorem sourceCurrentNonPluripolarMass_eq_representation (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i))
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) (u : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hread : ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i)) :
    sourceCurrentNonPluripolarMass T hc h11 hp =
      sourceMixedNonPluripolarMass (fun i => nativeClosedFormToAtlas (θ i)) u
        (fun i => isThetaPSH_nativeClosedFormToAtlas (hu i)) := by
  have hspec := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_currentTupleRepresentation T hc h11 hp)))
  apply sourceMixedNonPluripolarMass_eq_of_thetaPotentialCurrent_eq ω
  intro i
  simpa only [sourceNativeAtlasForm_roundTrip] using (hspec i).symm.trans (hread i)

/-- The current mass is finite. -/
theorem sourceCurrentNonPluripolarMass_lt_top (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    sourceCurrentNonPluripolarMass T hc h11 hp < ⊤ :=
  sourceMixedNonPluripolarMass_lt_top ω _ _ _

end Currents

section CurrentModification

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Source `prop:nppmassinv`, first identity: for a proper bimeromorphic
morphism `π : Y → X` onto a compact Kähler manifold (connectedness, a standing
assumption of the section, is not needed), from a Kähler
manifold `Y`, and original closed positive `(1,1)`-currents `T_i` on `X`,
`∫_Y π^*T_1 ∧ ⋯ ∧ π^*T_n = ∫_X T_1 ∧ ⋯ ∧ T_n`. -/
theorem sourceCurrentNonPluripolarMass_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (ωX : KahlerBackground (m + 1) X) (ωY : KahlerBackground (m + 1) Y)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    sourceCurrentNonPluripolarMass
      (fun i => sourceCurrentModificationPullback hπ (T i) (hc i) (h11 i) (hp i))
      (fun i => (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).1)
      (fun i => (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).2.1)
      (fun i => (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).2.2.1) =
      sourceCurrentNonPluripolarMass T hc h11 hp := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  obtain ⟨θ, v, hv, hread⟩ := exists_currentTupleRepresentation T hc h11 hp
  let η i := ClosedRealOneOneForm.pullback hπ.1 (θ i)
  let w i := v i ∘ π
  have hw i : IsThetaPshPotential (η i).val (w i) :=
    isThetaPshPotential_comp_of_isAnalyticModification hπ (θ i) (hv i)
  have hreadY i : sourceCurrentModificationPullback hπ (T i) (hc i) (h11 i) (hp i) =
      thetaPotentialCurrent (η i).val (w i) (hw i) :=
    (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).2.2.2
      (θ i) (v i) (hv i) (hread i)
  rw [sourceCurrentNonPluripolarMass_eq_representation ωY _ _ _ _ η w hw hreadY,
    sourceCurrentNonPluripolarMass_eq_representation ωX T hc h11 hp θ v hv hread]
  have hs i : (ofFixedModel (m + 1) X).IsThetaPSH (nativeClosedFormToAtlas (θ i)) (v i) :=
    isThetaPSH_nativeClosedFormToAtlas (hv i)
  have h := sourceMixedNonPluripolarMass_modification_pullback hπ
    (fun i => nativeClosedFormToAtlas (θ i)) v hs
  simpa only [η, w, sourceNativeAtlasForm_roundTrip] using h

end CurrentModification

end SGPT.NPP
