import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra

/-! Actual native I-volume homogeneity, including zero mass and dimension zero. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem nativeDomain {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  simpa only [sourceNativeAtlasForm_roundTrip] using hu

omit [BorelSpace M] in
private theorem generalCongr (ω : KahlerBackground n M)
    {θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i))
    (hθ : θ = η) (huv : u = v) :
    sourceGeneralMixedIVolume ω θ u hu = sourceGeneralMixedIVolume ω η v hv := by
  subst η
  subst v
  rfl

omit [BorelSpace M] in
private theorem nativeRead (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    sourceIVolume (nativeClosedFormToAtlas θ) u (nativeDomain hu) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials _) u hu := by
  simpa only [sourceNativeAtlasForm_roundTrip] using
    sourceIVolume_eq_native (nativeClosedFormToAtlas θ) u (nativeDomain hu)
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _)

/-- Genuine all-slot positive REAL homogeneity, without positive-mass inputs. -/
theorem sourceGeneralMixedIVolume_positive_smul_all (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {c : ℝ} (hc : 0 < c) :
    sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (c • θ i))
      (fun i x => (c : EReal) * u i x)
      (fun i => nativeDomain (RestrictedApproximantComparison.isThetaPshPotential_smul (hu i) hc)) =
      ENNReal.ofReal c ^ n * sourceGeneralMixedIVolume ω
        (fun i => nativeClosedFormToAtlas (θ i)) u (fun i => nativeDomain (hu i)) := by
  classical
  let Θ (s : Finset (Fin n)) i := if i ∈ s then c • θ i else θ i
  let v (s : Finset (Fin n)) i x := if i ∈ s then (c : EReal) * u i x else u i x
  have hΘ s i : IsThetaPshPotential (Θ s i).val (v s i) := by
    by_cases hi : i ∈ s
    · simpa only [Θ, v, if_pos hi] using
        RestrictedApproximantComparison.isThetaPshPotential_smul (hu i) hc
    · simpa only [Θ, v, if_neg hi] using hu i
  have hm (s : Finset (Fin n)) :
      sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (Θ s i))
        (v s) (fun i => nativeDomain (hΘ s i)) =
      ENNReal.ofReal c ^ s.card * sourceGeneralMixedIVolume ω
        (fun i => nativeClosedFormToAtlas (θ i)) u (fun i => nativeDomain (hu i)) := by
    induction s using Finset.induction_on with
    | empty => simp [Θ, v]
    | @insert a s ha ih =>
      have hs := sourceGeneralMixedIVolume_nonneg_smul_slot ω
        (fun i => nativeClosedFormToAtlas (Θ s i)) (v s)
        (fun i => nativeDomain (hΘ s i)) a hc.le
      have ef : Function.update (fun i => nativeClosedFormToAtlas (Θ s i)) a
          (nativeClosedFormToAtlas
            (c • atlasClosedFormToNative (nativeClosedFormToAtlas (Θ s a)))) =
          fun i => nativeClosedFormToAtlas (Θ (insert a s) i) := by
        funext i
        by_cases hi : i = a
        · subst i
          simp only [Function.update_self, sourceNativeAtlasForm_roundTrip,
            Θ, if_neg ha, Finset.mem_insert_self, if_true]
        · simp only [Function.update_of_ne hi, Θ, Finset.mem_insert, hi, false_or]
      have ev : Function.update (v s) a (fun x => (c : EReal) * v s a x) =
          v (insert a s) := by
        funext i x
        by_cases hi : i = a
        · subst i
          simp only [Function.update_self, v, if_neg ha, Finset.mem_insert_self, if_true]
        · simp only [Function.update_of_ne hi, v, Finset.mem_insert, hi, false_or]
      have hnew : ∀ i, (ofFixedModel n M).IsThetaPSH
          (Function.update (fun j => nativeClosedFormToAtlas (Θ s j)) a
            (nativeClosedFormToAtlas
              (c • atlasClosedFormToNative (nativeClosedFormToAtlas (Θ s a)))) i)
          (Function.update (v s) a (fun x => (c : EReal) * v s a x) i) := by
        rw [ef, ev]
        exact fun i => nativeDomain (hΘ (insert a s) i)
      have he := generalCongr ω hnew (fun i => nativeDomain (hΘ (insert a s) i)) ef ev
      exact he.symm.trans (hs.trans (by
        rw [ih, Finset.card_insert_of_notMem ha, pow_succ]
        ac_rfl))
  simpa only [Θ, v, Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin]
    using hm Finset.univ

/-- The literal native I-volume scales in every dimension, including zero mass. -/
theorem nativeIVolume_positive_smul (ω : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 < c) :
    iVolume (c • θ) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
      (fun x => (c : EReal) * u x)
      (RestrictedApproximantComparison.isThetaPshPotential_smul hu hc) =
      ENNReal.ofReal c ^ n * iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials _) u hu := by
  have hm := sourceGeneralMixedIVolume_positive_smul_all ω
    (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu) hc
  rw [sourceGeneralMixedIVolume_diagonal, sourceGeneralMixedIVolume_diagonal] at hm
  exact (nativeRead (c • θ) (fun x => (c : EReal) * u x)
    (RestrictedApproximantComparison.isThetaPshPotential_smul hu hc)).symm.trans
      (hm.trans (congrArg (fun z => ENNReal.ofReal c ^ n * z) (nativeRead θ u hu)))

end SGPT.PSH.VariableComplexAtlas
