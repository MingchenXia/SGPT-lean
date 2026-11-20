import SGPT.PSH.SourcePositiveMixedIVolumeAlgebra
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.AtTopBotIxx

/-! # The full general perturbative mixed I-volume definition

The actual positive-parameter family has a finite right limit, independent of
its genuine Kahler background. Original zero I-volumes and dimension zero are
retained. This module does not assert the six later general mixed-volume laws.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem perturbedPSH (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (ε : NNReal) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ε.property)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem zeroScaledPSH (ω : KahlerBackground n M) (c : NNReal) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas ((c : ℝ) • ω.form))
      (fun _ => (0 : EReal)) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (KahlerDomination.isSemipositive_smul ω.isSemipositive c.property)

/-- Every positive actual Kahler perturbation has positive individual I-volume,
even when the original genuine potential has zero actual or I-volume. -/
theorem sourceIVolume_add_kahler_pos (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {ε : NNReal} (hε : 0 < (ε : ℝ)) :
    0 < sourceIVolume
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u
      (perturbedPSH ω hu ε) := by
  let Γ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)
  have hΓ : (ofFixedModel n M).IsThetaPSH Γ u := perturbedPSH ω hu ε
  have hn := (isThetaPSH_iff_nativeThetaPotential Γ u).mp hΓ
  have hQ := (isThetaPSH_iff_nativeThetaPotential Γ _).mp
    (isThetaPSH_sourceIEnvelope hΓ)
  have hp : 0 < DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative Γ) u hn := by
    have ht := SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hε
    simpa only [Γ, sourceNativeAtlasForm_roundTrip, DiagonalMass.HasPositivePotentialMass] using ht
  have hmore : MoreSingularOn u (sourceIEnvelope Γ u) univ := by
    rw [sourceIEnvelope_eq_native Γ u hΓ]
    exact moreSingularOn_iSingularityEnvelope hn
  have hm := hp.trans_le (diagonalPotentialMass_mono_of_kahler ω hn hQ hmore)
  simpa only [sourceIVolume, sourcePotentialNonPluripolarMeasure,
    DiagonalMass.diagonalPotentialMass] using hm

private theorem zeroScaledIVolume_pos (ω : KahlerBackground n M) {c : NNReal}
    (hc : 0 < (c : ℝ)) :
    0 < sourceIVolume (nativeClosedFormToAtlas ((c : ℝ) • ω.form))
      (fun _ => (0 : EReal)) (zeroScaledPSH ω c) := by
  have hhalf : 0 < ((c / 2 : NNReal) : ℝ) := by simpa only [NNReal.coe_div, NNReal.coe_ofNat] using half_pos hc
  have ht := sourceIVolume_add_kahler_pos ω (zeroScaledPSH ω (c / 2)) hhalf
  simpa only [sourceNativeAtlasForm_roundTrip, NNReal.coe_div, NNReal.coe_ofNat,
    ← add_smul, add_halves] using ht

omit [BorelSpace M] in
private theorem mixedVolume_congr
    {θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i)) (hθ : θ = η) (huv : u = v) :
    sourceEnvelopeMixedIVolume θ u hu = sourceEnvelopeMixedIVolume η v hv := by
  subst η
  subst v
  rfl

private theorem mixedVolume_mono_add_kahler (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i))
    {c : NNReal} (hc : 0 < (c : ℝ)) :
    sourceEnvelopeMixedIVolume θ u hu ≤
      sourceEnvelopeMixedIVolume
        (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (c : ℝ) • ω.form))
        u (fun i => perturbedPSH ω (hu i) c) := by
  classical
  let Γ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M) := fun i =>
    nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (c : ℝ) • ω.form)
  let Θ : Finset (Fin n) → Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M) :=
    fun s i => if i ∈ s then Γ i else θ i
  have hΘ s i : (ofFixedModel n M).IsThetaPSH (Θ s i) (u i) := by
    by_cases hi : i ∈ s
    · simpa only [Θ, if_pos hi] using perturbedPSH ω (hu i) c
    · simpa only [Θ, if_neg hi] using hu i
  have hpΘ s i : 0 < sourceIVolume (Θ s i) (u i) (hΘ s i) := by
    by_cases hi : i ∈ s
    · simpa only [Θ, if_pos hi] using sourceIVolume_add_kahler_pos ω (hu i) hc
    · simpa only [Θ, if_neg hi] using hpos i
  have hmono s : sourceEnvelopeMixedIVolume θ u hu ≤
      sourceEnvelopeMixedIVolume (Θ s) u (hΘ s) := by
    induction s using Finset.induction_on with
    | empty =>
      exact (mixedVolume_congr hu (hΘ ∅) (by funext i; simp [Θ]) rfl).le
    | @insert a s ha ih =>
      have hadd := sourceEnvelopeMixedIVolume_add_slot ω (Θ s) u (hΘ s) (hpΘ s) a
        (nativeClosedFormToAtlas ((c : ℝ) • ω.form)) (fun _ => (0 : EReal))
        (zeroScaledPSH ω c) (zeroScaledIVolume_pos ω hc)
      have eθ : Function.update (Θ s) a
          (nativeClosedFormToAtlas (atlasClosedFormToNative (Θ s a) +
            atlasClosedFormToNative (nativeClosedFormToAtlas ((c : ℝ) • ω.form)))) =
          Θ (insert a s) := by
        funext i
        by_cases hi : i = a
        · subst i
          simp only [Function.update_self, Θ, if_neg ha, sourceNativeAtlasForm_roundTrip]
          simp only [Finset.mem_insert_self, if_true, Γ]
        · simp only [Function.update_of_ne hi, Θ, Finset.mem_insert, hi, false_or]
      have eu : Function.update u a (fun x => u a x + (0 : EReal)) = u := by
        simp only [add_zero, Function.update_eq_self]
      have eqv := mixedVolume_congr (by
        intro i
        simpa only [eθ, eu] using hΘ (insert a s) i) (hΘ (insert a s)) eθ eu
      exact ih.trans ((le_self_add.trans_eq hadd.symm).trans_eq eqv)
  simpa only [Θ, Finset.mem_univ, if_true, Γ] using hmono Finset.univ

/-- The actual family is monotone on ALL positive nonnegative-real parameters;
no equality with its unperturbed zero endpoint is assumed. -/
theorem sourceMixedIVolumeKahlerPerturbation_mono_pos (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    MonotoneOn (sourceMixedIVolumeKahlerPerturbation ω θ u hu) (Ioi (0 : NNReal)) := by
  intro s hs t _ hst
  by_cases heq : s = t
  · subst t; exact le_rfl
  have hdiff : 0 < ((t - s : NNReal) : ℝ) := by
    exact_mod_cast (tsub_pos_iff_lt.mpr (lt_of_le_of_ne hst heq))
  let Γ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M) := fun i =>
    nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (s : ℝ) • ω.form)
  have hΓ i : (ofFixedModel n M).IsThetaPSH (Γ i) (u i) := perturbedPSH ω (hu i) s
  have hpΓ i : 0 < sourceIVolume (Γ i) (u i) (hΓ i) :=
    sourceIVolume_add_kahler_pos ω (hu i) (by exact_mod_cast hs)
  have hm := mixedVolume_mono_add_kahler ω Γ u hΓ hpΓ hdiff
  have eθ : (fun i => nativeClosedFormToAtlas
      (atlasClosedFormToNative (Γ i) + ((t - s : NNReal) : ℝ) • ω.form)) =
      fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t : ℝ) • ω.form) := by
    funext i
    simp only [Γ, sourceNativeAtlasForm_roundTrip, add_assoc, ← add_smul,
      ← NNReal.coe_add, add_tsub_cancel_of_le hst]
  exact hm.trans_eq (mixedVolume_congr (fun i => perturbedPSH ω (hΓ i) (t - s))
    (fun i => perturbedPSH ω (hu i) t) eθ rfl)

/-- The literal infimum of the actual positive perturbation family. The
following theorems identify the printed right limit and Kahler independence. -/
def sourceGeneralMixedIVolume (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) : ENNReal :=
  ⨅ ε : Ioi (0 : NNReal), sourceMixedIVolumeKahlerPerturbation ω θ u hu ε

/-- Full positive-real right-filter existence, with all original zero I-volumes
and the actual dimension-zero empty tuple retained. -/
theorem sourceGeneralMixedIVolume_tendsto (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    Tendsto (sourceMixedIVolumeKahlerPerturbation ω θ u hu) (𝓝[>] (0 : NNReal))
      (𝓝 (sourceGeneralMixedIVolume ω θ u hu)) := by
  apply (tendsto_comp_coe_Ioi_atBot (a := (0 : NNReal))).mp
  exact tendsto_atBot_iInf (fun s t hst =>
    sourceMixedIVolumeKahlerPerturbation_mono_pos ω θ u hu s.property t.property hst)

/-- Agreement with the previous direct definition retains exactly its original
positive individual I-volume hypothesis; original NP masses may vanish. -/
theorem sourceGeneralMixedIVolume_eq_positive (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i)) :
    sourceGeneralMixedIVolume ω θ u hu = sourceEnvelopeMixedIVolume θ u hu :=
  tendsto_nhds_unique (sourceGeneralMixedIVolume_tendsto ω θ u hu)
    ((sourceEnvelopeMixedIVolume_tendsto_add_kahler ω θ u hu hpos).mono_left nhdsWithin_le_nhds)

/-- A genuine finite value for every original tuple, before any realification. -/
theorem sourceGeneralMixedIVolume_lt_top (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceGeneralMixedIVolume ω θ u hu < ⊤ := by
  have hle : sourceGeneralMixedIVolume ω θ u hu ≤
      sourceMixedIVolumeKahlerPerturbation ω θ u hu 1 :=
    iInf_le (fun ε : Ioi (0 : NNReal) => sourceMixedIVolumeKahlerPerturbation ω θ u hu ε)
      ⟨1, by change (0 : NNReal) < 1; exact zero_lt_one⟩
  have hf : sourceMixedIVolumeKahlerPerturbation ω θ u hu 1 < ⊤ :=
    sourceEnvelopeMixedIVolume_lt_top ω
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (1 : ℝ) • ω.form))
      u (fun i => perturbedPSH ω (hu i) 1)
  exact hle.trans_lt hf

private theorem generalMixedVolume_le_change_kahler (ω η : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceGeneralMixedIVolume ω θ u hu ≤ sourceGeneralMixedIVolume η θ u hu := by
  obtain ⟨C, hC, hρ⟩ := KahlerDomination.exists_pos_isKahler_add_smul η (-ω.form)
  let ρ : KahlerBackground n M := ⟨-ω.form + C • η.form, hρ⟩
  let A : NNReal := ⟨C, hC.le⟩
  have hA : 0 < A := by exact_mod_cast hC
  have hcomp (t : NNReal) (ht : 0 < t) :
      sourceMixedIVolumeKahlerPerturbation ω θ u hu t ≤
        sourceMixedIVolumeKahlerPerturbation η θ u hu (A * t) := by
    let Γ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M) := fun i =>
      nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t : ℝ) • ω.form)
    have hΓ i : (ofFixedModel n M).IsThetaPSH (Γ i) (u i) := perturbedPSH ω (hu i) t
    have hpΓ i : 0 < sourceIVolume (Γ i) (u i) (hΓ i) :=
      sourceIVolume_add_kahler_pos ω (hu i) (by exact_mod_cast ht)
    have hm := mixedVolume_mono_add_kahler ρ Γ u hΓ hpΓ (by exact_mod_cast ht)
    have eθ : (fun i => nativeClosedFormToAtlas
        (atlasClosedFormToNative (Γ i) + (t : ℝ) • ρ.form)) =
        fun i => nativeClosedFormToAtlas
          (atlasClosedFormToNative (θ i) + ((A * t : NNReal) : ℝ) • η.form) := by
      funext i
      simp only [Γ, sourceNativeAtlasForm_roundTrip, ρ, A]
      congr 1
      rw [smul_add, smul_neg, smul_smul, mul_comm (t : ℝ) C]
      abel
    exact hm.trans_eq (mixedVolume_congr (fun i => perturbedPSH ρ (hΓ i) t)
      (fun i => perturbedPSH η (hu i) (A * t)) eθ rfl)
  apply le_iInf
  intro r
  let t : NNReal := r.val / A
  have ht : 0 < t := div_pos r.property hA
  have he : A * t = r.val := by
    dsimp only [t]
    exact mul_div_cancel₀ _ hA.ne'
  calc
    sourceGeneralMixedIVolume ω θ u hu ≤ sourceMixedIVolumeKahlerPerturbation ω θ u hu t :=
      iInf_le (fun ε : Ioi (0 : NNReal) => sourceMixedIVolumeKahlerPerturbation ω θ u hu ε)
        ⟨t, ht⟩
    _ ≤ sourceMixedIVolumeKahlerPerturbation η θ u hu (A * t) := hcomp t ht
    _ = sourceMixedIVolumeKahlerPerturbation η θ u hu r :=
      congrArg (sourceMixedIVolumeKahlerPerturbation η θ u hu) he

/-- Actual smooth Kahler domination and all produced positive intermediate
I-volumes prove independence for EVERY original tuple, including all-zero ones. -/
theorem sourceGeneralMixedIVolume_kahler_independent (ω η : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceGeneralMixedIVolume ω θ u hu = sourceGeneralMixedIVolume η θ u hu :=
  le_antisymm (generalMixedVolume_le_change_kahler ω η θ u hu)
    (generalMixedVolume_le_change_kahler η ω θ u hu)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem perturbedGauge (ω : KahlerBackground n M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hc : SourceSmoothBackgroundChange θ η g) (ε : NNReal) :
    SourceSmoothBackgroundChange
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form))
      (nativeClosedFormToAtlas (atlasClosedFormToNative η + (ε : ℝ) • ω.form)) g := by
  refine ⟨hc.1, fun e z hz => ?_⟩
  simp only [sourceNativeAtlasForm_roundTrip, ClosedRealOneOneForm.coeff_add]
  rw [hc.2 e z hz]
  abel

/-- The SAME independent actual smooth gauges preserve the general infimum.
Only complete tensor identities on actual chart targets are required. -/
theorem sourceGeneralMixedIVolume_changeRepresentative (ω : KahlerBackground n M)
    (θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal) (g : Fin n → M → ℝ)
    (hc : ∀ i, SourceSmoothBackgroundChange (θ i) (η i) (g i))
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceGeneralMixedIVolume ω η (fun i x => u i x - (g i x : EReal))
      (fun i => sourceThetaPSH_sub_smooth (hc i) (hu i)) =
      sourceGeneralMixedIVolume ω θ u hu := by
  unfold sourceGeneralMixedIVolume
  apply iInf_congr
  intro ε
  exact sourceEnvelopeMixedIVolume_changeRepresentative ω
    (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (ε.val : ℝ) • ω.form))
    (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (η i) + (ε.val : ℝ) • ω.form))
    u g (fun i => perturbedGauge ω (hc i) ε) (fun i => perturbedPSH ω (hu i) ε)

end SGPT.PSH.VariableComplexAtlas
