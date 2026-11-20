import SGPT.PSH.SourceGeneralMixedIVolume
import SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass
import Mathlib.Analysis.SpecificLimits.Basic

/-! # General mixed I-volume algebra and diagonal with zero input masses

The represented original pairs retain arbitrary natural dimension, poles and
zero I-volumes. The separate Reg clause is not asserted by this module.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
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

/-- Symmetry of the actual general quantity, with no original positive-volume
hypothesis and with the original empty tuple retained. -/
theorem sourceGeneralMixedIVolume_perm (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (σ : Equiv.Perm (Fin n)) :
    sourceGeneralMixedIVolume ω (fun i => θ (σ i)) (fun i => u (σ i))
      (fun i => hu (σ i)) = sourceGeneralMixedIVolume ω θ u hu := by
  unfold sourceGeneralMixedIVolume
  apply iInf_congr
  intro ε
  exact sourceEnvelopeMixedIVolume_perm
    (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (ε : ℝ) • ω.form))
    u (fun i => perturbedPSH ω (hu i) ε) σ

/-- Actual different representatives in the same class and original all-level
I-order imply general-volume monotonicity, including all zero input masses. -/
theorem sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder
    (ω : KahlerBackground n M)
    (θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u v : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i))
    (hclass : ∀ i, RealBottChern.ofRepresentative (atlasClosedFormToNative (θ i)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative (η i)))
    (hI : ∀ i, sourceIOrder (ofFixedModel n M) (u i) (v i)) :
    sourceGeneralMixedIVolume ω θ u hu ≤ sourceGeneralMixedIVolume ω η v hv := by
  apply iInf_mono
  intro ε
  apply sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω
    _ _ u v (fun i => perturbedPSH ω (hu i) ε) (fun i => perturbedPSH ω (hv i) ε)
  · intro i
    simp only [sourceNativeAtlasForm_roundTrip, RealBottChern.ofRepresentative_add,
      hclass i]
  · exact hI

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

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem zeroScaledPSH (ω : KahlerBackground n M) (c : NNReal) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas ((c : ℝ) • ω.form))
      (fun _ => (0 : EReal)) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (KahlerDomination.isSemipositive_smul ω.isSemipositive c.property)

private theorem zeroScaledIVolume_pos (ω : KahlerBackground n M) {c : NNReal}
    (hc : 0 < (c : ℝ)) :
    0 < sourceIVolume (nativeClosedFormToAtlas ((c : ℝ) • ω.form))
      (fun _ => (0 : EReal)) (zeroScaledPSH ω c) := by
  have hhalf : 0 < ((c / 2 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using half_pos hc
  have ht := sourceIVolume_add_kahler_pos ω (zeroScaledPSH ω (c / 2)) hhalf
  simpa only [sourceNativeAtlasForm_roundTrip, NNReal.coe_div, NNReal.coe_ofNat,
    ← add_smul, add_halves] using ht

private theorem mixedVolume_mono_coefficients (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (r t : Fin n → NNReal) (hr : ∀ i, 0 < r i) (hrt : ∀ i, r i ≤ t i) :
    sourceEnvelopeMixedIVolume
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (r i : ℝ) • ω.form))
      u (fun i => perturbedPSH ω (hu i) (r i)) ≤
    sourceEnvelopeMixedIVolume
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t i : ℝ) • ω.form))
      u (fun i => perturbedPSH ω (hu i) (t i)) := by
  classical
  let Γ (q : Fin n → NNReal) i :=
    nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (q i : ℝ) • ω.form)
  let Θ (s : Finset (Fin n)) i := if i ∈ s then Γ t i else Γ r i
  have hΘ s i : (ofFixedModel n M).IsThetaPSH (Θ s i) (u i) := by
    by_cases hi : i ∈ s
    · simpa only [Θ, if_pos hi] using perturbedPSH ω (hu i) (t i)
    · simpa only [Θ, if_neg hi] using perturbedPSH ω (hu i) (r i)
  have hpΘ s i : 0 < sourceIVolume (Θ s i) (u i) (hΘ s i) := by
    by_cases hi : i ∈ s
    · simpa only [Θ, if_pos hi] using sourceIVolume_add_kahler_pos ω (hu i)
        (by exact_mod_cast (hr i).trans_le (hrt i))
    · simpa only [Θ, if_neg hi] using sourceIVolume_add_kahler_pos ω (hu i)
        (by exact_mod_cast hr i)
  have hm s : sourceEnvelopeMixedIVolume (Γ r) u (fun i => perturbedPSH ω (hu i) (r i)) ≤
      sourceEnvelopeMixedIVolume (Θ s) u (hΘ s) := by
    induction s using Finset.induction_on with
    | empty =>
      exact (mixedVolume_congr _ (hΘ ∅) (by funext i; simp [Θ]) rfl).le
    | @insert a s ha ih =>
      by_cases he : r a = t a
      · have eθ : Θ s = Θ (insert a s) := by
          funext i
          by_cases hi : i = a
          · subst i; simp only [Θ, if_neg ha, Finset.mem_insert_self, if_true, Γ, he]
          · simp only [Θ, Finset.mem_insert, hi, false_or]
        exact ih.trans_eq (mixedVolume_congr (hΘ s) (hΘ (insert a s)) eθ rfl)
      · have hc : 0 < ((t a - r a : NNReal) : ℝ) := by
          exact_mod_cast tsub_pos_iff_lt.mpr (lt_of_le_of_ne (hrt a) he)
        have hadd := sourceEnvelopeMixedIVolume_add_slot ω (Θ s) u (hΘ s) (hpΘ s) a
          (nativeClosedFormToAtlas (((t a - r a : NNReal) : ℝ) • ω.form))
          (fun _ => (0 : EReal)) (zeroScaledPSH ω (t a - r a)) (zeroScaledIVolume_pos ω hc)
        have eθ : Function.update (Θ s) a (nativeClosedFormToAtlas
            (atlasClosedFormToNative (Θ s a) +
              atlasClosedFormToNative (nativeClosedFormToAtlas (((t a-r a : NNReal) : ℝ) • ω.form)))) =
            Θ (insert a s) := by
          funext i
          by_cases hi : i = a
          · subst i
            simp only [Function.update_self, Θ, if_neg ha, Finset.mem_insert_self, if_true,
              Γ, sourceNativeAtlasForm_roundTrip, NNReal.coe_sub (hrt a)]
            congr 1
            module
          · simp only [Function.update_of_ne hi, Θ, Finset.mem_insert, hi, false_or]
        have eu : Function.update u a (fun x => u a x + (0 : EReal)) = u := by
          simp only [add_zero, Function.update_eq_self]
        have eqv := mixedVolume_congr (by intro i; simpa only [eθ, eu] using hΘ (insert a s) i)
          (hΘ (insert a s)) eθ eu
        exact ih.trans ((le_self_add.trans_eq hadd.symm).trans_eq eqv)
  simpa only [Θ, Finset.mem_univ, if_true, Γ] using hm Finset.univ

private theorem mul_tendsto_right (c : NNReal) (hc : 0 < c) :
    Tendsto (fun ε : NNReal => c * ε) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun ε : NNReal => c * ε) := continuous_const.mul continuous_id
    have ht : Tendsto (fun ε : NNReal => c * ε) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using h.tendsto (0 : NNReal)
    exact ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos hc hε

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem ratePSH (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (a : ℝ) (ha : 0 < a) (ε : NNReal) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + ((ε : ℝ) * a) • ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive (mul_nonneg ε.property ha.le))

/-- Every actual tuple of positive REAL perturbation rates has the same full
right limit. All genuine positive intermediate domains and masses are produced. -/
theorem sourceGeneralMixedIVolume_nonuniform_perturbation_tendsto (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Tendsto (fun ε : NNReal => sourceEnvelopeMixedIVolume
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + ((ε : ℝ) * a i) • ω.form))
      u (fun i => ratePSH ω (hu i) (a i) (ha i) ε)) (𝓝[>] (0 : NNReal))
      (𝓝 (sourceGeneralMixedIVolume ω θ u hu)) := by
  classical
  let A : Fin n → NNReal := fun i => ⟨a i, (ha i).le⟩
  have hA i : 0 < A i := by exact_mod_cast ha i
  let l : NNReal := (1 + ∑ i, (A i)⁻¹)⁻¹
  let h : NNReal := 1 + ∑ i, A i
  have hl : 0 < l := by dsimp only [l]; positivity
  have hh : 0 < h := by dsimp only [h]; positivity
  have hla i : l ≤ A i := by
    have hi : (A i)⁻¹ ≤ 1 + ∑ j, (A j)⁻¹ :=
      (Finset.single_le_sum (fun j _ => (zero_le : (0 : NNReal) ≤ (A j)⁻¹)) (Finset.mem_univ i)).trans
        (le_add_self)
    have hx := (inv_le_inv₀ (by positivity : (0 : NNReal) < 1 + ∑ j, (A j)⁻¹)
      (inv_pos.mpr (hA i))).mpr hi
    simpa only [inv_inv] using hx
  have hah i : A i ≤ h :=
    (Finset.single_le_sum (fun j _ => (zero_le : (0 : NNReal) ≤ A j)) (Finset.mem_univ i)).trans le_add_self
  have lower := (sourceGeneralMixedIVolume_tendsto ω θ u hu).comp (mul_tendsto_right l hl)
  have upper := (sourceGeneralMixedIVolume_tendsto ω θ u hu).comp (mul_tendsto_right h hh)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm := mixedVolume_mono_coefficients ω θ u hu (fun _ => l * ε)
      (fun i => ε * A i) (fun _ => mul_pos hl hε) (fun i => by
        simpa only [mul_comm l ε] using mul_le_mul_of_nonneg_left (hla i) ε.property)
    exact hm
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm := mixedVolume_mono_coefficients ω θ u hu (fun i => ε * A i)
      (fun _ => h * ε) (fun i => mul_pos hε (hA i)) (fun i => by
        simpa only [mul_comm h ε] using mul_le_mul_of_nonneg_left (hah i) ε.property)
    exact hm

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem updatePSH
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) (a : Fin n)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    ∀ i, (ofFixedModel n M).IsThetaPSH (Function.update θ a σ i) (Function.update u a v i) := by
  intro i
  by_cases hi : i = a
  · subst i; simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hi] using hu i

private def ratedVolume (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (ε : NNReal) : ENNReal :=
  sourceEnvelopeMixedIVolume
    (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + ((ε : ℝ) * r i) • ω.form))
    u (fun i => ratePSH ω (hu i) (r i) (hr i) ε)

/-- Independent one-slot addition of the general quantity, with genuine domains
and positive perturbed I-volumes produced even when every original mass is zero. -/
theorem sourceGeneralMixedIVolume_add_slot (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n) (σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourceGeneralMixedIVolume ω
      (Function.update θ a (nativeClosedFormToAtlas
        (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ)))
      (Function.update u a (fun x => u a x + v x))
      (updatePSH hu a (sourceIndependentSum_thetaPSH (hu a) hv)) =
      sourceGeneralMixedIVolume ω θ u hu +
        sourceGeneralMixedIVolume ω (Function.update θ a σ) (Function.update u a v)
          (updatePSH hu a hv) := by
  classical
  let r : Fin n → ℝ := fun i => if i = a then 1 / 2 else 1
  have hr i : 0 < r i := by dsimp only [r]; split <;> norm_num
  let τ := nativeClosedFormToAtlas (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ)
  let Θ := Function.update θ a τ
  let w := Function.update u a (fun x => u a x + v x)
  have hw := updatePSH hu a (sourceIndependentSum_thetaPSH (hu a) hv)
  have eqf : ∀ᶠ ε : NNReal in 𝓝[>] 0,
      sourceMixedIVolumeKahlerPerturbation ω Θ w hw ε =
        ratedVolume ω θ u hu r hr ε +
        ratedVolume ω (Function.update θ a σ) (Function.update u a v)
          (updatePSH hu a hv) r hr ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let Γ i := nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + ((ε : ℝ) * r i) • ω.form)
    have hΓ i : (ofFixedModel n M).IsThetaPSH (Γ i) (u i) := ratePSH ω (hu i) (r i) (hr i) ε
    have hp i : 0 < sourceIVolume (Γ i) (u i) (hΓ i) := by
      exact sourceIVolume_add_kahler_pos ω (hu i)
        (ε := ⟨(ε : ℝ) * r i, mul_nonneg ε.property (hr i).le⟩)
        (mul_pos (show 0 < (ε : ℝ) by exact_mod_cast hε) (hr i))
    let σ' := nativeClosedFormToAtlas (atlasClosedFormToNative σ + ((ε : ℝ) * (1 / 2)) • ω.form)
    have hv' : (ofFixedModel n M).IsThetaPSH σ' v := ratePSH ω hv (1 / 2) (by norm_num) ε
    have hvp : 0 < sourceIVolume σ' v hv' := by
      exact sourceIVolume_add_kahler_pos ω hv
        (ε := ⟨(ε : ℝ) * (1 / 2), mul_nonneg ε.property (by norm_num)⟩)
        (mul_pos (show 0 < (ε : ℝ) by exact_mod_cast hε) (by norm_num))
    have hadd := sourceEnvelopeMixedIVolume_add_slot ω Γ u hΓ hp a σ' v hv' hvp
    have el : Function.update Γ a (nativeClosedFormToAtlas
        (atlasClosedFormToNative (Γ a) + atlasClosedFormToNative σ')) =
        fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (Θ i) + (ε : ℝ) • ω.form) := by
      funext i
      by_cases hi : i = a
      · subst i
        simp only [Function.update_self, Γ, σ', Θ, τ, r, if_true,
          sourceNativeAtlasForm_roundTrip]
        congr 1
        module
      · simp only [Function.update_of_ne hi, Θ, Γ, r, if_neg hi, mul_one]
    have er : Function.update Γ a σ' = fun i => nativeClosedFormToAtlas
        (atlasClosedFormToNative (Function.update θ a σ i) + ((ε : ℝ) * r i) • ω.form) := by
      funext i
      by_cases hi : i = a
      · subst i; simp only [Function.update_self, σ', r, if_pos rfl]
      · simp only [Function.update_of_ne hi, Γ]
    have eleft := mixedVolume_congr
      (updatePSH hΓ a (sourceIndependentSum_thetaPSH (hΓ a) hv'))
      (fun i => perturbedPSH ω (hw i) ε) el rfl
    have eright := mixedVolume_congr (updatePSH hΓ a hv')
      (fun i => ratePSH ω ((updatePSH hu a hv) i) (r i) (hr i) ε) er rfl
    exact eleft.symm.trans (hadd.trans (congrArg (fun x => ratedVolume ω θ u hu r hr ε + x) eright))
  have hright := (sourceGeneralMixedIVolume_nonuniform_perturbation_tendsto ω θ u hu r hr).add
    (sourceGeneralMixedIVolume_nonuniform_perturbation_tendsto ω
      (Function.update θ a σ) (Function.update u a v) (updatePSH hu a hv) r hr)
  exact tendsto_nhds_unique (sourceGeneralMixedIVolume_tendsto ω Θ w hw)
    (hright.congr' (eqf.mono (fun _ h => h.symm)))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem nonnegScalingPSH (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {c : ℝ} (hc : 0 ≤ c) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
      (fun x => (c : EReal) * u x) := by
  by_cases he : c = 0
  · subst c
    simpa only [zero_smul, EReal.coe_zero, zero_mul, NNReal.coe_zero] using zeroScaledPSH ω 0
  · exact sourcePositiveScaling_thetaPSH hu (lt_of_le_of_ne hc (Ne.symm he))

/-- Every nonnegative REAL scalar, including zero, gives the actual slot
homogeneity identity. No original mass positivity is assumed. -/
theorem sourceGeneralMixedIVolume_nonneg_smul_slot (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n) {c : ℝ} (hc : 0 ≤ c) :
    sourceGeneralMixedIVolume ω
      (Function.update θ a (nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ a))))
      (Function.update u a (fun x => (c : EReal) * u a x))
      (updatePSH hu a (nonnegScalingPSH ω (hu a) hc)) =
      ENNReal.ofReal c * sourceGeneralMixedIVolume ω θ u hu := by
  classical
  by_cases he : c = 0
  · subst c
    let ζ : AtlasClosedRealOneOneForm (ofFixedModel n M) := nativeClosedFormToAtlas 0
    let Θ := Function.update θ a ζ
    let w := Function.update u a (fun _ => (0 : EReal))
    have hz : (ofFixedModel n M).IsThetaPSH ζ (fun _ => (0 : EReal)) := by
      simpa only [NNReal.coe_zero, zero_smul] using zeroScaledPSH ω 0
    have hw := updatePSH hu a hz
    have hadd := sourceGeneralMixedIVolume_add_slot ω Θ w hw a ζ (fun _ => (0 : EReal)) hz
    have hdup : sourceGeneralMixedIVolume ω Θ w hw =
        sourceGeneralMixedIVolume ω Θ w hw + sourceGeneralMixedIVolume ω Θ w hw := by
      simpa only [Θ, w, Function.update_self, ζ, sourceNativeAtlasForm_roundTrip,
        zero_add, add_zero, Function.update_idem] using hadd
    have hzero : sourceGeneralMixedIVolume ω Θ w hw = 0 := by
      apply (ENNReal.add_right_inj (sourceGeneralMixedIVolume_lt_top ω Θ w hw).ne).mp
      simpa only [add_zero] using hdup.symm
    simpa only [ENNReal.ofReal_zero, zero_mul, EReal.coe_zero, zero_smul, Θ, w, ζ]
      using hzero
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm he)
    let r : Fin n → ℝ := fun i => if i = a then c⁻¹ else 1
    have hr i : 0 < r i := by dsimp only [r]; split <;> positivity
    let τ := nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ a))
    let Θ := Function.update θ a τ
    let w := Function.update u a (fun x => (c : EReal) * u a x)
    have hw := updatePSH hu a (nonnegScalingPSH ω (hu a) hc)
    have eqf : ∀ᶠ ε : NNReal in 𝓝[>] 0,
        sourceMixedIVolumeKahlerPerturbation ω Θ w hw ε =
          ENNReal.ofReal c * ratedVolume ω θ u hu r hr ε := by
      filter_upwards [self_mem_nhdsWithin] with ε _
      let Γ i := nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + ((ε : ℝ) * r i) • ω.form)
      have hΓ i : (ofFixedModel n M).IsThetaPSH (Γ i) (u i) := ratePSH ω (hu i) (r i) (hr i) ε
      have hsmul := sourceEnvelopeMixedIVolume_positive_smul_slot Γ u hΓ a hcp
      have eθ : Function.update Γ a (nativeClosedFormToAtlas (c • atlasClosedFormToNative (Γ a))) =
          fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (Θ i) + (ε : ℝ) • ω.form) := by
        funext i
        by_cases hi : i = a
        · subst i
          simp only [Function.update_self, Γ, r, if_true, sourceNativeAtlasForm_roundTrip,
            Θ, τ, smul_add, smul_smul]
          congr 1
          have ht : c * ((ε : ℝ) * c⁻¹) = (ε : ℝ) := by field_simp
          rw [ht]
        · simp only [Function.update_of_ne hi, Γ, Θ, r, if_neg hi, mul_one]
      have eqv := mixedVolume_congr (updatePSH hΓ a (sourcePositiveScaling_thetaPSH (hΓ a) hcp))
        (fun i => perturbedPSH ω (hw i) ε) eθ rfl
      exact eqv.symm.trans hsmul
    have hright : Tendsto (fun ε => ENNReal.ofReal c * ratedVolume ω θ u hu r hr ε)
        (𝓝[>] (0 : NNReal)) (𝓝 (ENNReal.ofReal c * sourceGeneralMixedIVolume ω θ u hu)) :=
      ENNReal.Tendsto.const_mul
        (sourceGeneralMixedIVolume_nonuniform_perturbation_tendsto ω θ u hu r hr)
        (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_nhds_unique (sourceGeneralMixedIVolume_tendsto ω Θ w hw)
      (hright.congr' (eqf.mono (fun _ h => h.symm)))

private theorem perturbQ_models (ω : KahlerBackground n M) {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (ε : NNReal) (hε : 0 < (ε : ℝ)) :
    IsModelPotential (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)
      (sourceIEnvelope (nativeClosedFormToAtlas
        (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u) ∧
    IsIModelPotential (atlasClosedFormToNative θ + (ε : ℝ) • ω.form).val
      (sourceIEnvelope (nativeClosedFormToAtlas
        (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u) := by
  let Γ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)
  have hΓ : (ofFixedModel n M).IsThetaPSH Γ u := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [sourceNativeAtlasForm_roundTrip]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
      (KahlerDomination.isSemipositive_smul ω.isSemipositive ε.property)
  have hn := (isThetaPSH_iff_nativeThetaPotential _ _).mp hΓ
  have he := sourceIEnvelope_eq_native Γ u hΓ
  have hI := iSingularityEnvelope_isIModelPotential (atlasClosedFormToNative Γ).val
    (atlasClosedFormToNative Γ).property.1 (atlasClosedFormToNative Γ).property.2
    hn.1.hasSmoothLocalPotentials u hn
  have hp := sourceIVolume_add_kahler_pos ω hu hε
  have hP := singularityEnvelope_iSingularityEnvelope (atlasClosedFormToNative Γ).val
    (atlasClosedFormToNative Γ).property.1 (atlasClosedFormToNative Γ).property.2
    hn.1.hasSmoothLocalPotentials u hn
  have hqn := (isThetaPSH_iff_nativeThetaPotential _ _).mp (isThetaPSH_sourceIEnvelope hΓ)
  rw [sourceNativeAtlasForm_roundTrip] at hqn
  constructor
  · refine ⟨hqn, ?_, ?_⟩
    · simpa only [Γ, he, sourceNativeAtlasForm_roundTrip] using hP.symm
    · simpa only [sourceIVolume, sourcePotentialNonPluripolarMeasure,
        DiagonalMass.diagonalPotentialMass, Γ, sourceNativeAtlasForm_roundTrip] using hp
  · change IsIModelPotential _ (sourceIEnvelope Γ u)
    rw [he]
    simpa only [Γ, sourceNativeAtlasForm_roundTrip] using hI

omit [MeasurableSpace M] [BorelSpace M] in
private theorem perturbQ_mono (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {s t : NNReal} (hst : s ≤ t) :
    sourceIEnvelope (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (s : ℝ) • ω.form)) u ≤
    sourceIEnvelope (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (t : ℝ) • ω.form)) u := by
  let Γ (r : NNReal) := nativeClosedFormToAtlas (atlasClosedFormToNative θ + (r : ℝ) • ω.form)
  have hΓ r : (ofFixedModel n M).IsThetaPSH (Γ r) u := perturbedPSH ω hu r
  have hQ := (isThetaPSH_iff_nativeThetaPotential _ _).mp (isThetaPSH_sourceIEnvelope (hΓ s))
  rw [sourceNativeAtlasForm_roundTrip] at hQ
  have hQt : IsThetaPshPotential (atlasClosedFormToNative (Γ t)).val
      (sourceIEnvelope (Γ s) u) := by
    rw [sourceNativeAtlasForm_roundTrip]
    have hp := LocalPotentials.isThetaPshPotential_add_of_semipositive hQ
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr (by exact_mod_cast hst)))
    have he : atlasClosedFormToNative θ + (s : ℝ) • ω.form +
        ((t : ℝ) - (s : ℝ)) • ω.form = atlasClosedFormToNative θ + (t : ℝ) • ω.form := by module
    exact (congrArg (fun α : ClosedRealOneOneForm n M =>
      IsThetaPshPotential α.val (sourceIEnvelope (Γ s) u)) he).mp hp
  rw [sourceIEnvelope_eq_native (Γ t) u (hΓ t)]
  exact le_iSingularityEnvelope hQt (sourceIEnvelope_le_zero (Γ s) u)
    ((sourceIEquivalent_iff_native ⟨Γ s, hΓ s⟩
      ⟨Γ s, isThetaPSH_sourceIEnvelope (hΓ s)⟩).mp (sourceIEquivalent_iEnvelope (hΓ s))).symm

/-- The actual decreasing perturbed I-envelopes have the literal original
I-envelope as infimum, without positive original or limiting mass. -/
theorem sourceIEnvelope_kahlerPerturbation_iInf (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (ε : ℕ → NNReal)
    (hεpos : ∀ j, 0 < ε j) (hεanti : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    (⨅ j, sourceIEnvelope (nativeClosedFormToAtlas
      (atlasClosedFormToNative θ + (ε j : ℝ) • ω.form)) u) = sourceIEnvelope θ u := by
  let Γ j := nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε j : ℝ) • ω.form)
  let v j := sourceIEnvelope (Γ j) u
  have hp j : 0 < (ε j : ℝ) := by exact_mod_cast hεpos j
  have hm j := perturbQ_models ω hu (ε j) (hp j)
  have ha : Antitone v := fun _ _ hij => perturbQ_mono ω hu (hεanti hij)
  have hlim : Tendsto (fun j => (ε j : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hεlim
  have hI := VaryingBackgroundIModelGlobalClass.isIModelPotential_iInf_varying_models
    ω (atlasClosedFormToNative θ) hp
    (fun _ _ hij => by exact_mod_cast hεanti hij) hlim
    (fun j => (hm j).1) (fun j => (hm j).2) ha
  have hlow : sourceIEnvelope θ u ≤ ⨅ j, v j := by
    apply le_iInf
    intro j
    have h := perturbQ_mono ω hu (show (0 : NNReal) ≤ ε j from zero_le)
    have ht : nativeClosedFormToAtlas (atlasClosedFormToNative θ) = θ := by cases θ; rfl
    simpa only [NNReal.coe_zero, zero_smul, add_zero, ht] using h
  have hΓ0 : (ofFixedModel n M).IsThetaPSH (Γ 0) u := perturbedPSH ω hu (ε 0)
  have hv0 := (isThetaPSH_iff_nativeThetaPotential _ _).mp (isThetaPSH_sourceIEnvelope hΓ0)
  have horder : IOrderOnManifold (n := n) (⨅ j, v j) u :=
    (iOrderOnManifold_of_le hv0.1.quasiPlurisubharmonic (iInf_le v 0)).trans
      ((sourceIEquivalent_iff_native ⟨Γ 0, hΓ0⟩
        ⟨Γ 0, isThetaPSH_sourceIEnvelope hΓ0⟩).mp (sourceIEquivalent_iEnvelope hΓ0)).2
  apply le_antisymm
  · change (⨅ j, v j) ≤ sourceIEnvelope θ u
    rw [hI.envelope_eq, sourceIEnvelope_eq_native θ u hu]
    exact ActualIEnvelopeOrderInfimum.iSingularityEnvelope_le_of_iOrderOnManifold
      (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) horder
  · exact hlow

/-- The actual constant-tuple general volume equals the original single
I-volume in every dimension, even when the original I-volume vanishes. -/
theorem sourceGeneralMixedIVolume_diagonal (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceGeneralMixedIVolume ω (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu) =
      sourceIVolume θ u hu := by
  let ε : ℕ → NNReal := fun j => (1 / 2 : NNReal) ^ j
  have hp j : 0 < ε j := by dsimp only [ε]; positivity
  have ha : Antitone ε := by
    intro i j hij
    exact pow_le_pow_of_le_one (by positivity : (0 : NNReal) ≤ 1 / 2)
      (by norm_num : (1 / 2 : NNReal) ≤ 1) hij
  have hl : Tendsto ε atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  let Γ j := nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε j : ℝ) • ω.form)
  let v j := sourceIEnvelope (Γ j) u
  have hpos j : 0 < (ε j : ℝ) := by exact_mod_cast hp j
  have hm j := (perturbQ_models ω hu (ε j) (hpos j)).1
  have hanti : Antitone v := fun _ _ hij => perturbQ_mono ω hu (ha hij)
  have hlr : Tendsto (fun j => (ε j : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hl
  have hinf : (⨅ j, v j) = sourceIEnvelope θ u :=
    sourceIEnvelope_kahlerPerturbation_iInf ω hu ε hp ha hl
  have hmass := IEnvelopeVaryingBackgroundModelInfimum.tendsto_diagonalPotentialMass_iInf_varying_models
    ω (atlasClosedFormToNative θ) hpos
    (fun _ _ hij => by exact_mod_cast ha hij) hlr hm hanti
  have hmass' : Tendsto (fun j => sourceMixedIVolumeKahlerPerturbation ω
      (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu) (ε j)) atTop
      (𝓝 (sourceIVolume θ u hu)) := by
    have he j : sourceMixedIVolumeKahlerPerturbation ω
        (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu) (ε j) =
        DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ + (ε j : ℝ) • ω.form)
          (v j) (hm j).plurisubharmonic := by
      change sourceEnvelopeMixedIVolume (fun _ : Fin n => Γ j) (fun _ => u)
        (fun _ => perturbedPSH ω hu (ε j)) = _
      rw [sourceEnvelopeMixedIVolume_diagonal]
      simp only [sourceIVolume, sourcePotentialNonPluripolarMeasure, Γ,
        sourceNativeAtlasForm_roundTrip, DiagonalMass.diagonalPotentialMass, v]
    have ht : DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ)
        (⨅ j, v j) (IEnvelopeVaryingBackgroundModelInfimum.isThetaPshPotential_iInf_varying_models
          ω (atlasClosedFormToNative θ) (fun _ _ hij => by exact_mod_cast ha hij)
          hlr hm hanti) = sourceIVolume θ u hu := by
      simp only [hinf, sourceIVolume, sourcePotentialNonPluripolarMeasure,
        DiagonalMass.diagonalPotentialMass]
    rw [ht] at hmass
    exact hmass.congr (fun j => (he j).symm)
  have hlright : Tendsto ε atTop (𝓝[>] (0 : NNReal)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall hp⟩
  exact tendsto_nhds_unique
    ((sourceGeneralMixedIVolume_tendsto ω (fun _ : Fin n => θ) (fun _ => u)
      (fun _ => hu)).comp hlright) hmass'

end SGPT.PSH.VariableComplexAtlas
