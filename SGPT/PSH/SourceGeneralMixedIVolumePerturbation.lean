import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra
import SGPT.PSH.SourceTestCurveScalingProjection

/-!
# Class-uniform Kähler perturbation of the general mixed I-volume

The constant is selected from the actual smooth Bott–Chern classes before
all original representatives and potentials. Finite slot telescoping uses
the existing all-input addition and nonnegative scaling laws, including zero
masses, poles, dimension zero and both endpoints of the parameter interval.
Blueprint: `source_general_mixed_ivolume_perturbation.tex`.
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

private abbrev PSH (θ : ClosedRealOneOneForm n M) (u : M → EReal) : Prop :=
  (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) u

private abbrev V (ω : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (u : Fin n → M → EReal) (hu : ∀ i, PSH (θ i) (u i)) : ENNReal :=
  sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (θ i)) u hu

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem pshAdd {θ η : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : PSH θ u) (hv : PSH η v) : PSH (θ + η) (fun x => u x + v x) := by
  simpa only [sourceNativeAtlasForm_roundTrip] using sourceIndependentSum_thetaPSH hu hv

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem pshZero {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) :
    PSH θ (fun _ => (0 : EReal)) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact (LocalPotentials.isThetaPshPotential_zero_iff θ).mpr hθ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem pshBump (ω : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : PSH θ u) {t : ℝ} (ht : 0 ≤ t) : PSH (θ + t • ω.form) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    (by simpa only [sourceNativeAtlasForm_roundTrip] using
      (isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ht)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem updPSH {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, PSH (θ i) (u i)) (a : Fin n) {η : ClosedRealOneOneForm n M}
    {v : M → EReal} (hv : PSH η v) :
    ∀ i, PSH (Function.update θ a η i) (Function.update u a v i) := by
  intro i
  by_cases hi : i = a
  · subst i; simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hi] using hu i

omit [BorelSpace M] in
private theorem vcongr (ω : KahlerBackground n M)
    {θ η : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}
    (hu : ∀ i, PSH (θ i) (u i)) (hv : ∀ i, PSH (η i) (v i))
    (hθ : θ = η) (huv : u = v) : V ω θ u hu = V ω η v hv := by
  subst η; subst v; rfl

private theorem vaddSlot (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, PSH (θ i) (u i)) (a : Fin n) (η : ClosedRealOneOneForm n M)
    (v : M → EReal) (hv : PSH η v) :
    V ω (Function.update θ a (θ a + η)) (Function.update u a (fun x => u a x + v x))
      (updPSH hu a (pshAdd (hu a) hv)) = V ω θ u hu +
        V ω (Function.update θ a η) (Function.update u a v) (updPSH hu a hv) := by
  have h := sourceGeneralMixedIVolume_add_slot ω
    (fun i => nativeClosedFormToAtlas (θ i)) u hu a (nativeClosedFormToAtlas η) v hv
  have he : Function.update (fun i => nativeClosedFormToAtlas (θ i)) a
      (nativeClosedFormToAtlas (atlasClosedFormToNative (nativeClosedFormToAtlas (θ a)) +
        atlasClosedFormToNative (nativeClosedFormToAtlas η))) =
      fun i => nativeClosedFormToAtlas (Function.update θ a (θ a + η) i) := by
    funext i
    by_cases hi : i = a
    · subst i; simp only [Function.update_self, sourceNativeAtlasForm_roundTrip]
    · simp only [Function.update_of_ne hi]
  have hr : Function.update (fun i => nativeClosedFormToAtlas (θ i)) a
      (nativeClosedFormToAtlas η) =
      fun i => nativeClosedFormToAtlas (Function.update θ a η i) := by
    funext i
    by_cases hi : i = a
    · subst i; simp only [Function.update_self]
    · simp only [Function.update_of_ne hi]
  simpa only [he, hr] using h

private theorem vaddMono (ω : KahlerBackground n M)
    (θ η : Fin n → ClosedRealOneOneForm n M) (u v : Fin n → M → EReal)
    (hu : ∀ i, PSH (θ i) (u i)) (hv : ∀ i, PSH (η i) (v i)) :
    V ω θ u hu ≤ V ω (fun i => θ i + η i) (fun i x => u i x + v i x)
      (fun i => pshAdd (hu i) (hv i)) := by
  classical
  let Θ (s : Finset (Fin n)) i := if i ∈ s then θ i + η i else θ i
  let w (s : Finset (Fin n)) i x := if i ∈ s then u i x + v i x else u i x
  have hw s i : PSH (Θ s i) (w s i) := by
    by_cases hi : i ∈ s
    · simpa only [Θ, w, if_pos hi] using pshAdd (hu i) (hv i)
    · simpa only [Θ, w, if_neg hi] using hu i
  have hmono s : V ω θ u hu ≤ V ω (Θ s) (w s) (hw s) := by
    induction s using Finset.induction_on with
    | empty =>
      exact (vcongr ω hu (hw ∅) (by funext i; simp [Θ])
        (by funext i x; simp [w])).le
    | @insert a s ha ih =>
      have hadd := vaddSlot ω (Θ s) (w s) (hw s) a (η a) (v a) (hv a)
      have eθ : Function.update (Θ s) a (Θ s a + η a) = Θ (insert a s) := by
        funext i
        by_cases hi : i = a
        · subst i; simp [Θ, ha]
        · simp [Θ, Finset.mem_insert, hi]
      have ew : Function.update (w s) a (fun x => w s a x + v a x) = w (insert a s) := by
        funext i x
        by_cases hi : i = a
        · subst i; simp [w, ha]
        · simp [w, Finset.mem_insert, hi]
      exact ih.trans ((le_self_add.trans_eq hadd.symm).trans_eq
        (vcongr ω (updPSH (hw s) a (pshAdd (hw s a) (hv a)))
          (hw (insert a s)) eθ ew))
  simpa only [Θ, w, Finset.mem_univ, if_true] using hmono Finset.univ

/-- Addition of independent genuine positive currents increases the actual
all-input general mixed volume; no individual I-volume is assumed positive. -/
theorem sourceGeneralMixedIVolume_mono_independent_add (ω : KahlerBackground n M)
    (θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u v : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i)) :
    sourceGeneralMixedIVolume ω θ u hu ≤ sourceGeneralMixedIVolume ω
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) +
        atlasClosedFormToNative (η i))) (fun i x => u i x + v i x)
      (fun i => sourceIndependentSum_thetaPSH (hu i) (hv i)) := by
  have h := vaddMono ω (fun i => atlasClosedFormToNative (θ i))
    (fun i => atlasClosedFormToNative (η i)) u v
    (fun i => by simpa only [PSH, sourceAtlasNativeForm_roundTrip] using hu i)
    (fun i => by simpa only [PSH, sourceAtlasNativeForm_roundTrip] using hv i)
  simpa only [V, sourceAtlasNativeForm_roundTrip] using h

private theorem iOrderZero (ω : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : PSH θ u) : sourceIOrder (ofFixedModel n M) u (fun _ => 0) := by
  have h0 := pshZero ω.isSemipositive
  have hmore : SGPT.PSH.SingularityLE u (fun _ => 0) := by
    cases isEmpty_or_nonempty M with
    | inl h => exact ⟨0, fun x _ => (h.false x).elim⟩
    | inr h =>
      obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu).exists_global_upper_bound
      exact ⟨C, fun x _ => by simpa only [zero_add] using hC x⟩
  exact (sourceComparison_chain ω ⟨_, hu⟩ ⟨_, h0⟩ hmore).2

private def classRep (α : RealBottChern n M) : ClosedRealOneOneForm n M :=
  Quotient.out α

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem classRep_class (α : RealBottChern n M) :
    RealBottChern.ofRepresentative (classRep α) = α := Quotient.out_eq α

private theorem classBound (ω : KahlerBackground n M) (α : Fin n → RealBottChern n M) :
    ∃ B : ENNReal, B < ⊤ ∧
      ∀ (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
        (hu : ∀ i, PSH (θ i) (u i)),
        (∀ i, RealBottChern.ofRepresentative (θ i) = α i) →
        V ω (fun i => θ i + ω.form) u (fun i => by
          simpa only [one_smul] using pshBump ω (hu i) zero_le_one) ≤ B := by
  classical
  obtain ⟨D, hD, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul ω
    (fun i => classRep (α i))
  let η i := classRep (α i) + (D + 1) • ω.form
  have hη i : (η i).val.IsSemipositive := by
    have hh : η i = (classRep (α i) + D • ω.form) + ω.form := by dsimp [η]; module
    rw [hh]
    intro e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
      using add_nonneg (hdom i e z hz v) (ω.isSemipositive e z hz v)
  let B := V ω η (fun _ _ => 0) (fun i => pshZero (hη i))
  refine ⟨B, sourceGeneralMixedIVolume_lt_top ω _ _ _, ?_⟩
  intro θ u hu hclass
  have hD0 : PSH (D • ω.form) (fun _ => (0 : EReal)) :=
    pshZero (KahlerDomination.isSemipositive_smul ω.isSemipositive hD.le)
  have hb i : PSH (θ i + ω.form) (u i) := by
    simpa only [one_smul] using pshBump ω (hu i) zero_le_one
  have hmono := vaddMono ω (fun i => θ i + ω.form) (fun _ => D • ω.form)
    u (fun _ _ => 0) hb (fun _ => hD0)
  have heq : (fun i => θ i + ω.form + D • ω.form) =
      fun i => θ i + (D + 1) • ω.form := by funext i; module
  have hbig i : PSH (θ i + (D + 1) • ω.form) (u i) :=
    pshBump ω (hu i) (by linarith)
  have hm : V ω (fun i => θ i + ω.form) u hb ≤
      V ω (fun i => θ i + (D + 1) • ω.form) u hbig :=
    hmono.trans_eq (vcongr ω _ _ heq (by simp only [add_zero]))
  apply hm.trans
  apply sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω
    (fun i => nativeClosedFormToAtlas (θ i + (D + 1) • ω.form))
    (fun i => nativeClosedFormToAtlas (η i)) u (fun _ _ => 0) hbig
    (fun i => pshZero (hη i))
  · intro i
    simp only [sourceNativeAtlasForm_roundTrip, η, RealBottChern.ofRepresentative_add,
      hclass i, classRep_class]
  · exact fun i => iOrderZero ω (hu i)

private def bump (ω : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (s : Finset (Fin n)) (t : ℝ) (i : Fin n) : ClosedRealOneOneForm n M :=
  if i ∈ s then θ i + t • ω.form else θ i

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem bumpPSH (ω : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, PSH (θ i) (u i)) (s : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, PSH (bump ω θ s t i) (u i) := by
  intro i
  by_cases hi : i ∈ s
  · simpa only [bump, if_pos hi] using pshBump ω (hu i) ht
  · simpa only [bump, if_neg hi] using hu i

private theorem coefficientBound (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, PSH (θ i) (u i)) (s : Finset (Fin n)) (a : Fin n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    V ω (Function.update (bump ω θ s t) a ω.form)
      (Function.update u a (fun _ => 0))
      (updPSH (bumpPSH ω hu s ht) a (pshZero ω.isSemipositive)) ≤
        V ω (fun i => θ i + ω.form) u (fun i => by
          simpa only [one_smul] using pshBump ω (hu i) zero_le_one) := by
  classical
  let Θ := Function.update (bump ω θ s t) a ω.form
  let w := Function.update u a (fun _ => (0 : EReal))
  have hw := updPSH (bumpPSH ω hu s ht) a (pshZero ω.isSemipositive)
  let η i := if i = a then θ i else (if i ∈ s then (1 - t) else 1) • ω.form
  let v i x := if i = a then u i x else (0 : EReal)
  have hv i : PSH (η i) (v i) := by
    by_cases hi : i = a
    · simpa only [η, v, if_pos hi] using hu i
    · have hc : 0 ≤ (if i ∈ s then (1 - t) else 1 : ℝ) := by
        split_ifs <;> linarith
      simpa only [η, v, if_neg hi] using
        pshZero (KahlerDomination.isSemipositive_smul ω.isSemipositive hc)
  have hmono := vaddMono ω Θ η w v hw hv
  have eθ : (fun i => Θ i + η i) = fun i => θ i + ω.form := by
    funext i
    by_cases hi : i = a
    · subst i; simp only [Θ, η, Function.update_self, if_true]; abel
    · simp only [Θ, η, Function.update_of_ne hi, if_neg hi, bump]
      split_ifs <;> module
  have ew : (fun i x => w i x + v i x) = u := by
    funext i x
    by_cases hi : i = a
    · subst i; simp [w, v]
    · simp [w, v, hi]
  exact hmono.trans_eq (vcongr ω _ _ eθ ew)

omit [BorelSpace M] in
private theorem sourceVcongr (ω : KahlerBackground n M)
    {θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i))
    (hθ : θ = η) (huv : u = v) :
    sourceGeneralMixedIVolume ω θ u hu = sourceGeneralMixedIVolume ω η v hv := by
  subst η; subst v; rfl

private theorem zeroSlotScale (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, PSH (θ i) (u i)) (a : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    V ω (Function.update θ a (t • ω.form)) (Function.update u a (fun _ => 0))
      (updPSH hu a (pshZero
        (KahlerDomination.isSemipositive_smul ω.isSemipositive ht))) =
      ENNReal.ofReal t * V ω (Function.update θ a ω.form)
        (Function.update u a (fun _ => 0)) (updPSH hu a (pshZero ω.isSemipositive)) := by
  have h := sourceGeneralMixedIVolume_nonneg_smul_slot ω
    (fun i => nativeClosedFormToAtlas (Function.update θ a ω.form i))
    (Function.update u a (fun _ => 0)) (updPSH hu a (pshZero ω.isSemipositive)) a ht
  have eθ : Function.update (fun i => nativeClosedFormToAtlas (Function.update θ a ω.form i)) a
      (nativeClosedFormToAtlas (t • atlasClosedFormToNative
        (nativeClosedFormToAtlas (Function.update θ a ω.form a)))) =
      fun i => nativeClosedFormToAtlas (Function.update θ a (t • ω.form) i) := by
    funext i
    by_cases hi : i = a
    · subst i; simp only [Function.update_self, sourceNativeAtlasForm_roundTrip]
    · simp only [Function.update_of_ne hi]
  have eu : Function.update (Function.update u a (fun _ => (0 : EReal))) a
      (fun x => (t : EReal) * Function.update u a (fun _ => (0 : EReal)) a x) =
      Function.update u a (fun _ => (0 : EReal)) := by
    simp only [Function.update_self, mul_zero, Function.update_idem]
  have hl : ∀ i, (ofFixedModel n M).IsThetaPSH
      (Function.update (fun i => nativeClosedFormToAtlas (Function.update θ a ω.form i)) a
        (nativeClosedFormToAtlas (t • atlasClosedFormToNative
          (nativeClosedFormToAtlas (Function.update θ a ω.form a)))) i)
      (Function.update (Function.update u a (fun _ => (0 : EReal))) a
        (fun x => (t : EReal) * Function.update u a (fun _ => (0 : EReal)) a x) i) := by
    intro i
    rw [congrFun eθ i, congrFun eu i]
    exact updPSH hu a (pshZero
      (KahlerDomination.isSemipositive_smul ω.isSemipositive ht)) i
  have he := sourceVcongr ω hl (updPSH hu a (pshZero
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ht))) eθ eu
  exact he.symm.trans h

private theorem bumpStep (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, PSH (θ i) (u i)) (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s)
    {t : ℝ} (ht : 0 ≤ t) :
    V ω (bump ω θ (insert a s) t) u (bumpPSH ω hu (insert a s) ht) =
      V ω (bump ω θ s t) u (bumpPSH ω hu s ht) + ENNReal.ofReal t *
        V ω (Function.update (bump ω θ s t) a ω.form)
          (Function.update u a (fun _ => 0))
          (updPSH (bumpPSH ω hu s ht) a (pshZero ω.isSemipositive)) := by
  classical
  have hzero : PSH (t • ω.form) (fun _ => (0 : EReal)) :=
    pshZero (KahlerDomination.isSemipositive_smul ω.isSemipositive ht)
  have hadd := vaddSlot ω (bump ω θ s t) u (bumpPSH ω hu s ht) a
    (t • ω.form) (fun _ => 0) hzero
  have eθ : Function.update (bump ω θ s t) a (bump ω θ s t a + t • ω.form) =
      bump ω θ (insert a s) t := by
    funext i
    by_cases hi : i = a
    · subst i; simp [bump, ha]
    · simp [bump, hi]
  have eu : Function.update u a (fun x => u a x + 0) = u := by simp
  have he := vcongr ω (updPSH (bumpPSH ω hu s ht) a
    (pshAdd (bumpPSH ω hu s ht a) hzero)) (bumpPSH ω hu (insert a s) ht) eθ eu
  exact he.symm.trans (hadd.trans (congrArg
    (fun z => V ω (bump ω θ s t) u (bumpPSH ω hu s ht) + z)
    (zeroSlotScale ω _ _ (bumpPSH ω hu s ht) a ht)))

private theorem bumpBound (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, PSH (θ i) (u i)) {B : ENNReal} (hB : B < ⊤)
    (hbase : V ω (fun i => θ i + ω.form) u (fun i => by
      simpa only [one_smul] using pshBump ω (hu i) zero_le_one) ≤ B)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (V ω θ u hu).toReal ≤
        (V ω (fun i => θ i + t • ω.form) u (fun i => pshBump ω (hu i) ht)).toReal ∧
      (V ω (fun i => θ i + t • ω.form) u (fun i => pshBump ω (hu i) ht)).toReal ≤
        (V ω θ u hu).toReal + (n : ℝ) * t * B.toReal := by
  classical
  have hfin (Θ : Fin n → ClosedRealOneOneForm n M) (w : Fin n → M → EReal)
      (hw : ∀ i, PSH (Θ i) (w i)) : V ω Θ w hw ≠ ⊤ :=
    (sourceGeneralMixedIVolume_lt_top ω _ _ _).ne
  have hsum (s : Finset (Fin n)) :
      (V ω θ u hu).toReal ≤ (V ω (bump ω θ s t) u (bumpPSH ω hu s ht)).toReal ∧
      (V ω (bump ω θ s t) u (bumpPSH ω hu s ht)).toReal ≤
        (V ω θ u hu).toReal + (s.card : ℝ) * t * B.toReal := by
    induction s using Finset.induction_on with
    | empty =>
      have he : bump ω θ ∅ t = θ := by funext i; simp [bump]
      have hv := vcongr ω (bumpPSH ω hu ∅ ht) hu he rfl
      simp only [hv, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero, le_refl, and_self]
    | @insert a s ha ih =>
      let Θ := Function.update (bump ω θ s t) a ω.form
      let w := Function.update u a (fun _ => (0 : EReal))
      have hw := updPSH (bumpPSH ω hu s ht) a (pshZero ω.isSemipositive)
      have hc : V ω Θ w hw ≤ B := (coefficientBound ω θ u hu s a ht ht1).trans hbase
      have hcr : (V ω Θ w hw).toReal ≤ B.toReal := ENNReal.toReal_mono hB.ne hc
      have hstep := bumpStep ω θ u hu s a ha ht
      have hreal : (V ω (bump ω θ (insert a s) t) u
          (bumpPSH ω hu (insert a s) ht)).toReal =
          (V ω (bump ω θ s t) u (bumpPSH ω hu s ht)).toReal + t * (V ω Θ w hw).toReal := by
        rw [hstep, ENNReal.toReal_add (hfin _ _ _)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin Θ w hw)),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
      constructor
      · rw [hreal]
        exact ih.1.trans (le_add_of_nonneg_right
          (mul_nonneg ht ENNReal.toReal_nonneg))
      · rw [hreal, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
        calc
          (V ω (bump ω θ s t) u (bumpPSH ω hu s ht)).toReal + t * (V ω Θ w hw).toReal ≤
              ((V ω θ u hu).toReal + (s.card : ℝ) * t * B.toReal) + t * B.toReal :=
            add_le_add ih.2 (mul_le_mul_of_nonneg_left hcr ht)
          _ = (V ω θ u hu).toReal + ((s.card : ℝ) + 1) * t * B.toReal := by ring
  have hbump : bump ω θ Finset.univ t = fun i => θ i + t • ω.form := by
    funext i
    simp [bump]
  have he := vcongr ω (bumpPSH ω hu Finset.univ ht) (fun i => pshBump ω (hu i) ht)
    hbump rfl
  have h := hsum Finset.univ
  rw [he] at h
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- The actual GENERAL mixed volume after Kähler perturbation. At zero this
is the general original value, with no identification of the separate direct
I-envelope formula at vanishing original I-volumes. -/
def sourceGeneralMixedIVolumeKahlerPerturbed (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) (t : ℝ) (ht : 0 ≤ t) : ENNReal :=
  V ω (fun i => atlasClosedFormToNative (θ i) + t • ω.form) u
    (fun i => pshBump ω (by simpa only [PSH, sourceAtlasNativeForm_roundTrip] using hu i) ht)

/-- A strictly positive perturbation constant is chosen from the actual
Bott–Chern classes BEFORE every original representative and potential. The
entire real parameter interval [0,1], zero masses and dimension zero remain. -/
theorem sourceGeneralMixedIVolume_class_uniform_perturbation_bound
    (ω : KahlerBackground n M) (α : Fin n → RealBottChern n M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
        (u : Fin n → M → EReal)
        (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)),
        (∀ i, RealBottChern.ofRepresentative (atlasClosedFormToNative (θ i)) = α i) →
        ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ 1 →
          0 ≤ (sourceGeneralMixedIVolumeKahlerPerturbed ω θ u hu t ht).toReal -
            (sourceGeneralMixedIVolume ω θ u hu).toReal ∧
          (sourceGeneralMixedIVolumeKahlerPerturbed ω θ u hu t ht).toReal -
            (sourceGeneralMixedIVolume ω θ u hu).toReal ≤ C * t := by
  obtain ⟨B, hB, hbound⟩ := classBound ω α
  refine ⟨1 + (n : ℝ) * B.toReal, by positivity, ?_⟩
  intro θ u hu hclass t ht ht1
  have hn i : PSH (atlasClosedFormToNative (θ i)) (u i) := by
    simpa only [PSH, sourceAtlasNativeForm_roundTrip] using hu i
  have h := bumpBound ω (fun i => atlasClosedFormToNative (θ i)) u hn hB
    (hbound _ u hn hclass) ht ht1
  have he : V ω (fun i => atlasClosedFormToNative (θ i)) u hn =
      sourceGeneralMixedIVolume ω θ u hu := by
    simp only [V, sourceAtlasNativeForm_roundTrip]
  change 0 ≤ (V ω (fun i => atlasClosedFormToNative (θ i) + t • ω.form) u _).toReal -
      (sourceGeneralMixedIVolume ω θ u hu).toReal ∧ _
  rw [he] at h
  constructor
  · linarith [h.1]
  · change (V ω (fun i => atlasClosedFormToNative (θ i) + t • ω.form) u _).toReal -
        (sourceGeneralMixedIVolume ω θ u hu).toReal ≤ (1 + (n : ℝ) * B.toReal) * t
    nlinarith [h.2]

end SGPT.PSH.VariableComplexAtlas
