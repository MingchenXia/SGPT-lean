import SGPT.Foundations.Analysis.Pending.ActualGlobalizedMixedCapacityConvergence
import SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedIntegrals
import SGPT.Foundations.Analysis.Pending.ActualLocalMixedIntegralSlots

set_option autoImplicit false

/-! # Actual local mixed weak continuity from relative capacity

The synchronized global lift produces every masked weak limit. Genuine
finite slot differences remove its fixed smooth local potential, and true
homogeneity removes its positive scale. No local weak certificate is an
input of the public theorem. Unbounded non-pluripolar lower semicontinuity
remains separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualLocalMixedCapacityContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere GlobalNonPluripolar BedfordTaylor MixedMongeAmpere
  GlobalSlotStokes ChartPartition PatchLocalBoundedMeasure LocalBedfordTaylorCalculus

noncomputable section

variable {n : ℕ}

private def processed (S : Finset (Fin n)) (m : Fin n → Bool)
    (a p : Fin n → ComplexModel n → ℝ) (i : Fin n) (z : ComplexModel n) : ℝ :=
  if i ∈ S then a i z else if m i then a i z + p i z else p i z

private theorem processed_psh {Q : Opens (ComplexModel n)}
    {a p : Fin n → ComplexModel n → ℝ} (ha : IsLocallyBoundedMixedPshOn Q a)
    (hp : IsLocallyBoundedMixedPshOn Q p) (S : Finset (Fin n)) (m : Fin n → Bool) :
    IsLocallyBoundedMixedPshOn Q (processed S m a p) := by
  classical
  intro i
  change IsLocallyBoundedPshOn Q (fun z =>
    if i ∈ S then a i z else if m i then a i z + p i z else p i z)
  by_cases hi : i ∈ S
  · simpa only [processed, if_pos hi] using ha i
  · cases hm : m i
    · simpa only [processed, if_neg hi, hm, Bool.false_eq_true, ↓reduceIte] using hp i
    · simpa only [processed, if_neg hi, hm, ↓reduceIte] using
        isLocallyBoundedPshOn_add (ha i) (hp i)

private theorem integral_tuple_congr {Q : Opens (ComplexModel n)}
    {a b : Fin n → ComplexModel n → ℝ}
    (ha : IsLocallyBoundedMixedPshOn Q a) (hb : IsLocallyBoundedMixedPshOn Q b)
    (hab : a = b) (h : ComplexModel n → ℝ) :
    (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q a ha) =
      ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q b hb := by
  subst b
  rfl

private theorem remove_fixed_shift {Q : Opens (ComplexModel n)} {I : Type*}
    (F : Filter I) {u : I → Fin n → ComplexModel n → ℝ}
    {v p : Fin n → ComplexModel n → ℝ}
    (hu : ∀ j, IsLocallyBoundedMixedPshOn Q (u j))
    (hv : IsLocallyBoundedMixedPshOn Q v) (hp : IsLocallyBoundedMixedPshOn Q p)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ Q)
    (hlim : ∀ m : Fin n → Bool, Tendsto
      (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed ∅ m (u j) p)
        (processed_psh (hu j) hp ∅ m)) F
      (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed ∅ m v p)
        (processed_psh hv hp ∅ m)))) :
    Tendsto (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (u j) (hu j)) F
      (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q v hv)) := by
  classical
  have hrec (S : Finset (Fin n)) : ∀ m : Fin n → Bool, Tendsto
      (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed S m (u j) p)
        (processed_psh (hu j) hp S m)) F
      (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed S m v p)
        (processed_psh hv hp S m))) := by
    induction S using Finset.induction_on with
    | empty => exact hlim
    | @insert k S hkS ih =>
      intro m
      have hsum (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn Q a) :
          (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k true) a p)
            (processed_psh ha hp S (Function.update m k true))) =
          (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed (insert k S) m a p)
            (processed_psh ha hp (insert k S) m)) +
          ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k false) a p)
            (processed_psh ha hp S (Function.update m k false)) := by
        obtain ⟨hA, hB, hSum, hidentity⟩ := ActualLocalMixedIntegralSlots.integral_slot_add
          (processed_psh ha hp (insert k S) m) k (ha k) (hp k)
        have eA : Function.update (processed (insert k S) m a p) k (a k) =
            processed (insert k S) m a p := by
          funext i z
          by_cases hi : i = k
          · subst i
            simp [processed]
          · simp [Function.update_of_ne hi]
        have eB : Function.update (processed (insert k S) m a p) k (p k) =
            processed S (Function.update m k false) a p := by
          funext i z
          by_cases hi : i = k
          · subst i
            simp [processed, hkS]
          · simp [processed, hi]
        have eSum : Function.update (processed (insert k S) m a p) k (fun z => a k z + p k z) =
            processed S (Function.update m k true) a p := by
          funext i z
          by_cases hi : i = k
          · subst i
            simp [processed, hkS]
          · simp [processed, hi]
        exact (integral_tuple_congr hSum
          (processed_psh ha hp S (Function.update m k true)) eSum h).symm.trans
          ((hidentity h hc hk ht).trans (congrArg₂ (fun x y : ℝ => x + y)
            (integral_tuple_congr hA (processed_psh ha hp (insert k S) m) eA h)
            (integral_tuple_congr hB (processed_psh ha hp S (Function.update m k false)) eB h)))
      have heq (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn Q a) :
          (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed (insert k S) m a p)
            (processed_psh ha hp (insert k S) m)) =
          (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k true) a p)
            (processed_psh ha hp S (Function.update m k true))) -
          ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k false) a p)
            (processed_psh ha hp S (Function.update m k false)) := by
        linarith [hsum a ha]
      have hl := (ih (Function.update m k true)).sub (ih (Function.update m k false))
      exact (hl.congr (fun j => (heq (u j) (hu j)).symm)).trans
        (by rw [← heq v hv])
  have ep (a : Fin n → ComplexModel n → ℝ) :
      processed Finset.univ (fun _ => true) a p = a := by
    funext i z
    simp [processed]
  simpa only [ep] using hrec Finset.univ (fun _ => true)

private theorem integral_smaller_domain {D Q : Opens (ComplexModel n)}
    {a : Fin n → ComplexModel n → ℝ} (ha : IsLocallyBoundedMixedPshOn D a)
    (hQD : Q ≤ D) {h : ComplexModel n → ℝ} (ht : tsupport h ⊆ Q) :
    (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D a ha) =
      ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q a
        (fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (ha i) hQD) := by
  have hlim : IsBTLimit D a (canonicalMixedBedfordTaylorMeasure D a ha) :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec D a ha)
  have hμ : (canonicalMixedBedfordTaylorMeasure D a ha).restrict (Q : Set (ComplexModel n)) =
      canonicalMixedBedfordTaylorMeasure Q a
        (fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (ha i) hQD) :=
    (hlim.restrict_opens hQD).unique (IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (canonicalMixedBedfordTaylorMeasure_spec Q a
        (fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (ha i) hQD)))
  calc
    _ = ∫ z in Q, h z ∂canonicalMixedBedfordTaylorMeasure D a ha :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
        image_eq_zero_of_notMem_tsupport (fun hh => hz (ht hh)))).symm
    _ = _ := by rw [hμ]

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

private theorem core_integral_transport (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {O : Set M} (hO : IsOpen O)
    (hOS : O ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))
    (Q : Opens (ComplexModel n))
    (hQ : (Q : Set (ComplexModel n)) = (D : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' O)
    {w : Fin n → M → EReal} (hw : ∀ i, IsThetaPshPotential omega.form.val (w i))
    (hb : ∀ i, IsBoundedPotentialOn (w i)
      (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n))))
    (f : Fin n → ComplexModel n → ℝ)
    (hcore : ∀ i x, x ∈ O → w i x = ((f i (e.val x) : ℝ) : EReal))
    (hG : IsLocallyBoundedMixedPshOn Q (fun i z => f i z + ρ z))
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ Q) :
    Continuous (chartExtend e h) ∧
      (∫ x, chartExtend e h x ∂globalMixedMeasure (fun _ : Fin n => omega.form) w
        (fun i => (hw i).1)) =
      ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (fun i z => f i z + ρ z) hG := by
  let J := ThetaCapacityChart.diagSlotChart omega.form e D hDt ρ hρ
  obtain ⟨Q', hQ', hG', hidentity⟩ :=
    ActualChartCoreMixedIntegrals.exists_core_mixed_integral_identity J hw hb hO hOS f hcore
  have hQQ : Q' = Q := SetLike.coe_injective (hQ'.trans hQ.symm)
  subst Q'
  exact hidentity h hc hk ht

/-- Actual local capacity convergence of normalized PSH tuples produces
ordinary canonical mixed weak convergence, without an incoming weak certificate. -/
theorem tendsto_integral_of_relative_capacity (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {u : ℕ → Fin n → ComplexModel n → ℝ} {v : Fin n → ComplexModel n → ℝ}
    (hu : ∀ j, IsLocallyBoundedMixedPshOn D (u j))
    (hv : IsLocallyBoundedMixedPshOn D v)
    (huB : ∀ j i z, z ∈ D → -1 ≤ u j i z ∧ u j i z ≤ 0)
    (hvB : ∀ i z, z ∈ D → -1 ≤ v i z ∧ v i z ≤ 0)
    (hcap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V {z | z ∈ T ∧ a < |u j i z - v i z|})
        atTop (𝓝 0))
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ K) :
    Tendsto (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j))
      atTop (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D v hv)) := by
  classical
  obtain ⟨δ, hδ, O, lift, hO, hKO, hOS, hPSH, hWeak⟩ :=
    ActualGlobalizedMixedCapacityConvergence.exists_synchronized_mixed_weak_lift
      omega e hDt hρ hK hKD
  let Q : Opens (ComplexModel n) :=
    ⟨(D : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' O,
      (e.val.symm.continuousOn.mono hDt).isOpen_inter_preimage D.isOpen hO⟩
  have hQD : Q ≤ D := inter_subset_left
  have hKQ : K ⊆ (Q : Set (ComplexModel n)) :=
    fun z hz => ⟨hKD hz, hKO ⟨z, hz, rfl⟩⟩
  have htQ : tsupport h ⊆ Q := ht.trans hKQ
  let huQ : ∀ j, IsLocallyBoundedMixedPshOn Q (u j) :=
    fun j i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hu j i) hQD
  let hvQ : IsLocallyBoundedMixedPshOn Q v :=
    fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hv i) hQD
  choose hδu hIu using fun j => ActualLocalMixedIntegralSlots.integral_positive_scale (huQ j) hδ
  obtain ⟨hδv, hIv⟩ := ActualLocalMixedIntegralSlots.integral_positive_scale hvQ hδ
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hρpsh : PlurisubharmonicOn (fun z => (ρ z : EReal)) (D : Set (ComplexModel n)) := by
    simpa [chartFunction] using
      BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hzero.1 e hρ
  let p : Fin n → ComplexModel n → ℝ := fun _ z => ρ z - δ
  have hpD : IsLocallyBoundedMixedPshOn D p := by
    intro i
    apply isLocallyBoundedPshOn_of_continuousOn
    · simpa only [p, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using hρpsh.add_const (-δ)
    · exact hρ.2.2.1.continuousOn.sub continuousOn_const
  let hpQ : IsLocallyBoundedMixedPshOn Q p :=
    fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hpD i) hQD
  have hmasked : ∀ m : Fin n → Bool, Tendsto
      (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q
        (processed ∅ m (fun i z => δ * u j i z) p) (processed_psh (hδu j) hpQ ∅ m))
      atTop (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q
        (processed ∅ m (fun i z => δ * v i z) p) (processed_psh hδv hpQ ∅ m))) := by
    intro m
    let masked (a : Fin n → ComplexModel n → ℝ) : Fin n → ComplexModel n → ℝ :=
      fun i z => if m i then a i z else 0
    have hmaskedPSH (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn D a) :
        IsLocallyBoundedMixedPshOn D (masked a) := by
      intro i
      cases hm : m i
      · change IsLocallyBoundedPshOn D (fun z => if m i then a i z else 0)
        simp only [hm, Bool.false_eq_true, ↓reduceIte]
        exact isLocallyBoundedPshOn_of_abs_le
          (fun z _ => plurisubharmonicAt_const 0 EReal.zero_ne_top z) (C := 0)
          (fun _ _ => by simp)
      · change IsLocallyBoundedPshOn D (fun z => if m i then a i z else 0)
        simpa only [hm, ↓reduceIte] using ha i
    have hmaskedBox (a : Fin n → ComplexModel n → ℝ)
        (ha : ∀ i z, z ∈ D → -1 ≤ a i z ∧ a i z ≤ 0) :
        ∀ i z, z ∈ D → -1 ≤ masked a i z ∧ masked a i z ≤ 0 := by
      intro i z hz
      cases hm : m i
      · simp [masked, hm]
      · simpa only [masked, hm, ↓reduceIte] using ha i z hz
    have hmaskedCap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
        IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a → Tendsto
        (fun j => relCapacity V {z | z ∈ T ∧ a < |masked (u j) i z - masked v i z|})
        atTop (𝓝 0) := by
      intro i V hVD T hT hTV a ha
      cases hm : m i
      · simp [masked, hm, not_lt_of_ge ha.le]
      · simpa only [masked, hm, ↓reduceIte] using hcap i V hVD T hT hTV a ha
    obtain ⟨hW, hV, hlimits⟩ := hWeak (fun j => masked (u j)) (masked v)
      (fun j i => hmaskedPSH (u j) (hu j) i) (hmaskedPSH v hv)
      (fun j => hmaskedBox (u j) (huB j)) (hmaskedBox v hvB) hmaskedCap
    have ec (a : Fin n → ComplexModel n → ℝ) :
        (fun i z => δ * masked a i z - δ + ρ z) =
          processed ∅ m (fun i z => δ * a i z) p := by
      funext i z
      cases hm : m i <;> simp [masked, processed, hm, p] <;> ring
    let hGU (j : ℕ) : IsLocallyBoundedMixedPshOn Q
        (fun i z => δ * masked (u j) i z - δ + ρ z) :=
      (ec (u j)).symm ▸ processed_psh (hδu j) hpQ ∅ m
    let hGV : IsLocallyBoundedMixedPshOn Q
        (fun i z => δ * masked v i z - δ + ρ z) :=
      (ec v).symm ▸ processed_psh hδv hpQ ∅ m
    have hTU (j : ℕ) := core_integral_transport omega e hDt hρ hO hOS Q rfl (hW j)
      (fun i => ⟨-1, 0, fun x _ =>
        (hPSH (masked (u j) i) (hmaskedPSH (u j) (hu j) i)
          (hmaskedBox (u j) (huB j) i)).2.1 x⟩)
      (fun i z => δ * masked (u j) i z - δ)
      (fun i => (hPSH (masked (u j) i) (hmaskedPSH (u j) (hu j) i)
        (hmaskedBox (u j) (huB j) i)).2.2) (hGU j) hc hk htQ
    have hTV := core_integral_transport omega e hDt hρ hO hOS Q rfl hV
      (fun i => ⟨-1, 0, fun x _ =>
        (hPSH (masked v i) (hmaskedPSH v hv i) (hmaskedBox v hvB i)).2.1 x⟩)
      (fun i z => δ * masked v i z - δ)
      (fun i => (hPSH (masked v i) (hmaskedPSH v hv i) (hmaskedBox v hvB i)).2.2)
      hGV hc hk htQ
    have hl : Tendsto (fun j => ∫ x, chartExtend e h x
        ∂globalMixedMeasure (fun _ : Fin n => omega.form)
          (fun i => lift (masked (u j) i)) (fun i => (hW j i).1)) atTop
        (𝓝 (∫ x, chartExtend e h x ∂globalMixedMeasure (fun _ : Fin n => omega.form)
          (fun i => lift (masked v i)) (fun i => (hV i).1))) :=
      hlimits ⟨chartExtend e h, hTV.1⟩
    rw [hTV.2] at hl
    have hl' := hl.congr (fun j => (hTU j).2)
    rw [integral_tuple_congr hGV (processed_psh hδv hpQ ∅ m) (ec v) h] at hl'
    exact hl'.congr (fun j =>
      integral_tuple_congr (hGU j) (processed_psh (hδu j) hpQ ∅ m) (ec (u j)) h)
  have hscaled := remove_fixed_shift atTop hδu hδv hpQ hc hk htQ hmasked
  have hreal : Tendsto (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (u j) (huQ j))
      atTop (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q v hvQ)) := by
    have hh := hscaled.div_const (δ ^ n)
    simpa only [hIu, hIv, mul_div_cancel_left₀ _ (pow_ne_zero n hδ.ne')] using hh
  rw [integral_smaller_domain hv hQD htQ]
  exact hreal.congr (fun j => (integral_smaller_domain (hu j) hQD htQ).symm)

end
end SGPT.Foundations.Analysis.Pending.ActualLocalMixedCapacityContinuity
