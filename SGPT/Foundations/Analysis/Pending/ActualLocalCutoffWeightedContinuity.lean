import SGPT.Foundations.Analysis.Pending.ActualGlobalizedCutoffWeightedConvergence
import SGPT.Foundations.Analysis.Pending.ActualBoundedChartTestAlgebra
import SGPT.Foundations.Analysis.Pending.ActualLocalMixedIntegralSlots
import SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedIntegrals

set_option autoImplicit false

/-! # Actual ordinary local mixed convergence with cutoff weights

One true common lift produces all masked weighted limits. Actual compact
measurable-test slot differences remove its fixed smooth correction and
positive homogeneity removes its scale. Arbitrary off-domain ghosts are
not assumed measurable; actual weighted tests are internally measurable
from genuine local PSH zero extensions; the continuous test vanishes
outside the chart core. The final unbounded mass liminf remains separate.
-/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.ActualLocalCutoffWeightedContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.GlobalPotentialPatches
  GlobalNonPluripolar BedfordTaylor MixedMongeAmpere GlobalSlotStokes
  PatchLocalBoundedMeasure LocalBedfordTaylorCalculus ChartPartition

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
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKQ : K ⊆ Q)
    {h : I → ComplexModel n → ℝ} {h0 : ComplexModel n → ℝ}
    (hm : ∀ j, Measurable (h j)) (hm0 : Measurable h0)
    {C : ℝ} (hb : ∀ j z, |h j z| ≤ C) (hb0 : ∀ z, |h0 z| ≤ C)
    (hz : ∀ j z, z ∉ K → h j z = 0) (hz0 : ∀ z ∉ K, h0 z = 0)
    (hlim : ∀ m : Fin n → Bool, Tendsto
      (fun j => ∫ z, h j z ∂canonicalMixedBedfordTaylorMeasure Q (processed ∅ m (u j) p)
        (processed_psh (hu j) hp ∅ m)) F
      (𝓝 (∫ z, h0 z ∂canonicalMixedBedfordTaylorMeasure Q (processed ∅ m v p)
        (processed_psh hv hp ∅ m)))) :
    Tendsto (fun j => ∫ z, h j z ∂canonicalMixedBedfordTaylorMeasure Q (u j) (hu j)) F
      (𝓝 (∫ z, h0 z ∂canonicalMixedBedfordTaylorMeasure Q v hv)) := by
  classical
  have hrec (S : Finset (Fin n)) : ∀ m : Fin n → Bool, Tendsto
      (fun j => ∫ z, h j z ∂canonicalMixedBedfordTaylorMeasure Q (processed S m (u j) p)
        (processed_psh (hu j) hp S m)) F
      (𝓝 (∫ z, h0 z ∂canonicalMixedBedfordTaylorMeasure Q (processed S m v p)
        (processed_psh hv hp S m))) := by
    induction S using Finset.induction_on with
    | empty => exact hlim
    | @insert k S hkS ih =>
      intro m
      have hsum (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn Q a)
          (t : ComplexModel n → ℝ) (htm : Measurable t)
          (htb : ∀ z, |t z| ≤ C) (htz : ∀ z ∉ K, t z = 0) :
          (∫ z, t z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k true) a p)
            (processed_psh ha hp S (Function.update m k true))) =
          (∫ z, t z ∂canonicalMixedBedfordTaylorMeasure Q (processed (insert k S) m a p)
            (processed_psh ha hp (insert k S) m)) +
          ∫ z, t z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k false) a p)
            (processed_psh ha hp S (Function.update m k false)) := by
        obtain ⟨hA, hB, hSum, hidentity⟩ := ActualBoundedChartTestAlgebra.integral_slot_add_bounded
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
          (processed_psh ha hp S (Function.update m k true)) eSum t).symm.trans
          ((hidentity K hK hKQ t htm C htb htz).trans (congrArg₂ (fun x y : ℝ => x + y)
            (integral_tuple_congr hA (processed_psh ha hp (insert k S) m) eA t)
            (integral_tuple_congr hB (processed_psh ha hp S (Function.update m k false)) eB t)))
      have heq (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn Q a)
          (t : ComplexModel n → ℝ) (htm : Measurable t)
          (htb : ∀ z, |t z| ≤ C) (htz : ∀ z ∉ K, t z = 0) :
          (∫ z, t z ∂canonicalMixedBedfordTaylorMeasure Q (processed (insert k S) m a p)
            (processed_psh ha hp (insert k S) m)) =
          (∫ z, t z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k true) a p)
            (processed_psh ha hp S (Function.update m k true))) -
          ∫ z, t z ∂canonicalMixedBedfordTaylorMeasure Q (processed S (Function.update m k false) a p)
            (processed_psh ha hp S (Function.update m k false)) := by
        linarith [hsum a ha t htm htb htz]
      have hl := (ih (Function.update m k true)).sub (ih (Function.update m k false))
      exact (hl.congr (fun j => (heq (u j) (hu j) (h j) (hm j) (hb j) (hz j)).symm)).trans
        (by rw [← heq v hv h0 hm0 hb0 hz0])
  have ep (a : Fin n → ComplexModel n → ℝ) :
      processed Finset.univ (fun _ => true) a p = a := by
    funext i z
    simp [processed]
  simpa only [ep] using hrec Finset.univ (fun _ => true)

private theorem integral_smaller_domain {D Q : Opens (ComplexModel n)}
    {a : Fin n → ComplexModel n → ℝ} (ha : IsLocallyBoundedMixedPshOn D a)
    (hQD : Q ≤ D) {h : ComplexModel n → ℝ} (hz : ∀ z ∉ Q, h z = 0) :
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
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ = _ := by rw [hμ]


private theorem classifier_test_properties {D : Opens (ComplexModel n)}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (ht : tsupport h ⊆ K)
    {m : ℕ} {Φ : (Fin m → ℝ) → ℝ} (hΦ : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin m → ComplexModel n → ℝ,
      (∀ i, IsLocallyBoundedPshOn D (w i)) →
      (∀ i y, y ∈ D → -1 ≤ w i y ∧ w i y ≤ 0) →
      Measurable (fun y => h y * Φ (fun i => w i y)) ∧
      (∀ y, |h y * Φ (fun i => w i y)| ≤ C) ∧
      ∀ y ∉ K, h y * Φ (fun i => w i y) = 0 := by
  classical
  obtain ⟨H, hH⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin m → ℝ) 1).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max H 0 * max B 0, mul_nonneg (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro w hw hwB
  have hzero : ∀ y ∉ K, h y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun hz => hy (ht hz))
  have heq : (fun y => h y * Φ (fun i => w i y)) =
      (fun y => h y * Φ (fun i => (D : Set (ComplexModel n)).indicator (w i) y)) := by
    funext y
    by_cases hy : y ∈ D
    · simp only [Set.indicator_of_mem hy]
    · rw [hzero y (fun hyK => hy (hKD hyK))]
      simp
  have hm : Measurable (fun y => h y * Φ (fun i => w i y)) := by
    rw [heq]
    exact hc.measurable.mul (hΦ.measurable.comp (measurable_pi_lambda _ fun i =>
      LocalBedfordTaylorProducts.measurable_indicator_of_isLocallyBoundedPshOn (hw i)))
  refine ⟨hm, fun y => ?_, fun y hy => by rw [hzero y hy]; simp⟩
  by_cases hy : y ∈ K
  · have hmember : (fun i => w i y) ∈ closedBall (0 : Fin m → ℝ) 1 := by
      rw [mem_closedBall]
      apply (dist_pi_le_iff zero_le_one).mpr
      intro i
      have hh := hwB i y (hKD hy)
      simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using (abs_le.mpr ⟨hh.1, hh.2.trans (by norm_num)⟩)
    rw [abs_mul]
    exact mul_le_mul
      (by simpa only [Real.norm_eq_abs] using (hH y hy).trans (le_max_left H 0))
      (by simpa only [Real.norm_eq_abs] using (hB _ hmember).trans (le_max_left B 0))
      (abs_nonneg _) (le_max_right _ _)
  · rw [hzero y hy]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

private theorem lipschitz_reconstruct {m : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
      (fun y : Fin m → ℝ => fun i => δ⁻¹ * (y i + δ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (inv_nonneg.mpr hδ.le) dist_nonneg)).mpr
  intro i
  change |δ⁻¹ * (x i + δ) - δ⁻¹ * (y i + δ)| ≤ δ⁻¹ * dist x y
  have heq : δ⁻¹ * (x i + δ) - δ⁻¹ * (y i + δ) = δ⁻¹ * (x i - y i) := by ring
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using dist_le_pi_dist x y i)
    (inv_nonneg.mpr hδ.le)

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem continuous_chart_zero_extension (e : ComplexChart n M)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ e.val.target) : Continuous (chartExtend e h) := by
  have hK : IsCompact (e.val.symm '' tsupport h) :=
    hk.image_of_continuousOn (e.val.symm.continuousOn.mono ht)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ e.val.symm '' tsupport h
  · obtain ⟨z, hz, hzx⟩ := hx
    have hxS : x ∈ e.val.source := hzx ▸ e.val.map_target (ht hz)
    have hh : ContinuousAt (fun y => h (e.val y)) x :=
      hc.continuousAt.comp (e.val.continuousAt hxS)
    apply hh.congr
    filter_upwards [e.val.open_source.mem_nhds hxS] with y hy
    exact (chartExtend_of_mem hy).symm
  · apply continuousAt_const.congr
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact (chartExtend_eq_zero_of_notMem_image hy).symm

private theorem core_arbitrary_integral_transport (omega : KahlerBackground n M)
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
    {h : ComplexModel n → ℝ} (ht : Function.support h ⊆ Q) :
    (∫ x, chartExtend e h x ∂globalMixedMeasure (fun _ : Fin n => omega.form) w
      (fun i => (hw i).1)) =
      ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (fun i z => f i z + ρ z) hG := by
  let J := ThetaCapacityChart.diagSlotChart omega.form e D hDt ρ hρ
  obtain ⟨Q', hQ', hG', hidentity⟩ :=
    ActualBoundedChartTestAlgebra.exists_core_arbitrary_test_integrals J hw hb hO hOS f hcore
  have hQQ : Q' = Q := SetLike.coe_injective (hQ'.trans hQ.symm)
  subst Q'
  exact hidentity h ht

/-- Actual local PSH seed capacity convergence and mixed tuple capacity
convergence produce the true ordinary local cutoff-weighted integral limit. -/
theorem tendsto_integral_classifier_of_relative_capacity (omega : KahlerBackground n M)
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
    {m : ℕ} {w : ℕ → Fin m → ComplexModel n → ℝ}
    {z : Fin m → ComplexModel n → ℝ}
    (hw : ∀ j i, IsLocallyBoundedPshOn D (w j i))
    (hz : ∀ i, IsLocallyBoundedPshOn D (z i))
    (hwB : ∀ j i y, y ∈ D → -1 ≤ w j i y ∧ w j i y ≤ 0)
    (hzB : ∀ i y, y ∈ D → -1 ≤ z i y ∧ z i y ≤ 0)
    (hseedcap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V {y | y ∈ T ∧ a < |w j i y - z i y|})
        atTop (𝓝 0))
    {Φ : (Fin m → ℝ) → ℝ} {L : NNReal} (hΦ : LipschitzWith L Φ)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ K) :
    Tendsto (fun j => ∫ y, h y * Φ (fun i => w j i y)
      ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j))
      atTop (𝓝 (∫ y, h y * Φ (fun i => z i y) ∂canonicalMixedBedfordTaylorMeasure D v hv)) := by
  classical
  obtain ⟨δ, hδ, O, lift, hO, hKO, hOS, hPSH, hWeak⟩ :=
    ActualGlobalizedCutoffWeightedConvergence.exists_synchronized_classifier_weighted_lift
      omega e hDt hρ hK hKD
  let Q : Opens (ComplexModel n) :=
    ⟨(D : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' O,
      (e.val.symm.continuousOn.mono hDt).isOpen_inter_preimage D.isOpen hO⟩
  have hQD : Q ≤ D := inter_subset_left
  have hKQ : K ⊆ (Q : Set (ComplexModel n)) :=
    fun z hz => ⟨hKD hz, hKO ⟨z, hz, rfl⟩⟩
  let test (j : ℕ) (y : ComplexModel n) : ℝ := h y * Φ (fun i => w j i y)
  let test0 (y : ComplexModel n) : ℝ := h y * Φ (fun i => z i y)
  obtain ⟨C, _hC, htest⟩ := classifier_test_properties hK hKD hc ht hΦ.continuous
  have hm : ∀ j, Measurable (test j) := fun j => (htest (w j) (hw j) (hwB j)).1
  have hm0 : Measurable test0 := (htest z hz hzB).1
  have hb : ∀ j y, |test j y| ≤ C := fun j => (htest (w j) (hw j) (hwB j)).2.1
  have hb0 : ∀ y, |test0 y| ≤ C := (htest z hz hzB).2.1
  have hzero : ∀ j y, y ∉ K → test j y = 0 := fun j => (htest (w j) (hw j) (hwB j)).2.2
  have hzero0 : ∀ y ∉ K, test0 y = 0 := (htest z hz hzB).2.2
  have hsupport (j : ℕ) : Function.support (test j) ⊆ Q := by
    intro y hy
    by_contra hyQ
    exact hy (hzero j y (fun hyK => hyQ (hKQ hyK)))
  have hsupport0 : Function.support test0 ⊆ Q := by
    intro y hy
    by_contra hyQ
    exact hy (hzero0 y (fun hyK => hyQ (hKQ hyK)))
  let reconstruct : (Fin m → ℝ) → Fin m → ℝ := fun y i => δ⁻¹ * (y i + δ)
  let Ψ : (Fin m → ℝ) → ℝ := fun y => Φ (reconstruct y)
  have hΨ : LipschitzWith (L * ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩) Ψ :=
    hΦ.comp (lipschitz_reconstruct hδ)
  have hchartweight (a : Fin m → ComplexModel n → ℝ)
      (ha : ∀ i, IsLocallyBoundedPshOn D (a i))
      (haB : ∀ i y, y ∈ D → -1 ≤ a i y ∧ a i y ≤ 0) :
      chartExtend e (fun y => h y * Φ (fun i => a i y)) =
        fun x => chartExtend e h x * Ψ (fun i => (lift (a i) x).toReal) := by
    funext x
    by_cases hxS : x ∈ e.val.source
    · rw [chartExtend_of_mem hxS, chartExtend_of_mem hxS]
      by_cases hh : h (e.val x) = 0
      · simp only [hh, zero_mul]
      · have hxK := ht (subset_tsupport h hh)
        have hxO : x ∈ O := by
          have hx := hKO ⟨e.val x, hxK, e.val.left_inv hxS⟩
          exact hx
        have heq : reconstruct (fun i => (lift (a i) x).toReal) = fun i => a i (e.val x) := by
          funext i
          dsimp only [reconstruct]
          rw [(hPSH (a i) (ha i) (haB i)).2.2 x hxO, EReal.toReal_coe]
          field_simp [hδ.ne']
          ring
        change h (e.val x) * Φ (fun i => a i (e.val x)) =
          h (e.val x) * Φ (reconstruct (fun i => (lift (a i) x).toReal))
        rw [heq]
    · rw [chartExtend_of_notMem hxS, chartExtend_of_notMem hxS]
      simp only [zero_mul]
  have hglobaltest : Continuous (chartExtend e h) :=
    continuous_chart_zero_extension e hc hk (ht.trans (hKD.trans hDt))
  let huQ : ∀ j, IsLocallyBoundedMixedPshOn Q (u j) :=
    fun j i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hu j i) hQD
  let hvQ : IsLocallyBoundedMixedPshOn Q v :=
    fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hv i) hQD
  choose hδu hIu using fun j => ActualLocalMixedIntegralSlots.integral_positive_scale (huQ j) hδ
  obtain ⟨hδv, hIv⟩ := ActualLocalMixedIntegralSlots.integral_positive_scale hvQ hδ
  have hzeroPSH := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hρpsh : PlurisubharmonicOn (fun z => (ρ z : EReal)) (D : Set (ComplexModel n)) := by
    simpa [chartFunction] using
      BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hzeroPSH.1 e hρ
  let p : Fin n → ComplexModel n → ℝ := fun _ z => ρ z - δ
  have hpD : IsLocallyBoundedMixedPshOn D p := by
    intro i
    apply isLocallyBoundedPshOn_of_continuousOn
    · simpa only [p, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using hρpsh.add_const (-δ)
    · exact hρ.2.2.1.continuousOn.sub continuousOn_const
  let hpQ : IsLocallyBoundedMixedPshOn Q p :=
    fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hpD i) hQD
  have hmasked : ∀ mask : Fin n → Bool, Tendsto
      (fun j => ∫ z, test j z ∂canonicalMixedBedfordTaylorMeasure Q
        (processed ∅ mask (fun i z => δ * u j i z) p) (processed_psh (hδu j) hpQ ∅ mask))
      atTop (𝓝 (∫ z, test0 z ∂canonicalMixedBedfordTaylorMeasure Q
        (processed ∅ mask (fun i z => δ * v i z) p) (processed_psh hδv hpQ ∅ mask))) := by
    intro mask
    let masked (a : Fin n → ComplexModel n → ℝ) : Fin n → ComplexModel n → ℝ :=
      fun i z => if mask i then a i z else 0
    have hmaskedPSH (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn D a) :
        IsLocallyBoundedMixedPshOn D (masked a) := by
      intro i
      cases hm : mask i
      · change IsLocallyBoundedPshOn D (fun z => if mask i then a i z else 0)
        simp only [hm, Bool.false_eq_true, ↓reduceIte]
        exact isLocallyBoundedPshOn_of_abs_le
          (fun z _ => plurisubharmonicAt_const 0 EReal.zero_ne_top z) (C := 0)
          (fun _ _ => by simp)
      · change IsLocallyBoundedPshOn D (fun z => if mask i then a i z else 0)
        simpa only [hm, ↓reduceIte] using ha i
    have hmaskedBox (a : Fin n → ComplexModel n → ℝ)
        (ha : ∀ i z, z ∈ D → -1 ≤ a i z ∧ a i z ≤ 0) :
        ∀ i z, z ∈ D → -1 ≤ masked a i z ∧ masked a i z ≤ 0 := by
      intro i z hz
      cases hm : mask i
      · simp [masked, hm]
      · simpa only [masked, hm, ↓reduceIte] using ha i z hz
    have hmaskedCap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
        IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a → Tendsto
        (fun j => relCapacity V {z | z ∈ T ∧ a < |masked (u j) i z - masked v i z|})
        atTop (𝓝 0) := by
      intro i V hVD T hT hTV a ha
      cases hm : mask i
      · simp [masked, hm, not_lt_of_ge ha.le]
      · simpa only [masked, hm, ↓reduceIte] using hcap i V hVD T hT hTV a ha
    obtain ⟨hW, hV, hlimits⟩ := hWeak (fun j => masked (u j)) (masked v)
      (fun j i => hmaskedPSH (u j) (hu j) i) (hmaskedPSH v hv)
      (fun j => hmaskedBox (u j) (huB j)) (hmaskedBox v hvB) hmaskedCap
      m w z hw hz hwB hzB hseedcap
    have ec (a : Fin n → ComplexModel n → ℝ) :
        (fun i z => δ * masked a i z - δ + ρ z) =
          processed ∅ mask (fun i z => δ * a i z) p := by
      funext i z
      cases hm : mask i <;> simp [masked, processed, hm, p] <;> ring
    let hGU (j : ℕ) : IsLocallyBoundedMixedPshOn Q
        (fun i z => δ * masked (u j) i z - δ + ρ z) :=
      (ec (u j)).symm ▸ processed_psh (hδu j) hpQ ∅ mask
    let hGV : IsLocallyBoundedMixedPshOn Q
        (fun i z => δ * masked v i z - δ + ρ z) :=
      (ec v).symm ▸ processed_psh hδv hpQ ∅ mask
    have hTU (j : ℕ) := core_arbitrary_integral_transport omega e hDt hρ hO hOS Q rfl (hW j)
      (fun i => ⟨-1, 0, fun x _ =>
        (hPSH (masked (u j) i) (hmaskedPSH (u j) (hu j) i)
          (hmaskedBox (u j) (huB j) i)).2.1 x⟩)
      (fun i z => δ * masked (u j) i z - δ)
      (fun i => (hPSH (masked (u j) i) (hmaskedPSH (u j) (hu j) i)
        (hmaskedBox (u j) (huB j) i)).2.2) (hGU j) (hsupport j)
    have hTV := core_arbitrary_integral_transport omega e hDt hρ hO hOS Q rfl hV
      (fun i => ⟨-1, 0, fun x _ =>
        (hPSH (masked v i) (hmaskedPSH v hv i) (hmaskedBox v hvB i)).2.1 x⟩)
      (fun i z => δ * masked v i z - δ)
      (fun i => (hPSH (masked v i) (hmaskedPSH v hv i) (hmaskedBox v hvB i)).2.2)
      hGV hsupport0
    have hl : Tendsto (fun j => ∫ x, chartExtend e h x * Ψ
        (fun i => (lift (w j i) x).toReal)
        ∂globalMixedMeasure (fun _ : Fin n => omega.form)
          (fun i => lift (masked (u j) i)) (fun i => (hW j i).1)) atTop
        (𝓝 (∫ x, chartExtend e h x * Ψ (fun i => (lift (z i) x).toReal)
          ∂globalMixedMeasure (fun _ : Fin n => omega.form)
            (fun i => lift (masked v i)) (fun i => (hV i).1))) :=
      hlimits Ψ _ hΨ ⟨chartExtend e h, hglobaltest⟩
    have hUeq (j : ℕ) :
        (∫ x, chartExtend e h x * Ψ (fun i => (lift (w j i) x).toReal)
          ∂globalMixedMeasure (fun _ : Fin n => omega.form)
            (fun i => lift (masked (u j) i)) (fun i => (hW j i).1)) =
          ∫ y, test j y ∂canonicalMixedBedfordTaylorMeasure Q
            (processed ∅ mask (fun i y => δ * u j i y) p)
            (processed_psh (hδu j) hpQ ∅ mask) := by
      rw [← hchartweight (w j) (hw j) (hwB j)]
      exact (hTU j).trans (integral_tuple_congr (hGU j)
        (processed_psh (hδu j) hpQ ∅ mask) (ec (u j)) (test j))
    have hVeq :
        (∫ x, chartExtend e h x * Ψ (fun i => (lift (z i) x).toReal)
          ∂globalMixedMeasure (fun _ : Fin n => omega.form)
            (fun i => lift (masked v i)) (fun i => (hV i).1)) =
          ∫ y, test0 y ∂canonicalMixedBedfordTaylorMeasure Q
            (processed ∅ mask (fun i y => δ * v i y) p)
            (processed_psh hδv hpQ ∅ mask) := by
      rw [← hchartweight z hz hzB]
      exact hTV.trans (integral_tuple_congr hGV (processed_psh hδv hpQ ∅ mask) (ec v) test0)
    rw [hVeq] at hl
    exact hl.congr hUeq
  have hscaled := remove_fixed_shift atTop hδu hδv hpQ hK hKQ hm hm0 hb hb0 hzero hzero0 hmasked
  have hreal : Tendsto (fun j => ∫ z, test j z ∂canonicalMixedBedfordTaylorMeasure Q (u j) (huQ j))
      atTop (𝓝 (∫ z, test0 z ∂canonicalMixedBedfordTaylorMeasure Q v hvQ)) := by
    have hh := hscaled.div_const (δ ^ n)
    simpa only [hIu, hIv, mul_div_cancel_left₀ _ (pow_ne_zero n hδ.ne')] using hh
  rw [integral_smaller_domain hv hQD (fun y hy => hzero0 y (fun hyK => hy (hKQ hyK)))]
  exact hreal.congr (fun j => (integral_smaller_domain (hu j) hQD
    (fun y hy => hzero j y (fun hyK => hy (hKQ hyK)))).symm)

end
end SGPT.Foundations.Analysis.Pending.ActualLocalCutoffWeightedContinuity
