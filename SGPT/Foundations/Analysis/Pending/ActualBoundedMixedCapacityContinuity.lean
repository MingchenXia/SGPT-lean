import SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityDomination
import SGPT.Foundations.Analysis.Pending.SingularSmoothTestStokes
import SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! # Actual bounded mixed weak convergence from Kähler capacity

Global bounded adaptation of the Xing input in DDL Proposition 2.2.
Actual original-capacity domination, genuine smooth test pairs and full
one-slot IBP produce smooth-test convergence; actual chart-smooth uniform
approximation yields every continuous test. Arbitrary original closed
backgrounds, all dimensions, disconnected and empty manifolds are retained.
Unbounded capacity lower semicontinuity remains a separate truncation step.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityContinuity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
  ActualBoundedMixedCapacityDomination CapacityWeightedConvergence ThetaCapacity
  FullMixedSingularIntegrationByParts RelativeEnergyIntegrability BoundedGlobalProduct

noncomputable section

private theorem abs_toReal_le_of_box {B : ℝ} {v : EReal}
    (hv : ((-B : ℝ) : EReal) ≤ v ∧ v ≤ (B : EReal)) : |v.toReal| ≤ B := by
  have hb : v ≠ ⊥ := (lt_of_lt_of_le (EReal.bot_lt_coe _) hv.1).ne'
  have ht : v ≠ ⊤ := (lt_of_le_of_lt hv.2 (EReal.coe_lt_top _)).ne
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal hv.1 (EReal.coe_ne_bot _) ht
  · simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal hv.2 hb (EReal.coe_ne_top _)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

private theorem integral_error_of_capacity
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {p : ℕ → Fin n → M → EReal}
    (hp : ∀ j i, IsThetaPshPotential (θ i).val (p j i))
    {B : ℝ} (hB : 0 ≤ B)
    (hpB : ∀ j i x, ((-B : ℝ) : EReal) ≤ p j i x ∧ p j i x ≤ (B : EReal))
    {f : ℕ → M → ℝ} {g : M → ℝ} (hf : ∀ j, Measurable (f j)) (hg : Measurable g)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ j x, |f j x| ≤ D) (hgD : ∀ x, |g x| ≤ D)
    (hcap : ∀ δ : ℝ, 0 < δ → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | δ < |f j x - g x|}) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, (f j x - g x)
      ∂globalMixedMeasure θ (p j) (fun i => (hp j i).1)) atTop (𝓝 0) := by
  let μ : ℕ → Measure M := fun j => globalMixedMeasure θ (p j) (fun i => (hp j i).1)
  have hfinite : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  let : ∀ j, IsFiniteMeasure (μ j) := hfinite
  obtain ⟨K, _hK, hdom⟩ := exists_uniform_capacity_bound omega θ B hB
  have hmod : Tendsto (fun t : ℝ≥0∞ => ENNReal.ofReal K * t) (𝓝 0) (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul (tendsto_id : Tendsto (fun t : ℝ≥0∞ => t) (𝓝 0) (𝓝 0))
      (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using hh
  have hcontrol : UniformCapacityControl (thetaCapacity omega.form (fun _ => 0)) μ (μ 0) :=
    uniformCapacityControl_of_modulus hmod
      (fun j E _ => hdom (p j) (hp j) (hpB j) E)
      (fun E _ => hdom (p 0) (hp 0) (hpB 0) E)
  have heq : ∀ j, μ j univ = μ 0 univ := fun j =>
    FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega
      (hp j) (hp 0) (fun i => BoundedMongeAmpereEnergy.sameSingularityType_of_bounded
        ⟨-B, B, hpB j i⟩ ⟨-B, B, hpB 0 i⟩)
  have hmass : ∀ j, (μ j).real univ ≤ (μ 0).real univ := by
    intro j
    change (μ j univ).toReal ≤ (μ 0 univ).toReal
    exact le_of_eq (congrArg ENNReal.toReal (heq j))
  have hh := tendsto_integral_sub_of_tendsto_capacity hcontrol hf hg
    (measurable_const (a := (1 : ℝ))) hD zero_le_one (measureReal_nonneg)
    hfD hgD (fun _ => by norm_num) (Eventually.of_forall hmass) hcap
  have ht : Tendsto (fun j => (∫ x, f j x ∂μ j) - ∫ x, g x ∂μ j) atTop (𝓝 0) := by
    simpa only [one_mul] using hh
  exact ht.congr' (Eventually.of_forall fun j =>
    (integral_sub (integrable_of_bounded (hf j) (hfD j))
      (integrable_of_bounded hg hgD)).symm)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_chartSmooth_uniform_approx (h : C(M, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ℝ, ChartSmooth (n := n) g ∧ ∀ x, |g x - h x| < ε := by
  classical
  let S : M → Opens M := fun x =>
    ⟨{y | |h y - h x| < ε / 2}, isOpen_lt (h.continuous.sub continuous_const).abs continuous_const⟩
  have hcover : ∀ x : M, ∃ y, x ∈ S y := fun x => ⟨x, by
    change |h x - h x| < ε / 2
    simp only [sub_self, abs_zero]
    positivity⟩
  obtain ⟨m, χ, idx, hχ, hn, hsupp, _hc, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S hcover
  let g : M → ℝ := fun y => ∑ a, h (idx a) * χ a y
  refine ⟨g, ?_, ?_⟩
  · intro e
    change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun z => ∑ a, h (idx a) * χ a (e.val.symm z)) e.val.target
    exact ContDiffOn.sum fun a _ => contDiffOn_const.mul (hχ a e)
  · intro x
    have he : g x - h x = ∑ a, χ a x * (h (idx a) - h x) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
      simp only [g, mul_comm]
    have hterm : ∀ a : Fin m, χ a x * |h (idx a) - h x| ≤ χ a x * (ε / 2) := by
      intro a
      by_cases hz : χ a x = 0
      · simp only [hz, zero_mul, le_refl]
      · have hxS := hsupp a (subset_tsupport (χ a) hz)
        change |h x - h (idx a)| < ε / 2 at hxS
        exact mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hxS.le) (hn a x)
    have hh : |g x - h x| ≤ ε / 2 := by
      calc
        _ = |∑ a, χ a x * (h (idx a) - h x)| := by rw [he]
        _ ≤ ∑ a, |χ a x * (h (idx a) - h x)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a, χ a x * |h (idx a) - h x| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul, abs_of_nonneg (hn a x)]
        _ ≤ ∑ a, χ a x * (ε / 2) := Finset.sum_le_sum fun a _ => hterm a
        _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    exact hh.trans_lt (by linarith)

private theorem tendsto_updated_smooth_difference
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {p : ℕ → Fin n → M → EReal}
    (hp : ∀ j i, IsThetaPshPotential (θ i).val (p j i))
    {B : ℝ} (hB : 0 ≤ B)
    (hpB : ∀ j i x, ((-B : ℝ) : EReal) ≤ p j i x ∧ p j i x ≤ (B : EReal))
    (k : Fin n) {a : ℕ → M → EReal} {b : M → EReal}
    (ha : ∀ j, IsThetaPshPotential (θ k).val (a j))
    (hb : IsThetaPshPotential (θ k).val b)
    (haB : ∀ j x, ((-B : ℝ) : EReal) ≤ a j x ∧ a j x ≤ (B : EReal))
    (hbB : ∀ x, ((-B : ℝ) : EReal) ≤ b x ∧ b x ≤ (B : EReal))
    (hcap : ∀ δ : ℝ, 0 < δ → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | δ < |(a j x).toReal - (b x).toReal|}) atTop (𝓝 0))
    (g : M → ℝ) (hg : ChartSmooth (n := n) g) :
    Tendsto (fun j =>
      (∫ x, g x ∂updatedMixedMeasure k (fun i _ => hp j i) (ha j)) -
      ∫ x, g x ∂updatedMixedMeasure k (fun i _ => hp j i) hb) atTop (𝓝 0) := by
  classical
  obtain ⟨A, _hA, ht, hz, htz⟩ := SingularSmoothTestStokes.exists_smooth_test_background omega g hg
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    (ProductTestForms.ChartSmooth.continuous hg).continuousOn
  let R : ℝ := max B (max D 0)
  have hR : 0 ≤ R := le_trans hB (le_max_left _ _)
  have hBR : B ≤ R := le_max_left _ _
  have hDR : D ≤ R := (le_max_left D 0).trans (le_max_right _ _)
  have htest : ∀ x, ((-R : ℝ) : EReal) ≤ (g x : EReal) ∧ (g x : EReal) ≤ (R : EReal) := by
    intro x
    have hgd : |g x| ≤ D := by simpa only [Real.norm_eq_abs] using hD x (mem_univ x)
    have hh : |g x| ≤ R := hgd.trans hDR
    exact ⟨EReal.coe_le_coe_iff.mpr (abs_le.mp hh).1,
      EReal.coe_le_coe_iff.mpr (abs_le.mp hh).2⟩
  have hzero : ∀ x : M, ((-R : ℝ) : EReal) ≤ 0 ∧ (0 : EReal) ≤ (R : EReal) := by
    intro x
    exact ⟨by exact_mod_cast neg_nonpos.mpr hR, by exact_mod_cast hR⟩
  have hlimit {r : M → EReal}
      (hr : IsThetaPshPotential (A • omega.form).val r)
      (hrB : ∀ x, ((-R : ℝ) : EReal) ≤ r x ∧ r x ≤ (R : EReal)) :
      Tendsto (fun j => ∫ x, ((a j x).toReal - (b x).toReal)
        ∂updatedMixedMeasure k (fun i _ => hp j i) hr) atTop (𝓝 0) := by
    apply integral_error_of_capacity omega
      (fun j => isThetaPshPotential_update k (fun i _ => hp j i) hr) hR
    · intro j i x
      by_cases hi : i = k
      · subst hi
        simpa only [Function.update_self] using hrB x
      · rw [Function.update_of_ne hi]
        exact ⟨(EReal.coe_le_coe_iff.mpr (neg_le_neg hBR)).trans (hpB j i x).1,
          (hpB j i x).2.trans (EReal.coe_le_coe_iff.mpr hBR)⟩
    · exact fun j => GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal (ha j).1
    · exact GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hb.1
    · exact hB
    · exact fun j x => abs_toReal_le_of_box (haB j x)
    · exact fun x => abs_toReal_le_of_box (hbB x)
    · exact hcap
  have hl := (hlimit ht htest).sub (hlimit hz hzero)
  simp only [sub_zero] at hl
  apply hl.congr'
  filter_upwards [] with j
  have hs := integral_sub_mixed_update_symm omega k (fun i _ => hp j i)
    (ha j) hb ht hz
    (BoundedMongeAmpereEnergy.sameSingularityType_of_bounded ⟨-B, B, haB j⟩ ⟨-B, B, hbB⟩) htz
  have hc (x : M) : canonicalERealDiffToReal (g x : EReal) 0 = g x := by
    simpa only [EReal.coe_zero, sub_zero] using canonicalERealDiffToReal_coe_coe (g x) 0
  have hab (x : M) : canonicalERealDiffToReal (a j x) (b x) =
      (a j x).toReal - (b x).toReal := by
    apply canonicalDiff_eq_sub_toReal
    · exact (lt_of_le_of_lt (haB j x).2 (EReal.coe_lt_top _)).ne
    · exact (lt_of_le_of_lt (hbB x).2 (EReal.coe_lt_top _)).ne
    · have hna : a j x ≠ ⊥ := (lt_of_lt_of_le (EReal.bot_lt_coe _) (haB j x).1).ne'
      have hnb : b x ≠ ⊥ := (lt_of_lt_of_le (EReal.bot_lt_coe _) (hbB x).1).ne'
      simp only [hna, hnb]
  simpa only [hc, hab] using hs.symm

private theorem tendsto_integral_chartSmooth
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    {B : ℝ} (hB : 0 ≤ B)
    (huB : ∀ j i x, ((-B : ℝ) : EReal) ≤ u j i x ∧ u j i x ≤ (B : EReal))
    (hvB : ∀ i x, ((-B : ℝ) : EReal) ≤ v i x ∧ v i x ≤ (B : EReal))
    (hcap : ∀ i δ, 0 < δ → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | δ < |(u j i x).toReal - (v i x).toReal|}) atTop (𝓝 0))
    (g : M → ℝ) (hg : ChartSmooth (n := n) g) :
    Tendsto (fun j => ∫ x, g x ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1))
      atTop (𝓝 (∫ x, g x ∂globalMixedMeasure θ v (fun i => (hv i).1))) := by
  classical
  let ψ : ℕ → ℕ → Fin n → M → EReal := fun j m i => if i.val < m then u j i else v i
  have hψ : ∀ j m i, IsThetaPshPotential (θ i).val (ψ j m i) := by
    intro j m i
    dsimp only [ψ]
    split_ifs
    · exact hu j i
    · exact hv i
  have hψB : ∀ j m i x, ((-B : ℝ) : EReal) ≤ ψ j m i x ∧ ψ j m i x ≤ (B : EReal) := by
    intro j m i x
    dsimp only [ψ]
    split_ifs
    · exact huB j i x
    · exact hvB i x
  let f : ℕ → Fin (n + 1) → ℝ := fun j m =>
    ∫ x, g x ∂globalMixedMeasure θ (ψ j m.val) (fun i => (hψ j m.val i).1)
  have hstep (k : Fin n) : Tendsto (fun j => f j k.succ - f j k.castSucc) atTop (𝓝 0) := by
    have hh := tendsto_updated_smooth_difference omega (fun j i => hψ j k.val i) hB
      (fun j i x => hψB j k.val i x) k (fun j => hu j k) (hv k)
      (fun j x => huB j k x) (hvB k) (hcap k) g hg
    apply hh.congr'
    filter_upwards [] with j
    have hforms : Function.update θ k (θ k) = θ := Function.update_eq_self k θ
    have hpa : Function.update (ψ j k.val) k (u j k) = ψ j (k.val + 1) := by
      funext i
      by_cases hi : i = k
      · subst hi
        simp [ψ]
      · rw [Function.update_of_ne hi]
        have hne : i.val ≠ k.val := fun h => hi (Fin.ext h)
        have heq : i.val < k.val + 1 ↔ i.val < k.val := by omega
        simp only [ψ, heq]
    have hpb : Function.update (ψ j k.val) k (v k) = ψ j k.val := by
      funext i
      by_cases hi : i = k
      · subst hi
        simp [ψ]
      · exact Function.update_of_ne hi _ _
    have ha : updatedMixedMeasure k (fun i _ => hψ j k.val i) (hu j k) =
        globalMixedMeasure θ (ψ j (k.val + 1)) (fun i => (hψ j (k.val + 1) i).1) :=
      globalMixedMeasure_congr hforms hpa _ _
    have hb : updatedMixedMeasure k (fun i _ => hψ j k.val i) (hv k) =
        globalMixedMeasure θ (ψ j k.val) (fun i => (hψ j k.val i).1) :=
      globalMixedMeasure_congr hforms hpb _ _
    simp only [ha, hb, f, Fin.val_succ, Fin.val_castSucc]
  have ht : Tendsto (fun j => f j (Fin.last n) - f j 0) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ fun k _ => hstep k
    simpa only [Finset.sum_const_zero, DeepCoincidenceIntegrationByParts.sum_fin_successive_sub] using hh
  have hzero : ∀ j, ψ j 0 = v := by intro j; funext i; simp [ψ]
  have hlast : ∀ j, ψ j n = u j := by intro j; funext i; simp [ψ, i.isLt]
  have hfzero : ∀ j, f j 0 = ∫ x, g x ∂globalMixedMeasure θ v (fun i => (hv i).1) := by
    intro j
    have hh := globalMixedMeasure_congr rfl (hzero j) (fun i => (hψ j 0 i).1) (fun i => (hv i).1)
    simp only [f, Fin.val_zero, hh]
  have hflast : ∀ j, f j (Fin.last n) =
      ∫ x, g x ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1) := by
    intro j
    have hh := globalMixedMeasure_congr rfl (hlast j) (fun i => (hψ j n i).1) (fun i => (hu j i).1)
    simp only [f, Fin.val_last, hh]
  have hh : Tendsto (fun j => f j (Fin.last n) - f j 0 +
      ∫ x, g x ∂globalMixedMeasure θ v (fun i => (hv i).1)) atTop
      (𝓝 (0 + ∫ x, g x ∂globalMixedMeasure θ v (fun i => (hv i).1))) :=
    ht.add tendsto_const_nhds
  simpa only [hflast, hfzero, sub_add_cancel, zero_add] using hh

/-- Actual full mixed weak convergence follows from a common finite box and
original Kähler-capacity convergence in every genuine independent slot.
The conclusion uses every continuous real test, including dimension zero. -/
theorem tendsto_integral_continuous_of_capacity
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    {B : ℝ} (hB : 0 ≤ B)
    (huB : ∀ j i x, ((-B : ℝ) : EReal) ≤ u j i x ∧ u j i x ≤ (B : EReal))
    (hvB : ∀ i x, ((-B : ℝ) : EReal) ≤ v i x ∧ v i x ≤ (B : EReal))
    (hcap : ∀ i δ, 0 < δ → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | δ < |(u j i x).toReal - (v i x).toReal|}) atTop (𝓝 0))
    (h : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, h x ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1))
      atTop (𝓝 (∫ x, h x ∂globalMixedMeasure θ v (fun i => (hv i).1))) := by
  let μ : ℕ → Measure M := fun j => globalMixedMeasure θ (u j) (fun i => (hu j i).1)
  let ν : Measure M := globalMixedMeasure θ v (fun i => (hv i).1)
  let : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  let : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure omega _
  have heq : ∀ j, (μ j).real univ = ν.real univ := by
    intro j
    exact congrArg ENNReal.toReal
      (FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega (hu j) hv
        (fun i => BoundedMongeAmpereEnergy.sameSingularityType_of_bounded
          ⟨-B, B, huB j i⟩ ⟨-B, B, hvB i⟩))
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (4 * (ν.real univ + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨g, hg, hgh⟩ := exists_chartSmooth_uniform_approx (n := n) h hδ
  have hgc : Continuous g := ProductTestForms.ChartSmooth.continuous hg
  have herror (σ : Measure M) [IsFiniteMeasure σ] :
      |(∫ x, h x ∂σ) - ∫ x, g x ∂σ| ≤ δ * σ.real univ := by
    rw [← integral_sub
      (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hh := norm_integral_le_of_norm_le_const (μ := σ) (f := fun x => h x - g x)
      (C := δ) (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_sub_comm] using (hgh x).le)
    simpa only [Real.norm_eq_abs] using hh
  have hsmall : δ * ν.real univ < ε / 4 := by
    have hh : δ * (ν.real univ + 1) = ε / 4 := by
      dsimp only [δ]
      field_simp
    nlinarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_chartSmooth omega hu hv hB huB hvB hcap g hg)
    (ε / 2) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have hleft : |(∫ x, h x ∂μ j) - ∫ x, g x ∂μ j| < ε / 4 := by
    exact (herror (μ j)).trans_lt (by rw [heq j]; exact hsmall)
  have hright : |(∫ x, g x ∂ν) - ∫ x, h x ∂ν| < ε / 4 := by
    rw [abs_sub_comm]
    exact (herror ν).trans_lt hsmall
  have hmiddle : |(∫ x, g x ∂μ j) - ∫ x, g x ∂ν| < ε / 2 := by
    simpa only [Real.dist_eq] using hN j hj
  rw [Real.dist_eq]
  calc
    |(∫ x, h x ∂μ j) - ∫ x, h x ∂ν| =
        |((∫ x, h x ∂μ j) - ∫ x, g x ∂μ j) +
          ((∫ x, g x ∂μ j) - ∫ x, g x ∂ν) +
          ((∫ x, g x ∂ν) - ∫ x, h x ∂ν)| := by congr 1; ring
    _ ≤ |(∫ x, h x ∂μ j) - ∫ x, g x ∂μ j| +
        |(∫ x, g x ∂μ j) - ∫ x, g x ∂ν| +
        |(∫ x, g x ∂ν) - ∫ x, h x ∂ν| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by linarith

end
end SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityContinuity
