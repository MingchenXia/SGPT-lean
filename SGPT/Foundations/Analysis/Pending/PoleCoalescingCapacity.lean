import SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence
import SGPT.Foundations.Analysis.Pending.NonPluripolarPoleCoalescing
import SGPT.Foundations.Analysis.Pending.ThetaCapacityUnboundedQuasiContinuity

set_option autoImplicit false

/-!
# Actual coalescing weights converge in capacity

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2, weight inputs only.
The capacity gaps of the actual max-scaled signed differences are contained
in fixed deep sublevels, whose capacity decay is proved by Guedj--Zeriahi.
Actual moving-product measure capacity control and weak convergence remain
separate producers.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity

open FirstPass FirstPass.PositiveClasses RelativeEnergyIntegrability
open NonPluripolarPoleCoalescing CapacityWeightedConvergence
open ThetaCapacity ThetaCapacitySublevel ThetaCapacityUnboundedQuasiContinuity

noncomputable section

/-- Away from a fixed deep sublevel the actual signed-weight error is bounded
uniformly by the scaling parameter times the fixed depth. -/
theorem abs_coalescingWeight_sub_le {X : Type*} {u v : X → EReal}
    {B eps k : ℝ} (heps : 0 ≤ eps) (_hk : 0 ≤ k)
    (huv : u ≤ v) (hv : v ≤ 0) (hgap : ∀ x, v x ≤ u x + (B : EReal))
    {x : X} (hx : ((-k : ℝ) : EReal) ≤ v x) :
    |canonicalERealDiffToReal (u x) (poleCoalescingApprox eps u v x) -
      canonicalERealDiffToReal (u x) (v x)| ≤ eps * k := by
  have htype : SameSingularityTypeOn u v univ :=
    ⟨MoreSingularOn.of_le fun y _ => huv y, ⟨B, fun y _ => hgap y⟩⟩
  have hvt : v x ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hv x)
  have hvb : v x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hx
  have hut : u x ≠ ⊤ := ne_top_of_le_ne_top hvt (huv x)
  have hub : u x ≠ ⊥ := fun h => hvb ((sameSingularityTypeOn_eq_bot_iff htype
    (mem_univ x)).mp h)
  have hbds := poleCoalescingApprox_bounds heps huv hv hgap x
  have hpt : poleCoalescingApprox eps u v x ≠ ⊤ :=
    ne_top_of_le_ne_top hvt hbds.2.1
  have hpb : poleCoalescingApprox eps u v x ≠ ⊥ := ne_bot_of_le_ne_bot hub hbds.1
  rw [canonicalDiff_eq_sub_toReal hut hpt
      (sameSingularityTypeOn_eq_bot_iff
        (sameSingularityType_poleCoalescingApprox heps huv hv hgap).symm (mem_univ x)),
    canonicalDiff_eq_sub_toReal hut hvt (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))]
  have hrealV : ((v x).toReal : EReal) = v x := EReal.coe_toReal hvt hvb
  have hrealP : ((poleCoalescingApprox eps u v x).toReal : EReal) =
      poleCoalescingApprox eps u v x := EReal.coe_toReal hpt hpb
  have hlower : (1 + eps) * (v x).toReal ≤ (poleCoalescingApprox eps u v x).toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_mul, hrealV, hrealP]
    exact le_max_right _ _
  have hupper : (poleCoalescingApprox eps u v x).toReal ≤ (v x).toReal :=
    EReal.toReal_le_toReal hbds.2.1 hpb hvt
  have hdepth : -k ≤ (v x).toReal := by
    apply EReal.coe_le_coe_iff.mp
    rwa [hrealV]
  have hmul := mul_le_mul_of_nonneg_left hdepth heps
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg heps _hk]

/-- The original ordered signed difference has the same explicit uniform
bound as every coalescing approximation. -/
theorem abs_canonicalDiff_le_of_orderGap {X : Type*} {u v : X → EReal}
    {B : ℝ} (hB : 0 ≤ B) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) (x : X) :
    |canonicalERealDiffToReal (u x) (v x)| ≤ B := by
  have h := abs_canonicalDiff_poleCoalescingApprox_le hB (le_refl 0) huv hv hgap x
  simpa only [poleCoalescingApprox, add_zero, EReal.coe_one, one_mul,
    max_eq_right (huv x)] using h

/-- The actual canonical weight is Borel measurable, including common poles. -/
theorem measurable_canonicalWeight {X : Type*} [MeasurableSpace X]
    {u v : X → EReal} (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x => canonicalERealDiffToReal (u x) (v x)) :=
  measurable_canonicalERealDiffToReal.comp (hu.prodMk hv)

/-- Max scaling gives the actual measurable varying signed weights. -/
theorem measurable_coalescingWeight {X : Type*} [MeasurableSpace X]
    {u v : X → EReal} (hu : Measurable u) (hv : Measurable v) (eps : ℝ) :
    Measurable (fun x => canonicalERealDiffToReal (u x)
      (poleCoalescingApprox eps u v x)) :=
  measurable_canonicalWeight hu (hu.max (measurable_const.mul hv))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual coalescing signed-weight gap converges to zero in the zero-
reference theta capacity for every positive tolerance. -/
theorem tendsto_thetaCapacity_coalescingWeight_gap
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (htheta : theta.val.IsSemipositive) {u v : M → EReal}
    (hvP : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hv : v ≤ 0) {B : ℝ}
    (hgap : ∀ x, v x ≤ u x + (B : EReal))
    {eps : ℕ → ℝ} (heps : ∀ j, 0 < eps j) (hlim : Tendsto eps atTop (𝓝 0))
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun j => thetaCapacity theta (fun _ => 0)
      {x | delta < |canonicalERealDiffToReal (u x) (poleCoalescingApprox (eps j) u v x) -
        canonicalERealDiffToReal (u x) (v x)|}) atTop (𝓝 0) := by
  have hzero : IsThetaPshPotential theta.val (fun _ => 0) :=
    (LocalPotentials.isThetaPshPotential_zero_iff theta).mpr htheta
  have hsub := tendsto_thetaCapacity_sublevel omega hzero hvP hv
  simp only [zero_add] at hsub
  apply ENNReal.tendsto_nhds_zero.mpr
  intro eta heta
  obtain ⟨k, hk⟩ := ((hsub.eventually_lt_const heta)).exists
  have hparam : Tendsto (fun j => eps j * (k : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul_const (k : ℝ)
  filter_upwards [hparam.eventually_lt_const hdelta] with j hj
  refine le_trans (thetaCapacity_mono ?_) hk.le
  intro x hx
  by_contra hnot
  have hxv : ((-(k : ℝ) : ℝ) : EReal) ≤ v x := not_lt.mp hnot
  have hbound := abs_coalescingWeight_sub_le (heps j).le (Nat.cast_nonneg k)
    huv hv hgap hxv
  exact (not_lt_of_ge (hbound.trans hj.le)) hx

/-- An actual nonpositive genuine potential is quasicontinuous over the zero
reference, with no boundedness assumption on the potential. -/
theorem quasiContinuousFor_toReal_of_le_zero
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (htheta : theta.val.IsSemipositive) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hu0 : u ≤ 0) :
    QuasiContinuousFor (thetaCapacity theta (fun _ => 0)) (fun x => (u x).toReal) := by
  intro eta heta
  obtain ⟨r, _hr0, hr, hre⟩ := ENNReal.lt_iff_exists_real_btwn.mp heta
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  have hzero : IsThetaPshPotential theta.val (fun _ => 0) :=
    (LocalPotentials.isThetaPshPotential_zero_iff theta).mpr htheta
  obtain ⟨G, hG, hcap, hcont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_compl_of_le omega hzero hu hu0
      (le_refl (0 : ℝ)) (fun _ => by simp) continuous_const hrpos
  exact ⟨G, hG, hcap.trans hre, hcont⟩

/-- The actual same-type canonical signed difference is quasicontinuous for
the actual theta capacity, including its prescribed value on common poles. -/
theorem quasiContinuousFor_canonicalWeight
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (htheta : theta.val.IsSemipositive) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hu0 : u ≤ 0) (hv0 : v ≤ 0) (htype : SameSingularityTypeOn u v univ) :
    QuasiContinuousFor (thetaCapacity theta (fun _ => 0))
      (fun x => canonicalERealDiffToReal (u x) (v x)) := by
  intro eta heta
  obtain ⟨r, _hr0, hr, hre⟩ := ENNReal.lt_iff_exists_real_btwn.mp heta
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  have hhalf : (0 : ℝ≥0∞) < ENNReal.ofReal (r / 2) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨G, hG, hGcap, huG⟩ :=
    quasiContinuousFor_toReal_of_le_zero omega htheta hu hu0 _ hhalf
  obtain ⟨H, hH, hHcap, hvH⟩ :=
    quasiContinuousFor_toReal_of_le_zero omega htheta hv hv0 _ hhalf
  refine ⟨G ∪ H, hG.union hH, ?_, ?_⟩
  · calc
      thetaCapacity theta (fun _ => 0) (G ∪ H)
          ≤ thetaCapacity theta (fun _ => 0) G + thetaCapacity theta (fun _ => 0) H :=
        thetaCapacity_union_le _ _ _ _
      _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := ENNReal.add_lt_add hGcap hHcap
      _ = ENNReal.ofReal r := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      _ < eta := hre
  · refine ((huG.mono (compl_subset_compl.mpr subset_union_left)).sub
      (hvH.mono (compl_subset_compl.mpr subset_union_right))).congr ?_
    intro x _
    exact canonicalDiff_eq_sub_toReal (hu.1.quasiPlurisubharmonic.ne_top x)
      (hv.1.quasiPlurisubharmonic.ne_top x) (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))

end

end SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity
