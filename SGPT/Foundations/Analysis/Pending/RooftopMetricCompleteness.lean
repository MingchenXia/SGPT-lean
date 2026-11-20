import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.Lattice

set_option autoImplicit false

/-!
# Abstract rooftop metric completeness

Xia SGPT PDF0165--0166, Definitions 4.3.3--4.3.4, Lemma 4.3.4,
and Proposition 4.3.2. The source binary-operation axioms produce their
own meet-semilattice. Actual metric continuity closes its induced order.
Finite tail meets and the genuine controlled-sequence completeness
criterion prove the full equivalence, for arbitrary rooftop metric spaces.
No Darvas or pluripotential hypotheses are imposed here.
-/

open Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopMetricCompleteness

noncomputable section

/-- The exact source pre-rooftop binary-operation axioms, on an arbitrary set. -/
structure PreRooftopStructure (α : Type*) where
  meet : α → α → α
  meet_comm : ∀ a b, meet a b = meet b a
  meet_assoc : ∀ a b c, meet (meet a b) c = meet a (meet b c)
  meet_idem : ∀ a, meet a a = a

/-- The source operation produces a genuine meet-semilattice and its partial order. -/
@[instance_reducible]
def PreRooftopStructure.toSemilatticeInf {α : Type*} (R : PreRooftopStructure α) :
    SemilatticeInf α := by
  letI : Min α := ⟨R.meet⟩
  exact SemilatticeInf.mk' R.meet_comm R.meet_assoc R.meet_idem

/-- The produced partial order is exactly the source order, with no external order premise. -/
theorem PreRooftopStructure.le_iff_meet_eq_left {α : Type*} (R : PreRooftopStructure α)
    (a b : α) :
    letI := R.toSemilatticeInf
    a ≤ b ↔ R.meet a b = a := by
  change R.meet b a = a ↔ R.meet a b = a
  rw [R.meet_comm b a]

/-- The exact source rooftop metric structure: one-slot metric contraction. -/
structure RooftopMetricStructure (α : Type*) [MetricSpace α] extends PreRooftopStructure α where
  dist_meet_le : ∀ a b c, dist (meet a c) (meet b c) ≤ dist a b

variable {α : Type*} [MetricSpace α]

/-- The actual source joint distance bound, equation (4.23). -/
theorem RooftopMetricStructure.dist_meet_le_add_dist (R : RooftopMetricStructure α)
    (a b a' b' : α) :
    dist (R.meet a b) (R.meet a' b') ≤ dist a a' + dist b b' := by
  have hsecond : dist (R.meet a' b) (R.meet a' b') ≤ dist b b' := by
    rw [R.meet_comm a' b, R.meet_comm a' b']
    exact R.dist_meet_le b b' a'
  exact (dist_triangle _ (R.meet a' b) _).trans
    (add_le_add (R.dist_meet_le a a' b) hsecond)

/-- Actual two-Lipschitz continuity for the maximum product metric. -/
theorem RooftopMetricStructure.meet_lipschitzWith (R : RooftopMetricStructure α) :
    LipschitzWith 2 (fun p : α × α => R.meet p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_ofNat, Prod.dist_eq]
  have h := R.dist_meet_le_add_dist p.1 p.2 q.1 q.2
  have h1 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have h2 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  linarith

/-- Actual joint continuity uses the given metric topology. -/
theorem RooftopMetricStructure.meet_continuous (R : RooftopMetricStructure α) :
    Continuous (fun p : α × α => R.meet p.1 p.2) := R.meet_lipschitzWith.continuous

/-- The produced order is closed under actual metric limits along any nontrivial filter. -/
theorem RooftopMetricStructure.le_of_tendsto_of_eventually_le (R : RooftopMetricStructure α)
    {I : Type*} {F : Filter I} [NeBot F] {ui vi : I → α} {u v : α} :
    letI := R.toPreRooftopStructure.toSemilatticeInf
    Tendsto ui F (𝓝 u) → Tendsto vi F (𝓝 v) →
      (∀ᶠ i in F, ui i ≤ vi i) → u ≤ v := by
  let := R.toPreRooftopStructure.toSemilatticeInf
  intro hu hv hle
  have hmeet := (R.meet_continuous.tendsto (u, v)).comp (hu.prodMk_nhds hv)
  have hleft : Tendsto (fun i => R.meet (ui i) (vi i)) F (𝓝 u) :=
    hu.congr' (by
      filter_upwards [hle] with i hi
      exact ((R.toPreRooftopStructure.le_iff_meet_eq_left _ _).mp hi).symm)
  exact (R.toPreRooftopStructure.le_iff_meet_eq_left u v).mpr
    (tendsto_nhds_unique hmeet hleft)

omit [MetricSpace α] in
private def finiteTailMeet [SemilatticeInf α] (u : ℕ → α) (k : ℕ) : ℕ → α
  | 0 => u k
  | j + 1 => finiteTailMeet u k j ⊓ u (k + j + 1)

omit [MetricSpace α] in
private theorem finiteTailMeet_le_last [SemilatticeInf α] (u : ℕ → α) (k j : ℕ) :
    finiteTailMeet u k j ≤ u (k + j) := by
  cases j with
  | zero => simp only [finiteTailMeet, Nat.add_zero, le_refl]
  | succ j => exact inf_le_right

omit [MetricSpace α] in
private theorem finiteTailMeet_antitone [SemilatticeInf α] (u : ℕ → α) (k : ℕ) :
    Antitone (finiteTailMeet u k) :=
  antitone_nat_of_succ_le fun _ => inf_le_left

omit [MetricSpace α] in
private theorem finiteTailMeet_succ_length_le_succ_start [SemilatticeInf α]
    (u : ℕ → α) (k j : ℕ) :
    finiteTailMeet u k (j + 1) ≤ finiteTailMeet u (k + 1) j := by
  induction j with
  | zero => exact inf_le_right
  | succ j ih =>
    change finiteTailMeet u k (j + 1) ⊓ u (k + (j + 1) + 1) ≤
      finiteTailMeet u (k + 1) j ⊓ u (k + 1 + j + 1)
    rw [show k + (j + 1) + 1 = k + 1 + j + 1 by omega]
    exact inf_le_inf ih le_rfl

/-- The full source Proposition 4.3.2, for the order produced by the source operation. -/
theorem RooftopMetricStructure.completeSpace_iff_monotone_cauchySeq_tendsto
    (R : RooftopMetricStructure α) :
    letI := R.toPreRooftopStructure.toSemilatticeInf
    CompleteSpace α ↔
      (∀ u : ℕ → α, Monotone u → CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) ∧
      (∀ u : ℕ → α, Antitone u → CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) := by
  let := R.toPreRooftopStructure.toSemilatticeInf
  constructor
  · intro hcomplete
    let := hcomplete
    exact ⟨fun _ _ hc => cauchySeq_tendsto_of_complete hc,
      fun _ _ hc => cauchySeq_tendsto_of_complete hc⟩
  · rintro ⟨hinc, hdec⟩
    apply Metric.complete_of_convergent_controlled_sequences (fun N => (1 / (2 : ℝ)) ^ N)
      (fun _ => by positivity)
    intro ui hfast
    let T : ℕ → ℕ → α := finiteTailMeet ui
    have hTstep (k j : ℕ) : dist (T k j) (T k (j + 1)) ≤
        (1 / (2 : ℝ)) ^ k * (1 / (2 : ℝ)) ^ j := by
      have hmeet : R.meet (T k j) (ui (k + j)) = T k j :=
        (R.toPreRooftopStructure.le_iff_meet_eq_left _ _).mp (finiteTailMeet_le_last ui k j)
      have hcontract := R.dist_meet_le (ui (k + j)) (ui (k + j + 1)) (T k j)
      rw [R.meet_comm (ui (k + j)) (T k j), hmeet,
        R.meet_comm (ui (k + j + 1)) (T k j)] at hcontract
      calc
        _ ≤ dist (ui (k + j)) (ui (k + j + 1)) := hcontract
        _ ≤ (1 / (2 : ℝ)) ^ (k + j) :=
          (hfast (k + j) (k + j) (k + j + 1) le_rfl (Nat.le_succ _)).le
        _ = _ := pow_add _ _ _
    have hTcauchy (k : ℕ) : CauchySeq (T k) :=
      cauchySeq_of_le_geometric (1 / (2 : ℝ)) ((1 / (2 : ℝ)) ^ k) (by norm_num) (hTstep k)
    have hex (k : ℕ) := hdec (T k) (finiteTailMeet_antitone ui k) (hTcauchy k)
    choose y hylimit using hex
    have hybound (k : ℕ) : dist (ui k) (y k) ≤ 2 * (1 / (2 : ℝ)) ^ k := by
      have h := dist_le_of_le_geometric_of_tendsto₀ (1 / (2 : ℝ)) ((1 / (2 : ℝ)) ^ k)
        (by norm_num) (hTstep k) (hylimit k)
      change dist (ui k) (y k) ≤ _ at h
      norm_num at h
      nlinarith
    have hyinc (k : ℕ) : y k ≤ y (k + 1) :=
      R.le_of_tendsto_of_eventually_le
        ((hylimit k).comp (tendsto_add_atTop_nat 1)) (hylimit (k + 1))
        (Eventually.of_forall fun j => finiteTailMeet_succ_length_le_succ_start ui k j)
    have hymono : Monotone y := monotone_nat_of_le_succ hyinc
    have hystep (k : ℕ) : dist (y k) (y (k + 1)) ≤ 5 * (1 / (2 : ℝ)) ^ k := by
      have hmiddle : dist (ui k) (ui (k + 1)) ≤ (1 / (2 : ℝ)) ^ k :=
        (hfast k k (k + 1) le_rfl (Nat.le_succ _)).le
      have htri := (dist_triangle (y k) (ui k) (y (k + 1))).trans
        (add_le_add le_rfl (dist_triangle (ui k) (ui (k + 1)) (y (k + 1))))
      rw [dist_comm (y k) (ui k)] at htri
      have hb0 := hybound k
      have hb1 := hybound (k + 1)
      rw [pow_succ] at hb1
      nlinarith [pow_nonneg (by norm_num : 0 ≤ 1 / (2 : ℝ)) k]
    have hycauchy : CauchySeq y :=
      cauchySeq_of_le_geometric (1 / (2 : ℝ)) 5 (by norm_num) hystep
    obtain ⟨Y, hylim⟩ := hinc y hymono hycauchy
    refine ⟨Y, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
    have hpow : Tendsto (fun k : ℕ => (1 / (2 : ℝ)) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hydist : Tendsto (fun k => dist (y k) Y) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hylim
    have hupper := ((tendsto_const_nhds (x := (2 : ℝ))).mul hpow).add hydist
    simp only [mul_zero, zero_add] at hupper
    apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hupper
    exact (dist_triangle (ui k) (y k) Y).trans (add_le_add (hybound k) le_rfl)

end

end SGPT.Foundations.Analysis.Pending.RooftopMetricCompleteness
