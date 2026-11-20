import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

set_option autoImplicit false

/-!
# Sets of outer capacity zero are pluripolar (step C1 of I-0510)

On a compact connected Kähler manifold `(M, ω)` of positive dimension and positive volume, a set
`E` of outer Monge--Ampère capacity zero (`Cap_ω(G)` arbitrarily small over open `G ⊇ E`,
`Cap_ω = thetaCapacity ω 0`) lies in the pole set of one `ω`-PSH potential
(`exists_isThetaPshPotential_poles_of_outerCapacityZero`), hence is `ManifoldLocallyPluripolar`
(`manifoldLocallyPluripolar_of_outerCapacityZero`).  This is the global form of Bedford--Taylor's
"`c^*(E) = 0` ⇒ `E` pluripolar" (Guedj--Zeriahi, *Intrinsic capacities on compact Kähler
manifolds*, 2005), and no Josefson theorem is used.

## The construction

Choose nested open `G₀ ⊇ G₁ ⊇ ⋯ ⊇ E` with `(k+2)^n Cap_ω(G_k) < 2^{-(k+1)} ∫ ω^n`, and continuous
`h_k ≥ 0` with `G_k = {h_k > 0}` (`exists_continuous_pos_iff`, `M` is metrizable).  The obstacles

  `F_j = ∑_{k < j} -min (1, j h_k)`

are continuous, decrease in `j`, satisfy `-j ≤ F_j ≤ 0`, `F_j ≥ -k` off `G_k`, and `F_j → -∞` on
`E`.  By the layered dichotomy (`PluripolarCapacityDichotomy.exists_rooftopEnvelope_eq_zero_of_layers`)
every envelope `u_j = P_ω(F_j)` attains `0`; the `u_j` decrease, so by the compactness of
`PSH(M, ω)` (`ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le`) their limit
is finite somewhere, hence (identity principle, `M` connected) a genuine `ω`-PSH potential, and it
is `-∞` on `E` because `u_j ≤ F_j`.

The positivity of the volume `∫ ω^n` is a hypothesis here (`hvol`); it holds on every nonempty
compact Kähler manifold of positive dimension and is recorded as the remaining input.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero

noncomputable section

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-- In a metrizable space every open set is the positivity set of a continuous function
`h ≥ 0`. -/
theorem exists_continuous_pos_iff {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {G : Set X} (hG : IsOpen G) :
    ∃ h : X → ℝ, Continuous h ∧ (∀ x, 0 ≤ h x) ∧ ∀ x, 0 < h x ↔ x ∈ G := by
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  by_cases hne : (Gᶜ).Nonempty
  · refine ⟨fun x => Metric.infDist x Gᶜ, Metric.continuous_infDist_pt _,
      fun x => Metric.infDist_nonneg, fun x => ?_⟩
    rw [← hG.isClosed_compl.notMem_iff_infDist_pos hne, mem_compl_iff, not_not]
  · refine ⟨fun _ => 1, continuous_const, fun _ => zero_le_one,
      fun x => ⟨fun _ => ?_, fun _ => one_pos⟩⟩
    by_contra hx
    exact hne ⟨x, hx⟩

section Cut

variable {X : Type*}

/-- The obstacle `-min (1, l h)`. -/
def cutObstacle (h : X → ℝ) (l : ℕ) (x : X) : ℝ := -min 1 ((l : ℝ) * h x)

theorem cutObstacle_mem {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) (l : ℕ) (x : X) :
    -1 ≤ cutObstacle h l x ∧ cutObstacle h l x ≤ 0 := by
  unfold cutObstacle
  refine ⟨neg_le_neg (min_le_left _ _), neg_nonpos.mpr (le_min zero_le_one ?_)⟩
  exact mul_nonneg (Nat.cast_nonneg l) (hh x)

theorem cutObstacle_antitone {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) (x : X) :
    Antitone fun l => cutObstacle h l x := by
  intro l l' hll'
  unfold cutObstacle
  refine neg_le_neg (min_le_min le_rfl ?_)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hll') (hh x)

theorem cutObstacle_of_eq_zero {h : X → ℝ} {x : X} (hx : h x = 0) (l : ℕ) :
    cutObstacle h l x = 0 := by
  simp [cutObstacle, hx]

theorem cutObstacle_eq_neg_one {h : X → ℝ} {x : X} {l : ℕ} (hl : 1 ≤ (l : ℝ) * h x) :
    cutObstacle h l x = -1 := by
  simp [cutObstacle, min_eq_left hl]

end Cut

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- `E` has outer `Cap_ω`-capacity zero. -/
def OuterCapacityZero (omega : KahlerBackground n M) (E : Set M) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : Set M, IsOpen G ∧ E ⊆ G ∧
    thetaCapacity omega.form (fun _ => 0) G < ε

/-- **Step C1 of I-0510: a set of outer capacity zero lies in the pole set of one `ω`-PSH
potential.** -/
theorem exists_isThetaPshPotential_poles_of_outerCapacityZero (hn : 0 < n) [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hvol : 0 < diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega))
    {E : Set M} (hE : OuterCapacityZero omega E) :
    ∃ φ : M → EReal, IsThetaPshPotential omega.form.val φ ∧ ∀ x ∈ E, φ x = ⊥ := by
  classical
  have := DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold n M
  set θ : ClosedRealOneOneForm n M := omega.form with hθ
  have h0 := isThetaPshPotential_zero omega
  set vol : ℝ≥0∞ := diagonalPotentialMass θ (fun _ => 0) h0 with hvoldef
  -- the capacity budget
  set b : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 2) ^ n with hbdef
  have hb : ∀ k, 0 < b k := fun k => by positivity
  have hbudget : ∀ k, 0 < vol * ENNReal.ofReal (b k) := fun k =>
    ENNReal.mul_pos hvol.ne' (ENNReal.ofReal_pos.mpr (hb k)).ne'
  choose G' hG'o hEG' hG'cap using fun k => hE _ (hbudget k)
  set G : ℕ → Set M := fun k => ⋂ i ∈ Finset.range (k + 1), G' i with hGdef
  have hGo : ∀ k, IsOpen (G k) := fun k =>
    isOpen_biInter_finset fun i _ => hG'o i
  have hGanti : Antitone G := by
    intro k k' hkk' x hx
    simp only [hGdef, mem_iInter] at hx ⊢
    intro i hi
    exact hx i (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi)
      (Nat.succ_le_succ hkk')))
  have hEG : ∀ k, E ⊆ G k := fun k x hx => by
    simp only [hGdef, mem_iInter]
    exact fun i _ => hEG' i hx
  have hGcap : ∀ k, thetaCapacity θ (fun _ => 0) (G k) < vol * ENNReal.ofReal (b k) := by
    intro k
    refine lt_of_le_of_lt (thetaCapacity_mono fun x hx => ?_) (hG'cap k)
    simp only [hGdef, mem_iInter] at hx
    exact hx k (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hsum : ∀ j : ℕ, ∑ k ∈ Finset.range (j + 1),
      ENNReal.ofReal (((k : ℝ) + 2) ^ n) * thetaCapacity θ (fun _ => 0) (G k) < vol := by
    intro j
    have hterm : ∀ k ∈ Finset.range (j + 1),
        ENNReal.ofReal (((k : ℝ) + 2) ^ n) * thetaCapacity θ (fun _ => 0) (G k) <
          vol * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
      intro k _
      have hpos : (0 : ℝ) < ((k : ℝ) + 2) ^ n := by positivity
      have heq : ENNReal.ofReal (((k : ℝ) + 2) ^ n) * (vol * ENNReal.ofReal (b k)) =
          vol * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul hpos.le, hbdef]
        congr 2
        field_simp
      rw [← heq]
      exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top
        (hGcap k)
    calc ∑ k ∈ Finset.range (j + 1),
          ENNReal.ofReal (((k : ℝ) + 2) ^ n) * thetaCapacity θ (fun _ => 0) (G k)
        < ∑ k ∈ Finset.range (j + 1), vol * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) :=
          ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ hterm
      _ = vol * ENNReal.ofReal (∑ k ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ (k + 1)) := by
          rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
      _ ≤ vol * ENNReal.ofReal 1 := by
          gcongr
          have h2 := sum_geometric_two_le (j + 1)
          calc ∑ k ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ (k + 1)
              = (1 / 2) * ∑ k ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ k := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun k _ => by ring
            _ ≤ (1 / 2) * 2 := by gcongr
            _ = 1 := by norm_num
      _ = vol := by rw [ENNReal.ofReal_one, mul_one]
  -- the positivity functions of the `G_k`
  choose h hcont hnonneg hpos using fun k => exists_continuous_pos_iff (hGo k)
  -- the obstacles
  set F : ℕ → M → ℝ := fun j x => ∑ k ∈ Finset.range j, cutObstacle (h k) j x with hFdef
  have hFcont : ∀ j, Continuous (F j) := by
    intro j
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((continuous_const.min (continuous_const.mul (hcont k)))).neg
  have hF0 : ∀ j x, F j x ≤ 0 := fun j x =>
    Finset.sum_nonpos fun k _ => (cutObstacle_mem (hnonneg k) j x).2
  have hFj : ∀ (j : ℕ) x, -(j : ℝ) ≤ F j x := by
    intro j x
    have : ∑ k ∈ Finset.range j, (-1 : ℝ) ≤ F j x :=
      Finset.sum_le_sum fun k _ => (cutObstacle_mem (hnonneg k) j x).1
    simpa using this
  have hlayer : ∀ (j m : ℕ) x, x ∉ G m → -(m : ℝ) ≤ F j x := by
    intro j m x hx
    have hzero : ∀ k, m ≤ k → cutObstacle (h k) j x = 0 := fun k hmk =>
      cutObstacle_of_eq_zero (le_antisymm (not_lt.mp fun hlt =>
        hx (hGanti hmk ((hpos k x).mp hlt))) (hnonneg k x)) j
    have hle : ∀ k ∈ Finset.range j, -(if k < m then (1 : ℝ) else 0) ≤ cutObstacle (h k) j x := by
      intro k _
      split_ifs with hkm
      · exact (cutObstacle_mem (hnonneg k) j x).1
      · rw [hzero k (not_lt.mp hkm), neg_zero]
    have h1 := Finset.sum_le_sum hle
    rw [Finset.sum_neg_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    have hcard : ((Finset.filter (fun k => k < m) (Finset.range j)).card : ℝ) ≤ m := by
      have : (Finset.filter (fun k => k < m) (Finset.range j)) ⊆ Finset.range m := by
        intro k hk
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      exact_mod_cast (Finset.card_le_card this).trans (Finset.card_range m).le
    linarith
  have hFanti : ∀ x, Antitone fun j => F j x := by
    intro x
    refine antitone_nat_of_succ_le fun j => ?_
    simp only [hFdef]
    rw [Finset.sum_range_succ]
    calc ∑ k ∈ Finset.range j, cutObstacle (h k) (j + 1) x + cutObstacle (h j) (j + 1) x
        ≤ ∑ k ∈ Finset.range j, cutObstacle (h k) (j + 1) x + 0 :=
          add_le_add le_rfl (cutObstacle_mem (hnonneg j) (j + 1) x).2
      _ ≤ ∑ k ∈ Finset.range j, cutObstacle (h k) j x := by
          rw [add_zero]
          exact Finset.sum_le_sum fun k _ =>
            cutObstacle_antitone (hnonneg k) x (Nat.le_succ j)
  -- the envelopes
  have hbig := isBigClass_kahler omega
  set u : ℕ → M → EReal := fun j => rooftopEnvelope θ.val (fun y => (F j y : EReal)) with hudef
  have hu : ∀ j, IsThetaPshPotential θ.val (u j) := fun j =>
    ContinuousObstacleEnvelopeContact.isThetaPshPotential_rooftopEnvelope_of_continuous
      hn θ hbig (hFcont j)
  have hule : ∀ j x, u j x ≤ (F j x : EReal) := fun j x =>
    ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous (hFcont j)
      (ContinuousObstacleEnvelopeContact.rooftopCompetitors_nonempty_of_isBigClass hn θ hbig
        (hFcont j)) (hu j).1 x
  have huanti : ∀ x, Antitone fun j => u j x := by
    intro x j j' hjj'
    exact rooftopEnvelope_mono (fun y => EReal.coe_le_coe_iff.mpr (hFanti y hjj')) x
  have htouch : ∀ j, ∃ x, ((-(0 : ℝ) : ℝ) : EReal) ≤ u j x := by
    intro j
    obtain ⟨x, hx⟩ := exists_rooftopEnvelope_eq_zero_of_layers hn omega hGo hGanti (hFcont j)
      (hF0 j) (hFj j) (fun m x hx => hlayer j m x hx) (hsum j)
    refine ⟨x, ?_⟩
    change _ ≤ rooftopEnvelope θ.val (fun y => (F j y : EReal)) x
    rw [hx, neg_zero, EReal.coe_zero]
  obtain ⟨x₀, hx₀⟩ :=
    ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le hu huanti htouch
  set φ : M → EReal := fun x => ⨅ j, u j x with hφdef
  have hφpsh : ThetaPlurisubharmonic θ.val φ :=
    ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun j => (hu j).1) huanti
  refine ⟨φ, ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hφpsh ⟨x₀, hx₀⟩,
    fun x hx => ?_⟩
  -- on `E` the obstacles go to `-∞`
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt (-y)
  have hev : ∀ᶠ j in atTop, N ≤ j ∧ ∀ k ∈ Finset.range N, 1 ≤ (j : ℝ) * h k x := by
    refine (eventually_ge_atTop N).and ((Filter.eventually_all_finset _).mpr fun k _ => ?_)
    have hk : 0 < h k x := (hpos k x).mpr (hEG k hx)
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / h k x)
    filter_upwards [eventually_ge_atTop m] with j hj
    have hmj : (m : ℝ) ≤ j := by exact_mod_cast hj
    calc (1 : ℝ) = (1 / h k x) * h k x := by field_simp
      _ ≤ (j : ℝ) * h k x := by gcongr; linarith
  obtain ⟨j, hjN, hjk⟩ := hev.exists
  have hFle : F j x ≤ -(N : ℝ) := by
    simp only [hFdef]
    rw [← Finset.sum_range_add_sum_Ico _ hjN]
    have h1 : ∑ k ∈ Finset.range N, cutObstacle (h k) j x = -(N : ℝ) := by
      rw [Finset.sum_congr rfl fun k hk => cutObstacle_eq_neg_one (hjk k hk)]
      simp
    have h2 : ∑ k ∈ Finset.Ico N j, cutObstacle (h k) j x ≤ 0 :=
      Finset.sum_nonpos fun k _ => (cutObstacle_mem (hnonneg k) j x).2
    linarith
  calc φ x ≤ u j x := iInf_le (fun j => u j x) j
    _ ≤ (F j x : EReal) := hule j x
    _ ≤ ((-(N : ℝ) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hFle
    _ < (y : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)

/-- **Sets of outer capacity zero are `ManifoldLocallyPluripolar`.** -/
theorem manifoldLocallyPluripolar_of_outerCapacityZero (hn : 0 < n) [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hvol : 0 < diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega))
    {E : Set M} (hE : OuterCapacityZero omega E) :
    ManifoldLocallyPluripolar (n := n) E := by
  obtain ⟨φ, hφ, hpoles⟩ := exists_isThetaPshPotential_poles_of_outerCapacityZero hn omega hvol hE
  exact ManifoldLocallyPluripolar.mono (quasiPsh_poles_manifoldLocallyPluripolar
    hφ.quasiPshPotential) fun x hx => hpoles x hx

end

end SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
