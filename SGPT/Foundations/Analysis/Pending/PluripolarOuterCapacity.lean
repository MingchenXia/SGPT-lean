import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacitySublevel
import SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
import SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere

set_option autoImplicit false

/-!
# Locally pluripolar sets have outer capacity zero; countable unions (steps C2, C3 of I-0510)

On a compact Kähler manifold `(M, ω)` with `Cap_ω = thetaCapacity ω 0`:

* **C2** (`outerCapacityZero_of_manifoldLocallyPluripolar`): a `ManifoldLocallyPluripolar` set has
  *outer* capacity zero — it lies in open sets of arbitrarily small `Cap_ω`.  (The inner statement
  `Cap_ω(E) = 0` is `ThetaCapacity.thetaCapacity_eq_zero_of_manifoldLocallyPluripolar`; the outer
  one is what the pluripolarity criterion of step C1 consumes.)
* **C3** (`manifoldLocallyPluripolar_iUnion`, `countablyStablePluripolar`): a countable union of
  `ManifoldLocallyPluripolar` sets is `ManifoldLocallyPluripolar` (Lelong's theorem) on a compact
  connected Kähler manifold — this is the predicate
  `RooftopObstacleQuasiEverywhere.CountablyStablePluripolar` consumed by Xia's (2.20).

*Proof of C2.*  Near every point `x`, in the chart `e` at `x`, the local witness `ψ` of the chart
image (`ψ` psh, `≢ -∞`, `= -∞` on the image of `E`) has sublevel sets `{ψ < -k} ∩ B(e x, r/2)`
of relative capacity `O(1/k)` (`BedfordTaylor.exists_relCapacity_sublevel_le`: CLN for an
unbounded weight, uniform over the competitors), and the chart comparison
`ThetaCapacityChart.thetaCapacity_le_relCapacity` transfers this to `Cap_ω` of the open sets
`G_k = e⁻¹({ψ < -k} ∩ B(e x, r/2))`, which contain `E` near `x`.  A finite cover of the compact
`M` and finite subadditivity finish the proof.

*Proof of C3.*  Outer capacity zero is countably stable (choose `G_j ⊇ S_j` with
`Cap_ω(G_j) < ε_j`, `∑ ε_j < ε`, and use countable subadditivity), and C1
(`KahlerVolumePositive.manifoldLocallyPluripolar_of_outerCapacityZero'`) returns from outer
capacity zero to pluripolarity.  In dimension `0` every `ManifoldLocallyPluripolar` set is empty
(`eq_empty_of_manifoldLocallyPluripolar_dim_zero`), so the predicate holds trivially there.

No Josefson theorem is used.  Sources: Bedford--Taylor, *A new capacity for plurisubharmonic
functions* (Acta Math. 1982), §3, Prop. 3.6 and Thm 7.1; Guedj--Zeriahi, *Intrinsic capacities on
compact Kähler manifolds* (J. Geom. Anal. 2005), §3 and Thm 5.2.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity

noncomputable section

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
open SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
open SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- In dimension `0` a `ManifoldLocallyPluripolar` set is empty: the model space is a point, so a
local witness is finite at the only point of its domain. -/
theorem eq_empty_of_manifoldLocallyPluripolar_dim_zero {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel 0) N] [IsComplexManifold 0 N] {S : Set N}
    (hS : ManifoldLocallyPluripolar (n := 0) (M := N) S) : S = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  set e : ComplexChart 0 N := complexChartAt (n := 0) y
  have hys : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hys
  obtain ⟨V, u, -, hzV, -, -, ⟨a, haV, hua⟩, hp⟩ := hS e (e.val y) hz
  have ha : a = e.val y := by
    ext i
    exact i.elim0
  apply hua
  rw [ha]
  refine hp _ hzV ⟨hz, ?_⟩
  show e.val.symm (e.val y) ∈ S
  rw [e.val.left_inv hys]
  exact hy

section Compact

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- Finite subadditivity of `Cap_θ` over a `Finset`. -/
theorem thetaCapacity_biUnion_finset_le {ι : Type*} (theta : ClosedRealOneOneForm n M)
    (V : M → EReal) (s : Finset ι) (G : ι → Set M) :
    thetaCapacity theta V (⋃ i ∈ s, G i) ≤ ∑ i ∈ s, thetaCapacity theta V (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (thetaCapacity_union_le theta V _ _).trans (add_le_add le_rfl ih)

/-- **C2, local form.**  Near every point, a `ManifoldLocallyPluripolar` set lies in open sets
`G_k` whose capacities are bounded by a sequence tending to `0`. -/
theorem exists_local_capacity_cover (omega : KahlerBackground n M) {E : Set M}
    (hE : ManifoldLocallyPluripolar (n := n) E) (x : M) :
    ∃ (N : Set M) (G : ℕ → Set M) (b : ℕ → ℝ≥0∞), IsOpen N ∧ x ∈ N ∧
      (∀ k, IsOpen (G k)) ∧ (∀ k, E ∩ N ⊆ G k) ∧
      (∀ k, thetaCapacity omega.form (fun _ => 0) (G k) ≤ b k) ∧
      Tendsto b atTop (𝓝 0) := by
  classical
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  set z : ComplexModel n := e.val x with hzdef
  have hz : z ∈ e.val.target := e.val.map_source hx
  -- the local pluripolar witness and a local potential of `ω`
  obtain ⟨V, ψ, hVo, hzV, hVc, hψ, hne, hp⟩ := hE e z hz
  obtain ⟨W, ρ, hzW, hρ, -⟩ := (isThetaPshPotential_zero omega).1 e z hz
  have hopen : IsOpen (V ∩ W ∩ e.val.target) := (hVo.inter hρ.1).inter e.val.open_target
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hopen z ⟨⟨hzV, hzW⟩, hz⟩
  set r : ℝ := r₀ / 7 with hrdef
  have hr : 0 < r := by positivity
  have h6 : closedBall z (6 * r) ⊆ V ∩ W ∩ e.val.target :=
    (closedBall_subset_ball (by linarith)).trans hball
  set D : TopologicalSpace.Opens (ComplexModel n) := ⟨ball z (6 * r), isOpen_ball⟩ with hDdef
  have hD : (D : Set (ComplexModel n)) ⊆ e.val.target := fun y hy =>
    (h6 (ball_subset_closedBall hy)).2
  have hρD : IsSmoothLocalPotential omega.form.val e D ρ :=
    hρ.mono isOpen_ball fun y hy => (h6 (ball_subset_closedBall hy)).1.2
  -- a bound for the local potential
  obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall z (6 * r)).exists_bound_of_continuousOn
    (hρ.2.2.1.continuousOn.mono fun y hy => (h6 hy).1.2)
  set L : ℝ := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hL : ∀ y ∈ (D : Set (ComplexModel n)), |ρ y| ≤ L := fun y hy =>
    (hL₀ y (ball_subset_closedBall hy)).trans (le_max_left _ _)
  -- the sublevel sets
  have hbV : closedBall z (3 * r) ⊆ V :=
    (closedBall_subset_closedBall (by linarith)).trans fun y hy => (h6 hy).1.1
  have hhalfV : ball z (r / 2) ⊆ V :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hbV)
  set O : ℕ → Set (ComplexModel n) :=
    fun k => ball z (r / 2) ∩ {y | ψ y < ((-(k : ℝ) : ℝ) : EReal)} with hOdef
  have hOo : ∀ k, IsOpen (O k) := fun k => isOpen_ball_inter_sublevel hψ hhalfV _
  have hrel := tendsto_relCapacity_sublevel z hr (Ω := D)
    (closedBall_subset_ball (by linarith)) hVc hψ hne hbV
  refine ⟨e.val.source ∩ e.val ⁻¹' ball z (r / 2), fun k => e.val.source ∩ e.val ⁻¹' O k,
    fun k => ENNReal.ofReal ((0 - 0 + 2 * L + 2) ^ n) * relCapacity D (O k),
    e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hx, mem_ball_self (by positivity)⟩, fun k => e.val.isOpen_inter_preimage (hOo k),
    fun k y hy => ?_, fun k => ?_, ?_⟩
  · -- `E` near `x` lies in every `G_k`
    obtain ⟨hyE, hys, hyb⟩ := hy
    refine ⟨hys, hyb, ?_⟩
    have hmem : e.val y ∈ pluripolarChartSet E e := by
      refine ⟨e.val.map_source hys, ?_⟩
      show e.val.symm (e.val y) ∈ E
      rw [e.val.left_inv hys]
      exact hyE
    have hbot : ψ (e.val y) = ⊥ := hp (e.val y) (hhalfV hyb) hmem
    show ψ (e.val y) < _
    rw [hbot]
    exact EReal.bot_lt_coe _
  · -- the chart comparison
    have hsub : e.val.source ∩ e.val ⁻¹' O k ⊆
        (diagSlotChart omega.form e D hD ρ hρD).source := fun y hy =>
      ⟨hy.1, ball_subset_ball (by linarith) hy.2.1⟩
    refine (thetaCapacity_le_relCapacity e D hD ρ hρD (c := 0) (d := 0) le_rfl hL0
      (fun _ => by simp) hL _ hsub).trans ?_
    exact mul_le_mul_right (relCapacity_mono (by rintro _ ⟨y, hy, rfl⟩; exact hy.2)) _
  · have h := ENNReal.Tendsto.const_mul hrel
      (Or.inr (ENNReal.ofReal_ne_top (r := (0 - 0 + 2 * L + 2) ^ n)))
    rw [mul_zero] at h
    exact h

/-- **Step C2 of I-0510: a `ManifoldLocallyPluripolar` set has outer capacity zero.** -/
theorem outerCapacityZero_of_manifoldLocallyPluripolar (omega : KahlerBackground n M)
    {E : Set M} (hE : ManifoldLocallyPluripolar (n := n) E) : OuterCapacityZero omega E := by
  classical
  choose N G b hNo hxN hGo hEG hcap hb using fun x => exists_local_capacity_cover omega hE x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.mpr ⟨x, hxN x⟩)
  intro ε hε
  have hsum : Tendsto (fun k => ∑ x ∈ t, b x k) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum t fun x _ => hb x
  obtain ⟨k, hk⟩ := (hsum.eventually (gt_mem_nhds hε)).exists
  refine ⟨⋃ x ∈ t, G x k, isOpen_biUnion fun x _ => hGo x k, fun y hy => ?_, ?_⟩
  · obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x, hxt, hEG x k ⟨hy, hyx⟩⟩
  · calc thetaCapacity omega.form (fun _ => 0) (⋃ x ∈ t, G x k)
        ≤ ∑ x ∈ t, thetaCapacity omega.form (fun _ => 0) (G x k) :=
          thetaCapacity_biUnion_finset_le _ _ t _
      _ ≤ ∑ x ∈ t, b x k := Finset.sum_le_sum fun x _ => hcap x k
      _ < ε := hk

omit [BorelSpace M] in
/-- Outer capacity zero is stable under countable unions. -/
theorem OuterCapacityZero.iUnion {omega : KahlerBackground n M} {S : ℕ → Set M}
    (h : ∀ j, OuterCapacityZero omega (S j)) : OuterCapacityZero omega (⋃ j, S j) := by
  intro ε hε
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose G hGo hSG hGcap using fun j => h j (ε' j) (by exact_mod_cast hε'pos j)
  refine ⟨⋃ j, G j, isOpen_iUnion hGo, iUnion_mono hSG, ?_⟩
  calc thetaCapacity omega.form (fun _ => 0) (⋃ j, G j)
      ≤ ∑' j, thetaCapacity omega.form (fun _ => 0) (G j) := thetaCapacity_iUnion_le _ _ _
    _ ≤ ∑' j, (ε' j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => (hGcap j).le
    _ < ε := hε'sum

/-- **Step C3 of I-0510 (Lelong): countable unions of `ManifoldLocallyPluripolar` sets are
`ManifoldLocallyPluripolar`** on a compact connected Kähler manifold of positive dimension. -/
theorem manifoldLocallyPluripolar_iUnion (hn : 0 < n) [ConnectedSpace M]
    (omega : KahlerBackground n M) {S : ℕ → Set M}
    (hS : ∀ j, ManifoldLocallyPluripolar (n := n) (S j)) :
    ManifoldLocallyPluripolar (n := n) (⋃ j, S j) :=
  manifoldLocallyPluripolar_of_outerCapacityZero' hn omega
    (OuterCapacityZero.iUnion fun j => outerCapacityZero_of_manifoldLocallyPluripolar omega (hS j))

end Compact

/-- **The predicate `CountablyStablePluripolar` holds on every compact connected Kähler
manifold** (any dimension; no measurable structure is needed in the statement). -/
theorem countablyStablePluripolar [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) : CountablyStablePluripolar n M := by
  intro S hS
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hempty : ∀ j, S j = ∅ := fun j => eq_empty_of_manifoldLocallyPluripolar_dim_zero (hS j)
    simp only [hempty, iUnion_empty]
    exact manifoldLocallyPluripolar_empty
  · borelize M
    exact manifoldLocallyPluripolar_iUnion hn omega hS

end

end SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
