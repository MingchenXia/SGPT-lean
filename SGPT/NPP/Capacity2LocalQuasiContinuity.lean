import SGPT.NPP.Capacity2QuasiContinuity
import SGPT.Foundations.Analysis.Pending.ThetaCapacityQuasiContinuity
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacitySublevel

/-!
# Quasi-continuity of quasi-psh functions on open subsets

Source `ex:psh_qc` (chapter `chapter_npp.tex`): a quasi-psh function on an open subset
`U ⊆ X` is quasi-continuous on `U`.  Here quasi-psh on `U` is taken in its local form
`IsLocalQuasiPshOn` (in every holomorphic chart of `X`, near every point over `U`, the
coordinate expression is psh plus smooth, and the function is not identically `-∞` near any
point of `U`); `Capacity2QuasiPshBridge` shows that the source's `def:qpsh` for the complex
manifold `U` implies it.

Proof (Guedj--Zeriahi, Thm. 4.20, via Bedford--Taylor).  Near `x ∈ U`, in a chart ball `D`,
`u = p + h` with `p` psh and `h` smooth.  For a level `k`, `max(p, -k)` is a bounded psh
function, quasi-continuous for the relative capacity of `D` (Bedford--Taylor), and the open
sublevel set `{p < -k}` has relative capacity `O(1/k)` (Chern--Levine--Nirenberg); the global
Kähler capacity of a subset of the chart neighbourhood is at most a constant times the relative
capacity of its image.  The neighbourhood does not depend on the tolerance, so the local
statements glue along a countable subcover of `U` (`X` is second countable).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal NNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open ThetaCapacity
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The coercion `ℝ → EReal` commutes with `max`. -/
theorem coe_max_ereal' (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_max

/-- Quasi-psh functions on an open subset `U ⊆ X`, local form: in every holomorphic chart the
coordinate expression is psh plus smooth near every point over `U`, and no point of `U` has a
neighbourhood on which the function is identically `-∞` (on `U`).  Values outside `U` are
irrelevant. -/
def IsLocalQuasiPshOn (U : Set M) (u : M → EReal) : Prop :=
  (∀ e : ComplexChart n M, QuasiPlurisubharmonicOn (chartFunction u e)
      (e.val.target ∩ e.val.symm ⁻¹' U)) ∧
    ∀ x ∈ U, ∀ W : Set M, IsOpen W → x ∈ W → ∃ y ∈ W ∩ U, u y ≠ ⊥

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Local quasi-continuity for the Kähler capacity**, with the neighbourhood chosen before
the tolerance. -/
theorem exists_nhds_forall_kahlerCapacity_qc (omega : KahlerBackground n M) {U : Set M}
    (hUo : IsOpen U) {u : M → EReal} (hu : IsLocalQuasiPshOn (n := n) U u) {x : M} (hx : x ∈ U) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ N ⊆ U ∧ ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧ thetaCapacity omega.form (fun _ => 0) G < ENNReal.ofReal eps ∧
        (∀ y ∈ N \ G, u y ≠ ⊥) ∧ ContinuousOn (fun y => (u y).toReal) (N \ G) := by
  classical
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel n := e.val x with hz₀
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hxs
  have hz₀U : z₀ ∈ e.val.target ∩ e.val.symm ⁻¹' U :=
    ⟨hz₀t, by simpa only [mem_preimage, hz₀, e.val.left_inv hxs] using hx⟩
  obtain ⟨p, h, hp, hh, heq⟩ := hu.1 e z₀ hz₀U
  obtain ⟨Up, hUpo, hz₀Up, hpdisc⟩ := hp
  obtain ⟨W, rho, hz₀W, hrho⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials omega.form e z₀ hz₀t
  have hS : Up ∩ W ∩ {y | ContDiffAt ℝ ∞ h y} ∩
      {y | chartFunction u e y = p y + (h y : EReal)} ∩ (e.val.target ∩ e.val.symm ⁻¹' U) ∈
        𝓝 z₀ :=
    inter_mem (inter_mem (inter_mem (inter_mem (hUpo.mem_nhds hz₀Up) (hrho.1.mem_nhds hz₀W))
      hh) heq) ((e.val.isOpen_inter_preimage_symm hUo).mem_nhds hz₀U)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hS
  have hbUp : ball z₀ r ⊆ Up := fun z hz => (hrS hz).1.1.1.1
  have hbW : ball z₀ r ⊆ W := fun z hz => (hrS hz).1.1.1.2
  have hbh : ∀ z ∈ ball z₀ r, ContDiffAt ℝ ∞ h z := fun z hz => (hrS hz).1.1.2
  have hbeq : ∀ z ∈ ball z₀ r, chartFunction u e z = p z + (h z : EReal) := fun z hz =>
    (hrS hz).1.2
  have hbU : ∀ z ∈ ball z₀ r, z ∈ e.val.target ∧ e.val.symm z ∈ U := fun z hz => (hrS hz).2
  set R : ℝ := r / 8 with hR_def
  have hR : 0 < R := by positivity
  have hcb : closedBall z₀ (4 * R) ⊆ ball z₀ r :=
    closedBall_subset_ball (by rw [hR_def]; linarith)
  set D : Opens (ComplexModel n) := ⟨ball z₀ (4 * R), isOpen_ball⟩ with hD_def
  have hDr : (D : Set (ComplexModel n)) ⊆ ball z₀ r := ball_subset_closedBall.trans hcb
  have hDt : (D : Set (ComplexModel n)) ⊆ e.val.target := fun z hz => (hbU z (hDr hz)).1
  have hrhoD : IsSmoothLocalPotential omega.form.val e (D : Set (ComplexModel n)) rho :=
    hrho.mono isOpen_ball (hDr.trans hbW)
  obtain ⟨L, hLbd⟩ := (isCompact_closedBall z₀ (4 * R)).exists_bound_of_continuousOn
    ((hrho.2.2.1.continuousOn).mono (hcb.trans hbW))
  have hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L := fun z hz => by
    simpa [Real.norm_eq_abs] using hLbd z (ball_subset_closedBall hz)
  have hL0 : 0 ≤ L := le_trans (abs_nonneg (rho z₀))
    (by simpa [Real.norm_eq_abs] using hLbd z₀ (mem_closedBall_self (by positivity)))
  -- the psh part on the ball
  have hpOn : PlurisubharmonicOn p (ball z₀ r) :=
    (hpdisc.mono hbUp).plurisubharmonicOn isOpen_ball
  have hpt : ∀ z ∈ ball z₀ r, p z ≠ ⊤ := fun z hz => hpdisc.ne_top z (hbUp hz)
  obtain ⟨zmax, hzmax, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (nonempty_closedBall.mpr (by positivity : (0 : ℝ) ≤ 4 * R)) (isCompact_closedBall z₀ (4 * R))
    (hpdisc.upperSemicontinuousOn.mono (hcb.trans hbUp))
  set B : ℝ := (p zmax).toReal
  have hpB : ∀ z ∈ closedBall z₀ (4 * R), p z ≤ (B : EReal) := fun z hz =>
    (hmax hz).trans (EReal.le_coe_toReal (hpt zmax (hcb hzmax)))
  have hne : ∃ a ∈ ball z₀ r, p a ≠ ⊥ := by
    obtain ⟨y, ⟨hyW, hyU⟩, hyb⟩ := hu.2 x hx (e.val.source ∩ e.val ⁻¹' ball z₀ r)
      (e.val.isOpen_inter_preimage isOpen_ball) ⟨hxs, mem_ball_self hr⟩
    refine ⟨e.val y, hyW.2, fun hpb => hyb ?_⟩
    have h1 := hbeq (e.val y) hyW.2
    simp only [chartFunction, e.val.left_inv hyW.1, hpb, EReal.bot_add] at h1
    exact h1
  -- the sublevel estimate
  obtain ⟨A, Ssub, hSpos, hsub⟩ := exists_relCapacity_sublevel_le z₀ (half_pos hR) (Ω := D)
    (closedBall_subset_ball (by linarith)) (convex_ball z₀ r).isPreconnected hpOn hne
    ((closedBall_subset_ball (by rw [hR_def]; linarith)))
  set K : ℝ := (0 - 0 + 2 * L + 2) ^ n with hK_def
  have hK0 : 0 < K := pow_pos (by linarith) n
  -- the neighbourhood
  set N : Set M := e.val.source ∩ e.val ⁻¹' ball z₀ (R / 2 / 2) with hN_def
  have hNo : IsOpen N := e.val.isOpen_inter_preimage isOpen_ball
  have hxN : x ∈ N := ⟨hxs, mem_ball_self (by positivity)⟩
  have hNr : ∀ y ∈ N, e.val y ∈ ball z₀ r := fun y hy =>
    ball_subset_ball (by rw [hR_def]; linarith) hy.2
  have hNU : N ⊆ U := fun y hy => by
    have := (hbU (e.val y) (hNr y hy)).2
    rwa [e.val.left_inv hy.1] at this
  refine ⟨N, hNo, hxN, hNU, fun eps heps => ?_⟩
  have heps' : 0 < eps / (2 * K) := by positivity
  -- the truncation level
  have hlim : Tendsto (fun k : ℕ => A / (Ssub + k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ Ssub tendsto_natCast_atTop_atTop)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds heps')).exists
  set g : ComplexModel n → ℝ := fun z => (max (p z) (((-(k : ℝ)) : ℝ) : EReal)).toReal with hg_def
  have hgcoe : ∀ z ∈ ball z₀ r, ((g z : ℝ) : EReal) = max (p z) (((-(k : ℝ)) : ℝ) : EReal) :=
    fun z hz => EReal.coe_toReal (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hpt z hz))
      (EReal.coe_lt_top _))) (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _))
  have hgpsh : PlurisubharmonicOn (fun z => ((g z : ℝ) : EReal)) (D : Set (ComplexModel n)) := by
    intro z hz
    have hmaxpsh := ((hpOn.mono hDr).max (plurisubharmonicOn_const (-(k : ℝ)) _)) z hz
    refine hmaxpsh.congr ?_
    filter_upwards [D.isOpen.mem_nhds hz] with w hw
    exact (hgcoe w (hDr hw)).symm
  have hg : IsLocallyBoundedPshOn D g := by
    refine isLocallyBoundedPshOn_of_abs_le hgpsh (C := k + |B|) fun z hz => ?_
    have hgz : ((g z : ℝ) : EReal) = max (p z) (((-(k : ℝ)) : ℝ) : EReal) := hgcoe z (hDr hz)
    have hlo : -(k : ℝ) ≤ g z := by
      have : (((-(k : ℝ)) : ℝ) : EReal) ≤ (g z : EReal) := hgz ▸ le_max_right _ _
      exact EReal.coe_le_coe_iff.mp this
    have hhi : g z ≤ max B (-(k : ℝ)) := by
      have : (g z : EReal) ≤ ((max B (-(k : ℝ)) : ℝ) : EReal) := by
        rw [hgz, coe_max_ereal']
        exact max_le_max (hpB z (ball_subset_closedBall hz)) le_rfl
      exact EReal.coe_le_coe_iff.mp this
    rw [abs_le]
    constructor
    · have := abs_nonneg B; linarith
    · have := le_abs_self B; have := abs_nonneg B; have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rcases le_total B (-(k : ℝ)) with h1 | h1
      · rw [max_eq_right h1] at hhi; linarith
      · rw [max_eq_left h1] at hhi; linarith
  obtain ⟨G₀, hG₀o, hG₀cap, hG₀cont⟩ :=
    IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_ball hg (x₀ := z₀) hR
      (closedBall_subset_ball (by linarith)) heps'
  set G₁ : Set (ComplexModel n) :=
    ball z₀ (R / 2 / 2) ∩ {z | p z < (((-(k : ℝ)) : ℝ) : EReal)} with hG₁_def
  have hG₁o : IsOpen G₁ := isOpen_ball_inter_sublevel hpOn
    (ball_subset_ball (by rw [hR_def]; linarith)) _
  have hG₁cap : relCapacity D G₁ ≤ ENNReal.ofReal (eps / (2 * K)) :=
    (hsub k).trans (ENNReal.ofReal_le_ofReal hk.le)
  set G : Set M := e.val.source ∩ e.val ⁻¹' ((G₀ ∪ G₁) ∩ (D : Set (ComplexModel n))) with hG_def
  have hGo : IsOpen G := e.val.isOpen_inter_preimage ((hG₀o.union hG₁o).inter D.isOpen)
  have hGsub : G ⊆ (ThetaCapacityChart.diagSlotChart omega.form e D hDt rho hrhoD).source :=
    fun y hy => ⟨hy.1, hy.2.2⟩
  refine ⟨G, hGo, ?_, ?_⟩
  · have h1 := ThetaCapacityChart.thetaCapacity_le_relCapacity (V := fun _ => 0) e D hDt rho
      hrhoD (c := 0) (d := 0) le_rfl hL0 (fun _ => ⟨le_rfl, le_rfl⟩) hL G hGsub
    have h2 : relCapacity D (e.val '' G) ≤ relCapacity D G₀ + relCapacity D G₁ := by
      refine (relCapacity_mono ?_).trans (relCapacity_union_le D G₀ G₁)
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2.1
    have h3 : relCapacity D (e.val '' G) < ENNReal.ofReal (eps / K) := by
      refine h2.trans_lt ((ENNReal.add_lt_add_of_lt_of_le
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hG₁cap) hG₀cap hG₁cap).trans_eq ?_)
      rw [← ENNReal.ofReal_add heps'.le heps'.le]
      congr 1
      field_simp
      ring
    have hKne : ENNReal.ofReal K ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hK0
    calc thetaCapacity omega.form (fun _ => 0) G
        ≤ ENNReal.ofReal K * relCapacity D (e.val '' G) := by rw [hK_def]; exact h1
      _ < ENNReal.ofReal K * ENNReal.ofReal (eps / K) := by
        rw [mul_comm, mul_comm (ENNReal.ofReal K)]
        exact ENNReal.mul_lt_mul_left hKne ENNReal.ofReal_ne_top h3
      _ = ENNReal.ofReal eps := by
        rw [← ENNReal.ofReal_mul hK0.le, mul_div_cancel₀ _ hK0.ne']
  -- the point values off `G`
  have hoff : ∀ y ∈ N \ G, e.val y ∉ G₀ ∧ e.val y ∉ G₁ := by
    rintro y ⟨hyN, hyG⟩
    have hyD : e.val y ∈ (D : Set (ComplexModel n)) :=
      ball_subset_ball (by rw [hR_def]; linarith) hyN.2
    exact ⟨fun h0 => hyG ⟨hyN.1, Or.inl h0, hyD⟩, fun h1 => hyG ⟨hyN.1, Or.inr h1, hyD⟩⟩
  have hval : ∀ y ∈ N \ G, u y = ((g (e.val y) + h (e.val y) : ℝ) : EReal) := by
    intro y hy
    obtain ⟨-, h1⟩ := hoff y hy
    have hpk : (((-(k : ℝ)) : ℝ) : EReal) ≤ p (e.val y) := not_lt.mp fun hlt => h1 ⟨hy.1.2, hlt⟩
    have hb := hbeq (e.val y) (hNr y hy.1)
    simp only [chartFunction, e.val.left_inv hy.1.1] at hb
    rw [hb, EReal.coe_add, hgcoe _ (hNr y hy.1), max_eq_left hpk]
  refine ⟨fun y hy => by rw [hval y hy]; exact EReal.coe_ne_bot _, ?_⟩
  have hmaps : MapsTo e.val (N \ G) (ball z₀ (R / 2) \ G₀) := fun y hy =>
    ⟨ball_subset_ball (by rw [hR_def]; linarith) hy.1.2, (hoff y hy).1⟩
  have hc1 : ContinuousOn (fun z => g z + h z) (ball z₀ (R / 2) \ G₀) := by
    refine hG₀cont.add ?_
    intro z hz
    exact ((hbh z (ball_subset_ball (by rw [hR_def]; linarith) hz.1)).continuousAt).continuousWithinAt
  have hcomp : ContinuousOn (fun y => g (e.val y) + h (e.val y)) (N \ G) :=
    hc1.comp (e.val.continuousOn.mono fun y hy => hy.1.1) hmaps
  refine hcomp.congr fun y hy => ?_
  rw [hval y hy, EReal.toReal_coe]

/-- **Kähler-capacity quasi-continuity on an open set**: for every `η > 0` there is an open
`G` of Kähler capacity `< η` such that `u` is finite and continuous on `U \ G`. -/
theorem exists_isOpen_kahlerCapacity_lt_on_open (omega : KahlerBackground n M) {U : Set M}
    (hUo : IsOpen U) {u : M → EReal} (hu : IsLocalQuasiPshOn (n := n) U u) {η : ℝ≥0∞}
    (hη : 0 < η) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity omega.form (fun _ => 0) G < η ∧
      (∀ y ∈ U \ G, u y ≠ ⊥) ∧ ContinuousOn (fun y => (u y).toReal) (U \ G) := by
  classical
  rcases eq_empty_or_nonempty U with hU0 | hUne
  · refine ⟨∅, isOpen_empty, by simpa using hη, ?_, ?_⟩
    · intro y hy; rw [hU0] at hy; exact absurd hy.1 (notMem_empty y)
    · rw [hU0, empty_sdiff]; exact continuousOn_empty _
  choose N hNo hxN hNU hNqc using fun x : U => exists_nhds_forall_kahlerCapacity_qc omega hUo hu x.2
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : U => N x) hNo
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    have : x ∈ ⋃ i ∈ T, N i := hTeq ▸ mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp this
    exact ⟨i, hi⟩
  obtain ⟨f, rfl⟩ := hTc.exists_eq_range hTne
  obtain ⟨ε', hε'pos, hsum⟩ := ENNReal.exists_pos_sum_of_countable hη.ne' ℕ
  choose G hGo hGcap hGf hGcont using fun m : ℕ => hNqc (f m) (ε' m) (hε'pos m)
  have hcover : ∀ y ∈ U, ∃ m, y ∈ N (f m) := by
    intro y hy
    have : y ∈ ⋃ i ∈ range f, N i := hTeq ▸ mem_iUnion.mpr ⟨⟨y, hy⟩, hxN ⟨y, hy⟩⟩
    obtain ⟨i, ⟨m, rfl⟩, hm⟩ := mem_iUnion₂.mp this
    exact ⟨m, hm⟩
  refine ⟨⋃ m, G m, isOpen_iUnion hGo, ?_, ?_, ?_⟩
  · calc thetaCapacity omega.form (fun _ => 0) (⋃ m, G m)
        ≤ ∑' m, thetaCapacity omega.form (fun _ => 0) (G m) := thetaCapacity_iUnion_le _ _ _
      _ ≤ ∑' m, (ε' m : ℝ≥0∞) := ENNReal.tsum_le_tsum fun m => by
          simpa only [ENNReal.ofReal_coe_nnreal] using (hGcap m).le
      _ < η := hsum
  · intro y hy
    obtain ⟨m, hm⟩ := hcover y hy.1
    exact hGf m y ⟨hm, fun h => hy.2 (mem_iUnion.mpr ⟨m, h⟩)⟩
  · intro y hy
    obtain ⟨m, hm⟩ := hcover y hy.1
    have hc : ContinuousWithinAt (fun y => (u y).toReal) ((U \ ⋃ m, G m) ∩ N (f m)) y :=
      ((hGcont m) y ⟨hm, fun h => hy.2 (mem_iUnion.mpr ⟨m, h⟩)⟩).mono fun z hz =>
        ⟨hz.2, fun h => hz.1.2 (mem_iUnion.mpr ⟨m, h⟩)⟩
    exact (continuousWithinAt_inter ((hNo (f m)).mem_nhds hm)).mp hc

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A local quasi-psh function never takes the value `+∞` on `U`. -/
theorem IsLocalQuasiPshOn.ne_top {U : Set M} {u : M → EReal}
    (hu : IsLocalQuasiPshOn (n := n) U u) {x : M} (hx : x ∈ U) : u x ≠ ⊤ := by
  set e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz₀U : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' U :=
    ⟨e.val.map_source hxs, by simpa only [mem_preimage, e.val.left_inv hxs] using hx⟩
  obtain ⟨p, h, hp, -, heq⟩ := hu.1 e (e.val x) hz₀U
  have h1 : chartFunction u e (e.val x) = p (e.val x) + (h (e.val x) : EReal) := heq.self_of_nhds
  simp only [chartFunction, e.val.left_inv hxs] at h1
  rw [h1]
  exact EReal.add_ne_top hp.ne_top (EReal.coe_ne_top _)

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A local quasi-psh function is upper semicontinuous at every point of `U`. -/
theorem IsLocalQuasiPshOn.upperSemicontinuousAt {U : Set M} {u : M → EReal}
    (hu : IsLocalQuasiPshOn (n := n) U u) {x : M} (hx : x ∈ U) :
    UpperSemicontinuousAt u x := by
  set e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz₀t : e.val x ∈ e.val.target := e.val.map_source hxs
  have hz₀U : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' U :=
    ⟨hz₀t, by simpa only [mem_preimage, e.val.left_inv hxs] using hx⟩
  obtain ⟨p, h, hp, hh, heq⟩ := hu.1 e (e.val x) hz₀U
  obtain ⟨Up, hUpo, hz₀Up, hpdisc⟩ := hp
  have hpusc : UpperSemicontinuousAt p (e.val x) := fun c hc => by
    have h1 := hpdisc.upperSemicontinuousOn _ hz₀Up c hc
    rwa [nhdsWithin_eq_nhds.mpr (hUpo.mem_nhds hz₀Up)] at h1
  have hhc : ContinuousAt (fun y => (h y : EReal)) (e.val x) :=
    continuous_coe_real_ereal.continuousAt.comp hh.self_of_nhds.continuousAt
  have hsum : UpperSemicontinuousAt (fun y => p y + (h y : EReal)) (e.val x) :=
    hpusc.add' hhc.upperSemicontinuousAt
      (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
  have hF : UpperSemicontinuousAt (chartFunction u e) (e.val x) := by
    intro c hc
    have h0 : chartFunction u e (e.val x) = p (e.val x) + (h (e.val x) : EReal) :=
      heq.self_of_nhds
    have hc' : p (e.val x) + (h (e.val x) : EReal) < c := by rw [← h0]; exact hc
    filter_upwards [hsum c hc', heq] with y hy hyeq
    rwa [hyeq]
  intro c hc
  have hc' : chartFunction u e (e.val x) < c := by
    simpa only [chartFunction, e.val.left_inv hxs] using hc
  filter_upwards [(e.val.continuousAt hxs).eventually (hF c hc'),
    e.val.open_source.mem_nhds hxs] with y hy hys
  simpa only [chartFunction, e.val.left_inv hys] using hy

omit [IsComplexManifold n M] [CompactSpace M] in
/-- A local quasi-psh function on an open set is Borel on that set. -/
theorem IsLocalQuasiPshOn.measurable_restrict {U : Opens M} {u : M → EReal}
    (hu : IsLocalQuasiPshOn (n := n) (U : Set M) u) :
    Measurable (fun x : U => u x.1) := by
  have husc : UpperSemicontinuous (fun x : U => u x.1) := fun x c hc =>
    continuous_subtype_val.continuousAt.eventually ((hu.upperSemicontinuousAt x.2) c hc)
  exact husc.measurable

/-- **Source `ex:psh_qc`, first claim, on an open subset.**  A quasi-psh function on an open
`U ⊆ X` (local form) is quasi-continuous on `U` (`def:qc_fun`, capacity of any big form). -/
theorem sourceQuasiContinuousOn_of_isLocalQuasiPshOn (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {u : M → EReal} (hu : IsLocalQuasiPshOn (n := n) (U : Set M) u) :
    SourceQuasiContinuousOn θ U (fun x => u x.1) := by
  refine ⟨hu.measurable_restrict, fun ε hε => ?_⟩
  obtain ⟨C, hC, hctl⟩ := exists_source_capacity_control_by_kahler omega θ hbig (half_pos hε)
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2 / C) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ := exists_isOpen_kahlerCapacity_lt_on_open omega U.isOpen hu hη
  refine ⟨G ∩ U, hGo.inter U.isOpen, inter_subset_right, ?_, fun x => (u x.1).toReal, ?_, ?_⟩
  · calc sourceThetaCapacity θ (G ∩ U)
        ≤ sourceThetaCapacity θ G := sourceThetaCapacity_mono θ inter_subset_left
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C *
            sourceThetaCapacity (nativeClosedFormToAtlas omega.form) G := hctl G
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C * ENNReal.ofReal (ε / 2 / C) := by
          rw [sourceThetaCapacity_kahler]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hGc.le zero_le)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne',
            ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  · intro x hx
    have hxG : x.1 ∉ G := fun h => hx ⟨h, x.2⟩
    exact (hGcont x.1 ⟨x.2, hxG⟩).comp continuous_subtype_val.continuousWithinAt
      fun y hy => ⟨y.2, fun h => hy ⟨h, y.2⟩⟩
  · intro x hx
    have hxG : x.1 ∉ G := fun h => hx ⟨h, x.2⟩
    exact (EReal.coe_toReal (hu.ne_top x.2) (hGf x.1 ⟨x.2, hxG⟩)).symm

/-- **Source `ex:psh_qc`, second claim, on an open subset.**  For quasi-psh `φ, ψ` on an open
`U ⊆ X` (local form), the function equal to `φ - ψ` where `φ ∨ ψ ≠ -∞` and to `+∞` elsewhere is
quasi-continuous on `U`. -/
theorem sourceQuasiContinuousOn_qpshDifference_of_isLocalQuasiPshOn
    (omega : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {φ ψ : M → EReal} (hφ : IsLocalQuasiPshOn (n := n) (U : Set M) φ)
    (hψ : IsLocalQuasiPshOn (n := n) (U : Set M) ψ) :
    SourceQuasiContinuousOn θ U (fun x => qpshDifference φ ψ x.1) := by
  refine ⟨measurable_qpshDifference hφ.measurable_restrict hψ.measurable_restrict,
    fun ε hε => ?_⟩
  obtain ⟨C, hC, hctl⟩ := exists_source_capacity_control_by_kahler omega θ hbig (half_pos hε)
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2 / C) / 2 :=
    ENNReal.half_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ := exists_isOpen_kahlerCapacity_lt_on_open omega U.isOpen hφ hη
  obtain ⟨H, hHo, hHc, hHf, hHcont⟩ := exists_isOpen_kahlerCapacity_lt_on_open omega U.isOpen hψ hη
  have hGH : thetaCapacity omega.form (fun _ => 0) (G ∪ H) ≤ ENNReal.ofReal (ε / 2 / C) :=
    (thetaCapacity_union_le _ _ _ _).trans
      ((add_le_add hGc.le hHc.le).trans (ENNReal.add_halves _).le)
  refine ⟨(G ∪ H) ∩ U, (hGo.union hHo).inter U.isOpen, inter_subset_right, ?_,
    fun x => (φ x.1).toReal - (ψ x.1).toReal, ?_, ?_⟩
  · calc sourceThetaCapacity θ ((G ∪ H) ∩ U)
        ≤ sourceThetaCapacity θ (G ∪ H) := sourceThetaCapacity_mono θ inter_subset_left
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C *
            sourceThetaCapacity (nativeClosedFormToAtlas omega.form) (G ∪ H) := hctl _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C * ENNReal.ofReal (ε / 2 / C) := by
          rw [sourceThetaCapacity_kahler]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hGH zero_le)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne',
            ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  · intro x hx
    have hxG : x.1 ∉ G := fun h => hx ⟨Or.inl h, x.2⟩
    have hxH : x.1 ∉ H := fun h => hx ⟨Or.inr h, x.2⟩
    have hc1 : ContinuousWithinAt (fun y : U => (φ y.1).toReal)
        {y : U | y.1 ∉ (G ∪ H) ∩ U} x :=
      (hGcont x.1 ⟨x.2, hxG⟩).comp continuous_subtype_val.continuousWithinAt
        fun y (hy : y.1 ∉ (G ∪ H) ∩ U) => ⟨y.2, fun h => hy ⟨Or.inl h, y.2⟩⟩
    have hc2 : ContinuousWithinAt (fun y : U => (ψ y.1).toReal)
        {y : U | y.1 ∉ (G ∪ H) ∩ U} x :=
      (hHcont x.1 ⟨x.2, hxH⟩).comp continuous_subtype_val.continuousWithinAt
        fun y (hy : y.1 ∉ (G ∪ H) ∩ U) => ⟨y.2, fun h => hy ⟨Or.inr h, y.2⟩⟩
    exact hc1.sub hc2
  · intro x hx
    have hxG : x.1 ∉ G := fun h => hx ⟨Or.inl h, x.2⟩
    have hxH : x.1 ∉ H := fun h => hx ⟨Or.inr h, x.2⟩
    exact qpshDifference_eq_coe (hφ.ne_top x.2) (hGf x.1 ⟨x.2, hxG⟩) (hψ.ne_top x.2)
      (hHf x.1 ⟨x.2, hxH⟩)

end SGPT.NPP
