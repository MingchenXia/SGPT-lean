import SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal
import SGPT.Foundations.Analysis.Pending.BedfordTaylorQuasiContinuity
import SGPT.Foundations.Analysis.Pending.ThetaCapacityQuasiContinuity

set_option autoImplicit false

/-!
# Xia's Theorem 2.3.2 on an open set where the data are locally bounded

`Pending.ThetaCapacityQuasiContinuity` proves quasi-continuity for `Cap_theta`
only when the reference `V` **and** the potential `w` are bounded on all of
`M`, and `Pending.ThetaCapacityBoundedDegeneracy` shows that pair of
hypotheses is unsatisfiable as soon as `nK({theta}) != emptyset` — the only
case Nakamaye's theorem is about.

`Pending.ThetaCapacityChartLocal` localized the chart bridge, so the same
argument now runs with the two bounds imposed only on an open set `Omega`.
That is exactly the shape Xia uses: his Theorem 2.4.4 works on
`G' <<- G <<- X \ nK({theta})`, where `V_theta` and `P_theta(f)` are locally
bounded by Lemma 2.4.1 and nowhere else.

Two statements:

* the pointwise form, with the neighbourhood chosen before the tolerance —
  this is what makes a compactness argument possible;
* the form over a compact subset `K` of `Omega`: one open `G` of arbitrarily
  small `Cap_theta(-, V)` outside which `w` is continuous on `K`.

The proof is the one of `Pending.ThetaCapacityQuasiContinuity`, with the chart
ball shrunk so that its slot-chart source stays inside `Omega`, and with the
two global bounds replaced by the bounds on that source.
-/

open Set MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
open FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal
open SGPT.Foundations.Analysis.Pending

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Quasi-continuity near a point of an open set on which the data are
bounded, with the neighbourhood chosen first.**  The neighbourhood `N` depends
only on the chart, the local potential and `Omega`, not on `eps`. -/
theorem exists_nhds_forall_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hw : IsThetaPshPotential theta.val w)
    {Omega : Set M} (hOmega : IsOpen Omega) {x : M} (hx : x ∈ Omega)
    (hwb : IsBoundedPotentialOn w Omega) (hVb : IsBoundedPotentialOn V Omega) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ N ⊆ Omega ∧ ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (w y).toReal) (N \ G) := by
  classical
  obtain ⟨cw, dw, hwbd⟩ := hwb
  obtain ⟨cV, dV, hVbd⟩ := hVb
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel n := e.val x with hz₀
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hxs
  obtain ⟨W, rho, hz₀W, hrho⟩ :=
    SGPT.Foundations.Analysis.Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials
      theta e z₀ hz₀t
  -- the coordinate points whose chart preimage lies in `Omega`
  set T : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' Omega with hT_def
  have hTopen : IsOpen T :=
    e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hOmega
  have hz₀T : z₀ ∈ T := by
    refine ⟨hz₀t, ?_⟩
    show e.val.symm (e.val x) ∈ Omega
    rwa [e.val.left_inv hxs]
  obtain ⟨r, hr, hrWT⟩ := Metric.isOpen_iff.mp (hrho.1.inter hTopen) z₀ ⟨hz₀W, hz₀T⟩
  set R : ℝ := r / 8 with hR_def
  have hR : 0 < R := by positivity
  have hcb : closedBall z₀ (4 * R) ⊆ W ∩ T := by
    refine subset_trans ?_ hrWT
    refine closedBall_subset_ball ?_
    rw [hR_def]; linarith
  set D : Opens (ComplexModel n) := ⟨ball z₀ (4 * R), isOpen_ball⟩ with hD_def
  have hDWT : (D : Set (ComplexModel n)) ⊆ W ∩ T :=
    ball_subset_closedBall.trans hcb
  have hDW : (D : Set (ComplexModel n)) ⊆ W := fun z hz => (hDWT hz).1
  have hDT : (D : Set (ComplexModel n)) ⊆ T := fun z hz => (hDWT hz).2
  have hDt : (D : Set (ComplexModel n)) ⊆ e.val.target := hDW.trans hrho.2.1
  have hrhoD : IsSmoothLocalPotential theta.val e (D : Set (ComplexModel n)) rho :=
    hrho.mono isOpen_ball hDW
  set J := diagSlotChart theta e D hDt rho hrhoD with hJ_def
  -- the slot-chart source sits inside `Omega`
  have hJsub : (J.source : Set M) ⊆ Omega := by
    rintro y ⟨hys, hyD⟩
    have : e.val.symm (e.val y) ∈ Omega := (hDT hyD).2
    rwa [e.val.left_inv hys] at this
  have hwJ : ∀ y ∈ (J.source : Set M), (cw : EReal) ≤ w y ∧ w y ≤ (dw : EReal) :=
    fun y hy => hwbd y (hJsub hy)
  have hVJ : ∀ y ∈ (J.source : Set M), (cV : EReal) ≤ V y ∧ V y ≤ (dV : EReal) :=
    fun y hy => hVbd y (hJsub hy)
  have hwD : ∀ z ∈ (D : Set (ComplexModel n)),
      (cw : EReal) ≤ w (e.val.symm z) ∧ w (e.val.symm z) ≤ (dw : EReal) := by
    intro z hz
    exact hwJ _ ((J.patch (fun _ => w) (fun _ => hw.1)).map_target hz)
  have hz₀D : z₀ ∈ (D : Set (ComplexModel n)) :=
    mem_ball_self (by positivity : (0 : ℝ) < 4 * R)
  have hxJ : x ∈ (J.source : Set M) := ⟨hxs, hz₀D⟩
  have hcVdV : cV ≤ dV := by
    have h := hVJ x hxJ
    exact EReal.coe_le_coe_iff.mp (h.1.trans h.2)
  -- a uniform bound for the local potential on the ball
  obtain ⟨L, hLbd⟩ := (isCompact_closedBall z₀ (4 * R)).exists_bound_of_continuousOn
    ((hrho.2.2.1.continuousOn).mono (fun z hz => (hcb hz).1))
  have hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L := fun z hz => by
    simpa [Real.norm_eq_abs] using hLbd z (ball_subset_closedBall hz)
  have hL0 : 0 ≤ L := le_trans (abs_nonneg (rho z₀))
    (by simpa [Real.norm_eq_abs] using hLbd z₀ (mem_closedBall_self (by positivity)))
  set g : ComplexModel n → ℝ := correctedChartReal w e rho with hg_def
  have hg : IsLocallyBoundedPshOn D g :=
    correctedChartReal_isLocallyBoundedPshOn_of_boundedOn hw.1 hrhoD hwD hL
  set K : ℝ := (dV - cV + 2 * L + 2) ^ n with hK_def
  have hK0 : 0 < K := by
    have : 0 < dV - cV + 2 * L + 2 := by linarith
    exact pow_pos this n
  have h3R : closedBall z₀ (3 * R) ⊆ (D : Set (ComplexModel n)) := by
    refine closedBall_subset_ball ?_
    linarith
  set N : Set M := e.val.source ∩ e.val ⁻¹' (ball z₀ (R / 2)) with hN_def
  have hNopen : IsOpen N := e.val.isOpen_inter_preimage isOpen_ball
  have hxN : x ∈ N := ⟨hxs, mem_ball_self (by positivity)⟩
  have hNJ : N ⊆ (J.source : Set M) := by
    rintro y ⟨hys, hyb⟩
    exact ⟨hys, ball_subset_ball (by linarith) hyb⟩
  refine ⟨N, hNopen, hxN, hNJ.trans hJsub, ?_⟩
  intro eps heps
  have heps' : 0 < eps / K := by positivity
  obtain ⟨G₀, hG₀open, hG₀cap, hG₀cont⟩ :=
    IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_ball hg hR h3R heps'
  set G : Set M := e.val.source ∩ e.val ⁻¹' (G₀ ∩ (D : Set (ComplexModel n)))
    with hG_def
  have hGopen : IsOpen G := e.val.isOpen_inter_preimage (hG₀open.inter D.isOpen)
  have hGsub : G ⊆ (J.source : Set M) := fun y hy => ⟨hy.1, hy.2.2⟩
  have hGimg : e.val '' G ⊆ G₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2.1
  have hcap : thetaCapacity theta V G < ENNReal.ofReal eps := by
    have h1 := thetaCapacity_le_relCapacity_of_boundedOn (V := V) e D hDt rho hrhoD
      hcVdV hL0 hVJ hL G hGsub
    rw [← hK_def] at h1
    have h2 : relCapacity D (e.val '' G) < ENNReal.ofReal (eps / K) :=
      lt_of_le_of_lt (relCapacity_mono hGimg) hG₀cap
    have hKne : ENNReal.ofReal K ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hK0
    have h3 : relCapacity D (e.val '' G) * ENNReal.ofReal K <
        ENNReal.ofReal (eps / K) * ENNReal.ofReal K :=
      ENNReal.mul_lt_mul_left hKne ENNReal.ofReal_ne_top h2
    have h4 : ENNReal.ofReal (eps / K) * ENNReal.ofReal K = ENNReal.ofReal eps := by
      rw [← ENNReal.ofReal_mul heps'.le, div_mul_cancel₀ _ hK0.ne']
    calc thetaCapacity theta V G
        ≤ ENNReal.ofReal K * relCapacity D (e.val '' G) := h1
      _ = relCapacity D (e.val '' G) * ENNReal.ofReal K := mul_comm _ _
      _ < ENNReal.ofReal (eps / K) * ENNReal.ofReal K := h3
      _ = ENNReal.ofReal eps := h4
  refine ⟨G, hGopen, hcap, ?_⟩
  have hmaps : MapsTo e.val (N \ G) (ball z₀ (R / 2) \ G₀) := by
    rintro y ⟨hyN, hyG⟩
    refine ⟨hyN.2, fun hmem => hyG ⟨hyN.1, hmem, ?_⟩⟩
    exact ball_subset_ball (by linarith) hyN.2
  have hcont₁ : ContinuousOn (fun z => g z - rho z) (ball z₀ (R / 2) \ G₀) := by
    refine hG₀cont.sub (((hrho.2.2.1.continuousOn).mono ?_))
    exact fun z hz => hDW (ball_subset_ball (by linarith) hz.1)
  have hcomp : ContinuousOn (fun y => g (e.val y) - rho (e.val y)) (N \ G) :=
    hcont₁.comp (e.val.continuousOn.mono fun y hy => hy.1.1) hmaps
  refine hcomp.congr ?_
  rintro y ⟨hyN, -⟩
  have hinv : e.val.symm (e.val y) = y := e.val.left_inv hyN.1
  simp only [hg_def, correctedChartReal, hinv]
  ring


/-- **Xia, SGPT, Theorem 2.3.2 over a compact subset** (`xia-sgpt:page-0063`).
If `V` and `w` are bounded on an open `Omega` and `K subset Omega` is compact,
then for every `eps > 0` there is one open `G` with `Cap_theta(G, V) < eps`
outside which `w` is continuous on `K`.

The passage from the pointwise statement is the source's: the neighbourhoods do
not depend on `eps`, so a finite subcover of `K` is extracted first and the
tolerance is then divided among its members, finite subadditivity of
`Cap_theta` bounding the union. -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hw : IsThetaPshPotential theta.val w)
    {Omega : Set M} (hOmega : IsOpen Omega)
    (hwb : IsBoundedPotentialOn w Omega) (hVb : IsBoundedPotentialOn V Omega)
    {K : Set M} (hK : IsCompact K) (hKO : K ⊆ Omega)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (w y).toReal) (K \ G) := by
  classical
  choose N hNopen hxN _hNsub hNeps using fun y : Omega =>
    exists_nhds_forall_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn
      hw hOmega y.2 hwb hVb
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover N hNopen
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hKO hy⟩, hxN _⟩)
  set m : ℝ := (s.card : ℝ) with hm_def
  have hden : (0 : ℝ) < 2 * (m + 1) := by positivity
  set delta : ℝ := eps / (2 * (m + 1)) with hdelta_def
  have hdelta : 0 < delta := by positivity
  choose G hGopen hGcap hGcont using fun y : Omega => hNeps y delta hdelta
  refine ⟨⋃ i ∈ s, G i, isOpen_biUnion fun i _ => hGopen i, ?_, ?_⟩
  · have hsum : thetaCapacity theta V (⋃ i ∈ s, G i) ≤
        ∑ i ∈ s, thetaCapacity theta V (G i) :=
      ThetaCapacityQuasiContinuity.thetaCapacity_biUnion_finset_le theta V s G
    have hbound : ∑ i ∈ s, thetaCapacity theta V (G i) ≤
        ∑ _i ∈ s, ENNReal.ofReal delta :=
      Finset.sum_le_sum fun i _ => (hGcap i).le
    have hconst : ∑ _i ∈ s, ENNReal.ofReal delta =
        (s.card : ℝ≥0∞) * ENNReal.ofReal delta := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : (s.card : ℝ≥0∞) * ENNReal.ofReal delta =
        ENNReal.ofReal (m * delta) := by
      rw [hm_def, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have harith : m * delta < eps := by
      rw [hdelta_def, ← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc thetaCapacity theta V (⋃ i ∈ s, G i)
        ≤ ∑ i ∈ s, thetaCapacity theta V (G i) := hsum
      _ ≤ ∑ _i ∈ s, ENNReal.ofReal delta := hbound
      _ = (s.card : ℝ≥0∞) * ENNReal.ofReal delta := hconst
      _ = ENNReal.ofReal (m * delta) := hcast
      _ < ENNReal.ofReal eps := (ENNReal.ofReal_lt_ofReal_iff heps).mpr harith
  · intro y hy
    obtain ⟨i, hiS, hyi⟩ : ∃ i ∈ s, y ∈ N i := by
      simpa using hs hy.1
    have hyG : y ∉ G i := fun hmem => hy.2 (mem_biUnion hiS hmem)
    have h1 : ContinuousWithinAt (fun z => (w z).toReal) (N i \ G i) y :=
      hGcont i y ⟨hyi, hyG⟩
    have hsub : (K \ ⋃ j ∈ s, G j) ∩ N i ⊆ N i \ G i := by
      rintro z ⟨hz, hzN⟩
      exact ⟨hzN, fun hmem => hz.2 (mem_biUnion hiS hmem)⟩
    exact (continuousWithinAt_inter ((hNopen i).mem_nhds hyi)).mp (h1.mono hsub)


end

end SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
