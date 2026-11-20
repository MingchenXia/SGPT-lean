import SGPT.Foundations.Analysis.Pending.RooftopTruncationReference

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Xia's Step 1.2 for a measurable obstacle and an arbitrary approximating family

`Pending.RooftopTruncationConcentration` carries out Xia's Step 1.2
(`xia-sgpt:page-0080`--`page-0081`) for an **upper semicontinuous** obstacle `f`.  Its core,
`RooftopTruncationConcentration.exists_isOpen_measure_inter_eq_zero_of_antitone`, uses upper
semicontinuity of `f` for one thing only: the measurability of `f`.  Everything else it needs from
the obstacle is the local `Cap_theta` quasi-continuity of one reference truncation
`f \/ (V_theta - C)`, and from the approximating family `p_k` only that the `p_k` are
nonpositive `theta`-PSH potentials decreasing to `w` with `theta^n_{p_k}` carried by
`{p_k >= f}`.

This module records that generality, for obstacles which are **not** upper semicontinuous —
the affine obstacle `a phi + (1-a) psi` of Xia's Theorem 2.4.5 (`a > 1`) is the case in view
(`Pending.DominationPrincipleAffineContactProof`):

* `exists_isOpen_measure_inter_eq_zero_of_antitone_of_measurable`: the core, with `Measurable f`
  in place of `UpperSemicontinuous f`; the upper semicontinuous form
  `RooftopTruncationConcentration.exists_isOpen_measure_inter_eq_zero_of_antitone` is now its
  corollary (the definitions it needs live in `Pending.RooftopTruncationReference`);
* `diagonalPotentialMeasure_lt_eq_zero_of_antitone_family`: **contact passes to decreasing
  limits** — if `p_k` decrease to a `theta`-PSH `w`, each `theta^n_{p_k}` gives no mass to
  `{p_k < f}`, and `f <= 0` is measurable with quasi-continuous reference truncations, then
  `theta^n_w` gives no mass to `{w < f}`.  The truncation level `C` and the gap `delta` are let
  go exactly as in `RooftopTruncationConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_nonpos`.

The family is a hypothesis, not a construction: no envelope and no bigness of the obstacle
enter beyond what the core uses (`IsBigClass` for the slot charts off `nK({theta})`).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
open SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
open SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
open SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### The local estimate for a measurable obstacle -/

section Core

variable [Nonempty M] {theta : ClosedRealOneOneForm n M} {f w : M → EReal}
  {p : ℕ → M → EReal}

/-- **The heart of Xia's Step 1.2 for a measurable obstacle**
(`xia-sgpt:page-0080`--`page-0081`).  The statement of
`RooftopTruncationConcentration.exists_isOpen_measure_inter_eq_zero_of_antitone` with
`Measurable f` in place of `UpperSemicontinuous f`; the proof is the same (upper
semicontinuity was used only for measurability). -/
theorem exists_isOpen_measure_inter_eq_zero_of_antitone_of_measurable (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hfmeas : Measurable f) (hf0 : ∀ x, f x ≤ 0) {C : ℝ} (hC1 : 1 ≤ C)
    (hfqcC : ∀ Omega : Set M, IsOpen Omega →
      IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
      ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
        ∃ G : Set M, IsOpen G ∧
          thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
          ContinuousOn (fun y => (refTrunc theta f C y).toReal) (K \ G))
    (hp : ∀ k, IsThetaPshPotential theta.val (p k)) (hp0 : ∀ k y, p k y ≤ 0)
    (hpanti : ∀ y, Antitone fun k => p k y)
    (hw : IsThetaPshPotential theta.val w) (hwp : ∀ k y, w y ≤ p k y)
    (hplim : ∀ y, Tendsto (fun k => p k y) atTop (𝓝 (w y)))
    (hzero : ∀ k, diagonalPotentialMeasure theta (p k) (hp k)
      {y : M | p k y < f y} = 0)
    {delta : ℝ} (hdelta : 0 < delta)
    {x : M} (hx : x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      diagonalPotentialMeasure theta w hw
        (O ∩ ({y : M | w y + (delta : EReal) < f y} ∩
          {y : M | thetaPshSupremum theta.val y + ((-C : ℝ) : EReal) < w y})) = 0 := by
  classical
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  have hV0 : ∀ y, V y ≤ (0 : EReal) := fun y => by
    simpa [hVdef] using thetaPshSupremum_le_zero theta.val y
  have hCneg : ((-C : ℝ) : EReal) ≤ 0 := by
    rw [show (0 : EReal) = ((0 : ℝ) : EReal) from by norm_num, EReal.coe_le_coe_iff]
    linarith
  have hVcpot : IsThetaPshPotential theta.val (fun y => V y + ((-C : ℝ) : EReal)) :=
    hV.add_const _
  have hVc0 : ∀ y, V y + ((-C : ℝ) : EReal) ≤ (0 : EReal) := by
    intro y
    calc V y + ((-C : ℝ) : EReal) ≤ 0 + ((-C : ℝ) : EReal) := add_le_add (hV0 y) le_rfl
      _ = ((-C : ℝ) : EReal) := zero_add _
      _ ≤ 0 := hCneg
  -- the maxima against the truncated reference
  set u : ℕ → M → EReal := fun k y => max (p k y) (V y + ((-C : ℝ) : EReal)) with hudef
  set ulim : M → EReal := fun y => max (w y) (V y + ((-C : ℝ) : EReal)) with hulimdef
  have humax : ∀ (k : ℕ) (y : M), u k y = max (p k y) (V y + ((-C : ℝ) : EReal)) :=
    fun _ _ => rfl
  have hulmax : ∀ y : M, ulim y = max (w y) (V y + ((-C : ℝ) : EReal)) := fun _ => rfl
  have hu : ∀ k, IsThetaPshPotential theta.val (u k) := fun k =>
    IsThetaPshPotential.max (hp k) hVcpot
  have hulim : IsThetaPshPotential theta.val ulim := IsThetaPshPotential.max hw hVcpot
  have hu0 : ∀ k, u k ≤ 0 := fun k y => max_le (hp0 k y) (hVc0 y)
  have hulim0 : ulim ≤ 0 := fun y => max_le ((hwp 0 y).trans (hp0 0 y)) (hVc0 y)
  have hsand : ∀ k y, V y ≤ u k y + (C : EReal) := by
    intro k y
    calc V y = V y + ((-C : ℝ) : EReal) + (C : EReal) :=
          (RooftopEnvelopeNormalization.add_coe_neg_add (V y) C).symm
      _ ≤ u k y + (C : EReal) := add_le_add (le_max_right _ _) le_rfl
  have hsandlim : ∀ y, V y ≤ ulim y + (C : EReal) := by
    intro y
    calc V y = V y + ((-C : ℝ) : EReal) + (C : EReal) :=
          (RooftopEnvelopeNormalization.add_coe_neg_add (V y) C).symm
      _ ≤ ulim y + (C : EReal) := add_le_add (le_max_right _ _) le_rfl
  have hanti : ∀ y, Antitone fun k => u k y :=
    fun y j k hjk => max_le_max (hpanti y hjk) le_rfl
  have hlim : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (ulim y)) :=
    fun y => (hplim y).max tendsto_const_nhds
  -- measurability
  have hpmeas : ∀ k, Measurable (p k) := fun k =>
    (hp k).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hwdmeas : Measurable fun y => w y + (delta : EReal) :=
    (hw.add_const delta).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hVcmeas : Measurable fun y => V y + ((-C : ℝ) : EReal) :=
    hVcpot.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hwmeas : Measurable w :=
    hw.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hAmeas : MeasurableSet {y : M | w y + (delta : EReal) < f y} :=
    measurableSet_lt hwdmeas hfmeas
  -- plurifine locality
  have hlocp : ∀ (k : ℕ) (s : Set M), MeasurableSet s →
      diagonalPotentialMeasure theta (u k) (hu k)
          (s ∩ {y : M | V y + ((-C : ℝ) : EReal) < p k y}) =
        diagonalPotentialMeasure theta (p k) (hp k)
          (s ∩ {y : M | V y + ((-C : ℝ) : EReal) < p k y}) :=
    fun k s hs => measure_inter_lt_left theta (hp k) hVcpot (hu k) hs
  have hlocw : ∀ s : Set M, MeasurableSet s →
      diagonalPotentialMeasure theta ulim hulim
          (s ∩ {y : M | V y + ((-C : ℝ) : EReal) < w y}) =
        diagonalPotentialMeasure theta w hw
          (s ∩ {y : M | V y + ((-C : ℝ) : EReal) < w y}) :=
    fun s hs => measure_inter_lt_left theta hw hVcpot hulim hs
  -- the first piece of the inclusion is null for every member of the family
  have hfirst : ∀ k : ℕ, diagonalPotentialMeasure theta (u k) (hu k)
      ({z : M | p k z < f z} ∩
        {y : M | V y + ((-C : ℝ) : EReal) < w y}) = 0 := by
    intro k
    have hsub : {z : M | p k z < f z} ∩
        {y : M | V y + ((-C : ℝ) : EReal) < w y} ⊆
          {z : M | p k z < f z} ∩
            {y : M | V y + ((-C : ℝ) : EReal) < p k y} :=
      fun y hy => ⟨hy.1, lt_of_lt_of_le hy.2 (hwp k y)⟩
    refine measure_mono_null hsub ?_
    rw [hlocp k _ (measurableSet_lt (hpmeas k) hfmeas)]
    exact measure_mono_null inter_subset_left (hzero k)
  -- the elementary inclusion
  have hincl : ∀ (k : ℕ) (y : M),
      y ∈ {z : M | w z + (delta : EReal) < f z} ∩
        {z : M | V z + ((-C : ℝ) : EReal) < w z} →
      y ∈ ({z : M | p k z < f z} ∩
            {z : M | V z + ((-C : ℝ) : EReal) < w z}) ∪
          {z : M | ulim z + (delta : EReal) ≤ u k z} := by
    intro k y hy
    by_cases hcase : ulim y + (delta : EReal) ≤ u k y
    · exact Or.inr hcase
    · push Not at hcase
      refine Or.inl ⟨?_, hy.2⟩
      have hul : ulim y = w y := by rw [hulmax y]; exact max_eq_left hy.2.le
      calc p k y ≤ u k y := le_max_left _ _
        _ < ulim y + (delta : EReal) := hcase
        _ = w y + (delta : EReal) := by rw [hul]
        _ < f y := hy.1
  -- ## The slot chart around the point
  obtain ⟨N, hN, hVbN⟩ :=
    exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus hn theta hbig hV hx
  obtain ⟨Omega, hOmegaN, hOmegaOpen, hxOmega⟩ := mem_nhds_iff.mp hN
  have hVbO : IsBoundedPotentialOn V Omega := hVbN.mono hOmegaN
  obtain ⟨e, D, hD, rho, hrho, L, O, hL, hsrcOmega, hOopen, hxO, hOS⟩ :=
    exists_diagSlotChart_source_subset_closure_subset theta hOmegaOpen hxOmega
  have hSopen : IsOpen ((diagSlotChart theta e D hD rho hrho).source : Set M) :=
    (diagSlotChart theta e D hD rho hrho).source.isOpen
  have hVbS : IsBoundedPotentialOn V
      ((diagSlotChart theta e D hD rho hrho).source : Set M) := hVbO.mono hsrcOmega
  have hKcomp : IsCompact (closure O) := isClosed_closure.isCompact
  obtain ⟨a, b, hab⟩ := id hVbS
  have hOsub : O ⊆ ((diagSlotChart theta e D hD rho hrho).source : Set M) :=
    subset_closure.trans hOS
  -- bounds on the slot-chart source
  have hubS : ∀ k, IsBoundedPotentialOn (u k)
      ((diagSlotChart theta e D hD rho hrho).source : Set M) := by
    intro k
    refine ⟨a - C, 0, fun y hy => ⟨?_, ?_⟩⟩
    · have h1 : ((a - C : ℝ) : EReal) = ((a : ℝ) : EReal) + ((-C : ℝ) : EReal) := by
        rw [EReal.coe_sub, sub_eq_add_neg, EReal.coe_neg]
      rw [h1]
      exact le_trans (add_le_add (hab y hy).1 le_rfl) (le_max_right _ _)
    · simpa using hu0 k y
  have hulimbS : IsBoundedPotentialOn ulim
      ((diagSlotChart theta e D hD rho hrho).source : Set M) := by
    refine ⟨a - C, 0, fun y hy => ⟨?_, ?_⟩⟩
    · have h1 : ((a - C : ℝ) : EReal) = ((a : ℝ) : EReal) + ((-C : ℝ) : EReal) := by
        rw [EReal.coe_sub, sub_eq_add_neg, EReal.coe_neg]
      rw [h1]
      exact le_trans (add_le_add (hab y hy).1 le_rfl) (le_max_right _ _)
    · simpa using hulim0 y
  -- the truncation level at which the obstacle may be replaced by a bounded one
  -- the obstacle truncated against the reference at level `C`
  have hrefmax : ∀ y : M, refTrunc theta f C y = max (f y) (V y + ((-C : ℝ) : EReal)) :=
    fun _ => rfl
  have hfB : ∀ y : M, f y ≤ refTrunc theta f C y := fun y => le_max_left _ _
  have hfB0 : ∀ y : M, refTrunc theta f C y ≤ (0 : EReal) :=
    fun y => max_le (hf0 y) (hVc0 y)
  have hfBlow : ∀ y ∈ ((diagSlotChart theta e D hD rho hrho).source : Set M),
      ((a - C : ℝ) : EReal) ≤ refTrunc theta f C y := by
    intro y hy
    rw [hrefmax y,
      show ((a - C : ℝ) : EReal) = ((a : ℝ) : EReal) + ((-C : ℝ) : EReal) from by
        rw [EReal.coe_sub, sub_eq_add_neg, EReal.coe_neg]]
    exact le_max_of_le_right (add_le_add (hab y hy).1 le_rfl)
  have hw0 : ∀ y : M, w y ≤ (0 : EReal) := fun y => (hwp 0 y).trans (hp0 0 y)
  -- the second piece has capacity tending to zero
  have hcapten : Tendsto (fun k => thetaCapacity theta V
      (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}))
      atTop (𝓝 0) :=
    tendsto_thetaCapacity_of_antitone_of_boundedOn hSopen hVbS hKcomp hOS hu hubS
      hulim hulimbS hanti hlim (by linarith : (0:ℝ) < delta / 2)
  have hsecond : ∀ k : ℕ, diagonalPotentialMeasure theta (u k) (hu k)
      (closure O ∩ {z : M | ulim z + (delta : EReal) ≤ u k z}) ≤
        ENNReal.ofReal (C ^ n) * thetaCapacity theta V
          (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}) := by
    intro k
    have hsub : (closure O ∩ {z : M | ulim z + (delta : EReal) ≤ u k z}) ⊆
        (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}) := by
      intro y hy
      have hyS := hOS hy.1
      obtain ⟨r, hr⟩ : ∃ r : ℝ, ulim y = (r : EReal) :=
        ⟨(ulim y).toReal,
          (EReal.coe_toReal (hulimbS.ne_top hyS) (hulimbS.ne_bot hyS)).symm⟩
      refine ⟨hy.1, ?_⟩
      have hhalf : ulim y + ((delta / 2 : ℝ) : EReal) <
          ulim y + (delta : EReal) := by
        rw [hr, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith
      exact hhalf.trans_le hy.2
    calc diagonalPotentialMeasure theta (u k) (hu k)
          (closure O ∩ {z : M | ulim z + (delta : EReal) ≤ u k z})
        ≤ diagonalPotentialMeasure theta (u k) (hu k)
            (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (C ^ n) * thetaCapacityV theta
            (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}) :=
          diagonalPotentialMeasure_le_thetaCapacityV (hu k) (hu0 k) hC1 (hsand k) _
      _ = _ := rfl
  -- ## The open enlargement
  have hopen : ∀ eps : ℝ, 0 < eps → ∃ G O₁ : Set M, IsOpen G ∧ IsOpen O₁ ∧
      thetaCapacity theta V G < ENNReal.ofReal eps ∧ O₁ ⊆ O ∧
      (O ∩ ({y : M | w y + (delta : EReal) < f y} ∩
          {y : M | V y + ((-C : ℝ) : EReal) < w y})) ⊆ G ∪ O₁ ∧
      (O₁ \ G) ⊆ ({y : M | w y + (delta : EReal) < f y} ∩
          {y : M | V y + ((-C : ℝ) : EReal) < w y}) := by
    intro eps heps
    have heps4 : (0 : ℝ) < eps / 4 := by linarith
    obtain ⟨G1, hG1o, hG1c, hG1cont⟩ :=
      exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hulim hSopen hulimbS
        (V := V) hVbS hKcomp hOS heps4
    obtain ⟨G2, hG2o, hG2c, hG2cont⟩ :=
      exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hV hSopen hVbS
        (V := V) hVbS hKcomp hOS heps4
    obtain ⟨G3, hG3o, hG3c, hG3cont⟩ :=
      hfqcC ((diagSlotChart theta e D hD rho hrho).source : Set M) hSopen hVbS
        (closure O) hKcomp hOS (eps / 4) heps4
    have hGo : IsOpen (G1 ∪ G2 ∪ G3) := (hG1o.union hG2o).union hG3o
    have hGc : thetaCapacity theta V (G1 ∪ G2 ∪ G3) < ENNReal.ofReal eps := by
      have h12 : thetaCapacity theta V (G1 ∪ G2) ≤
          thetaCapacity theta V G1 + thetaCapacity theta V G2 :=
        thetaCapacity_union_le theta V G1 G2
      have hsum : thetaCapacity theta V (G1 ∪ G2 ∪ G3) ≤
          ENNReal.ofReal (eps / 4) + ENNReal.ofReal (eps / 4) +
            ENNReal.ofReal (eps / 4) :=
        (thetaCapacity_union_le theta V (G1 ∪ G2) G3).trans
          (add_le_add (h12.trans (add_le_add hG1c.le hG2c.le)) hG3c.le)
      refine lt_of_le_of_lt hsum ?_
      rw [← ENNReal.ofReal_add heps4.le heps4.le,
        ← ENNReal.ofReal_add (by positivity) heps4.le]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith)
    -- the three functions are continuous off the exceptional set
    have hcont1 : ContinuousOn (fun y => (ulim y).toReal) (closure O \ (G1 ∪ G2 ∪ G3)) :=
      hG1cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inl (Or.inl h))⟩
    have hcont2 : ContinuousOn (fun y => (V y).toReal) (closure O \ (G1 ∪ G2 ∪ G3)) :=
      hG2cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inl (Or.inr h))⟩
    have hcont3 : ContinuousOn (fun y => (refTrunc theta f C y).toReal)
        (closure O \ (G1 ∪ G2 ∪ G3)) :=
      hG3cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
    -- the plurifine-open target is relatively open off the exceptional set
    have hulimfin : ∀ y ∈ closure O \ (G1 ∪ G2 ∪ G3),
        ulim y = (((ulim y).toReal : ℝ) : EReal) := fun y hy =>
      (EReal.coe_toReal (hulimbS.ne_top (hOS hy.1)) (hulimbS.ne_bot (hOS hy.1))).symm
    have hVfin : ∀ y ∈ closure O \ (G1 ∪ G2 ∪ G3),
        V y = (((V y).toReal : ℝ) : EReal) := fun y hy =>
      (EReal.coe_toReal (hVbS.ne_top (hOS hy.1)) (hVbS.ne_bot (hOS hy.1))).symm
    have hTfin : ∀ y ∈ closure O \ (G1 ∪ G2 ∪ G3),
        refTrunc theta f C y = (((refTrunc theta f C y).toReal : ℝ) : EReal) := by
      intro y hy
      refine (EReal.coe_toReal (ne_top_of_le_ne_top (by simp) (hfB0 y))
        (ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (a - C))
          (hfBlow y (hOS hy.1))))).symm
    have htr1 : ∀ y ∈ closure O \ (G1 ∪ G2 ∪ G3),
        (ulim y + (delta : EReal) < refTrunc theta f C y ↔
          (ulim y).toReal + delta < (refTrunc theta f C y).toReal) := by
      intro y hy
      obtain ⟨r, hr⟩ : ∃ r : ℝ, ulim y = (r : EReal) := ⟨_, hulimfin y hy⟩
      obtain ⟨t, ht⟩ : ∃ t : ℝ, refTrunc theta f C y = (t : EReal) := ⟨_, hTfin y hy⟩
      simp only [hr, ht, ← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.toReal_coe]
    have htr2 : ∀ y ∈ closure O \ (G1 ∪ G2 ∪ G3),
        (V y + ((-C : ℝ) : EReal) < ulim y ↔ (V y).toReal - C < (ulim y).toReal) := by
      intro y hy
      obtain ⟨r, hr⟩ : ∃ r : ℝ, ulim y = (r : EReal) := ⟨_, hulimfin y hy⟩
      obtain ⟨v, hv⟩ : ∃ v : ℝ, V y = (v : EReal) := ⟨_, hVfin y hy⟩
      simp only [hr, hv, ← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.toReal_coe]
      constructor <;> intro h <;> linarith
    have hUso : IsOpen {z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) |
        ulim z.val + (delta : EReal) < refTrunc theta f C z.val ∧
        V z.val + ((-C : ℝ) : EReal) < ulim z.val} := by
      have heq : {z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) |
          ulim z.val + (delta : EReal) < refTrunc theta f C z.val ∧
          V z.val + ((-C : ℝ) : EReal) < ulim z.val} =
          {z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) |
            (ulim z.val).toReal + delta < (refTrunc theta f C z.val).toReal ∧
            (V z.val).toReal - C < (ulim z.val).toReal} := by
        ext z
        exact and_congr (htr1 z.val z.2) (htr2 z.val z.2)
      rw [heq]
      have h1 : Continuous fun z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) =>
          (ulim z.val).toReal := continuousOn_iff_continuous_domRestrict.mp hcont1
      have h2 : Continuous fun z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) =>
          (V z.val).toReal := continuousOn_iff_continuous_domRestrict.mp hcont2
      have h3 : Continuous fun z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) =>
          (refTrunc theta f C z.val).toReal := continuousOn_iff_continuous_domRestrict.mp hcont3
      exact (isOpen_lt (h1.add continuous_const) h3).inter
        (isOpen_lt (h2.sub continuous_const) h1)
    obtain ⟨O₀, hO₀o, hO₀⟩ := isOpen_induced_iff.mp hUso
    refine ⟨G1 ∪ G2 ∪ G3, O₀ ∩ O, hGo, hO₀o.inter hOopen, hGc, inter_subset_right,
      ?_, ?_⟩
    · -- the target is covered by the exceptional set and the open enlargement
      intro y hy
      by_cases hyG : y ∈ G1 ∪ G2 ∪ G3
      · exact Or.inl hyG
      refine Or.inr ⟨?_, hy.1⟩
      have hys : y ∈ closure O \ (G1 ∪ G2 ∪ G3) := ⟨subset_closure hy.1, hyG⟩
      have hul : ulim y = w y := by rw [hulmax y]; exact max_eq_left hy.2.2.le
      have hmem : (⟨y, hys⟩ : (closure O \ (G1 ∪ G2 ∪ G3) : Set M)) ∈
          {z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) |
            ulim z.val + (delta : EReal) < refTrunc theta f C z.val ∧
            V z.val + ((-C : ℝ) : EReal) < ulim z.val} := by
        refine ⟨?_, lt_of_lt_of_le hy.2.2 (by rw [hulmax y]; exact le_max_left _ _)⟩
        calc ulim y + (delta : EReal) = w y + (delta : EReal) := by rw [hul]
          _ < f y := hy.2.1
          _ ≤ refTrunc theta f C y := hfB y
      have : (⟨y, hys⟩ : (closure O \ (G1 ∪ G2 ∪ G3) : Set M)) ∈ Subtype.val ⁻¹' O₀ := by
        rw [hO₀]; exact hmem
      exact this
    · -- the open enlargement, off the exceptional set, is inside the target
      intro y hy
      have hys : y ∈ closure O \ (G1 ∪ G2 ∪ G3) := ⟨subset_closure hy.1.2, hy.2⟩
      have hmem : (⟨y, hys⟩ : (closure O \ (G1 ∪ G2 ∪ G3) : Set M)) ∈
          {z : (closure O \ (G1 ∪ G2 ∪ G3) : Set M) |
            ulim z.val + (delta : EReal) < refTrunc theta f C z.val ∧
            V z.val + ((-C : ℝ) : EReal) < ulim z.val} := by
        rw [← hO₀]; exact hy.1.1
      obtain ⟨h1, h2⟩ := hmem
      have hwgt : V y + ((-C : ℝ) : EReal) < w y := by
        by_contra hle
        push Not at hle
        rw [hulmax y, max_eq_right hle] at h2
        exact lt_irrefl _ h2
      have hul : ulim y = w y := by rw [hulmax y]; exact max_eq_left hwgt.le
      refine ⟨?_, hwgt⟩
      have hwd : w y ≤ w y + (delta : EReal) := by
        rcases eq_or_ne (w y) ⊥ with hb | hb
        · rw [hb, EReal.bot_add]
        · obtain ⟨r, hr⟩ : ∃ r : ℝ, w y = (r : EReal) :=
            ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top (by simp) (hw0 y)) hb).symm⟩
          rw [hr, ← EReal.coe_add]
          exact EReal.coe_le_coe_iff.mpr (by linarith)
      rw [hul, hrefmax y] at h1
      rcases lt_max_iff.mp h1 with h | h
      · exact h
      · exact absurd h (not_lt.mpr (lt_of_lt_of_le hwgt hwd).le)
  -- ## Conclusion
  refine ⟨O, hOopen, hxO, ?_⟩
  have hassoc : O ∩ ({y : M | w y + (delta : EReal) < f y} ∩
      {y : M | V y + ((-C : ℝ) : EReal) < w y}) =
      (O ∩ {y : M | w y + (delta : EReal) < f y}) ∩
        {y : M | V y + ((-C : ℝ) : EReal) < w y} := by
    ext y
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  rw [hassoc, ← hlocw _ (hOopen.measurableSet.inter hAmeas)]
  refine eq_zero_of_forall_le_mul_ofReal
    (K := 2 * ENNReal.ofReal (C ^ n))
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) ?_
  intro eps heps
  obtain ⟨G, O₁, hGo, hO₁o, hGc, hO₁O, hincl1, hincl2⟩ := hopen eps heps
  have hport : diagonalPotentialMeasure theta ulim hulim O₁ ≤
      liminf (fun k => diagonalPotentialMeasure theta (u k) (hu k) O₁) atTop :=
    diagonalPotentialMeasure_le_liminf_of_antitone (e := e) (D := D) (hD := hD)
      (rho := rho) (hrho := hrho) hu hulim hubS hulimbS hL hanti hlim hO₁o
      (hO₁O.trans hOsub)
  have hbd : ∀ k : ℕ, diagonalPotentialMeasure theta (u k) (hu k) O₁ ≤
      ENNReal.ofReal (C ^ n) * thetaCapacity theta V G +
      ENNReal.ofReal (C ^ n) * thetaCapacity theta V
        (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}) := by
    intro k
    have hcover : O₁ ⊆ G ∪ (O₁ \ G) := by
      intro y hy
      by_cases h : y ∈ G
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    have hsplit : (O₁ \ G) ⊆
        ({z : M | p k z < f z} ∩ {z : M | V z + ((-C : ℝ) : EReal) < w z}) ∪
          (closure O ∩ {z : M | ulim z + (delta : EReal) ≤ u k z}) := by
      intro y hy
      rcases hincl k y (hincl2 hy) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨subset_closure (hO₁O hy.1), h⟩
    calc diagonalPotentialMeasure theta (u k) (hu k) O₁
        ≤ diagonalPotentialMeasure theta (u k) (hu k) (G ∪ (O₁ \ G)) :=
          measure_mono hcover
      _ ≤ diagonalPotentialMeasure theta (u k) (hu k) G +
            diagonalPotentialMeasure theta (u k) (hu k) (O₁ \ G) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (C ^ n) * thetaCapacity theta V G +
            (diagonalPotentialMeasure theta (u k) (hu k)
                ({z : M | p k z < f z} ∩
                  {z : M | V z + ((-C : ℝ) : EReal) < w z}) +
              diagonalPotentialMeasure theta (u k) (hu k)
                (closure O ∩ {z : M | ulim z + (delta : EReal) ≤ u k z})) :=
          add_le_add
            (diagonalPotentialMeasure_le_thetaCapacityV (hu k) (hu0 k) hC1 (hsand k) G)
            ((measure_mono hsplit).trans (measure_union_le _ _))
      _ ≤ ENNReal.ofReal (C ^ n) * thetaCapacity theta V G +
            ENNReal.ofReal (C ^ n) * thetaCapacity theta V
              (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}) := by
          rw [hfirst k, zero_add]
          exact add_le_add le_rfl (hsecond k)
  have hliminf : liminf (fun k => diagonalPotentialMeasure theta (u k) (hu k) O₁) atTop ≤
      ENNReal.ofReal (C ^ n) * thetaCapacity theta V G := by
    have h0 : Tendsto (fun k => ENNReal.ofReal (C ^ n) * thetaCapacity theta V
        (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}))
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C ^ n)) hcapten
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    have hten : Tendsto (fun k => ENNReal.ofReal (C ^ n) * thetaCapacity theta V G +
        ENNReal.ofReal (C ^ n) * thetaCapacity theta V
          (closure O ∩ {y : M | ulim y + ((delta / 2 : ℝ) : EReal) < u k y}))
        atTop (𝓝 (ENNReal.ofReal (C ^ n) * thetaCapacity theta V G)) := by
      simpa using tendsto_const_nhds.add h0
    refine le_trans (liminf_le_liminf (Eventually.of_forall hbd)) ?_
    exact le_of_eq hten.liminf_eq
  calc diagonalPotentialMeasure theta ulim hulim
        ((O ∩ {y : M | w y + (delta : EReal) < f y}) ∩
          {y : M | V y + ((-C : ℝ) : EReal) < w y})
      ≤ diagonalPotentialMeasure theta ulim hulim (G ∪ O₁) :=
        measure_mono fun y hy => hincl1 ⟨hy.1.1, hy.1.2, hy.2⟩
    _ ≤ diagonalPotentialMeasure theta ulim hulim G +
          diagonalPotentialMeasure theta ulim hulim O₁ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C ^ n) * thetaCapacity theta V G +
          ENNReal.ofReal (C ^ n) * thetaCapacity theta V G :=
        add_le_add
          (diagonalPotentialMeasure_le_thetaCapacityV hulim hulim0 hC1 hsandlim G)
          (hport.trans hliminf)
    _ ≤ ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps +
          ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps := by
        gcongr
    _ = 2 * ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps := by ring

end Core

/-! ### Contact passes to decreasing limits -/

section Step

variable [Nonempty M] {theta : ClosedRealOneOneForm n M} {f w : M → EReal}
  {p : ℕ → M → EReal}

/-- **The `delta`-level statement above a truncated reference**, for an arbitrary
approximating family (`xia-sgpt:page-0081`, equation (2.26)). -/
theorem diagonalPotentialMeasure_lt_add_inter_eq_zero_of_antitone_family (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hfmeas : Measurable f) (hf0 : ∀ x, f x ≤ 0)
    (hfqc : RefTruncationsQuasiContinuous theta f)
    (hp : ∀ k, IsThetaPshPotential theta.val (p k)) (hp0 : ∀ k y, p k y ≤ 0)
    (hpanti : ∀ y, Antitone fun k => p k y)
    (hw : IsThetaPshPotential theta.val w) (hwp : ∀ k y, w y ≤ p k y)
    (hplim : ∀ y, Tendsto (fun k => p k y) atTop (𝓝 (w y)))
    (hzero : ∀ k, diagonalPotentialMeasure theta (p k) (hp k)
      {y : M | p k y < f y} = 0)
    {C : ℝ} (hC1 : 1 ≤ C) {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta w hw
      ({y : M | w y + (delta : EReal) < f y} ∩
        {y : M | thetaPshSupremum theta.val y + ((-C : ℝ) : EReal) < w y}) = 0 := by
  refine measure_eq_zero_of_forall_exists_isOpen
    (diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hw) ?_
  intro x hx
  exact exists_isOpen_measure_inter_eq_zero_of_antitone_of_measurable hn hbig hV hfmeas hf0 hC1
    (hfqc C (le_trans zero_le_one hC1)) hp hp0 hpanti hw hwp hplim hzero hdelta hx.2

/-- **The `delta`-level statement**, for an arbitrary approximating family: the truncation
level `C` is let go to infinity along the integers, the poles of `w` being pluripolar. -/
theorem diagonalPotentialMeasure_lt_add_eq_zero_of_antitone_family (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hfmeas : Measurable f) (hf0 : ∀ x, f x ≤ 0)
    (hfqc : RefTruncationsQuasiContinuous theta f)
    (hp : ∀ k, IsThetaPshPotential theta.val (p k)) (hp0 : ∀ k y, p k y ≤ 0)
    (hpanti : ∀ y, Antitone fun k => p k y)
    (hw : IsThetaPshPotential theta.val w) (hwp : ∀ k y, w y ≤ p k y)
    (hplim : ∀ y, Tendsto (fun k => p k y) atTop (𝓝 (w y)))
    (hzero : ∀ k, diagonalPotentialMeasure theta (p k) (hp k)
      {y : M | p k y < f y} = 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta w hw {y : M | w y + (delta : EReal) < f y} = 0 := by
  classical
  have hV0 : ∀ y, thetaPshSupremum theta.val y ≤ (0 : EReal) := fun y => by
    simpa using thetaPshSupremum_le_zero theta.val y
  have hw0 : ∀ y : M, w y ≤ (0 : EReal) := fun y => (hwp 0 y).trans (hp0 0 y)
  have hpoles : diagonalPotentialMeasure theta w hw {y : M | w y = ⊥} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hw.1) _
      (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential)
  have hsub : {y : M | w y + (delta : EReal) < f y} ⊆
      {y : M | w y = ⊥} ∪
        ⋃ m : ℕ, ({y : M | w y + (delta : EReal) < f y} ∩
          {y : M | thetaPshSupremum theta.val y +
            ((-((m : ℝ) + 1) : ℝ) : EReal) < w y}) := by
    intro y hy
    by_cases hbot : w y = ⊥
    · exact Or.inl hbot
    refine Or.inr ?_
    have htop : w y ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hw0 y)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w y = (r : EReal) := ⟨_, (EReal.coe_toReal htop hbot).symm⟩
    rcases eq_or_ne (thetaPshSupremum theta.val y) ⊥ with hVb | hVb
    · refine mem_iUnion.mpr ⟨0, hy, ?_⟩
      show thetaPshSupremum theta.val y + _ < w y
      rw [hVb, EReal.bot_add, hr]
      exact EReal.bot_lt_coe r
    · have hVt : thetaPshSupremum theta.val y ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp) (hV0 y)
      obtain ⟨v, hv⟩ : ∃ v : ℝ, thetaPshSupremum theta.val y = (v : EReal) :=
        ⟨_, (EReal.coe_toReal hVt hVb).symm⟩
      obtain ⟨m, hm⟩ := exists_nat_gt (v - r)
      refine mem_iUnion.mpr ⟨m, hy, ?_⟩
      show thetaPshSupremum theta.val y + _ < w y
      rw [hv, hr, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      linarith
  refine measure_mono_null hsub ?_
  refine measure_union_null hpoles (measure_iUnion_null fun m => ?_)
  exact diagonalPotentialMeasure_lt_add_inter_eq_zero_of_antitone_family hn hbig hV hfmeas hf0
    hfqc hp hp0 hpanti hw hwp hplim hzero (le_add_of_nonneg_left (by positivity)) hdelta

/-- **Contact passes to decreasing limits.**  Let `f <= 0` be measurable with quasi-continuous
reference truncations, and let `p_k` be nonpositive `theta`-PSH potentials decreasing to a
`theta`-PSH potential `w <= p_k`, with `theta^n_{p_k}` giving no mass to `{p_k < f}`.  Then
`theta^n_w` gives no mass to `{w < f}`.

With `p_k = P_theta(f \/ (V_theta - k))` and `w = P_theta(f)` this is Xia's Step 1.2
(`xia-sgpt:page-0080`--`page-0081`); the family is left free so that obstacles which are not
upper semicontinuous can be approximated by envelopes of lower semicontinuous majorants. -/
theorem diagonalPotentialMeasure_lt_eq_zero_of_antitone_family (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hfmeas : Measurable f) (hf0 : ∀ x, f x ≤ 0)
    (hfqc : RefTruncationsQuasiContinuous theta f)
    (hp : ∀ k, IsThetaPshPotential theta.val (p k)) (hp0 : ∀ k y, p k y ≤ 0)
    (hpanti : ∀ y, Antitone fun k => p k y)
    (hw : IsThetaPshPotential theta.val w) (hwp : ∀ k y, w y ≤ p k y)
    (hplim : ∀ y, Tendsto (fun k => p k y) atTop (𝓝 (w y)))
    (hzero : ∀ k, diagonalPotentialMeasure theta (p k) (hp k)
      {y : M | p k y < f y} = 0) :
    diagonalPotentialMeasure theta w hw {y : M | w y < f y} = 0 := by
  classical
  have hpoles : diagonalPotentialMeasure theta w hw {y : M | w y = ⊥} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hw.1) _
      (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential)
  refine measure_mono_null (lt_subset_union_iUnion_add w f) ?_
  refine measure_union_null hpoles (measure_iUnion_null fun m => ?_)
  exact diagonalPotentialMeasure_lt_add_eq_zero_of_antitone_family hn hbig hV hfmeas hf0 hfqc
    hp hp0 hpanti hw hwp hplim hzero (by positivity)

end Step

end

end SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable
