import SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentration
import SGPT.Foundations.Analysis.Pending.RooftopDecreasingLimitQE

set_option autoImplicit false

/-!
# The majorant engine of Xia's Theorem 2.4.4 with (2.20) only quasi-everywhere (C6 of I-0510)

`Pending.RooftopMajorantFamilyConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants`
runs Xia's capacity argument along a decreasing family `g_k` of real majorants of the obstacle,
assuming Xia's (2.20) `P_θ(g_k) ≤ g_k` **everywhere** for the members.  For Xia's Step 2 family
(`Pending.QuasiContinuousMajorantFamily`: lower semicontinuous tail suprema of Tietze extensions)
(2.20) holds only quasi-everywhere.  This module proves the same theorem with `hple` weakened to
quasi-everywhere, under countable stability of pluripolarity (`hcount`, proved on compact
connected Kähler manifolds by `PluripolarOuterCapacity.countablyStablePluripolar`).

The pointwise inequality was used three times: for `P_θ(g_k) ≤ 0` (now from the quasi-everywhere
inequality, `ContinuousObstacleEnvelopeContact.le_coe_of_ae_in_charts_le`), for the convergence
`P_θ(g_k) ↓ P_θ(f)` (now `RooftopDecreasingLimitQE.tendsto_rooftopEnvelope_of_antitone_qe`), and in
the local splitting of `RooftopLocalConcentration.diagonalPotentialMeasure_inter_lt_add_eq_zero`,
which is applied to the corrected majorants `g'_k = g_k` off the pluripolar set `{P_θ(g_k) > g_k}`
and `g'_k = P_θ(g_k)` on it: they dominate `P_θ(g_k)` and `f` everywhere and have the same
non-contact set as `g_k`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentrationQE

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
open SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
open SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
open SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood
open SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
open SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
open SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink

noncomputable section

open SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere
open SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentration

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M] {theta : ClosedRealOneOneForm n M} {f : M → EReal}

/-- **Xia, SGPT, Theorem 2.4.4, `delta` level, for a bounded obstacle presented by a decreasing
family of real majorants, with (2.20) only quasi-everywhere for the members.** -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants_qe
    (hn : 0 < n) (hcount : CountablyStablePluripolar n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {g : ℕ → M → ℝ}
    (hg0 : ∀ k x, g k x ≤ 0)
    (hgmaj : ∀ k x, f x ≤ ((g k x : ℝ) : EReal))
    (hganti : ∀ x, Antitone fun k => g k x)
    (hginf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x)
    (hu : ∀ k, IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun y => ((g k y : ℝ) : EReal)))
    (hple : ∀ k, QuasiEverywhere (n := n) (fun x =>
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal)))
    (hcontact : ∀ k, diagonalPotentialMeasure theta
      (rooftopEnvelope theta.val fun y => ((g k y : ℝ) : EReal)) (hu k)
      {y : M | rooftopEnvelope theta.val (fun z => ((g k z : ℝ) : EReal)) y <
        ((g k y : ℝ) : EReal)} = 0)
    {c : ℝ}
    (hfc : ∀ x, thetaPshSupremum theta.val x + (c : EReal) ≤ f x)
    (hf0 : ∀ x, f x ≤ 0)
    (hfqc : ∀ Omega : Set M, IsOpen Omega →
      IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
      ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧
        thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (f y).toReal) (K \ G))
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f))
    (hw0 : ∀ x, rooftopEnvelope theta.val f x ≤ 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {x : M | rooftopEnvelope theta.val f x + (delta : EReal) < f x} = 0 := by
  classical
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  set w : M → EReal := rooftopEnvelope theta.val f with hwdef
  set u : ℕ → M → EReal :=
    fun k => rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) with hudef
  have hu0 : ∀ k x, u k x ≤ (0 : EReal) := by
    intro k x
    have h := le_coe_of_ae_in_charts_le (F := fun _ => (0 : ℝ)) (hu k).1 continuous_const
      (fun e => by
        filter_upwards [(hple k).ae_in_chart e volume] with z hz
        exact hz.trans (EReal.coe_le_coe_iff.mpr (hg0 k _))) x
    simpa using h
  have hleV : ∀ k, u k ≤ V := fun k =>
    le_thetaPshSupremum (hu k) (fun x => by simpa using hu0 k x)
  have hVf : ∀ x, V x + (c : EReal) ≤ f x := hfc
  have hVc : ∀ k x, V x + (c : EReal) ≤ u k x := fun k =>
    le_rooftopEnvelope (hV.add_const _)
      (quasiEverywhere_of_forall fun x => (hVf x).trans (hgmaj k x))
  have hne : (rooftopCompetitors theta.val f).Nonempty :=
    ⟨fun x => V x + (c : EReal), hV.add_const _, quasiEverywhere_of_forall hVf⟩
  have hVcw : ∀ x, V x + (c : EReal) ≤ w x :=
    le_rooftopEnvelope (hV.add_const _) (quasiEverywhere_of_forall hVf)
  -- the capacity sandwich
  set Cst : ℝ := max (-c) 1 with hCstdef
  have hC1 : (1 : ℝ) ≤ Cst := le_max_right _ _
  have hlbV : ∀ k x, V x ≤ u k x + (Cst : EReal) := fun k x =>
    (le_add_neg_of_add_coe_le c (hVc k x)).trans
      (add_le_add (le_refl _) (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  have hanti : ∀ x, Antitone fun k => u k x :=
    fun x => antitone_rooftopEnvelope_of_antitone hganti x
  have hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)) :=
    fun x => RooftopDecreasingLimitQE.tendsto_rooftopEnvelope_of_antitone_qe hcount
      (F := fun k y => ((g k y : ℝ) : EReal)) hginf
      (fun y j k hjk => EReal.coe_le_coe_iff.mpr (hganti y hjk)) (fun k => (hu k).1) hple hne x
  have hcontactO : ∀ (O : Set M) (k : ℕ), diagonalPotentialMeasure theta (u k) (hu k)
      (O ∩ {y : M | u k y < ((g k y : ℝ) : EReal)}) = 0 := fun O k =>
    measure_mono_null inter_subset_right (hcontact k)
  -- the majorants corrected on the pluripolar set where `u_k > g_k`
  set g' : ℕ → M → ℝ := fun k y =>
    if ((g k y : ℝ) : EReal) < u k y then (u k y).toReal else g k y with hg'def
  have hukg' : ∀ k y, u k y ≤ ((g' k y : ℝ) : EReal) := by
    intro k y
    simp only [hg'def]
    split_ifs with h
    · have hbot : u k y ≠ ⊥ := ne_bot_of_gt h
      have htop : u k y ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hu0 k y)
      rw [EReal.coe_toReal htop hbot]
    · exact not_lt.mp h
  have hfg' : ∀ k y, f y ≤ ((g' k y : ℝ) : EReal) := by
    intro k y
    simp only [hg'def]
    split_ifs with h
    · have hbot : u k y ≠ ⊥ := ne_bot_of_gt h
      have htop : u k y ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hu0 k y)
      rw [EReal.coe_toReal htop hbot]
      exact (hgmaj k y).trans h.le
    · exact hgmaj k y
  have hset : ∀ k, {y : M | u k y < ((g' k y : ℝ) : EReal)} =
      {y : M | u k y < ((g k y : ℝ) : EReal)} := by
    intro k
    ext y
    simp only [mem_ofPred_eq, hg'def]
    split_ifs with h
    · have hbot : u k y ≠ ⊥ := ne_bot_of_gt h
      have htop : u k y ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hu0 k y)
      rw [EReal.coe_toReal htop hbot]
      exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd (h.trans h') (lt_irrefl _)⟩
    · exact Iff.rfl
  have hcontactO' : ∀ (O : Set M) (k : ℕ), diagonalPotentialMeasure theta (u k) (hu k)
      (O ∩ {y : M | u k y < ((g' k y : ℝ) : EReal)}) = 0 := fun O k => by
    rw [hset k]
    exact hcontactO O k
  -- the local statement at every point off the non-Kähler locus
  have hloc : ∀ x ∈ {y : M | w y + (delta : EReal) < f y} \
      nonKahlerLocus (RealBottChern.ofRepresentative theta),
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
        diagonalPotentialMeasure theta w hw
          (O ∩ {y : M | w y + (delta : EReal) < f y}) = 0 := by
    intro x hx
    obtain ⟨N, hN, hVb0⟩ :=
      exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus hn theta hbig hV hx.2
    obtain ⟨Omega, hOmegaN, hOmegaOpen, hxOmega⟩ := mem_nhds_iff.mp hN
    have hVbO : IsBoundedPotentialOn V Omega := hVb0.mono hOmegaN
    obtain ⟨e, D, hD, rho, hrho, L, O, hL, hsrcOmega, hOopen, hxO, hOS⟩ :=
      exists_diagSlotChart_source_subset_closure_subset theta hOmegaOpen hxOmega
    have hVbS : IsBoundedPotentialOn V
        ((diagSlotChart theta e D hD rho hrho).source : Set M) := hVbO.mono hsrcOmega
    have hubS : ∀ k, IsBoundedPotentialOn (u k)
        ((diagSlotChart theta e D hD rho hrho).source : Set M) := fun k =>
      isBoundedPotentialOn_of_le_add_const hVbS (hVc k)
        (fun y => by rw [EReal.coe_zero]; exact hu0 k y)
    have hwbS : IsBoundedPotentialOn w
        ((diagSlotChart theta e D hD rho hrho).source : Set M) :=
      isBoundedPotentialOn_of_le_add_const hVbS hVcw
        (fun y => by rw [EReal.coe_zero]; exact hw0 y)
    have hfbS : IsBoundedPotentialOn f
        ((diagSlotChart theta e D hD rho hrho).source : Set M) :=
      isBoundedPotentialOn_of_le_add_const hVbS hfc
        (fun y => by rw [EReal.coe_zero]; exact hf0 y)
    have hKcomp : IsCompact (closure O) := isClosed_closure.isCompact
    have hqc : ∀ eps : ℝ, 0 < eps → ∃ A : Set M, IsOpen A ∧
        thetaCapacity theta V A < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (w y).toReal) (closure O \ A) ∧
        ContinuousOn (fun y => (f y).toReal) (closure O \ A) := by
      intro eps heps
      have heps4 : (0 : ℝ) < eps / 4 := by positivity
      obtain ⟨G1, hG1open, hG1cap, hG1cont⟩ :=
        exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hw
          (diagSlotChart theta e D hD rho hrho).source.isOpen hwbS hVbS hKcomp hOS heps4
      obtain ⟨G2, hG2open, hG2cap, hG2cont⟩ :=
        hfqc ((diagSlotChart theta e D hD rho hrho).source : Set M)
          (diagSlotChart theta e D hD rho hrho).source.isOpen hVbS (closure O) hKcomp
          hOS (eps / 4) heps4
      refine ⟨G1 ∪ G2, hG1open.union hG2open, ?_, ?_, ?_⟩
      · have hsum : thetaCapacity theta V (G1 ∪ G2) ≤
            ENNReal.ofReal (eps / 4) + ENNReal.ofReal (eps / 4) :=
          (thetaCapacity_union_le theta V G1 G2).trans
            (add_le_add hG1cap.le hG2cap.le)
        refine lt_of_le_of_lt hsum ?_
        rw [← ENNReal.ofReal_add heps4.le heps4.le]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by linarith)
      · exact hG1cont.mono (sdiff_subset_sdiff_right subset_union_left)
      · exact hG2cont.mono (sdiff_subset_sdiff_right subset_union_right)
    exact ⟨O, hOopen, hxO,
      diagonalPotentialMeasure_inter_lt_add_eq_zero (hD := hD) (hrho := hrho)
        (V := V) (w := w) (f := f) (u := u) (g := g') hu hw hV hubS hwbS hVbS hfbS
        hL hanti hlim hC1 hleV hlbV hukg' hfg' hOopen hOS (hcontactO' O) hqc hdelta⟩
  exact measure_eq_zero_of_forall_exists_isOpen
    (diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hw) hloc

end

end SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentrationQE
