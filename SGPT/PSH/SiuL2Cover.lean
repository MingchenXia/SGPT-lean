import SGPT.PSH.SiuL2Product

/-!
# Chart-ball covers of `X` adapted to `L` and a positive `G`

Blueprint `claude-siu-l2.tex`, node `claude-siu-l2:cover`.

`SiuCover μ L G`: on a compact complex manifold `X` with a smooth positive volume `μ`, for
holomorphic line bundles `L, G` with smooth metrics such that `θ_G = c₁(G, h_G)` is a Kähler form,
a finite family of chart balls `B(z_a, R_a)` in the preferred charts at points `p_a`, inside the
base sets of the preferred frames of `L` and `G`, with a chart-smooth partition of unity
`χ_a` (`tsupport χ_a ⊆ z_a⁻¹ B(z_a, R_a/4)`), the densities of `μ` in the charts (between `A⁻¹`
and `A` on the balls), a bound `M` for `|∂̄(χ_a ∘ z_l⁻¹)|²` on the `R_l`-balls, and the positivity
`Levi(-log |e_G|²) ≥ c_a |ξ|²` on the balls (`exists_siuCover`).  Nothing depends on the powers
of `L` and `G` or on any weight.  This is the analogue of `SGPT.PSH.GlobalL2.CoverData` in which
the positivity is carried by `G` instead of `L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.SiuL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- The data of `claude-siu-l2:cover`. -/
structure SiuCover (μ : Measure X) (L G : HermitianHolomorphicLineBundle.{0, 0} n X) where
  m : ℕ
  pt : Fin m → X
  R : Fin m → ℝ
  R_pos : ∀ a, 0 < R a
  hball : ∀ a, ball (ctr (n := n) (pt a)) (2 * R a) ⊆
    (complexChartAt (n := n) (pt a)).val.target ∩ (complexChartAt (n := n) (pt a)).val.symm ⁻¹'
      ((prefFrame L (pt a)).val.baseSet ∩ (prefFrame G (pt a)).val.baseSet)
  χ : Fin m → X → ℝ
  χ_smooth : ∀ a, ChartSmooth (n := n) (χ a)
  χ_nonneg : ∀ a x, 0 ≤ χ a x
  sum_χ : ∀ x, ∑ a, χ a x = 1
  tsupport_χ : ∀ a, tsupport (χ a) ⊆ (complexChartAt (n := n) (pt a)).val.source ∩
    (complexChartAt (n := n) (pt a)).val ⁻¹' ball (ctr (n := n) (pt a)) (R a / 4)
  dens : Fin m → ComplexModel n → ℝ
  dens_cont : ∀ a, ContinuousOn (dens a) (complexChartAt (n := n) (pt a)).val.target
  dens_map : ∀ a, Measure.map (complexChartAt (n := n) (pt a)).val
      (μ.restrict (complexChartAt (n := n) (pt a)).val.source) =
    (volume.restrict (complexChartAt (n := n) (pt a)).val.target).withDensity
      (fun z => ENNReal.ofReal (dens a z))
  Aμ : ℝ
  Aμ_pos : 0 < Aμ
  dens_le : ∀ a, ∀ z ∈ ball (ctr (n := n) (pt a)) (R a), dens a z ≤ Aμ
  one_le : ∀ a, ∀ z ∈ ball (ctr (n := n) (pt a)) (R a), 1 ≤ Aμ * dens a z
  M : ℝ
  dbar_χ_le : ∀ a l, ∀ z ∈ ball (ctr (n := n) (pt l)) (R l),
    dbarNormSq (fun z => ((χ a ((complexChartAt (n := n) (pt l)).val.symm z) : ℝ) : ℂ)) z ≤ M
  cG : Fin m → ℝ
  cG_pos : ∀ a, 0 < cG a
  levi_G : ∀ a, ∀ w ∈ ball (ctr (n := n) (pt a)) (R a), ∀ v : ComplexModel n,
    cG a * ‖v‖ ^ 2 ≤ leviForm (frameWeight (prefFrame G (pt a)) (complexChartAt (n := n) (pt a))) w v

/-- The per-point part of the cover data. -/
theorem exists_siu_point_data {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (hG : IsSourceSmoothHermitianMetric G)
    {θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG) (hK : θG.val.IsKahler)
    (p : X) :
    ∃ R : ℝ, 0 < R ∧
      ball (ctr (n := n) p) (2 * R) ⊆
        (complexChartAt (n := n) p).val.target ∩ (complexChartAt (n := n) p).val.symm ⁻¹'
          ((prefFrame L p).val.baseSet ∩ (prefFrame G p).val.baseSet) ∧
      (∃ cG : ℝ, 0 < cG ∧ ∀ w ∈ ball (ctr (n := n) p) R, ∀ v : ComplexModel n,
        cG * ‖v‖ ^ 2 ≤ leviForm (frameWeight (prefFrame G p) (complexChartAt (n := n) p)) w v) ∧
      ∃ dens : ComplexModel n → ℝ, ContinuousOn dens (complexChartAt (n := n) p).val.target ∧
        Measure.map (complexChartAt (n := n) p).val
            (μ.restrict (complexChartAt (n := n) p).val.source) =
          (volume.restrict (complexChartAt (n := n) p).val.target).withDensity
            (fun z => ENNReal.ofReal (dens z)) ∧
        ∃ B : ℝ, 0 < B ∧ ∀ z ∈ ball (ctr (n := n) p) R, dens z ≤ B ∧ 1 ≤ B * dens z := by
  set c := complexChartAt (n := n) p with hc
  set z₀ := ctr (n := n) p with hz₀def
  have hp : p ∈ c.val.source := mem_complexChartAt_source p
  have hz₀ : z₀ ∈ c.val.target := c.val.map_source hp
  set O := c.val.target ∩ c.val.symm ⁻¹' ((prefFrame L p).val.baseSet ∩ (prefFrame G p).val.baseSet)
    with hOdef
  have hO : IsOpen O := c.val.isOpen_inter_preimage_symm
    ((prefFrame L p).val.open_baseSet.inter (prefFrame G p).val.open_baseSet)
  have hz₀O : z₀ ∈ O := ⟨hz₀, by
    rw [mem_preimage, hz₀def, ctr, c.val.left_inv hp]; exact ⟨mem_prefFrame L p, mem_prefFrame G p⟩⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hO z₀ hz₀O
  set R : ℝ := ε / 2 with hRdef
  have hR : 0 < R := by positivity
  have h2R : 2 * R = ε := by rw [hRdef]; ring
  have hballO : ball z₀ (2 * R) ⊆ O := by rw [h2R]; exact hεsub
  have hcl : closedBall z₀ R ⊆ ball z₀ (2 * R) := closedBall_subset_ball (by linarith)
  have hGs : ContDiffOn ℝ ∞ (frameWeight (prefFrame G p) c) (ball z₀ (2 * R)) :=
    (contDiffOn_frameWeight hG (prefFrame G p) c).mono fun z hz => ⟨(hballO hz).1, (hballO hz).2.2⟩
  refine ⟨R, hR, hballO, ?_, ?_⟩
  · obtain ⟨mω, hmω, hmle⟩ := exists_lineValue_lower_bound_of_isCompact' hK.1 c
      (isCompact_closedBall z₀ R) (hcl.trans fun z hz => (hballO hz).1)
    refine ⟨Real.pi * mω, by positivity, fun w hw v => ?_⟩
    have hw2 : w ∈ ball z₀ (2 * R) := hcl (ball_subset_closedBall hw)
    have h2 : ContDiffAt ℝ 2 (frameWeight (prefFrame G p) c) w :=
      ((hGs w hw2).contDiffAt (isOpen_ball.mem_nhds hw2)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hdiag := smoothDDC_complexDiagonal_eq_leviForm h2 v
    have hθw : smoothDDC (frameWeight (prefFrame G p) c) w = θG.val.coeff c w :=
      (hθG c (prefFrame G p) w (hballO hw2).1 (hballO hw2).2.2).symm
    rw [hθw] at hdiag
    have hlev : leviForm (frameWeight (prefFrame G p) c) w v =
        Real.pi * θG.val.coeff c w ![v, Complex.I • v] := by
      rw [hdiag]; field_simp
    rw [hlev]
    have := hmle w (ball_subset_closedBall hw) v
    calc Real.pi * mω * ‖v‖ ^ 2 = Real.pi * (mω * ‖v‖ ^ 2) := by ring
      _ ≤ Real.pi * θG.val.coeff c w ![v, Complex.I • v] :=
          mul_le_mul_of_nonneg_left this Real.pi_pos.le
  · obtain ⟨dens, hdsm, hdpos, hdmap⟩ := hμ c
    have hdc : ContinuousOn dens c.val.target := hdsm.continuousOn
    have hKt : closedBall z₀ R ⊆ c.val.target := hcl.trans fun z hz => (hballO hz).1
    obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall z₀ R).exists_bound_of_continuousOn (hdc.mono hKt)
    obtain ⟨zm, hzm, hmin⟩ := (isCompact_closedBall z₀ R).exists_isMinOn
      ⟨z₀, mem_closedBall_self hR.le⟩ (hdc.mono hKt)
    have hb : 0 < dens zm := hdpos zm (hKt hzm)
    refine ⟨dens, hdc, hdmap, max B₁ (1 / dens zm), lt_max_of_lt_right (by positivity),
      fun z hz => ⟨?_, ?_⟩⟩
    · have hB := hB₁ z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hB
      exact ((le_abs_self _).trans hB).trans (le_max_left _ _)
    · have hmz : dens zm ≤ dens z := hmin (ball_subset_closedBall hz)
      calc (1 : ℝ) = (1 / dens zm) * dens zm := by field_simp
        _ ≤ max B₁ (1 / dens zm) * dens z :=
          mul_le_mul (le_max_right _ _) hmz hb.le (le_trans (by positivity) (le_max_right _ _))

/-- **Existence of the cover data** (`claude-siu-l2:cover`). -/
theorem exists_siuCover [CompactSpace X] {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (hG : IsSourceSmoothHermitianMetric G)
    {θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG) (hK : θG.val.IsKahler) :
    Nonempty (SiuCover μ L G) := by
  choose R hR hball hrest using fun p => exists_siu_point_data (L := L) hμ hG hθG hK p
  choose cG hcG hlevG using fun p => (hrest p).1
  choose dens hdc hdmap B hB hBle using fun p => (hrest p).2
  let S : X → TopologicalSpace.Opens X := fun p =>
    ⟨(complexChartAt (n := n) p).val.source ∩ (complexChartAt (n := n) p).val ⁻¹'
      ball (ctr (n := n) p) (R p / 4),
      (complexChartAt (n := n) p).val.isOpen_inter_preimage isOpen_ball⟩
  have hcover : ∀ x : X, ∃ p, x ∈ S p := fun x =>
    ⟨x, mem_complexChartAt_source x, mem_ball_self (by linarith [hR x])⟩
  obtain ⟨m, χ, idx, hχs, hχ0, hχS, -, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S hcover
  have hKt : ∀ q, closedBall (ctr (n := n) q) (R q) ⊆ (complexChartAt (n := n) q).val.target :=
    fun q => (closedBall_subset_ball (by linarith [hR q])).trans fun z hz => (hball q hz).1
  choose Mχ hMχ0 hMχ using fun (a : Fin m) (l : Fin m) =>
    bound_dbarNormSq_χ (hχs a) (idx l) (hKt (idx l))
  refine ⟨{
    m := m
    pt := idx
    R := fun a => R (idx a)
    R_pos := fun a => hR (idx a)
    hball := fun a => hball (idx a)
    χ := χ
    χ_smooth := hχs
    χ_nonneg := hχ0
    sum_χ := hsum
    tsupport_χ := hχS
    dens := fun a => dens (idx a)
    dens_cont := fun a => hdc (idx a)
    dens_map := fun a => hdmap (idx a)
    Aμ := 1 + ∑ a, B (idx a)
    Aμ_pos := by
      have : 0 ≤ ∑ a, B (idx a) := Finset.sum_nonneg fun a _ => (hB (idx a)).le
      linarith
    dens_le := fun a z hz => by
      have h1 := (hBle (idx a) z hz).1
      have h2 : B (idx a) ≤ ∑ a, B (idx a) :=
        Finset.single_le_sum (f := fun a => B (idx a)) (fun a _ => (hB (idx a)).le)
          (Finset.mem_univ a)
      linarith
    one_le := fun a z hz => by
      have h1 := (hBle (idx a) z hz).2
      have h2 : B (idx a) ≤ ∑ a, B (idx a) :=
        Finset.single_le_sum (f := fun a => B (idx a)) (fun a _ => (hB (idx a)).le)
          (Finset.mem_univ a)
      have hd : 0 ≤ dens (idx a) z := by
        by_contra hneg
        rw [not_le] at hneg
        nlinarith [hB (idx a)]
      nlinarith
    M := ∑ a, ∑ l, Mχ a l
    dbar_χ_le := fun a l z hz => by
      refine (hMχ a l z hz).trans ?_
      have h1 : Mχ a l ≤ ∑ l', Mχ a l' :=
        Finset.single_le_sum (f := fun l' => Mχ a l') (fun l' _ => hMχ0 a l') (Finset.mem_univ l)
      have h2 : ∑ l', Mχ a l' ≤ ∑ a', ∑ l', Mχ a' l' :=
        Finset.single_le_sum (f := fun a' => ∑ l', Mχ a' l')
          (fun a' _ => Finset.sum_nonneg fun l' _ => hMχ0 a' l') (Finset.mem_univ a)
      linarith
    cG := fun a => cG (idx a)
    cG_pos := fun a => hcG (idx a)
    levi_G := fun a => hlevG (idx a) }⟩

end SGPT.PSH.SiuL2
