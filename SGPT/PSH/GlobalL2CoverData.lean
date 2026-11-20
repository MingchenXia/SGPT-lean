import SGPT.PSH.GlobalL2CoverBasics
import SGPT.PSH.GlobalL2Statement
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.ChartPartition

/-!
# Chart-ball covers adapted to two line bundles

Blueprint `claude-global-l2:cover`.  `exists_coverData`: on a compact complex manifold `X` with a
Kähler background `ω`, a smooth positive volume `μ`, holomorphic line bundles `L, T` with smooth
metrics, `θ = c₁(L, h_L)` and `δ > 0`, there is a finite family of chart balls `B(z_a, R_a)` in
the preferred charts at points `p_a`, inside the base sets of the preferred frames of `L` and `T`,
with

* smooth local potentials `ρ'_a` of `θ - δω` on `B(z_a, 2R_a)`;
* a chart-smooth partition of unity `χ_a` with `tsupport χ_a ⊆ z_a⁻¹ B(z_a, R_a/4)`;
* the densities of `μ` in the charts, between `A⁻¹` and `A` on the balls;
* a bound `M` for `|∂̄(χ_a ∘ z_l⁻¹)|²` on the `R_l`-balls;
* `Levi(ρ_L - ρ') ≥ δ c_a |ξ|²` (`ρ_L = -log |e_L|²`) and `Levi(-log |e_T|²) ≥ -C_a |ξ|²` on the
  balls.

None of these data depends on the power `k` or on the weight.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The preferred atlas frame of a line bundle at a point. -/
def prefFrame (L : HermitianHolomorphicLineBundle.{0, 0} n X) (p : X) : AtlasFrame L :=
  ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩

theorem mem_prefFrame (L : HermitianHolomorphicLineBundle.{0, 0} n X) (p : X) :
    p ∈ (prefFrame L p).val.baseSet :=
  mem_baseSet_trivializationAt ℂ L.Fiber p

/-- The local weight `-log |e|²` of a frame in a chart. -/
def frameWeight {L : HermitianHolomorphicLineBundle.{0, 0} n X} (e : AtlasFrame L)
    (c : ComplexChart n X) (z : ComplexModel n) : ℝ :=
  -Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2)

theorem contDiffOn_frameWeight {L : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (e : AtlasFrame L) (c : ComplexChart n X) :
    ContDiffOn ℝ ∞ (frameWeight e c) (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let := e.property
  refine ((hL c e).log fun z hz => ?_).neg
  exact (sq_pos_of_pos (frameNorm_pos L.Fiber e.val hz.2)).ne'

theorem coeff_sub_smul (θ η : ClosedRealOneOneForm n X) (δ : ℝ) (c : ComplexChart n X)
    (z : ComplexModel n) :
    (θ - δ • η).val.coeff c z = θ.val.coeff c z - δ • η.val.coeff c z := by
  rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    ClosedRealOneOneForm.coeff_smul, ← sub_eq_add_neg]

/-- The centre `z(p)` of the preferred chart at `p`. -/
def ctr (p : X) : ComplexModel n := (complexChartAt (n := n) p).val p

theorem ctr_mem_target (p : X) : ctr (n := n) p ∈ (complexChartAt (n := n) p).val.target :=
  (complexChartAt (n := n) p).val.map_source (mem_complexChartAt_source p)

variable [MeasurableSpace X] [BorelSpace X]

/-- The data of `claude-global-l2:cover`; nothing depends on the power `k` or on the weight. -/
structure CoverData (ωb : KahlerBackground n X) (μ : Measure X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (θ : ClosedRealOneOneForm n X) (δ : ℝ) where
  m : ℕ
  pt : Fin m → X
  R : Fin m → ℝ
  R_pos : ∀ a, 0 < R a
  hball : ∀ a, ball (ctr (n := n) (pt a)) (2 * R a) ⊆
    (complexChartAt (n := n) (pt a)).val.target ∩ (complexChartAt (n := n) (pt a)).val.symm ⁻¹'
      ((prefFrame L (pt a)).val.baseSet ∩ (prefFrame T (pt a)).val.baseSet)
  ρ' : Fin m → ComplexModel n → ℝ
  pot : ∀ a, IsSmoothLocalPotential (θ - δ • ωb.form).val (complexChartAt (n := n) (pt a))
    (ball (ctr (n := n) (pt a)) (2 * R a)) (ρ' a)
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
  cω : Fin m → ℝ
  cω_pos : ∀ a, 0 < cω a
  levi_L : ∀ a, ∀ w ∈ ball (ctr (n := n) (pt a)) (R a), ∀ v : ComplexModel n,
    δ * cω a * ‖v‖ ^ 2 ≤ leviForm
      (fun z => frameWeight (prefFrame L (pt a)) (complexChartAt (n := n) (pt a)) z - ρ' a z) w v
  CT : Fin m → ℝ
  CT_nonneg : ∀ a, 0 ≤ CT a
  levi_T : ∀ a, ∀ w ∈ ball (ctr (n := n) (pt a)) (R a), ∀ v : ComplexModel n,
    -(CT a * ‖v‖ ^ 2) ≤ leviForm (frameWeight (prefFrame T (pt a)) (complexChartAt (n := n) (pt a))) w v

/-- The per-point part of the cover data. -/
theorem exists_point_data (ωb : KahlerBackground n X) {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {θ : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ) {δ : ℝ} (hδ : 0 < δ) (p : X) :
    ∃ R : ℝ, 0 < R ∧
      ball (ctr (n := n) p) (2 * R) ⊆
        (complexChartAt (n := n) p).val.target ∩ (complexChartAt (n := n) p).val.symm ⁻¹'
          ((prefFrame L p).val.baseSet ∩ (prefFrame T p).val.baseSet) ∧
      ∃ ρ' : ComplexModel n → ℝ, IsSmoothLocalPotential (θ - δ • ωb.form).val
        (complexChartAt (n := n) p) (ball (ctr (n := n) p) (2 * R)) ρ' ∧
      (∃ cω : ℝ, 0 < cω ∧ ∀ w ∈ ball (ctr (n := n) p) R, ∀ v : ComplexModel n,
        δ * cω * ‖v‖ ^ 2 ≤ leviForm
          (fun z => frameWeight (prefFrame L p) (complexChartAt (n := n) p) z - ρ' z) w v) ∧
      (∃ CT : ℝ, 0 ≤ CT ∧ ∀ w ∈ ball (ctr (n := n) p) R, ∀ v : ComplexModel n,
        -(CT * ‖v‖ ^ 2) ≤ leviForm (frameWeight (prefFrame T p) (complexChartAt (n := n) p)) w v) ∧
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
  set O := c.val.target ∩ c.val.symm ⁻¹' ((prefFrame L p).val.baseSet ∩ (prefFrame T p).val.baseSet)
    with hOdef
  have hO : IsOpen O := c.val.isOpen_inter_preimage_symm
    ((prefFrame L p).val.open_baseSet.inter (prefFrame T p).val.open_baseSet)
  have hz₀O : z₀ ∈ O := ⟨hz₀, by
    rw [mem_preimage, hz₀def, ctr, c.val.left_inv hp]; exact ⟨mem_prefFrame L p, mem_prefFrame T p⟩⟩
  obtain ⟨W, ρ', hz₀W, hρ'⟩ := LocalPotentials.hasSmoothLocalPotentials_of_closed_typeOneOne
    (θ - δ • ωb.form).val (θ - δ • ωb.form).property.1 (θ - δ • ωb.form).property.2 c z₀ hz₀
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hO.inter hρ'.1) z₀ ⟨hz₀O, hz₀W⟩
  set R : ℝ := ε / 2 with hRdef
  have hR : 0 < R := by positivity
  have h2R : 2 * R = ε := by rw [hRdef]; ring
  have hballO : ball z₀ (2 * R) ⊆ O := by rw [h2R]; exact fun z hz => (hεsub hz).1
  have hballW : ball z₀ (2 * R) ⊆ W := by rw [h2R]; exact fun z hz => (hεsub hz).2
  have hcl : closedBall z₀ R ⊆ ball z₀ (2 * R) := closedBall_subset_ball (by linarith)
  have hρ'2 : IsSmoothLocalPotential (θ - δ • ωb.form).val c (ball z₀ (2 * R)) ρ' :=
    hρ'.mono isOpen_ball hballW
  have hLs : ContDiffOn ℝ ∞ (frameWeight (prefFrame L p) c) (ball z₀ (2 * R)) :=
    (contDiffOn_frameWeight hL (prefFrame L p) c).mono fun z hz => ⟨(hballO hz).1, (hballO hz).2.1⟩
  have hTs : ContDiffOn ℝ ∞ (frameWeight (prefFrame T p) c) (ball z₀ (2 * R)) :=
    (contDiffOn_frameWeight hT (prefFrame T p) c).mono fun z hz => ⟨(hballO hz).1, (hballO hz).2.2⟩
  refine ⟨R, hR, hballO, ρ', hρ'2, ?_, ?_, ?_⟩
  · -- the Kähler lower bound
    obtain ⟨mω, hmω, hmle⟩ := exists_lineValue_lower_bound_of_isCompact' ωb.isKahler.1 c
      (isCompact_closedBall z₀ R) (hcl.trans fun z hz => (hballO hz).1)
    refine ⟨Real.pi * mω, by positivity, fun w hw v => ?_⟩
    have hw2 : w ∈ ball z₀ (2 * R) := hcl (ball_subset_closedBall hw)
    have hsm : ContDiffOn ℝ ∞ (fun z => frameWeight (prefFrame L p) c z - ρ' z) (ball z₀ (2 * R)) :=
      hLs.sub hρ'2.2.2.1
    have h2 : ContDiffAt ℝ 2 (fun z => frameWeight (prefFrame L p) c z - ρ' z) w :=
      ((hsm w hw2).contDiffAt (isOpen_ball.mem_nhds hw2)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hdiag := smoothDDC_complexDiagonal_eq_leviForm h2 v
    have hddc : smoothDDC (fun z => frameWeight (prefFrame L p) c z - ρ' z) w =
        δ • ωb.form.val.coeff c w := by
      rw [smoothDDC_sub isOpen_ball hLs hρ'2.2.2.1 hw2, hρ'2.2.2.2 hw2, coeff_sub_smul]
      have hθw : smoothDDC (frameWeight (prefFrame L p) c) w = θ.val.coeff c w :=
        (hθ c (prefFrame L p) w (hballO hw2).1 (hballO hw2).2.1).symm
      rw [hθw]
      abel
    rw [hddc] at hdiag
    have hlev : leviForm (fun z => frameWeight (prefFrame L p) c z - ρ' z) w v =
        Real.pi * (δ * ωb.form.val.coeff c w ![v, Complex.I • v]) := by
      have := hdiag
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at this
      field_simp at this
      linarith
    rw [hlev]
    have := hmle w (ball_subset_closedBall hw) v
    calc δ * (Real.pi * mω) * ‖v‖ ^ 2 = (Real.pi * δ) * (mω * ‖v‖ ^ 2) := by ring
      _ ≤ (Real.pi * δ) * ωb.form.val.coeff c w ![v, Complex.I • v] :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · obtain ⟨C, hC0, hC⟩ := exists_neg_le_leviForm_of_contDiffOn isOpen_ball
      (isCompact_closedBall z₀ R) hcl hTs
    exact ⟨C, hC0, fun w hw v => hC w (ball_subset_closedBall hw) v⟩
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

theorem bound_dbarNormSq_χ {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (q : X) {R : ℝ}
    (hR : closedBall (ctr (n := n) q) R ⊆ (complexChartAt (n := n) q).val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (ctr (n := n) q) R,
      dbarNormSq (fun z => ((χ ((complexChartAt (n := n) q).val.symm z) : ℝ) : ℂ)) z ≤ C := by
  set c := complexChartAt (n := n) q
  have hs : ContDiffOn ℝ ∞ (fun z => ((χ (c.val.symm z) : ℝ) : ℂ)) c.val.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ c)
  have hcont := continuousOn_dbarNormSq c.val.open_target
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  obtain ⟨C, hC⟩ := (isCompact_closedBall _ R).exists_bound_of_continuousOn (hcont.mono hR)
  refine ⟨|C|, abs_nonneg C, fun z hz => ?_⟩
  have := hC z (ball_subset_closedBall hz)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_abs_self C))

/-- **Existence of the cover data** (`claude-global-l2:cover`). -/
theorem exists_coverData [CompactSpace X] (ωb : KahlerBackground n X) {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {θ : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (CoverData ωb μ L T θ δ) := by
  choose R hR hball ρ' hpot hrest using fun p => exists_point_data ωb hμ hL hT hθ hδ p
  choose cω hcω hlevL using fun p => (hrest p).1
  choose CT hCT hlevT using fun p => (hrest p).2.1
  choose dens hdc hdmap B hB hBle using fun p => (hrest p).2.2
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
    ρ' := fun a => ρ' (idx a)
    pot := fun a => hpot (idx a)
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
    cω := fun a => cω (idx a)
    cω_pos := fun a => hcω (idx a)
    levi_L := fun a => hlevL (idx a)
    CT := fun a => CT (idx a)
    CT_nonneg := fun a => hCT (idx a)
    levi_T := fun a => hlevT (idx a) }⟩

end SGPT.PSH.GlobalL2
