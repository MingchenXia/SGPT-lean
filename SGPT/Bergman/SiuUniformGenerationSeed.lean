import SGPT.NAPotential.SiuGenStep

/-!
# Local seeds for Siu generation with a fixed pole cover

The cover `D : SiuCover μ G G` is chosen before the varying target bundle `E`.
An actual multiplier-ideal germ and any local atlas frame of `E` at its base
point produce a holomorphic seed, a smooth cutoff and a compact transition
annulus. The scalar germ and frame need exist only on the smaller neighborhood
constructed here. Both its ordinary weighted energy and its pole-weighted
transition energy are proved finite.

No global correction assumption, fixed-ball trivialization of `E`, or estimate
uniform in `E` for this finite seed energy is required. The exponent of the
existing global correction solver can still depend on its `E`-adapted gluing
cover; this theorem does not remove that separate obstruction.

Blueprint: `siu-uniform-local-seed.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga
  SGPT.NAPotential.SiuGen

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- In any fixed chart and any prescribed open neighborhood, the genuine
theta-PSH decomposition supplies the PSH weight needed by local division.
Its smooth shift has finite bounds after shrinking; no bundle frame is used. -/
theorem exists_local_psh_weight_refinement
    {θ : SmoothRealForm (n + 1) (X × unitDisc) 2} {Φ : X × unitDisc → EReal}
    (hΦ : ThetaPlurisubharmonic θ Φ) (C : ComplexChart (n + 1) (X × unitDisc))
    {z₀ : ComplexModel (n + 1)} (hz₀ : z₀ ∈ C.val.target)
    {V : Set (ComplexModel (n + 1))} (hV : IsOpen V) (hz₀V : z₀ ∈ V)
    {c : ℝ} (hc : 0 < c) :
    ∃ (r A : ℝ) (ρ : ComplexModel (n + 1) → ℝ),
      0 < r ∧ 0 ≤ A ∧ closedBall z₀ (4 * r) ⊆ V ∧
      ContDiffOn ℝ ∞ ρ (closedBall z₀ (4 * r)) ∧
      PlurisubharmonicOn
        (fun z => (c : EReal) * (chartFunction Φ C z + (ρ z : EReal)))
        (ball z₀ (2 * r)) ∧
      ∀ z ∈ closedBall z₀ (4 * r), |ρ z| ≤ A ∧
        multiplierWeight 1 ((c : EReal) * (chartFunction Φ C z + (ρ z : EReal))) ≤
          ENNReal.ofReal (Real.exp (c * A)) * multiplierWeight c (chartFunction Φ C z) ∧
        multiplierWeight c (chartFunction Φ C z) ≤
          ENNReal.ofReal (Real.exp (c * A)) *
            multiplierWeight 1 ((c : EReal) * (chartFunction Φ C z + (ρ z : EReal))) := by
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hΦ C z₀ hz₀
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hV.inter hρ.1) z₀ ⟨hz₀V, hz₀W⟩
  set r : ℝ := δ / 8 with hrdef
  have hr : 0 < r := by positivity
  have hcl : closedBall z₀ (4 * r) ⊆ V ∩ W := by
    intro z hz
    apply hδsub
    rw [mem_ball]
    rw [hrdef] at hz
    have := mem_closedBall.mp hz
    linarith
  have hρc := hρ.2.2.1.continuousOn.mono (hcl.trans inter_subset_right)
  obtain ⟨A, hA⟩ := (isCompact_closedBall z₀ (4 * r)).exists_bound_of_continuousOn hρc
  have hbound : ∀ z ∈ closedBall z₀ (4 * r), |ρ z| ≤ |A| := by
    intro z hz
    have hnorm : |ρ z| ≤ A := by simpa only [Real.norm_eq_abs] using hA z hz
    exact hnorm.trans (le_abs_self A)
  have hlocal : PlurisubharmonicOn
      (fun z => (c : EReal) * (chartFunction Φ C z + (ρ z : EReal)))
      (ball z₀ (2 * r)) :=
    (hpsh.const_mul hc).mono fun z hz =>
      (hcl (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))).2
  have hfactor : ∀ z, multiplierWeight 1
      ((c : EReal) * (chartFunction Φ C z + (ρ z : EReal))) =
      ENNReal.ofReal (Real.exp (-(c * ρ z))) * multiplierWeight c (chartFunction Φ C z) := by
    intro z
    rw [add_comm (chartFunction Φ C z) (ρ z : EReal)]
    exact mw_one_mul_add_coe hc (ρ z) (hΦ.quasiPlurisubharmonic.ne_top _)
  refine ⟨r, |A|, ρ, hr, abs_nonneg A, hcl.trans inter_subset_left,
    hρ.2.2.1.mono (hcl.trans inter_subset_right), hlocal, fun z hz => ⟨hbound z hz, ?_, ?_⟩⟩
  · rw [hfactor z]
    refine mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) zero_le
    have hlow := (neg_le_abs (ρ z)).trans (hbound z hz)
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hlow hc.le
  · rw [hfactor z, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    calc multiplierWeight c (chartFunction Φ C z)
        = ENNReal.ofReal 1 * multiplierWeight c (chartFunction Φ C z) := by
          rw [ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          rw [Real.one_le_exp_iff]
          have hhigh := (le_abs_self (ρ z)).trans (hbound z hz)
          have hmul := mul_le_mul_of_nonneg_left hhigh hc.le
          linarith only [hmul]

set_option maxHeartbeats 1000000 in
/-- A fixed geometric pole cover supports a genuine local seed in any target
bundle. The finite energy constant may depend on that local frame and germ. -/
theorem exists_local_seed_fixedPole {μ : Measure X} [SFinite μ]
    {G : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ G G)
    {θ : SmoothRealForm (n + 1) (X × unitDisc) 2} {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential θ Φ)
    {E : HermitianHolomorphicLineBundle.{0, 0} n X} {m : ℕ} (hm : 0 < m)
    (q₀ : X × unitDisc) (e : AtlasFrame E) (he : q₀.1 ∈ e.val.baseSet)
    {g : X × unitDisc → ℂ}
    (hg : (multiplierIdeal (n := n + 1) (m : ℝ) Φ).mem q₀ g) :
    ∃ (a : Fin D.m) (U : Set (X × unitDisc))
      (F : (q : X × unitDisc) → E.Fiber q.1) (χ : X × unitDisc → ℝ)
      (K' : Set (X × unitDisc)) (r : ℝ),
      q₀ ∈ (D.chartP a).val.source ∧ 0 < r ∧ 8 * r ≤ D.siuPoleR a ∧
      U = (D.chartP a).val.source ∩ (D.chartP a).val ⁻¹'
        ball ((D.chartP a).val q₀) (4 * r) ∧ IsOpen U ∧ q₀ ∈ U ∧
      IsHolomorphicProdSectionOn E F U ∧
      (∀ q, F q = g q • e.val.symm q.1 1) ∧
      ChartSmooth (n := n + 1) χ ∧ tsupport χ ⊆ U ∧
      (∀ q, 0 ≤ χ q ∧ χ q ≤ 1) ∧
      (∀ᶠ q in 𝓝 q₀, χ q = 1 ∧
        e.val.continuousLinearMapAt ℂ q.1 (F q) = g q) ∧
      IsCompact K' ∧ K' ⊆ U ∧ q₀ ∉ K' ∧
      (∀ q ∈ U \ K', ∀ᶠ q' in 𝓝 q, χ q' = χ q) ∧
      (∫⁻ q in U, ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight (m : ℝ) (Φ q)
        ∂(prodMeasure μ)) < ⊤ ∧
      (∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1
        (SiuCover.thetaGen m Φ
          (D.poleP a ((D.chartX a).val q₀.1) q₀.2.val) q)
        ∂(prodMeasure μ)) < ⊤ := by
  classical
  have := e.property
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hΦtop : ∀ q, Φ q ≠ ⊤ := fun q => hΦ.1.quasiPlurisubharmonic.ne_top q
  -- step 0: the chart index and the pole
  obtain ⟨a, ha⟩ : ∃ a, q₀.1 ∈ tsupport (D.χ a) := by
    have hne : ∑ a, D.χ a q₀.1 ≠ 0 := by rw [D.sum_χ q₀.1]; exact one_ne_zero
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨a, subset_tsupport _ ha⟩
  have hxa := D.tsupport_χ a ha
  set C := D.chartP a with hC
  set p := (D.chartX a).val q₀.1 with hp
  set t₀ := q₀.2.val with ht₀
  set w₀ := C.val q₀ with hw₀
  have hw₀' : w₀ = prodL n (p, t₀) := D.chartP_apply a q₀
  have hq₀C : q₀ ∈ C.val.source := by rw [D.chartP_source]; exact ⟨hxa.1, mem_univ _⟩
  have hpR4 : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := hxa.2
  have hpc : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) := ball_subset_closedBall hpR4
  have ht₀1 : ‖t₀‖ < 1 := mem_unitDisc.mp q₀.2.property
  set Ψ : X × unitDisc → EReal := D.poleP a p t₀ with hΨdef
  have hΨtop : ∀ q, Ψ q ≠ ⊤ := D.poleP_ne_top hpc ht₀1
  have hRa := D.R_pos a
  have hrP := D.siuPoleR_pos a
  have hrPle := D.siuPoleR_le a
  -- step 1: the integrability of `g` in the chart `C`
  obtain ⟨hgx, hgint⟩ := hg
  have huscΦ : ∀ e₁ e₂ : ComplexChart (n + 1) (X × unitDisc),
      UpperSemicontinuousOn (chartFunction Φ e₁) (ChartWeightedL2.overlapDomain e₁ e₂) :=
    fun e₁ e₂ => (upperSemicontinuousOn_chartFunction_target hΦ.1 e₁).mono fun z hz => hz.1
  have hgc := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) C
    (complexChartAt (n := n + 1) q₀) hq₀C (mem_complexChartAt_source q₀) (huscΦ _ _) hm'.ne' hgint
  obtain ⟨-, U₀, hU₀o, hw₀U₀, hgU₀, -, hU₀int⟩ := hgc
  -- step 2: the radius
  obtain ⟨Vg, hVg, hVgo, hq₀Vg⟩ := eventually_nhds_iff.mp hgx
  set W₀ : Set (ComplexModel (n + 1)) := U₀ ∩ ball w₀ (D.siuPoleR a) ∩
    (C.val.target ∩ C.val.symm ⁻¹' (Vg ∩ Prod.fst ⁻¹' e.val.baseSet)) with hW₀
  have hW₀o : IsOpen W₀ := (hU₀o.inter isOpen_ball).inter
    (C.val.isOpen_inter_preimage_symm (hVgo.inter (e.val.open_baseSet.preimage continuous_fst)))
  have hw₀W₀ : w₀ ∈ W₀ := ⟨⟨hw₀U₀, mem_ball_self hrP⟩, C.val.map_source hq₀C, by
    simp only [mem_preimage, hw₀, C.val.left_inv hq₀C]; exact ⟨hq₀Vg, he⟩⟩
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := Metric.isOpen_iff.mp hW₀o w₀ hw₀W₀
  set r₁ : ℝ := min ρ₀ (D.siuPoleR a) / 8 with hr₁def
  have hr₁ : 0 < r₁ := by have := lt_min hρ₀ hrP; positivity
  have h8ρ : 8 * r₁ ≤ ρ₀ := by have := min_le_left ρ₀ (D.siuPoleR a); rw [hr₁def]; linarith
  have h8ε : 8 * r₁ ≤ D.siuPoleR a := by
    have := min_le_right ρ₀ (D.siuPoleR a); rw [hr₁def]; linarith
  have hW4 : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ W₀ := fun z hz =>
    hρ₀W (by rw [mem_ball]; linarith [mem_closedBall.mp hz])
  have hct : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ C.val.target := fun z hz => (hW4 z hz).2.1
  have hcVe : ∀ z ∈ closedBall w₀ (4 * r₁),
      C.val.symm z ∈ Vg ∧ (C.val.symm z).1 ∈ e.val.baseSet := fun z hz => (hW4 z hz).2.2
  have hcU₀ : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ U₀ := fun z hz => (hW4 z hz).1.1
  have hcP : ∀ z ∈ closedBall w₀ (4 * r₁), ‖z - w₀‖ < D.siuPoleR a := fun z hz => by
    have := (hW4 z hz).1.2; rwa [mem_ball, dist_eq_norm] at this
  have hcDomR : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1 := by
    intro z hz
    have hzt := hct z hz
    rw [pChart_target] at hzt
    refine ⟨?_, hzt.2⟩
    have h1 : ‖projX n z - p‖ ≤ ‖z - w₀‖ := by
      have hsq := norm_sub_sq_prodL z w₀
      rw [show projX n w₀ = p by rw [hw₀', projX_prodL],
        show projT n w₀ = t₀ by rw [hw₀', projT_prodL]] at hsq
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
        (by nlinarith [sq_nonneg ‖projT n z - t₀‖])
    have h2 := hcP z hz
    have h3 : ‖p - ctr (n := n) (D.pt a)‖ < D.R a / 4 := by
      have := hpR4; rwa [mem_ball, dist_eq_norm] at this
    rw [mem_ball, dist_eq_norm]
    calc ‖projX n z - ctr (n := n) (D.pt a)‖
        ≤ ‖projX n z - p‖ + ‖p - ctr (n := n) (D.pt a)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < D.R a := by linarith
  -- step 3: the local section `F = g e`
  set Uset : Set (X × unitDisc) := C.val.source ∩ C.val ⁻¹' ball w₀ (4 * r₁) with hUset
  have hUo : IsOpen Uset := C.val.isOpen_inter_preimage isOpen_ball
  have hUmem : ∀ y ∈ Uset, y ∈ Vg ∧ y.1 ∈ e.val.baseSet := by
    intro y hy
    have h := hcVe (C.val y) (ball_subset_closedBall hy.2)
    rwa [C.val.left_inv hy.1] at h
  set F : (q : X × unitDisc) → E.Fiber q.1 := fun q => g q • e.val.symm q.1 1 with hFdef
  have hgHol : ∀ y ∈ Uset, HolomorphicAt (n + 1) g y := fun y hy =>
    eventually_of_mem (hVgo.mem_nhds (hUmem y hy).1) fun y' hy' => hVg y' hy'
  have hF : IsHolomorphicProdSectionOn E F Uset := by
    intro q hq e' hqe'
    have := e'.property
    refine (HolomorphicAt.mul' (hgHol q hq)
      (holomorphicAt_transition_prod e e' (hUmem q hq).2 hqe')).congr
      (Eventually.of_forall fun q' => ?_)
    change g q' * e'.val.continuousLinearMapAt ℂ q'.1 (e.val.symm q'.1 1) =
      e'.val.continuousLinearMapAt ℂ q'.1 (g q' • e.val.symm q'.1 1)
    rw [map_smul, smul_eq_mul]
  have hFcoef : ∀ y : X × unitDisc, y.1 ∈ e.val.baseSet →
      e.val.continuousLinearMapAt ℂ y.1 (F y) = g y := by
    intro y hy
    change e.val.continuousLinearMapAt ℂ y.1 (g y • e.val.symm y.1 1) = g y
    rw [map_smul, trivialization_coef_frame e.val hy, smul_eq_mul, mul_one]
  have hFnorm : ∀ y, ‖F y‖ = ‖g y‖ * ‖e.val.symm y.1 1‖ := fun y => norm_smul _ _
  -- step 4: the cut-off `χ`, `1` on `B(w₀, r₁)`, supported in `B(w₀, 2r₁)`
  set β : ContDiffBump w₀ := ⟨r₁, 2 * r₁, hr₁, by linarith⟩ with hβ
  set χ : X × unitDisc → ℝ := ChartPartition.chartExtend C β with hχdef
  have hβt : tsupport β = closedBall w₀ (2 * r₁) := β.tsupport_eq
  have hcb2 : closedBall w₀ (2 * r₁) ⊆ C.val.target := fun z hz =>
    hct z (closedBall_subset_closedBall (by linarith) hz)
  have hχ : ChartSmooth (n := n + 1) χ := ChartPartition.chartSmooth_chartExtend C β.contDiff
    β.hasCompactSupport.isCompact (by rw [hβt]; exact hcb2)
  have hχU : tsupport χ ⊆ Uset := by
    refine (ChartPartition.support_chartExtend_subset C).trans ?_
    rw [hβt]
    have hcomp : IsCompact (C.val.symm '' closedBall w₀ (2 * r₁)) :=
      (isCompact_closedBall w₀ _).image_of_continuousOn (C.val.continuousOn_symm.mono hcb2)
    rw [hcomp.isClosed.closure_eq]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨C.val.map_target (hcb2 hw), ?_⟩
    rw [mem_preimage, C.val.right_inv (hcb2 hw), mem_ball]
    have := mem_closedBall.mp hw; linarith
  have hχ0 : ∀ y, 0 ≤ χ y := ChartPartition.chartExtend_nonneg fun z => β.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := ChartPartition.chartExtend_le_one fun z => β.le_one
  have hχone : ∀ y ∈ C.val.source, C.val y ∈ ball w₀ r₁ → χ y = 1 := by
    intro y hy hyr
    rw [hχdef, ChartPartition.chartExtend_of_mem hy]
    exact β.one_of_mem_closedBall (ball_subset_closedBall hyr)
  set A₀ : Set (ComplexModel (n + 1)) := closedBall w₀ (2 * r₁) ∩ {w | r₁ ≤ dist w w₀} with hA₀
  set K' : Set (X × unitDisc) := C.val.symm '' A₀ with hK'def
  have hA₀c : IsCompact A₀ := (isCompact_closedBall w₀ _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hK' : IsCompact K' :=
    hA₀c.image_of_continuousOn (C.val.continuousOn_symm.mono fun w hw => hcb2 hw.1)
  have hK'U : K' ⊆ Uset := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨C.val.map_target (hcb2 hw.1), ?_⟩
    rw [mem_preimage, C.val.right_inv (hcb2 hw.1), mem_ball]
    have := mem_closedBall.mp hw.1; linarith
  have hK'ann : ∀ y ∈ K', y ∈ C.val.source ∧ r₁ ≤ ‖C.val y - w₀‖ := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨C.val.map_target (hcb2 hw.1), ?_⟩
    rw [C.val.right_inv (hcb2 hw.1), ← dist_eq_norm]; exact hw.2
  have hconst : ∀ y ∈ Uset \ K', ∀ᶠ y' in 𝓝 y, χ y' = χ y := by
    rintro y ⟨⟨hy, -⟩, hyK⟩
    by_cases h1 : dist (C.val y) w₀ < r₁
    · have hO : IsOpen (C.val.source ∩ C.val ⁻¹' ball w₀ r₁) :=
        C.val.isOpen_inter_preimage isOpen_ball
      filter_upwards [hO.mem_nhds ⟨hy, h1⟩] with y' hy'
      rw [hχone y' hy'.1 hy'.2, hχone y hy h1]
    · have h3 : 2 * r₁ < dist (C.val y) w₀ := by
        by_contra hle
        exact hyK ⟨C.val y, ⟨mem_closedBall.mpr (not_lt.mp hle), not_lt.mp h1⟩,
          C.val.left_inv hy⟩
      have hO : IsOpen (C.val.source ∩ C.val ⁻¹' {w | 2 * r₁ < dist w w₀}) :=
        C.val.isOpen_inter_preimage (isOpen_lt continuous_const
          (continuous_id.dist continuous_const))
      have hval : ∀ y' ∈ C.val.source ∩ C.val ⁻¹' {w | 2 * r₁ < dist w w₀}, χ y' = 0 := by
        intro y' hy'
        rw [hχdef, ChartPartition.chartExtend_of_mem hy'.1]
        exact β.zero_of_le_dist (le_of_lt hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h3⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h3⟩]
  -- step 5: `∫_U |F|² e^{-mΦ} < ∞`
  obtain ⟨mE, ME, hmE0, hmEb⟩ := exists_frameNorm_bounds e C (by positivity : (0 : ℝ) ≤ 4 * r₁)
    (fun z hz => ⟨hct z hz, (hcVe z hz).2⟩)
  have hball4t : ball w₀ (4 * r₁) ⊆ C.val.target := fun z hz => hct z (ball_subset_closedBall hz)
  have hρc := D.dens_cont a
  have hmapa := D.dens_map a
  have hgcont : ContinuousOn (fun z => g (C.val.symm z)) (ball w₀ (4 * r₁)) :=
    (hgU₀.mono fun z hz => hcU₀ z (ball_subset_closedBall hz)).continuousOn
  have hfrcont : ContinuousOn (fun z => ‖e.val.symm (C.val.symm z).1 1‖) (ball w₀ (4 * r₁)) :=
    (frameNorm_continuousOn E.Fiber e.val).comp
      (continuous_fst.comp_continuousOn (C.val.continuousOn_symm.mono hball4t))
      fun z hz => (hcVe z (ball_subset_closedBall hz)).2
  have hwΦ : AEMeasurable (fun z => multiplierWeight (m : ℝ) (Φ (C.val.symm z)))
      (volume.restrict (ball w₀ (4 * r₁))) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((upperSemicontinuousOn_chartFunction_target hΦ.1 C).mono hball4t) hm'.ne'
  have hJ : ∫⁻ y in Uset, ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (m : ℝ) (Φ y)
      ∂(prodMeasure μ) < ⊤ := by
    have hcF : ContinuousOn (fun z => ‖F (C.val.symm z)‖ ^ 2) (ball w₀ (4 * r₁)) := by
      have : (fun z => ‖F (C.val.symm z)‖ ^ 2) =
          fun z => (‖g (C.val.symm z)‖ * ‖e.val.symm (C.val.symm z).1 1‖) ^ 2 := by
        funext z; rw [hFnorm]
      rw [this]
      exact (hgcont.norm.mul hfrcont).pow 2
    have hmeas : AEMeasurable (fun z => ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) *
        multiplierWeight (m : ℝ) (Φ (C.val.symm z))) (volume.restrict (ball w₀ (4 * r₁))) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (hcF.aestronglyMeasurable measurableSet_ball).aemeasurable).mul hwΦ
    rw [setLIntegral_pChart_eq (D.pt a, discOrigin) hρc hmapa isOpen_ball hball4t hmeas]
    have hME : 0 ≤ ME := (hmE0.le.trans (hmEb w₀ (mem_closedBall_self (by positivity))).1).trans
      (hmEb w₀ (mem_closedBall_self (by positivity))).2
    calc ∫⁻ z in ball w₀ (4 * r₁), ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) *
          multiplierWeight (m : ℝ) (Φ (C.val.symm z)) * ENNReal.ofReal (D.dens a (projX n z))
        ≤ ∫⁻ z in ball w₀ (4 * r₁), ENNReal.ofReal (ME ^ 2 * D.Aμ) *
            multiplierDensity (chartFunction Φ C) (m : ℝ) (fun z => g (C.val.symm z)) z := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          have hz4 : z ∈ closedBall w₀ (4 * r₁) := ball_subset_closedBall hz
          have hdom := hcDomR z hz4
          have hd1 : D.dens a (projX n z) ≤ D.Aμ := D.dens_le a _ hdom.1
          have hd2 : 1 ≤ D.Aμ * D.dens a (projX n z) := D.one_le a _ hdom.1
          have hd0 : 0 ≤ D.dens a (projX n z) := by
            by_contra hneg; push Not at hneg; nlinarith [D.Aμ_pos]
          have hfr := (hmEb z hz4).2
          have hfr0 : 0 ≤ ‖e.val.symm (C.val.symm z).1 1‖ := norm_nonneg _
          have h1 : ‖e.val.symm (C.val.symm z).1 1‖ ^ 2 ≤ ME ^ 2 := pow_le_pow_left₀ hfr0 hfr 2
          have h2 : ‖e.val.symm (C.val.symm z).1 1‖ ^ 2 * D.dens a (projX n z) ≤ ME ^ 2 * D.Aμ :=
            mul_le_mul h1 hd1 hd0 (sq_nonneg _)
          have hreal : ‖F (C.val.symm z)‖ ^ 2 * D.dens a (projX n z) ≤
              ME ^ 2 * D.Aμ * ‖g (C.val.symm z)‖ ^ 2 := by
            rw [hFnorm]
            calc (‖g (C.val.symm z)‖ * ‖e.val.symm (C.val.symm z).1 1‖) ^ 2 *
                  D.dens a (projX n z)
                = ‖g (C.val.symm z)‖ ^ 2 * (‖e.val.symm (C.val.symm z).1 1‖ ^ 2 *
                    D.dens a (projX n z)) := by ring
              _ ≤ ‖g (C.val.symm z)‖ ^ 2 * (ME ^ 2 * D.Aμ) :=
                  mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
              _ = ME ^ 2 * D.Aμ * ‖g (C.val.symm z)‖ ^ 2 := by ring
          have key : ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * ENNReal.ofReal (D.dens a (projX n z))
              ≤ ENNReal.ofReal (ME ^ 2 * D.Aμ) * ENNReal.ofReal (‖g (C.val.symm z)‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul (sq_nonneg _),
              ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) D.Aμ_pos.le)]
            exact ENNReal.ofReal_le_ofReal hreal
          show ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) *
              ENNReal.ofReal (D.dens a (projX n z)) ≤ ENNReal.ofReal (ME ^ 2 * D.Aμ) *
            (ENNReal.ofReal (‖g (C.val.symm z)‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)))
          calc ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) *
                ENNReal.ofReal (D.dens a (projX n z))
              = (ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * ENNReal.ofReal (D.dens a (projX n z))) *
                  multiplierWeight (m : ℝ) (Φ (C.val.symm z)) := by ring
            _ ≤ (ENNReal.ofReal (ME ^ 2 * D.Aμ) * ENNReal.ofReal (‖g (C.val.symm z)‖ ^ 2)) *
                  multiplierWeight (m : ℝ) (Φ (C.val.symm z)) := mul_le_mul_of_nonneg_right key zero_le
            _ = _ := by ring
      _ = ENNReal.ofReal (ME ^ 2 * D.Aμ) * ∫⁻ z in ball w₀ (4 * r₁),
            multiplierDensity (chartFunction Φ C) (m : ℝ) (fun z => g (C.val.symm z)) z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ME ^ 2 * D.Aμ) * ∫⁻ z in U₀,
            multiplierDensity (chartFunction Φ C) (m : ℝ) (fun z => g (C.val.symm z)) z :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set fun z hz =>
            hcU₀ z (ball_subset_closedBall hz)) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU₀int
  -- the energy of `F` over `K'` for the pole weight
  have hKint : ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) *
      multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ) < ⊤ := by
    set c₀ : ℝ := ((n : ℝ) + 3) * Real.log ((r₁ / 2) ^ 2) with hc₀
    calc ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)
          ∂(prodMeasure μ)
        ≤ ∫⁻ q in K', ENNReal.ofReal (Real.exp (-c₀)) *
            (ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight (m : ℝ) (Φ q)) ∂(prodMeasure μ) := by
          refine setLIntegral_mono' hK'.isClosed.measurableSet fun q hq => ?_
          have hlow : ((c₀ : ℝ) : EReal) ≤ Ψ q :=
            D.le_poleP t₀ hr₁ (by linarith) (by rw [← hw₀']; exact (hK'ann q hq).2)
          have := thetaGen_le_mw_of_le hm (hΦtop q) (hΨtop q) hlow
          calc ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)
              ≤ ENNReal.ofReal (‖F q‖ ^ 2) *
                  (ENNReal.ofReal (Real.exp (-c₀)) * multiplierWeight (m : ℝ) (Φ q)) :=
                mul_le_mul_of_nonneg_left this zero_le
            _ = _ := by ring
      _ = ENNReal.ofReal (Real.exp (-c₀)) * ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) *
            multiplierWeight (m : ℝ) (Φ q) ∂(prodMeasure μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (-c₀)) * ∫⁻ q in Uset, ENNReal.ofReal (‖F q‖ ^ 2) *
            multiplierWeight (m : ℝ) (Φ q) ∂(prodMeasure μ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hK'U) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ
  have hq₀U : q₀ ∈ Uset := ⟨hq₀C, mem_ball_self (by positivity)⟩
  have hnear : ∀ᶠ q in 𝓝 q₀, χ q = 1 ∧
      e.val.continuousLinearMapAt ℂ q.1 (F q) = g q := by
    have hO : IsOpen (C.val.source ∩ C.val ⁻¹' ball w₀ r₁) :=
      C.val.isOpen_inter_preimage isOpen_ball
    filter_upwards [hO.mem_nhds ⟨hq₀C, mem_ball_self hr₁⟩] with q hq
    refine ⟨hχone q hq.1 hq.2, hFcoef q ?_⟩
    exact (hUmem q ⟨hq.1, (ball_subset_ball (by linarith)) hq.2⟩).2
  have hq₀K : q₀ ∉ K' := by
    intro hq
    have h := (hK'ann q₀ hq).2
    rw [show C.val q₀ = w₀ from rfl, sub_self, norm_zero] at h
    exact (not_le_of_gt hr₁) h
  exact ⟨a, Uset, F, χ, K', r₁, hq₀C, hr₁, h8ε, rfl, hUo, hq₀U, hF,
    (fun _ => rfl), hχ, hχU, (fun q => ⟨hχ0 q, hχ1 q⟩), hnear,
    hK', hK'U, hq₀K, hconst, hJ, hKint⟩

end SGPT.Bergman.SiuUniformGeneration
