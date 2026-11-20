import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityLeviMargin
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.PlurisubharmonicLimits

set_option autoImplicit false

/-! # The SAME original density is genuine enlarged-background PSH, including zeros -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityThetaPsh
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction
  ActualGlobalSquaredBergmanDensity ActualOriginalSquaredDensityLeviMargin
  LocalPotentials LocalPotentialPullback

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The extended logarithm of the actual original sum, with its true pole values. -/
def originalWeight (F : FixedChartCover n X) (ρ : F.t → ComplexModel n → ℝ)
    (u : X → EReal) (k : ℕ) : X → EReal :=
  fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (density F ρ u k x))

private theorem iInf_max_neg_nat (a : EReal) :
    (⨅ j : ℕ, max a ((-(j : ℝ) : ℝ) : EReal)) = a := by
  apply le_antisymm
  · by_contra h
    obtain ⟨b, hab, hba⟩ := EReal.exists_rat_btwn_of_lt (lt_of_not_ge h)
    obtain ⟨j, hj⟩ := exists_nat_ge (-(b : ℝ))
    have hn : ((-(j : ℝ) : ℝ) : EReal) ≤ ((b : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by linarith)
    have h := (iInf_le (fun j : ℕ => max a ((-(j : ℝ) : ℝ) : EReal)) j).trans
      (max_le hab.le hn)
    exact not_lt_of_ge h hba
  · exact le_iInf fun _ => le_max_left _ _

private theorem pshOn_pole_recovery {U : Set (ComplexModel n)}
    {q : ComplexModel n → EReal} (hU : IsOpen U) (hq : ContinuousOn q U)
    (hp : PlurisubharmonicOn q {z | z ∈ U ∧ q z ≠ ⊥}) :
    PlurisubharmonicOn q U := by
  have hj : ∀ j : ℕ, PlurisubharmonicOn
      (fun z => max (q z) ((-(j : ℝ) : ℝ) : EReal)) U := by
    intro j z hz
    by_cases hbot : q z = ⊥
    · have he := ((hq z hz).continuousAt (hU.mem_nhds hz)).eventually
        (Iio_mem_nhds (show q z < ((-(j : ℝ) : ℝ) : EReal) by
          rw [hbot]; exact EReal.bot_lt_coe _))
      apply (plurisubharmonicAt_const (((-(j : ℝ) : ℝ) : EReal)) (EReal.coe_ne_top _) z).congr
      filter_upwards [he] with y hy
      exact (max_eq_right hy.le).symm
    · exact (hp z ⟨hz, hbot⟩).max
        (plurisubharmonicAt_const (((-(j : ℝ) : ℝ) : EReal)) (EReal.coe_ne_top _) z)
  have hlim := DiscPshOn.plurisubharmonicOn_iInf_of_antitone hU
    (fun j => (hj j).discPshOn) (fun z _ a b hab => by
      apply max_le_max_left
      exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast neg_le_neg (Nat.cast_le.mpr hab)))
  simpa only [iInf_max_neg_nat] using hlim

private theorem pshOn_of_smooth_levi {U : Set (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hL : ∀ z ∈ U, ∀ v, 0 ≤ leviForm f z v) :
    PlurisubharmonicOn (fun z => (f z : EReal)) U := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hU hf hx
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp (inter_mem heq (hU.mem_nhds hx))
  have hgL : ∀ y ∈ V, ∀ v, 0 ≤ leviForm g y v := by
    intro y hy v
    have hl : f =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact (hVsub hz).1
    have h2 := (hl.iteratedFDeriv ℝ 2).eq_of_nhds
    simpa only [leviForm, realHessian, h2] using hL y (hVsub hy).2 v
  apply ((plurisubharmonicOn_of_levi_nonneg
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hV hgL) x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  exact congrArg ((↑) : ℝ → EReal) (hVsub hy).1.symm

private theorem continuousOn_scaled_log_add {U : Set (ComplexModel n)}
    {S h : ComplexModel n → ℝ} (hU : IsOpen U)
    (hS : ContinuousOn S U) (hh : ContinuousOn h U) {a : ℝ} (ha : a ≠ 0) :
    ContinuousOn (fun z => (a : EReal) * ENNReal.log (ENNReal.ofReal (S z)) + (h z : EReal)) U := by
  intro z hz
  have hl := ENNReal.continuous_log.continuousAt.comp
    (ENNReal.continuous_ofReal.continuousAt.comp ((hS z hz).continuousAt (hU.mem_nhds hz)))
  have hm : ContinuousAt (fun y : ComplexModel n =>
      (a : EReal) * ENNReal.log (ENNReal.ofReal (S y))) z := (EReal.continuousAt_mul
    (p := ((a : EReal), ENNReal.log (ENNReal.ofReal (S z))))
    (Or.inl (EReal.coe_ne_zero.mpr ha)) (Or.inl (EReal.coe_ne_zero.mpr ha))
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
      (f := fun y : ComplexModel n => ((a : EReal), ENNReal.log (ENNReal.ofReal (S y))))
      (show ContinuousAt (fun y : ComplexModel n =>
        ((a : EReal), ENNReal.log (ENNReal.ofReal (S y)))) z from continuousAt_const.prodMk hl)
  have hc := continuous_coe_real_ereal.continuousAt.comp
    ((hh z hz).continuousAt (hU.mem_nhds hz))
  exact ((EReal.continuousAt_add
    (p := ((a : EReal) * ENNReal.log (ENNReal.ofReal (S z)), (h z : EReal)))
    (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
      (f := fun y : ComplexModel n =>
        ((a : EReal) * ENNReal.log (ENNReal.ofReal (S y)), (h y : EReal)))
      (show ContinuousAt (fun y : ComplexModel n =>
        ((a : EReal) * ENNReal.log (ENNReal.ofReal (S y)), (h y : EReal))) z from
          hm.prodMk hc)).continuousWithinAt

private theorem original_bergmanWeight (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j : F.t) :
    BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z)) := by
  let B := ball (F.center j) (F.bergmanRadius j)
  let Ω := ball (F.center j) (F.potentialRadius j)
  let Ψ := correctedWeight (F.chart j) (ρ j) u
  have hBΩ : B ⊆ Ω := ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
  have hΨ : PlurisubharmonicOn Ψ Ω := F.plurisubharmonicOn_correctedWeight hρ hu.1 j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  refine ⟨isOpen_ball, DemaillyApproximation.aemeasurable_multiplierWeight_restrict
    isOpen_ball (hΨ.upperSemicontinuousOn.mono hBΩ) hkR.ne', ?_⟩
  intro z hz
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  have hcb : closedBall z (ε / 2) ⊆ B :=
    (closedBall_subset_ball (by linarith)).trans hεB
  obtain ⟨C, _, hC⟩ := hΨ.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (ε / 2)) (hcb.trans hBΩ)
  refine ⟨Real.exp (-(k * C)), Real.exp_pos _, ε / 2, by positivity, hcb, fun t ht => ?_⟩
  rw [← multiplierWeight_coe]
  exact multiplierWeight_antitone hkR.le (hC t ht)

private theorem localDensity_chartSmoothOn (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} {k : ℕ} (j : F.t)
    (hBw : BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))) :
    ChartSmoothOn n (localDensity F ρ u k j) (F.cover.V j) := by
  intro e z hz
  have hpatch := F.V_subset_chartPatch j hz.2
  have hzt : z ∈ (chartTransition e (F.chart j)).source := ⟨hz.1, hpatch.1⟩
  have hzB : chartTransition e (F.chart j) z ∈
      ball (F.center j) (F.bergmanRadius j) := hpatch.2
  have hzΩ : chartTransition e (F.chart j) z ∈
      ball (F.center j) (F.potentialRadius j) :=
    ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le hzB
  have ht := chartTransition_contDiffAt_real e (F.chart j) hzt
  have hr := ((hρ j).2.2.1.contDiffAt (isOpen_ball.mem_nhds hzΩ)).comp z ht
  have hK := ((contDiffOn_toReal_bergmanSup hBw).contDiffAt
    (isOpen_ball.mem_nhds hzB)).comp z ht
  exact (((contDiffAt_const.mul hr).exp).mul hK).contDiffWithinAt

private theorem term_nonneg (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (j : F.t) (x : X) :
    0 ≤ bumpExtend (F.cover.V j) (fun y => F.cover.χ j y * F.cover.χ j y)
      (localDensity F ρ u k j) x :=
  bumpExtend_nonneg (fun y => mul_self_nonneg (F.cover.χ j y))
    (fun _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) x

private theorem smooth_density (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} {k : ℕ}
    (hBw : ∀ j, BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))) :
    ChartSmooth (n := n) (density F ρ u k) := by
  have hterm : ∀ j : F.t, ChartSmooth (n := n)
      (bumpExtend (F.cover.V j) (fun y => F.cover.χ j y * F.cover.χ j y)
        (localDensity F ρ u k j)) := by
    intro j
    apply chartSmooth_bumpExtend (F.cover.isOpen_V j)
      (fun e => (F.cover.χ_smooth j e).mul (F.cover.χ_smooth j e))
      (localDensity_chartSmoothOn F hρ j (hBw j))
    exact tsupport_mul_subset_left.trans (F.cover.tsupport_χ_subset j)
  intro e
  exact ContDiffOn.sum fun j _ => hterm j e

private theorem core_lower (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (x : X) :
    ∃ j : F.t, x ∈ F.cover.U j ∧ localDensity F ρ u k j x ≤ density F ρ u k x := by
  classical
  obtain ⟨j, hj⟩ := F.cover.cover x
  refine ⟨j, hj, ?_⟩
  have hv := F.cover.U_subset_V j hj
  have ht := Finset.single_le_sum (fun l _ => term_nonneg F ρ u k l x)
    (Finset.mem_univ j)
  simpa only [density, bumpExtend_of_mem hv, F.cover.χ_eq_one j x hj,
    one_mul] using ht

private theorem localDensity_pos_of_finite (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j : F.t) {x : X} (hx : x ∈ F.cover.U j)
    (hux : u x ≠ ⊥) : 0 < localDensity F ρ u k j x := by
  let B := ball (F.center j) (F.bergmanRadius j)
  let Ψ := correctedWeight (F.chart j) (ρ j) u
  have hpatch := F.V_subset_chartPatch j (F.cover.U_subset_V j hx)
  have hΨ : PlurisubharmonicOn Ψ B :=
    (F.plurisubharmonicOn_correctedWeight hρ hu.1 j).mono
      (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le)
  have hfinite : Ψ ((F.chart j).val x) ≠ ⊥ := by
    simpa only [Ψ, correctedWeight, chartFunction, (F.chart j).val.left_inv hpatch.1]
      using (by
        rw [← EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hux,
          ← EReal.coe_add]
        exact EReal.coe_ne_bot _ :
          u x + (ρ j ((F.chart j).val x) : EReal) ≠ ⊥)
  let R := ‖F.center j‖ + F.bergmanRadius j + 1
  have hR : 0 < R := by dsimp [R]; linarith [norm_nonneg (F.center j), F.bergmanRadius_pos j]
  obtain ⟨C, hC, hOT⟩ := exists_one_le_mul_bergmanSup n R hR
  have hbounded : ∀ z ∈ B, ‖z‖ < R := by
    intro z hz
    have hz' : ‖z - F.center j‖ < F.bergmanRadius j := by simpa only [B, mem_ball, dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z (F.center j)
    dsimp [R]; linarith
  have hpos := (hOT B isOpen_ball (convex_ball _ _) hbounded Ψ hΨ k
    (Nat.cast_pos.mpr hk) ((F.chart j).val x) hpatch.2 hfinite).2.1
  have hpos' : 0 < bergmanSup B (fun z => multiplierWeight k (Ψ z)) ((F.chart j).val x) := by
    rw [QuantitativeRegularizationBergmanInstanceTransport.bergmanSup_congr_instance
      (inferInstance : MeasurableSpace (ComplexModel n)) inferInstance
      (borel (ComplexModel n))
      (@BorelSpace.mk (ComplexModel n) _ (borel (ComplexModel n)) rfl)]
    exact hpos
  have hBw := original_bergmanWeight F hρ hu hk j
  exact mul_pos (Real.exp_pos _) (ENNReal.toReal_pos hpos'.ne'
    (bergmanSup_ne_top hBw hpatch.2))


private theorem corrected_psh_of_margin {η : ClosedRealOneOneForm n X}
    {e : ComplexChart n X} {B : Set (ComplexModel n)} {ρ σ S : ComplexModel n → ℝ}
    (hB : IsOpen B) (hρ : ContDiffOn ℝ ∞ ρ B)
    (hσ : IsSmoothLocalPotential η.val e B σ) (hS : ContDiffOn ℝ ∞ S B)
    (hS0 : ∀ y ∈ B, 0 ≤ S y) {C0 : ℝ} {k : ℕ} (hk : 0 < k)
    (hmargin : ∀ y ∈ B, 0 < S y → ∀ v : ComplexModel n,
      -(C0 / (k : ℝ) * η.val.coeff e y ![v, Complex.I • v]) ≤
        leviForm (fun t => (k : ℝ)⁻¹ * Real.log (S t) + ρ t) y v) :
    PlurisubharmonicOn (fun y =>
      (((k : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (S y)) +
        ((ρ y + (C0 / Real.pi / (k : ℝ)) * σ y : ℝ) : EReal)) B := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkInv : 0 < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  let c : ℝ := C0 / Real.pi / (k : ℝ)
  let h : ComplexModel n → ℝ := fun y => ρ y + c * σ y
  let q : ComplexModel n → EReal := fun y =>
    (((k : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (S y)) + (h y : EReal)
  let f : ComplexModel n → ℝ := fun y => (k : ℝ)⁻¹ * Real.log (S y) + h y
  have hh : ContDiffOn ℝ ∞ h B := hρ.add (contDiffOn_const.mul hσ.2.2.1)
  have hq : ContinuousOn q B := continuousOn_scaled_log_add hB
    hS.continuousOn hh.continuousOn hkInv.ne'
  let V : Set (ComplexModel n) := {y | y ∈ B ∧ 0 < S y}
  have hV : IsOpen V := hS.continuousOn.isOpen_inter_preimage hB isOpen_Ioi
  have hf : ContDiffOn ℝ ∞ f V :=
    (contDiffOn_const.mul ((hS.mono inter_subset_left).log (fun y hy => ne_of_gt hy.2))).add
      (hh.mono inter_subset_left)
  have hL : ∀ y ∈ V, ∀ v, 0 ≤ leviForm f y v := by
    intro y hy v
    have hf0 : ContDiffAt ℝ 2 (fun t => (k : ℝ)⁻¹ * Real.log (S t) + ρ t) y :=
      ((contDiffAt_const.mul (((hS y hy.1).contDiffAt (hB.mem_nhds hy.1)).log hy.2.ne')).add
        ((hρ y hy.1).contDiffAt (hB.mem_nhds hy.1))).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hσ2 : ContDiffAt ℝ 2 σ y :=
      ((hσ.2.2.1 y hy.1).contDiffAt (hB.mem_nhds hy.1)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hLeviσ : leviForm σ y v = Real.pi * η.val.coeff e y ![v, Complex.I • v] := by
      have hdiag := smoothDDC_complexDiagonal_eq_leviForm hσ2 v
      rw [hσ.2.2.2 hy.1] at hdiag
      exact (div_eq_iff Real.pi_ne_zero).mp hdiag.symm |>.trans (mul_comm _ _)
    have heq : f = (fun t => (k : ℝ)⁻¹ * Real.log (S t) + ρ t) + c • σ := by
      funext t
      change (k : ℝ)⁻¹ * Real.log (S t) + (ρ t + c * σ t) =
        ((k : ℝ)⁻¹ * Real.log (S t) + ρ t) + c * σ t
      ring
    have hσc : ContDiffAt ℝ 2 (c • σ) y := by
      change ContDiffAt ℝ 2 (fun t => c * σ t) y
      exact contDiffAt_const.mul hσ2
    rw [heq, leviForm_add hf0 hσc v, leviForm_smul hσ2, hLeviσ]
    have hm := hmargin y hy.1 hy.2 v
    have hc : c * (Real.pi * η.val.coeff e y ![v, Complex.I • v]) =
        C0 / (k : ℝ) * η.val.coeff e y ![v, Complex.I • v] := by
      dsimp [c]
      field_simp
    rw [hc]
    linarith
  have hfp := pshOn_of_smooth_levi hV hf hL
  have hqp : PlurisubharmonicOn q {y | y ∈ B ∧ q y ≠ ⊥} := by
    intro y hy
    have hSy : 0 < S y := by
      by_contra hn
      have he : S y = 0 := le_antisymm (le_of_not_gt hn) (hS0 y hy.1)
      have hbot : q y = ⊥ := by
        dsimp [q]; rw [he, ENNReal.ofReal_zero, ENNReal.log_zero,
          EReal.coe_mul_bot_of_pos hkInv]
        simp
      exact hy.2 hbot
    apply (hfp y ⟨hy.1, hSy⟩).congr
    filter_upwards [hV.mem_nhds ⟨hy.1, hSy⟩] with t ht
    dsimp [f, q]
    rw [ENNReal.log_ofReal_of_pos ht.2, ← EReal.coe_mul, ← EReal.coe_add]
  exact pshOn_pole_recovery hB hq hqp

private theorem theta_psh_at_of_chart {η : SmoothRealForm n X 2} {w : X → EReal}
    (e ei : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ e.val.target)
    {B : Set (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hη : IsSmoothLocalPotential η ei B h)
    (hq : PlurisubharmonicOn (fun y => w (ei.val.symm y) + (h y : EReal)) B)
    (hxsource : e.val.symm z ∈ ei.val.source) (hzB : ei.val (e.val.symm z) ∈ B) :
    ∃ W h', z ∈ W ∧ IsSmoothLocalPotential η e W h' ∧
      PlurisubharmonicOn (fun y => chartFunction w e y + (h' y : EReal)) W := by
  have hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : X → X) := contMDiff_id
  let T := coordinateMap (id : X → X) e ei
  let W := potentialDomain (id : X → X) e ei B
  have hW : IsOpen W := potentialDomain_isOpen hid e ei hη.1
  have hzW : z ∈ W := ⟨⟨hz, hxsource⟩, hzB⟩
  have hpull := isSmoothLocalPotential_pullback hid e hη
  have hηe : IsSmoothLocalPotential η e W (h ∘ T) :=
    (SmoothRealForm.pullback_id_geometricallyEq η).localPotential_iff e W (h ∘ T) |>.mp hpull
  refine ⟨W, h ∘ T, hzW, hηe, ?_⟩
  have hdiff : DifferentiableOn ℂ T W :=
    ((coordinateMap_contDiffOn hid e ei).differentiableOn (by simp)).mono inter_subset_left
  intro y hy
  have hp := HolomorphicPullback.plurisubharmonicAt_comp_holomorphic hW hdiff hy (hq (T y) hy.2)
  apply hp.congr
  filter_upwards [hW.mem_nhds hy] with t ht
  change w (ei.val.symm (T t)) + (h (T t) : EReal) =
    w (e.val.symm t) + (h (T t) : EReal)
  dsimp only [T, coordinateMap, Function.comp_apply, id_eq]
  have htS : e.val.symm t ∈ ei.val.source := ht.1.2
  rw [ei.val.left_inv htS]

/-- The SAME prescribed squared sum is genuine PSH for one uniform enlarged background,
including every original kernel zero. No positive mass or nonzero-kernel certificate is an input. -/
theorem exists_uniform_original_density_theta_psh [CompactSpace X]
    (F : FixedChartCover n X) (omega : KahlerBackground n X) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ (u : X → EReal), IsThetaPshPotential θ.val u → ∀ k : ℕ, 0 < k →
        IsThetaPshPotential (θ + (C / (k : ℝ)) • omega.form).val
          (originalWeight F ρ u k) := by
  classical
  obtain ⟨C0, hC0, hmargin⟩ := exists_uniform_original_density_levi_margin F omega
  let C : ℝ := C0 / Real.pi
  have hC : 0 < C := div_pos hC0 Real.pi_pos
  obtain ⟨σ, hσ⟩ := F.exists_potentials omega.form
  refine ⟨C, hC, fun θ ρ hρ u hu k hk => ?_⟩
  have hBw := fun j => original_bergmanWeight F hρ hu hk j
  have hSs := smooth_density F hρ hBw
  have hS0 : ∀ x : X, 0 ≤ density F ρ u k x :=
    fun x => Finset.sum_nonneg fun j _ => term_nonneg F ρ u k j x
  refine ⟨?_, ?_⟩
  · intro e z hz
    let x : X := e.val.symm z
    obtain ⟨i, hxi, r, hr, htarget, hcore, hall⟩ := hmargin θ ρ hρ x
    let ei := F.chart i
    let B := ball (ei.val x) r
    have hB : IsOpen B := isOpen_ball
    have hBΩ : B ⊆ ball (F.center i) (F.potentialRadius i) := by
      intro y hy
      have hpatch := F.V_subset_chartPatch i (F.cover.U_subset_V i (hcore y hy))
      have hb : y ∈ ball (F.center i) (F.bergmanRadius i) := by
        have hb' : ei.val (ei.val.symm y) ∈ ball (F.center i) (F.bergmanRadius i) := hpatch.2
        rwa [ei.val.right_inv (htarget hy)] at hb'
      exact ball_subset_ball (F.bergmanRadius_lt_potentialRadius i).le hb
    have hρB := (hρ i).mono hB hBΩ
    have hσB := (hσ i).mono hB hBΩ
    let S : ComplexModel n → ℝ := fun y => density F ρ u k (ei.val.symm y)
    let h : ComplexModel n → ℝ := fun y => ρ i y + (C / (k : ℝ)) * σ i y
    let q : ComplexModel n → EReal := fun y =>
      (((k : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (S y)) + (h y : EReal)
    have hS : ContDiffOn ℝ ∞ S B := (hSs ei).mono htarget
    have hqB : PlurisubharmonicOn q B := corrected_psh_of_margin hB hρB.2.2.1 hσB hS
      (fun y _ => hS0 (ei.val.symm y)) hk (hall u hu k hk)
    let η : ClosedRealOneOneForm n X := θ + (C / (k : ℝ)) • omega.form
    have hη : IsSmoothLocalPotential η.val ei B h :=
      localPotential_add hρB (localPotential_smul hσB (C / (k : ℝ)))
    have hxsource : x ∈ ei.val.source := (F.V_subset_chartPatch i (F.cover.U_subset_V i hxi)).1
    exact theta_psh_at_of_chart e ei hz hη hqB hxsource (mem_ball_self hr)
  · intro x U hU hxU
    obtain ⟨y, hyU, huy⟩ := hu.2 x U hU hxU
    obtain ⟨j, hyj, hj⟩ := core_lower F ρ u k y
    have hpos : 0 < density F ρ u k y :=
      lt_of_lt_of_le (localDensity_pos_of_finite F hρ hu hk j hyj huy) hj
    refine ⟨y, hyU, ?_⟩
    dsimp [originalWeight]
    rw [ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _

end SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityThetaPsh
