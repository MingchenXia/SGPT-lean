import SGPT.Trace.OTMarginPatch
import SGPT.Trace.OTMarginHolder

/-!
# The local package at a point of the submanifold

Blueprint `claude-ot3.tex`, node `claude-ot3:local-package`.

`exists_marginPatch` combines, at a point `p ∈ W`, the extension with gain
(`exists_gainPatch`), the pole region of the normal pole `Λ` (`exists_poleRegion`) and the
comparison of measures, into intrinsic statements on `X` for sections of a holomorphic line
bundle `V` with a continuous fibre norm: neighbourhoods `p ∈ B' ⊆ K' ⊆ B ⊆ K` (`B, B'` open,
`K, K'` compact) and a holomorphic section `S` on `B` with `S = s` on `W ∩ B`,

* `∫_K |S|² e^{-cψ} e^{-aΛ} dμ < ∞` (gain, `a = codim(W)(1 - 1/N)`);
* `∫_K e^{-c'Λ} dμ < ∞` for `0 ≤ c' < codim W`;
* holomorphic sections on `O ⊆ B` vanishing on `W` are `O(e^{Λ/2})` on compact sets;
* a holomorphic section `h` on `O ⊆ B` with `∫_O |h|² e^{-codim(W) Λ} dμ < ∞` vanishes on
  `W ∩ O`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Trace.TwistedL2 SGPT.Bergman.CompactHolomorphicSectionsDraft

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V]
  [MeasurableSpace X] [BorelSpace X]

/-- The image of a ball under `ζ⁻¹` is open. -/
theorem isOpen_finv_image (F : FlatData n m X W) {r : ℝ} (hr : ball (0 : ComplexModel n) r ⊆ F.flat.target) :
    IsOpen (finv F '' ball 0 r) := by
  rw [finv_image F hr]
  exact (continuousOn_fcoord F).isOpen_inter_preimage F.isOpen_ambSource isOpen_ball

/-- **The local package** at `p ∈ W`. -/
theorem exists_marginPatch {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hk : m ≤ n) (hmn : m < n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {Λ : X → EReal} (hΛm : Measurable Λ) (hΛtop : ∀ x, Λ x ≠ ⊤) (hΛbot : ∀ x, Λ x = ⊥ → x ∈ W)
    (hΛloc : ∀ p : W, ∃ U ∈ 𝓝 p.1, ∃ C : ℝ, ∀ y ∈ U, y ∉ W →
      |(Λ y).toReal - Real.log (normalWeight n m (fcoord (FlatData.ofRegularAtDim (hW p.1 p.2)) y))| ≤ C)
    {ψ : X → EReal} (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : N ≠ 0) {s : (y : W) → V y}
    (hs : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      IsAlongMultiplierSection V (m := m) c (fun y : W => ψ y) s) (p : W) :
    ∃ (B' K' B K : Set X) (S : (x : X) → V x),
      IsOpen B' ∧ IsOpen B ∧ IsCompact K' ∧ IsCompact K ∧ p.1 ∈ B' ∧ B' ⊆ K' ∧ K' ⊆ B ∧ B ⊆ K ∧
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V S B ∧
      (∀ y : W, y.1 ∈ B → S y = s y) ∧
      (∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) * multiplierWeight c (ψ x) *
        multiplierWeight (((n - m : ℕ) : ℝ) * (1 - 1 / (N : ℝ))) (Λ x) ∂μ ≠ ⊤) ∧
      (∀ c' : ℝ, 0 ≤ c' → c' < ((n - m : ℕ) : ℝ) → ∫⁻ x in K, multiplierWeight c' (Λ x) ∂μ ≠ ⊤) ∧
      (∀ (h : (x : X) → V x) (O : Set X), IsOpen O → O ⊆ B →
        SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V h O →
        (∀ x ∈ O, x ∈ W → h x = 0) → ∀ K₀ : Set X, IsCompact K₀ → K₀ ⊆ O →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K₀, ENNReal.ofReal (‖h x‖ ^ 2) ≤ ENNReal.ofReal C * EReal.exp (Λ x)) ∧
      (∀ (h : (x : X) → V x) (O : Set X), IsOpen O → O ⊆ B →
        SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V h O →
        ∀ y ∈ O, y ∈ W →
        ∫⁻ x in O, ENNReal.ofReal (‖h x‖ ^ 2) * multiplierWeight ((n - m : ℕ) : ℝ) (Λ x) ∂μ ≠ ⊤ →
        h y = 0) := by
  set Fd := FlatData.ofRegularAtDim (hW p.1 p.2) with hFd
  set e := trivializationAt ℂ V p.1 with he
  have hreg := hW p.1 p.2
  have hpF : p.1 ∈ Fd.ambSource := FlatData.mem_ambSource_ofRegularAtDim hreg
  have hp0 : fcoord Fd p.1 = 0 := hreg.2.2.choose_spec.2.1
  obtain ⟨rp, hrp, G, S, hballt, hbase, hGd, hSform, hShol, hSagree, hgain⟩ :=
    exists_gainPatch V hk hW hψ hc hN hs p
  obtain ⟨ε₀, hε₀, hpole⟩ := exists_poleRegion hμ Fd hmn hpF hp0 hΛm hΛtop hΛbot (hΛloc p)
  set ε := min (rp / 2) ε₀ with hεdef
  have hε : 0 < ε := lt_min (by positivity) hε₀
  have hεrp : ε < rp := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨hcbt, hsub, hlip, hcrit, CΛ, hLFb⟩ := hpole ε hε (min_le_right _ _)
  set B := finv Fd '' ball 0 ε with hB
  set K := finv Fd '' closedBall 0 ε with hK
  set B' := finv Fd '' ball 0 (ε / 2) with hB'
  set K' := finv Fd '' closedBall 0 (ε / 2) with hK'
  have hbt : ball (0 : ComplexModel n) ε ⊆ Fd.flat.target := ball_subset_closedBall.trans hcbt
  have hcb2 : closedBall (0 : ComplexModel n) (ε / 2) ⊆ ball 0 ε := closedBall_subset_ball (by linarith)
  have hBo : IsOpen B := isOpen_finv_image Fd hbt
  have hB'o : IsOpen B' := isOpen_finv_image Fd ((ball_subset_closedBall.trans hcb2).trans hbt)
  have hKc : IsCompact K := (isCompact_closedBall 0 ε).image_of_continuousOn
    ((continuousOn_finv Fd).mono hcbt)
  have hK'c : IsCompact K' := (isCompact_closedBall 0 (ε / 2)).image_of_continuousOn
    ((continuousOn_finv Fd).mono (hcb2.trans hbt))
  have hpB' : p.1 ∈ B' := ⟨0, mem_ball_self (by linarith), by rw [← hp0, finv_fcoord Fd hpF]⟩
  have hBrp : B ⊆ finv Fd '' ball 0 rp := image_mono (ball_subset_ball hεrp.le)
  have hKrp : closedBall (0 : ComplexModel n) ε ⊆ ball 0 rp := closedBall_subset_ball hεrp
  have hKe : K ⊆ e.baseSet := by rintro _ ⟨z, hz, rfl⟩; exact hbase z (hKrp hz)
  -- frame bounds on `K`
  have hfc : ContinuousOn (frameNorm V e) K := (frameNorm_continuousOn V e).mono hKe
  obtain ⟨Fp, hFp⟩ := hKc.exists_bound_of_continuousOn hfc
  have hKne : K.Nonempty := ⟨p.1, ⟨0, mem_closedBall_self hε.le, by rw [← hp0, finv_fcoord Fd hpF]⟩⟩
  obtain ⟨x₀, hx₀K, hmin⟩ := hKc.exists_isMinOn hKne hfc
  set Fm := frameNorm V e x₀ with hFm
  have hFm0 : 0 < Fm := frameNorm_pos V e (hKe hx₀K)
  have hFp' : ∀ x ∈ K, frameNorm V e x ≤ |Fp| := fun x hx => by
    have := hFp x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (frameNorm_pos V e (hKe hx)).le] at this
    exact this.trans (le_abs_self _)
  have hnorm : ∀ x ∈ e.baseSet, ∀ v : V x, ‖v‖ = ‖(e ⟨x, v⟩).2‖ * frameNorm V e x := by
    intro x hx v
    rw [SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame e hx v,
      Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hx]
    rfl
  -- coefficient of a holomorphic section
  have hcoefd : ∀ (h : (x : X) → V x) (O : Set X), IsOpen O → O ⊆ B →
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V h O →
      ∀ x ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (fun y => (e ⟨y, h y⟩).2) x := by
    intro h O hO hOB hh x hx
    have hxe : x ∈ e.baseSet := hKe (subset_of_subset_of_eq hOB rfl |>.trans (image_mono
      ball_subset_closedBall) hx)
    exact (Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e h hxe).mp
      ((hh x hx).mdifferentiableAt (hO.mem_nhds hx))
  have hBK : B ⊆ K := image_mono ball_subset_closedBall
  refine ⟨B', K', B, K, S, hB'o, hBo, hK'c, hKc, hpB', image_mono ball_subset_closedBall,
    image_mono hcb2, hBK, hShol.mono hBrp, fun y hy => hSagree y (hBrp hy), ?_, hsub, ?_, ?_⟩
  · -- the gain, intrinsically
    set a : ℝ := ((n - m : ℕ) : ℝ) * (1 - 1 / (N : ℝ)) with ha
    have ha0 : 0 ≤ a := by
      have : 1 / (N : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    set B₀ := finv Fd '' ball 0 rp with hB₀
    have hB₀o : IsOpen B₀ := isOpen_finv_image Fd hballt
    set f : X → ℝ≥0∞ := fun x => B₀.indicator (fun x => ENNReal.ofReal (‖S x‖ ^ 2)) x *
      multiplierWeight c (ψ x) * multiplierWeight a (Λ x) with hf
    have hψm : Measurable ψ := hψ.upperSemicontinuous.measurable
    have hfm : Measurable f := by
      refine ((measurable_indicator_of_continuousOn' hB₀o ?_).mul
        ((multiplierWeight_antitone hc.le).measurable.comp hψm)).mul
        ((multiplierWeight_antitone ha0).measurable.comp hΛm)
      exact ENNReal.continuous_ofReal.comp_continuousOn
        ((ContinuousFiberNorm.continuous.comp_continuousOn hShol.continuousOn).pow 2)
    obtain ⟨C₀, -, hC₀⟩ := lintegral_finv_image_le Fd hμ (isCompact_closedBall 0 ε) hcbt
    have hKB₀ : K ⊆ B₀ := image_mono hKrp
    have heqK : ∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) * multiplierWeight c (ψ x) *
        multiplierWeight a (Λ x) ∂μ = ∫⁻ x in K, f x ∂μ := by
      refine setLIntegral_congr_fun hKc.isClosed.measurableSet fun x hx => ?_
      rw [hf]; simp only; rw [indicator_of_mem (hKB₀ hx)]
    rw [heqK]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) (hC₀ f hfm)
    have hbound : ∫⁻ z in closedBall (0 : ComplexModel n) ε, f (finv Fd z) ≤
        ∫⁻ z in closedBall (0 : ComplexModel n) ε, ENNReal.ofReal (|Fp| ^ 2 * Real.exp (a * CΛ)) *
          (ENNReal.ofReal (‖G z‖ ^ 2) * multiplierWeight c (ψ (finv Fd z)) *
            ENNReal.ofReal (normalWeight n m z ^ (-a))) := by
      refine setLIntegral_mono_ae' measurableSet_closedBall ?_
      filter_upwards [ae_normalWeight_pos (m := m) hmn] with z hzpos hz
      have hzpl : z ∉ complexCoordinatePlane n m := fun h =>
        hzpos.ne' ((normalWeight_eq_zero_iff z).mpr h)
      have hxK : finv Fd z ∈ K := ⟨z, hz, rfl⟩
      have hxB₀ : finv Fd z ∈ B₀ := ⟨z, hKrp hz, rfl⟩
      rw [hf]; simp only; rw [indicator_of_mem hxB₀]
      have hSz : ‖S (finv Fd z)‖ ≤ ‖G z‖ * |Fp| := by
        rw [hSform _ hxB₀, fcoord_finv Fd (hcbt hz), hnorm _ (hKe hxK),
          e.apply_mk_symm (hKe hxK)]
        exact mul_le_mul_of_nonneg_left (hFp' _ hxK) (norm_nonneg _)
      have hΛz := hLFb a ha0 z hz hzpl
      calc ENNReal.ofReal (‖S (finv Fd z)‖ ^ 2) * multiplierWeight c (ψ (finv Fd z)) *
            multiplierWeight a (Λ (finv Fd z))
          ≤ ENNReal.ofReal ((‖G z‖ * |Fp|) ^ 2) * multiplierWeight c (ψ (finv Fd z)) *
            (ENNReal.ofReal (Real.exp (a * CΛ)) * ENNReal.ofReal (normalWeight n m z ^ (-a))) := by
            gcongr
      _ = _ := by
            rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]
            ring
    refine ne_top_of_le_ne_top ?_ hbound
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgain ε hε hεrp)
  · -- the Lipschitz bound
    intro h O hO hOB hh hhW K₀ hK₀ hK₀O
    have hgW : ∀ x ∈ O, x ∈ W → (e ⟨x, h x⟩).2 = 0 := by
      intro x hx hxW
      rw [hhW x hx hxW]
      have hxe : x ∈ e.baseSet := hKe (hBK (hOB hx))
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hxe, map_zero]
    obtain ⟨C, hC0, hC⟩ := hlip (fun y => (e ⟨y, h y⟩).2) O hO (hcoefd h O hO hOB hh) hgW K₀ hK₀
      (fun x hx => ⟨hK₀O hx, hBK (hOB (hK₀O hx))⟩)
    refine ⟨|Fp| ^ 2 * C, by positivity, fun x hx => ?_⟩
    have hxK : x ∈ K := hBK (hOB (hK₀O hx))
    rw [hnorm x (hKe hxK), mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul
      (sq_nonneg _), mul_comm (ENNReal.ofReal (‖(e ⟨x, h x⟩).2‖ ^ 2)), mul_assoc]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
      (hFp' x hxK) 2)) (hC x hx)
  · -- vanishing
    intro h O hO hOB hh y hyO hyW hint
    have hcoef0 : (e ⟨y, h y⟩).2 = 0 := by
      refine hcrit (fun y => (e ⟨y, h y⟩).2) O hO (hcoefd h O hO hOB hh) y hyO hyW (hOB hyO) ?_
      have hOK : O ∩ finv Fd '' closedBall 0 ε = O := inter_eq_left.mpr (hOB.trans hBK)
      rw [hOK]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (Fm ^ 2)⁻¹))
        hint) ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hO.measurableSet fun x hx => ?_
      have hxK : x ∈ K := hBK (hOB hx)
      have hFx : Fm ≤ frameNorm V e x := hmin hxK
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      rw [hnorm x (hKe hxK), mul_pow]
      have hF2 : Fm ^ 2 ≤ frameNorm V e x ^ 2 := pow_le_pow_left₀ hFm0.le hFx 2
      have hFm2 : 0 < Fm ^ 2 := by positivity
      calc ‖(e ⟨x, h x⟩).2‖ ^ 2 = (Fm ^ 2)⁻¹ * (Fm ^ 2 * ‖(e ⟨x, h x⟩).2‖ ^ 2) := by
            field_simp
        _ ≤ (Fm ^ 2)⁻¹ * (‖(e ⟨x, h x⟩).2‖ ^ 2 * frameNorm V e x ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [sq_nonneg ‖(e ⟨x, h x⟩).2‖]
    have hye : y ∈ e.baseSet := hKe (hBK (hOB hyO))
    rw [SGPT.PSH.GlobalL2.trivialization_eq_coef_smul_frame e hye (h y),
      Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hye]
    simp only [hcoef0, zero_smul]

/-! ### Submanifolds of full dimension -/

section FullDim


/-- The gain patch without pole, intrinsically: a smooth local extension with
`∫_K |S|² e^{-cψ} < ∞`. -/
theorem exists_gainPatch_intrinsic {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {m : ℕ} {W : Set X} (hk : m ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {ψ : X → EReal} (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) {c : ℝ} (hc : 0 < c)
    {s : (y : W) → V y}
    (hs : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      IsAlongMultiplierSection V (m := m) c (fun y : W => ψ y) s) (p : W) :
    ∃ (B' K B : Set X) (S : (x : X) → V x), IsOpen B' ∧ IsOpen B ∧ IsCompact K ∧ p.1 ∈ B' ∧
      B' ⊆ K ∧ K ⊆ B ∧
      (∀ x ∈ B, ContMDiffAt 𝓘(ℂ, ComplexModel n) (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (S x)) x) ∧
      (∀ y : W, y.1 ∈ B → S y = s y) ∧
      ∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) * multiplierWeight c (ψ x) ∂μ ≠ ⊤ := by
  set Fd := FlatData.ofRegularAtDim (hW p.1 p.2) with hFd
  set e := trivializationAt ℂ V p.1 with he
  have hreg := hW p.1 p.2
  have hpF : p.1 ∈ Fd.ambSource := FlatData.mem_ambSource_ofRegularAtDim hreg
  have hp0 : fcoord Fd p.1 = 0 := hreg.2.2.choose_spec.2.1
  obtain ⟨rp, hrp, G, S, hballt, hbase, hGd, hSform, hShol, hSagree, hgain⟩ :=
    exists_gainPatch V hk hW hψ hc (N := 1) one_ne_zero hs p
  set ε := rp / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεrp : ε < rp := by linarith
  have hcb : closedBall (0 : ComplexModel n) ε ⊆ ball 0 rp := closedBall_subset_ball hεrp
  set B := finv Fd '' ball 0 rp
  set K := finv Fd '' closedBall 0 ε
  set B' := finv Fd '' ball 0 ε
  have hBo : IsOpen B := isOpen_finv_image Fd hballt
  have hB'o : IsOpen B' := isOpen_finv_image Fd ((ball_subset_closedBall.trans hcb).trans hballt)
  have hKc : IsCompact K := (isCompact_closedBall 0 ε).image_of_continuousOn
    ((continuousOn_finv Fd).mono (hcb.trans hballt))
  have hKe : K ⊆ e.baseSet := by rintro _ ⟨z, hz, rfl⟩; exact hbase z (hcb hz)
  have hfc : ContinuousOn (frameNorm V e) K := (frameNorm_continuousOn V e).mono hKe
  obtain ⟨Fp, hFp⟩ := hKc.exists_bound_of_continuousOn hfc
  refine ⟨B', K, B, S, hB'o, hBo, hKc, ⟨0, mem_ball_self hε, by rw [← hp0, finv_fcoord Fd hpF]⟩,
    image_mono ball_subset_closedBall, image_mono hcb, fun x hx => ?_, hSagree, ?_⟩
  · -- smoothness
    obtain ⟨z, hz, rfl⟩ := hx
    have hzt := hballt hz
    have hxe := hbase z hz
    rw [Trivialization.contMDiffAt_section_iff e hxe]
    have hG' : ContDiffAt ℂ ∞ G (fcoord Fd (finv Fd z)) := by
      rw [fcoord_finv Fd hzt]
      exact contDiffAt_of_differentiableOn_complex hGd isOpen_ball hz
    have hxa := finv_mem Fd hzt
    have hco : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fcoord Fd) (finv Fd z) := by
      have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Fd.amb.val (finv Fd z) :=
        contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas Fd.amb.property) hxa.1
      have h2 : ContDiffAt ℂ ∞ Fd.flat (Fd.amb.val (finv Fd z)) :=
        contDiffAt_of_differentiableOn_complex Fd.differentiableOn_flat Fd.flat.open_source hxa.2
      exact h2.contMDiffAt.comp _ h1
    refine (hG'.contMDiffAt.comp _ hco).congr_of_eventuallyEq ?_
    filter_upwards [hBo.mem_nhds ⟨z, hz, rfl⟩, e.open_baseSet.mem_nhds hxe] with y hy hye
    rw [hSform y hy, e.apply_mk_symm hye]
    rfl
  · -- the gain
    have hψm : Measurable ψ := hψ.upperSemicontinuous.measurable
    set f : X → ℝ≥0∞ := fun x => B.indicator (fun x => ENNReal.ofReal (‖S x‖ ^ 2)) x *
      multiplierWeight c (ψ x) with hf
    have hfm : Measurable f :=
      (measurable_indicator_of_continuousOn' hBo (ENNReal.continuous_ofReal.comp_continuousOn
        ((ContinuousFiberNorm.continuous.comp_continuousOn hShol.continuousOn).pow 2))).mul
        ((multiplierWeight_antitone hc.le).measurable.comp hψm)
    obtain ⟨C₀, -, hC₀⟩ := lintegral_finv_image_le Fd hμ (isCompact_closedBall 0 ε)
      (hcb.trans hballt)
    have heqK : ∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) * multiplierWeight c (ψ x) ∂μ =
        ∫⁻ x in K, f x ∂μ := by
      refine setLIntegral_congr_fun hKc.isClosed.measurableSet fun x hx => ?_
      rw [hf]; simp only; rw [indicator_of_mem (image_mono hcb hx)]
    rw [heqK]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C₀))
      (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := |Fp| ^ 2)) (hgain ε hε hεrp))) ?_
    refine (hC₀ f hfm).trans (mul_le_mul' le_rfl ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_closedBall fun z hz => ?_
    have hxK : finv Fd z ∈ K := ⟨z, hz, rfl⟩
    rw [hf]; simp only
    rw [indicator_of_mem (show finv Fd z ∈ B from ⟨z, hcb hz, rfl⟩)]
    have hSz : ‖S (finv Fd z)‖ ≤ ‖G z‖ * |Fp| := by
      rw [hSform _ ⟨z, hcb hz, rfl⟩, fcoord_finv Fd (hballt (hcb hz)),
        SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame e (hKe hxK),
        Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e (hKe hxK)]
      refine mul_le_mul (le_of_eq ?_) ?_ (norm_nonneg _) (norm_nonneg _)
      · show ‖(e ⟨_, e.symm _ (G z)⟩).2‖ = ‖G z‖
        rw [e.apply_mk_symm (hKe hxK)]
      · have := hFp _ hxK
        rw [Real.norm_eq_abs, abs_of_nonneg (frameNorm_pos V e (hKe hxK)).le] at this
        exact this.trans (le_abs_self _)
    have hnw : normalWeight n m z ^ (-(((n - m : ℕ) : ℝ) * (1 - 1 / ((1 : ℕ) : ℝ)))) = 1 := by
      norm_num
    rw [hnw, ENNReal.ofReal_one, mul_one]
    calc ENNReal.ofReal (‖S (finv Fd z)‖ ^ 2) * multiplierWeight c (ψ (finv Fd z))
        ≤ ENNReal.ofReal ((‖G z‖ * |Fp|) ^ 2) * multiplierWeight c (ψ (finv Fd z)) := by gcongr
      _ = _ := by rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]; ring

end FullDim

end SGPT.Trace.OTMargin
