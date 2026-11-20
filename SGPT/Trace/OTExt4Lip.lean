import SGPT.Trace.OTExt4Datum
import SGPT.Trace.OTExt4Pole

/-!
# The `∂̄`-density of the glued section vanishes to first order along the submanifold

Blueprint `claude-ot-ext4.tex`, node `claude-ot-ext4:lip`.  Xia, *Foundations of
pluripotential theory*, q07, proof of `lem:critical-gain-initial-gluing`, last paragraph:
"`γ = |∂̄G|²` vanishes on `Y`, hence `γ ≤ C|w|²` in normal coordinates near each point of `Y`,
hence `γ ≤ C R_Y` near `Y`".

For local holomorphic sections `F_a` on `U_a` which agree on `W`, the density
`D_G = N² M ∑_{a,b} 1_{tsupp η_a ∩ tsupp η_b} |F_a - F_b|²` of `dbar_glued_le` satisfies
`D_G ≤ C R` on `X` (`exists_gluedDensity_le`): near `p ∈ W` the frame coefficient of
`F_a - F_b` is holomorphic and vanishes on `W`, so it is `O(R)` by the pole region of the normal
pole (`poleRegion_logPole`, clause `lip`); away from `W`, `R` is bounded below and `D_G` is
bounded.  Also: `D_G` is measurable, and `|G|² ≤ N S`, `D_G ≤ 4 N³ M S` for
`S = ∑_a 1_{tsupp η_a} |F_a|²` (`norm_glued_sq_le`, `gluedDensity_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OTMargin
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)

/-- The indicator of a closed set of a real function continuous on an open neighbourhood is
measurable. -/
theorem measurable_indicator_closed_real {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {O K : Set Y} (hO : IsOpen O) (hK : IsClosed K) (hKO : K ⊆ O)
    {f : Y → ℝ} (hf : ContinuousOn f O) : Measurable (K.indicator f) := by
  classical
  have h1 : Measurable (O.indicator f) := by
    rw [← Set.piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise hf continuousOn_const hO.measurableSet
  have h2 : K.indicator f = K.indicator (O.indicator f) := by
    funext x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem (hKO hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [h2]
  exact h1.indicator hK.measurableSet

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X} (V : HermitianHolomorphicLineBundle.{0, 0} n X)
  {ι : Type} [Fintype ι] {η : ι → X → ℝ} {U : ι → Set X} {F : ι → (x : X) → V.Fiber x}

theorem extSec_of_mem {U' : Set X} {F' : (x : X) → V.Fiber x} {x : X} (hx : x ∈ U') :
    extSec V U' F' x = F' x := by
  classical
  simp only [extSec, if_pos hx]

theorem glued_apply (x : X) : glued V η U F x = ∑ i, (η i x : ℂ) • extSec V (U i) (F i) x := rfl

/-- The norm of the extended section is continuous on its domain. -/
theorem continuousOn_norm_extSec {U' : Set X} {F' : (x : X) → V.Fiber x}
    (hF' : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber F' U') :
    ContinuousOn (fun x => ‖extSec V U' F' x‖) U' :=
  (ContinuousFiberNorm.continuous.comp_continuousOn hF'.continuousOn).congr fun x hx => by
    simp only [Function.comp_apply, extSec_of_mem V hx]

theorem continuousOn_norm_sub_extSec {U₁ U₂ : Set X} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {F₁ F₂ : (x : X) → V.Fiber x}
    (hF₁ : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber F₁ U₁)
    (hF₂ : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber F₂ U₂) :
    ContinuousOn (fun x => ‖extSec V U₁ F₁ x - extSec V U₂ F₂ x‖) (U₁ ∩ U₂) := by
  have h := isHolomorphicSectionOn_sub V.Fiber (hU₁.inter hU₂) (hF₁.mono inter_subset_left)
    (hF₂.mono inter_subset_right)
  refine (ContinuousFiberNorm.continuous.comp_continuousOn h.continuousOn).congr fun x hx => ?_
  simp only [Function.comp_apply, extSec_of_mem V hx.1, extSec_of_mem V hx.2]

variable [MeasurableSpace X] [BorelSpace X]

/-- The density `D_G` is measurable. -/
theorem measurable_gluedDensity (hU : ∀ i, IsOpen (U i)) (hηU : ∀ i, tsupport (η i) ⊆ U i)
    (hF : ∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber (F i) (U i))
    (M : ℝ) : Measurable (gluedDensity V M η U F) := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _
    fun b _ => ?_) _
  exact measurable_indicator_closed_real ((hU a).inter (hU b))
    ((isClosed_tsupport _).inter (isClosed_tsupport _))
    (inter_subset_inter (hηU a) (hηU b))
    ((continuousOn_norm_sub_extSec V (hU a) (hU b) (hF a) (hF b)).pow 2)

theorem gluedDensity_nonneg {M : ℝ} (hM : 0 ≤ M) (x : X) : 0 ≤ gluedDensity V M η U F x := by
  unfold gluedDensity
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_)
  exact indicator_nonneg (fun _ _ => by positivity) _

/-- `|G|² ≤ N ∑_a 1_{tsupp η_a} |F_a|²`. -/
theorem norm_glued_sq_le (hη0 : ∀ i x, 0 ≤ η i x) (hη1 : ∀ x, ∑ i, η i x = 1) (x : X) :
    ‖glued V η U F x‖ ^ 2 ≤ (Fintype.card ι : ℝ) *
      ∑ i, (tsupport (η i)).indicator (fun x => ‖extSec V (U i) (F i) x‖ ^ 2) x := by
  rw [glued_apply]
  refine (norm_sum_sq_le_card _).trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h := sq_le_indicator_tsupport (hη0 i) (fun y => SGPT.Trace.OTMargin.χ_le_one' hη0 hη1 i y) x
  by_cases hx : x ∈ tsupport (η i)
  · rw [indicator_of_mem hx] at h ⊢
    nlinarith [sq_nonneg ‖extSec V (U i) (F i) x‖]
  · rw [indicator_of_notMem hx] at h ⊢
    nlinarith [sq_nonneg (η i x), sq_nonneg ‖extSec V (U i) (F i) x‖]

/-- `D_G ≤ 4 N³ M ∑_a 1_{tsupp η_a} |F_a|²`. -/
theorem gluedDensity_le {M : ℝ} (hM : 0 ≤ M) (x : X) :
    gluedDensity V M η U F x ≤ 4 * (Fintype.card ι : ℝ) ^ 3 * M *
      ∑ i, (tsupport (η i)).indicator (fun x => ‖extSec V (U i) (F i) x‖ ^ 2) x := by
  set S : ι → ℝ := fun i => (tsupport (η i)).indicator (fun x => ‖extSec V (U i) (F i) x‖ ^ 2) x
  have hS0 : ∀ i, 0 ≤ S i := fun i => indicator_nonneg (fun _ _ => by positivity) _
  have hpair : ∀ a b, (tsupport (η a) ∩ tsupport (η b)).indicator
      (fun x => ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2) x ≤ 2 * S a + 2 * S b := by
    intro a b
    by_cases hx : x ∈ tsupport (η a) ∩ tsupport (η b)
    · rw [indicator_of_mem hx]
      have ha : S a = ‖extSec V (U a) (F a) x‖ ^ 2 := indicator_of_mem hx.1 _
      have hb : S b = ‖extSec V (U b) (F b) x‖ ^ 2 := indicator_of_mem hx.2 _
      rw [ha, hb]
      have h1 := norm_sub_le (extSec V (U a) (F a) x) (extSec V (U b) (F b) x)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖extSec V (U a) (F a) x‖ - ‖extSec V (U b) (F b) x‖)]
    · rw [indicator_of_notMem hx]; linarith [hS0 a, hS0 b]
  unfold gluedDensity
  have hsum : ∑ a, ∑ b, (tsupport (η a) ∩ tsupport (η b)).indicator
      (fun x => ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2) x ≤
      4 * (Fintype.card ι : ℝ) * ∑ i, S i := by
    calc _ ≤ ∑ a, ∑ b, (2 * S a + 2 * S b) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpair a b
      _ = 4 * (Fintype.card ι : ℝ) * ∑ i, S i := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum]
          ring
  calc (Fintype.card ι : ℝ) ^ 2 * M * _ ≤ (Fintype.card ι : ℝ) ^ 2 * M *
        (4 * (Fintype.card ι : ℝ) * ∑ i, S i) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- **`D_G = O(R)`** on `X`, for local holomorphic sections which agree on `W`. -/
theorem exists_gluedDensity_le [CompactSpace X] {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    (hWc : IsCompact W) (hmn : m < n) {ωb : KahlerBackground n X} {R : X → ℝ}
    (hR : IsGlobalNormalPole ωb W R) (hU : ∀ i, IsOpen (U i)) (hηU : ∀ i, tsupport (η i) ⊆ U i)
    (hF : ∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber (F i) (U i))
    (hagr : ∀ a b, ∀ x ∈ W, x ∈ U a → x ∈ U b → F a x = F b x) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, gluedDensity V M η U F x ≤ C * R x := by
  -- Step 1: near every point of `W`
  have hloc : ∀ p : W, ∃ ε : ℝ, 0 < ε ∧
      closedBall (0 : ComplexModel n) ε ⊆ (FlatData.ofRegularAtDim (hW p.1 p.2)).flat.target ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' closedBall 0 ε,
        gluedDensity V M η U F x ≤ C * R x := by
    intro p
    set Fd := FlatData.ofRegularAtDim (hW p.1 p.2)
    set e := trivializationAt ℂ V.Fiber p.1
    have hpF := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
    have hp0 : fcoord Fd p.1 = 0 := (hW p.1 p.2).2.2.choose_spec.2.1
    have h0t : (0 : ComplexModel n) ∈ Fd.flat.target := by rw [← hp0]; exact fcoord_mem Fd hpF
    have hfinv0 : finv Fd 0 = p.1 := by rw [← hp0, finv_fcoord Fd hpF]
    obtain ⟨ε₀, hε₀, hreg⟩ := poleRegion_logPole hμ hW hmn hR p
    have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), finv Fd z ∈ e.baseSet :=
      ((continuousOn_finv Fd).continuousAt (Fd.flat.open_target.mem_nhds h0t)).eventually
        (by rw [hfinv0]; exact e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ V.Fiber p.1))
    obtain ⟨ε₁, hε₁, hε₁s⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set ε := min ε₀ (ε₁ / 2) with hεdef
    have hε : 0 < ε := lt_min hε₀ (by positivity)
    obtain ⟨hct, -, hlip⟩ := hreg ε hε (min_le_left _ _)
    set Kp := finv Fd '' closedBall 0 ε with hKp
    have hKpc : IsCompact Kp := (isCompact_closedBall 0 ε).image_of_continuousOn
      ((continuousOn_finv Fd).mono hct)
    have hKpe : Kp ⊆ e.baseSet := by
      rintro _ ⟨z, hz, rfl⟩
      exact hε₁s z (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt
        ((min_le_right _ _).trans_lt (by linarith))))
    obtain ⟨Fb, hFb⟩ := hKpc.exists_bound_of_continuousOn ((frameNorm_continuousOn V.Fiber e).mono hKpe)
    -- the pairwise bounds
    have hpairs : ∀ a b, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Kp, (tsupport (η a) ∩ tsupport (η b)).indicator
        (fun x => ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2) x ≤ C * R x := by
      intro a b
      set O := U a ∩ U b ∩ e.baseSet with hO
      have hOo : IsOpen O := ((hU a).inter (hU b)).inter e.open_baseSet
      set g : X → ℂ := fun x => (e ⟨x, F a x - F b x⟩).2 with hg
      have hsub := isHolomorphicSectionOn_sub V.Fiber ((hU a).inter (hU b))
        ((hF a).mono inter_subset_left) ((hF b).mono inter_subset_right)
      have hgd : ∀ x ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x := fun x hx =>
        (Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e _ hx.2).mp
          ((hsub x hx.1).mdifferentiableAt (((hU a).inter (hU b)).mem_nhds hx.1))
      have hg0 : ∀ x ∈ O, x ∈ W → g x = 0 := fun x hx hxW => by
        show (e ⟨x, F a x - F b x⟩).2 = 0
        rw [hagr a b x hxW hx.1.1 hx.1.2, sub_self,
          ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hx.2, map_zero]
      set Kab := tsupport (η a) ∩ tsupport (η b) ∩ Kp with hKab
      have hKabc : IsCompact Kab := hKpc.inter_left
        ((isClosed_tsupport _).inter (isClosed_tsupport _))
      have hKabO : Kab ⊆ O ∩ finv Fd '' closedBall 0 ε := fun x hx =>
        ⟨⟨⟨hηU a hx.1.1, hηU b hx.1.2⟩, hKpe hx.2⟩, hx.2⟩
      obtain ⟨C, hC0, hC⟩ := hlip g O hOo hgd hg0 Kab hKabc hKabO
      refine ⟨C * Fb ^ 2, by positivity, fun x hxK => ?_⟩
      by_cases hx : x ∈ tsupport (η a) ∩ tsupport (η b)
      · rw [indicator_of_mem hx, extSec_of_mem V (hηU a hx.1), extSec_of_mem V (hηU b hx.2)]
        have hxe := hKpe hxK
        have hn : ‖F a x - F b x‖ = ‖g x‖ * ‖e.symm x 1‖ := by
          rw [SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame e hxe,
            Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hxe]
        have hgx := hC x ⟨hx, hxK⟩
        rw [← ENNReal.ofReal_mul hC0, ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg hC0 (hR.nonneg x))] at hgx
        have hfr : ‖e.symm x 1‖ ≤ Fb := by
          have := hFb x hxK
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
        rw [hn, mul_pow]
        calc ‖g x‖ ^ 2 * ‖e.symm x 1‖ ^ 2 ≤ (C * R x) * Fb ^ 2 :=
              mul_le_mul hgx (pow_le_pow_left₀ (norm_nonneg _) hfr 2) (sq_nonneg _)
                (mul_nonneg hC0 (hR.nonneg x))
          _ = C * Fb ^ 2 * R x := by ring
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (by positivity) (hR.nonneg x)
    choose C hC0 hC using hpairs
    refine ⟨ε, hε, hct, (Fintype.card ι : ℝ) ^ 2 * M * ∑ a, ∑ b, C a b,
      mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hC0 a b),
      fun x hx => ?_⟩
    unfold gluedDensity
    rw [mul_assoc _ (∑ a, ∑ b, C a b), Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by positivity)
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun b _ => hC a b x hx
  -- Step 2: a finite cover of `W`, and the bound off the cover
  choose ε hε hct C hC0 hC using hloc
  set A : W → Set X := fun p => finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' ball 0 (ε p)
  have hAo : ∀ p, IsOpen (A p) := fun p => isOpen_finv_image _ (ball_subset_closedBall.trans (hct p))
  have hpA : ∀ p : W, p.1 ∈ A p := by
    intro p
    have hpF := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
    have hp0 : fcoord (FlatData.ofRegularAtDim (hW p.1 p.2)) p.1 = 0 :=
      (hW p.1 p.2).2.2.choose_spec.2.1
    exact ⟨0, mem_ball_self (hε p), by rw [← hp0, finv_fcoord _ hpF]⟩
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover A hAo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hpA ⟨x, hx⟩⟩)
  have hNo : IsOpen (⋃ p ∈ t, A p) := isOpen_biUnion fun p _ => hAo p
  obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_off hR.continuous (fun x hx => hR.pos_of_notMem hx)
    hNo ht
  -- `D_G` is bounded
  have hbd : ∀ a b, ∃ B : ℝ, ∀ x, (tsupport (η a) ∩ tsupport (η b)).indicator
      (fun x => ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2) x ≤ B := by
    intro a b
    have hK : IsCompact (tsupport (η a) ∩ tsupport (η b)) :=
      ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      (((continuousOn_norm_sub_extSec V (hU a) (hU b) (hF a) (hF b)).pow 2).mono
        (inter_subset_inter (hηU a) (hηU b)))
    refine ⟨max B 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport (η a) ∩ tsupport (η b)
    · rw [indicator_of_mem hx]
      have := hB x hx
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    · rw [indicator_of_notMem hx]; exact le_max_right _ _
  choose B hB using hbd
  set Dmax : ℝ := (Fintype.card ι : ℝ) ^ 2 * M * ∑ a, ∑ b, max (B a b) 0 with hDmax
  have hDmax0 : 0 ≤ Dmax :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => le_max_right _ _)
  have hDle : ∀ x, gluedDensity V M η U F x ≤ Dmax := fun x => by
    unfold gluedDensity
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      (hB a b x).trans (le_max_left _ _)) (by positivity)
  refine ⟨∑ p ∈ t, C p + Dmax / r₀, add_nonneg (Finset.sum_nonneg fun p _ => hC0 p) (by positivity),
    fun x => ?_⟩
  have hRx := hR.nonneg x
  have hsum0 : 0 ≤ ∑ p ∈ t, C p := Finset.sum_nonneg fun p _ => hC0 p
  by_cases hx : x ∈ ⋃ p ∈ t, A p
  · obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp hx
    have h1 := hC p x (image_mono ball_subset_closedBall hxp)
    have h2 : C p ≤ ∑ p ∈ t, C p := Finset.single_le_sum (fun p _ => hC0 p) hpt
    have h3 : 0 ≤ Dmax / r₀ * R x := by positivity
    nlinarith
  · have hr := hr₀le x hx
    have h1 : Dmax ≤ Dmax / r₀ * R x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr₀]
      exact mul_le_mul_of_nonneg_left hr hDmax0
    nlinarith [hDle x]

end SGPT.Trace.OTExt4
