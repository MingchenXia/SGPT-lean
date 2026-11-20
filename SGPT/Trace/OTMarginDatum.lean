import SGPT.PSH.GlobalL2Correction

/-!
# Gluing finitely many local holomorphic sections: smoothness and `∂̄`-energy

Blueprint `claude-ot3.tex`, node `claude-ot3:datum`.

Let `(χ_a)` be a chart-smooth partition of unity on `X` and `sec_a` sections of `L^k ⊗ T`
holomorphic on open sets `U_a ⊇ tsupp χ_a`.  For the gluing system `G` of cover data `D`
(`CoverData.toGluingSystem`), the datum `v₀ = ∑_a χ_a sec_a` is smooth for `G`
(`isSmooth_datum`), and since `∑_a ∂̄χ_a = 0` and `∑_b χ_b = 1`,

  `∂̄ v₀ = ∑_{a,b} χ_b ∂̄χ_a (sec_a - sec_b)`,

so its `∂̄`-energy in every chart is bounded by the weighted `L²` norms of the differences
`sec_a - sec_b` over `tsupp χ_a ∩ tsupp χ_b` (`energy_datum_le`).  This is the general-datum input
of `GluingSystem.exists_correction` used for the extension along a submanifold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2

theorem sq_norm_double_sum_le {κ : Type} [Fintype κ] (x : κ → κ → ℂ) :
    ‖∑ a, ∑ b, x a b‖ ^ 2 ≤ (Fintype.card κ : ℝ) ^ 2 * ∑ a, ∑ b, ‖x a b‖ ^ 2 := by
  have h1 := GluingSystem.norm_sum_sq_le_card_mul (fun a => ∑ b, x a b)
  have h2 : ∀ a, ‖∑ b, x a b‖ ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ b, ‖x a b‖ ^ 2 := fun a =>
    GluingSystem.norm_sum_sq_le_card_mul (x a)
  calc ‖∑ a, ∑ b, x a b‖ ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ a, ‖∑ b, x a b‖ ^ 2 := h1
    _ ≤ (Fintype.card κ : ℝ) * ∑ a, (Fintype.card κ : ℝ) * ∑ b, ‖x a b‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h2 a) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem χ_le_one' {X ι : Type*} [Fintype ι] {χ : ι → X → ℝ} (hχ0 : ∀ a x, 0 ≤ χ a x)
    (hχ1 : ∀ x, ∑ a, χ a x = 1) (a : ι) (x : X) : χ a x ≤ 1 := by
  have : χ a x ≤ ∑ b, χ b x :=
    Finset.single_le_sum (f := fun b => χ b x) (fun b _ => hχ0 b x) (Finset.mem_univ a)
  linarith [hχ1 x]

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
  {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)
  (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
  {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
  (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
  {ι : Type} [Fintype ι] {χ : ι → X → ℝ} (hχ : ∀ a, ChartSmooth (n := n) (χ a))
  (hχ0 : ∀ a x, 0 ≤ χ a x) (hχ1 : ∀ x, ∑ a, χ a x = 1)
  {U : ι → Set X} (hU : ∀ a, IsOpen (U a)) (hχU : ∀ a, tsupport (χ a) ⊆ U a)
  {sec : ι → (x : X) → (twistedPower L T k).Fiber x}
  (hsec : ∀ a, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n)
    (twistedPower L T k).Fiber (sec a) (U a))

/-- The glued datum `∑_a χ_a sec_a`. -/
def gluedDatum (χ : ι → X → ℝ) (sec : ι → (x : X) → (twistedPower L T k).Fiber x) :
    (x : X) → (twistedPower L T k).Fiber x :=
  fun x => ∑ a, ((χ a x : ℝ) : ℂ) • sec a x

theorem isOpen_ball_inter_preimage (l : Fin D.m) {O : Set X} (hO : IsOpen O) :
    IsOpen (ball (ctr (n := n) (D.pt l)) (D.R l) ∩ (D.chartA l).val.symm ⁻¹' O) := by
  have := (D.chartA l).val.isOpen_inter_preimage_symm hO
  have heq : ball (ctr (n := n) (D.pt l)) (D.R l) ∩ (D.chartA l).val.symm ⁻¹' O =
      ball (ctr (n := n) (D.pt l)) (D.R l) ∩ ((D.chartA l).val.target ∩ (D.chartA l).val.symm ⁻¹' O) := by
    ext y; simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun h => ⟨h.1, D.ball_subset_target l h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [heq]; exact isOpen_ball.inter this

include hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec

/-- The coefficient of `sec_a` in chart `l` is holomorphic over `U_a`. -/
theorem differentiableOn_locCoef_sec (a : ι) (l : Fin D.m) :
    DifferentiableOn ℂ ((D.toGluingSystem hL hT hk hφ).locCoef l (sec a))
      (ball (ctr (n := n) (D.pt l)) (D.R l) ∩ (D.chartA l).val.symm ⁻¹' U a) := by
  refine (differentiableOn_coord_of_holomorphicSectionOn (D.frameE k l).val (D.chartA l) (hU a)
    (hsec a)).mono fun z hz => ⟨D.ball_subset_target l hz.1, hz.2, ?_⟩
  have hs : (D.chartA l).val.symm z ∈ (D.chartA l).val.source :=
    (D.chartA l).val.map_target (D.ball_subset_target l hz.1)
  exact D.mem_frameE_baseSet hs (by rw [(D.chartA l).val.right_inv (D.ball_subset_target l hz.1)]; exact hz.1)

omit hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec in
/-- The real function `χ ∘ z_l⁻¹`, as a complex function, vanishes near points outside the
topological support. -/
theorem eventually_χ_eq_zero {c : ComplexChart n X} {χ' : X → ℝ} {z : ComplexModel n}
    (hz : z ∈ c.val.target) (hns : c.val.symm z ∉ tsupport χ') :
    ∀ᶠ y in 𝓝 z, ((χ' (c.val.symm y) : ℝ) : ℂ) = 0 := by
  have h1 : ∀ᶠ y in 𝓝 z, χ' (c.val.symm y) = 0 :=
    (c.val.continuousAt_symm hz).eventually (notMem_tsupport_iff_eventuallyEq.mp hns)
  filter_upwards [h1] with y hy; rw [hy, Complex.ofReal_zero]

/-- Each term `χ_a sec_a` has smooth coefficients, and its `∂̄` is `∂̄χ_a · sec_a`. -/
theorem term_spec (a : ι) (l : Fin D.m) {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt l)) (D.R l)) :
    ContDiffAt ℝ ∞ (fun y => ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ) *
        (D.toGluingSystem hL hT hk hφ).locCoef l (sec a) y) z ∧
      ∀ e : ComplexModel n, dbarDir e (fun y => ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ) *
        (D.toGluingSystem hL hT hk hφ).locCoef l (sec a) y) z =
        dbarDir e (fun y => ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ)) z *
          (D.toGluingSystem hL hT hk hφ).locCoef l (sec a) z := by
  set G := D.toGluingSystem hL hT hk hφ
  set g := G.locCoef l (sec a)
  have hzt : z ∈ (D.chartA l).val.target := D.ball_subset_target l hz
  have hχs : ContDiffAt ℝ ∞ (fun y => ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hχ a (D.chartA l)).contDiffAt ((D.chartA l).val.open_target.mem_nhds hzt))
  by_cases hzU : (D.chartA l).val.symm z ∈ U a
  · have hO := isOpen_ball_inter_preimage D l (hU a)
    have hgd := differentiableOn_locCoef_sec D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec a l
    have hgC : ContDiffAt ℝ ∞ g z := contDiffAt_real_of_differentiableOn_complex hgd hO ⟨hz, hzU⟩
    have hgD : DifferentiableAt ℂ g z := hgd.differentiableAt (hO.mem_nhds ⟨hz, hzU⟩)
    refine ⟨hχs.mul hgC, fun e => ?_⟩
    rw [dbarDir_mul (hχs.differentiableAt (by simp)) (hgC.differentiableAt (by simp)),
      dbarDir_eq_zero_of_differentiableAt hgD, mul_zero, add_zero]
  · have hns : (D.chartA l).val.symm z ∉ tsupport (χ a) := fun h => hzU (hχU a h)
    have h0 := eventually_χ_eq_zero (c := D.chartA l) hzt hns
    have heq : (fun y => ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ) * g y) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with y hy; rw [hy, zero_mul]
    refine ⟨contDiffAt_const.congr_of_eventuallyEq heq, fun e => ?_⟩
    have heq' : (fun y => ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => 0 := h0
    rw [dbarDir_congr heq, dbarDir_congr heq', dbarDir_const, zero_mul]

/-- **The glued datum is smooth** for the gluing system. -/
theorem isSmooth_gluedDatum :
    (D.toGluingSystem hL hT hk hφ).IsSmooth (gluedDatum χ sec) := by
  intro l z hz
  set G := D.toGluingSystem hL hT hk hφ
  have h : G.locCoef l (gluedDatum χ sec) = fun y => ∑ a, ((χ a ((D.chartA l).val.symm y) : ℝ) : ℂ) *
      G.locCoef l (sec a) y := by
    funext y
    unfold GluingSystem.locCoef gluedDatum
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [h]
  exact (ContDiffAt.sum fun a _ =>
    (term_spec D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec a l hz).1).contDiffWithinAt

/-- **Pointwise `∂̄` bound** for the glued datum. -/
theorem dbarNormSq_gluedDatum_le (l : Fin D.m) {M : ℝ}
    (hM : ∀ a, ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      dbarNormSq (fun z => ((χ a ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ M)
    {z : ComplexModel n} (hz : z ∈ ball (ctr (n := n) (D.pt l)) (D.R l)) :
    dbarNormSq ((D.toGluingSystem hL hT hk hφ).locCoef l (gluedDatum χ sec)) z ≤
      (Fintype.card ι : ℝ) ^ 2 * M * ∑ a, ∑ b,
        (tsupport (χ a) ∩ tsupport (χ b)).indicator (fun _ => (1 : ℝ)) ((D.chartA l).val.symm z) *
          ‖(D.toGluingSystem hL hT hk hφ).locCoef l (fun x => sec a x - sec b x) z‖ ^ 2 := by
  set G := D.toGluingSystem hL hT hk hφ
  set c := ((D.chartA l).val.symm)
  set χt : ι → ComplexModel n → ℂ := fun a y => ((χ a (c y) : ℝ) : ℂ) with hχt
  set g : ι → ComplexModel n → ℂ := fun a => G.locCoef l (sec a) with hg
  have hzt : z ∈ (D.chartA l).val.target := D.ball_subset_target l hz
  have hχd : ∀ a, DifferentiableAt ℝ (χt a) z := fun a =>
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hχ a (D.chartA l)).contDiffAt ((D.chartA l).val.open_target.mem_nhds hzt))).differentiableAt
      (by simp)
  have hform : G.locCoef l (gluedDatum χ sec) = fun y => ∑ a, χt a y * g a y := by
    funext y
    unfold GluingSystem.locCoef gluedDatum
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  have hspec := fun a => term_spec D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec a l hz
  have hdir : ∀ e : ComplexModel n, dbarDir e (G.locCoef l (gluedDatum χ sec)) z =
      ∑ a, ∑ b, χt b z * (dbarDir e (χt a) z * (g a z - g b z)) := by
    intro e
    rw [hform, GluingSystem.dbarDir_finset_sum Finset.univ fun a _ =>
      ((hspec a).1.differentiableAt (by simp))]
    simp only [(hspec _).2 e]
    have hsum1 : ∑ b, χt b z = 1 := by
      simp only [hχt]; rw [← Complex.ofReal_sum, hχ1, Complex.ofReal_one]
    have hsum0 : ∑ a, dbarDir e (χt a) z = 0 := by
      rw [← GluingSystem.dbarDir_finset_sum Finset.univ fun a _ => hχd a]
      have : (fun y => ∑ a ∈ Finset.univ, χt a y) = fun _ => (1 : ℂ) := by
        funext y; simp only [hχt]; rw [← Complex.ofReal_sum, hχ1, Complex.ofReal_one]
      rw [this, dbarDir_const]
    rw [show (∑ a, ∑ b, χt b z * (dbarDir e (χt a) z * (g a z - g b z))) =
        ∑ a, (dbarDir e (χt a) z * g a z * ∑ b, χt b z -
          dbarDir e (χt a) z * ∑ b, χt b z * g b z) from
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring]
    rw [Finset.sum_sub_distrib, hsum1, ← Finset.sum_mul (s := Finset.univ)
      (f := fun a => dbarDir e (χt a) z), hsum0, zero_mul, sub_zero]
    simp only [mul_one]
    rfl
  -- the bound
  unfold dbarNormSq
  simp only [hdir]
  have hterm : ∀ a b, ∀ j : Fin n, ‖χt b z * (dbarDir (coordVec j) (χt a) z * (g a z - g b z))‖ ^ 2 ≤
      ‖dbarDir (coordVec j) (χt a) z‖ ^ 2 * ((tsupport (χ a) ∩ tsupport (χ b)).indicator
        (fun _ => (1 : ℝ)) (c z) * ‖g a z - g b z‖ ^ 2) := by
    intro a b j
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
    have hχb : ‖χt b z‖ ≤ 1 := by
      simp only [hχt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 b _)]
      exact χ_le_one' hχ0 hχ1 b _
    by_cases hb : c z ∈ tsupport (χ b)
    · by_cases ha : c z ∈ tsupport (χ a)
      · rw [indicator_of_mem (show c z ∈ tsupport (χ a) ∩ tsupport (χ b) from ⟨ha, hb⟩), one_mul]
        have : ‖χt b z‖ ^ 2 ≤ 1 := by
          calc ‖χt b z‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hχb 2
            _ = 1 := one_pow 2
        nlinarith [sq_nonneg ‖dbarDir (coordVec j) (χt a) z‖, sq_nonneg ‖g a z - g b z‖,
          mul_nonneg (sq_nonneg ‖dbarDir (coordVec j) (χt a) z‖) (sq_nonneg ‖g a z - g b z‖)]
      · have h0 := eventually_χ_eq_zero (c := D.chartA l) (χ' := χ a) hzt ha
        rw [dbarDir_congr h0, dbarDir_const, norm_zero]
        simp
    · have h0 : χt b z = 0 := by
        have := (notMem_tsupport_iff_eventuallyEq.mp hb).self_of_nhds
        simp only [Pi.zero_apply] at this
        simp only [hχt]; rw [this, Complex.ofReal_zero]
      rw [h0, norm_zero, zero_pow two_ne_zero, zero_mul]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (sq_nonneg _))
  calc ∑ j, ‖∑ a, ∑ b, χt b z * (dbarDir (coordVec j) (χt a) z * (g a z - g b z))‖ ^ 2
      ≤ ∑ j : Fin n, (Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b,
          ‖χt b z * (dbarDir (coordVec j) (χt a) z * (g a z - g b z))‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => sq_norm_double_sum_le _
    _ ≤ ∑ j : Fin n, (Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b,
          ‖dbarDir (coordVec j) (χt a) z‖ ^ 2 * ((tsupport (χ a) ∩ tsupport (χ b)).indicator
            (fun _ => (1 : ℝ)) (c z) * ‖g a z - g b z‖ ^ 2) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b j
    _ = (Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b, (∑ j : Fin n, ‖dbarDir (coordVec j) (χt a) z‖ ^ 2) *
          ((tsupport (χ a) ∩ tsupport (χ b)).indicator (fun _ => (1 : ℝ)) (c z) *
            ‖g a z - g b z‖ ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b, M *
          ((tsupport (χ a) ∩ tsupport (χ b)).indicator (fun _ => (1 : ℝ)) (c z) *
            ‖g a z - g b z‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum
          fun b _ => mul_le_mul_of_nonneg_right (hM a z hz) (mul_nonneg (indicator_nonneg
            (fun _ _ => zero_le_one) _) (sq_nonneg _))) (by positivity)
    _ = _ := by
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [G.locCoef_sub]

/-- The chart reading of the weighted density of `sec_a - sec_b` on `tsupp χ_a ∩ tsupp χ_b` is
a.e.-measurable on the chart ball. -/
theorem aemeasurable_term (l : Fin D.m) (a b : ι) :
    AEMeasurable (fun z => (tsupport (χ a) ∩ tsupport (χ b)).indicator
        ((D.toGluingSystem hL hT hk hφ).D (fun x => sec a x - sec b x)) ((D.chartA l).val.symm z))
      (volume.restrict (ball (ctr (n := n) (D.pt l)) (D.R l))) := by
  set G := D.toGluingSystem hL hT hk hφ
  set K := tsupport (χ a) ∩ tsupport (χ b) with hK
  set g := G.locCoef l (fun x => sec a x - sec b x) with hg
  have hB : ball (ctr (n := n) (D.pt l)) (D.R l) = ball (G.center l) (G.R l) := rfl
  have hKc : IsClosed K := (isClosed_tsupport _).inter (isClosed_tsupport _)
  set S' : Set (ComplexModel n) := closedBall (ctr (n := n) (D.pt l)) (D.R l) ∩
    (D.chartA l).val.symm ⁻¹' K with hS'
  have hS'c : IsClosed S' := ContinuousOn.preimage_isClosed_of_isClosed
    ((D.chartA l).val.continuousOn_symm.mono (D.closedBall_subset_target l)) isClosed_closedBall hKc
  have hS'm : MeasurableSet S' := hS'c.measurableSet
  have hgc : ContinuousOn g (S' ∩ ball (ctr (n := n) (D.pt l)) (D.R l)) := by
    rw [hg, G.locCoef_sub]
    have ha := differentiableOn_locCoef_sec D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec a l
    have hb := differentiableOn_locCoef_sec D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec b l
    exact (ha.continuousOn.mono fun z hz => ⟨hz.2, hχU a hz.1.2.1⟩).sub
      (hb.continuousOn.mono fun z hz => ⟨hz.2, hχU b hz.1.2.2⟩)
  have hind : AEMeasurable (S'.indicator fun z => ENNReal.ofReal (‖g z‖ ^ 2) * G.W l z)
      (volume.restrict (ball (ctr (n := n) (D.pt l)) (D.R l))) := by
    refine (aemeasurable_indicator_iff hS'm).mpr ?_
    rw [Measure.restrict_restrict hS'm]
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hgc.aestronglyMeasurable (hS'm.inter measurableSet_ball)).norm.aemeasurable.pow_const
        2)).mul ?_
    exact (G.aemeasurable_W l).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  refine hind.congr ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_))
  show S'.indicator (fun z => ENNReal.ofReal (‖g z‖ ^ 2) * G.W l z) z =
    K.indicator (G.D (fun x => sec a x - sec b x)) ((D.chartA l).val.symm z)
  by_cases hzK : (D.chartA l).val.symm z ∈ K
  · rw [indicator_of_mem (show z ∈ S' from ⟨ball_subset_closedBall hz, hzK⟩),
      indicator_of_mem hzK, show (D.chartA l).val.symm z = (G.chart l).symm z from rfl,
      G.D_chart l _ (by rw [← hB]; exact hz)]
  · rw [indicator_of_notMem (show z ∉ S' from fun h => hzK h.2), indicator_of_notMem hzK]

/-- **The `∂̄`-energy of the glued datum** in chart `l` is bounded by the weighted `L²` norms of
the differences `sec_a - sec_b` over `tsupp χ_a ∩ tsupp χ_b`. -/
theorem energy_gluedDatum_le (l : Fin D.m) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (D.toGluingSystem hL hT hk hφ).energy l (gluedDatum χ sec) ≤
      C * ∑ a, ∑ b, ∫⁻ x in tsupport (χ a) ∩ tsupport (χ b),
        (D.toGluingSystem hL hT hk hφ).D (fun x => sec a x - sec b x) x ∂μ := by
  set G := D.toGluingSystem hL hT hk hφ
  choose Ma hMa0 hMa using fun a : ι =>
    SGPT.PSH.GlobalL2.bound_dbarNormSq_χ (hχ a) (D.pt l) (D.closedBall_subset_target l)
  set M : ℝ := ∑ a, Ma a with hM
  have hMa_le : ∀ a, Ma a ≤ M := fun a =>
    Finset.single_le_sum (f := Ma) (fun b _ => hMa0 b) (Finset.mem_univ a)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun a _ => hMa0 a
  have hB : ball (ctr (n := n) (D.pt l)) (D.R l) = ball (G.center l) (G.R l) := rfl
  set F : ι → ι → ComplexModel n → ℝ≥0∞ := fun a b z =>
    (tsupport (χ a) ∩ tsupport (χ b)).indicator (G.D (fun x => sec a x - sec b x))
      ((D.chartA l).val.symm z) with hF
  have hFm : ∀ a b, AEMeasurable (F a b) (volume.restrict (ball (ctr (n := n) (D.pt l)) (D.R l))) :=
    fun a b => aemeasurable_term D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec l a b
  refine ⟨ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M) * G.A,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top G.A_ne_top, ?_⟩
  -- pointwise
  have hpt : ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      ENNReal.ofReal (dbarNormSq (G.locCoef l (gluedDatum χ sec)) z) * G.W l z ≤
        ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M) * ∑ a, ∑ b, F a b z := by
    intro z hz
    have h := dbarNormSq_gluedDatum_le D hL hT hk hφ hχ hχ0 hχ1 hU hχU hsec l
      (fun a z hz => (hMa a z hz).trans (hMa_le a)) hz
    calc ENNReal.ofReal (dbarNormSq (G.locCoef l (gluedDatum χ sec)) z) * G.W l z
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M * ∑ a, ∑ b,
            (tsupport (χ a) ∩ tsupport (χ b)).indicator (fun _ => (1 : ℝ))
              ((D.chartA l).val.symm z) * ‖G.locCoef l (fun x => sec a x - sec b x) z‖ ^ 2) *
            G.W l z := mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl
      _ = ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M) * ∑ a, ∑ b, F a b z := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc, ENNReal.ofReal_sum_of_nonneg
            (fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (indicator_nonneg
              (fun _ _ => zero_le_one) _) (sq_nonneg _)), Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (indicator_nonneg
            (fun _ _ => zero_le_one) _) (sq_nonneg _)), Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hF]
          simp only
          by_cases hzK : (D.chartA l).val.symm z ∈ tsupport (χ a) ∩ tsupport (χ b)
          · rw [indicator_of_mem hzK, indicator_of_mem hzK, one_mul,
              show (D.chartA l).val.symm z = (G.chart l).symm z from rfl,
              G.D_chart l _ (by rw [← hB]; exact hz)]
          · rw [indicator_of_notMem hzK, indicator_of_notMem hzK, zero_mul, ENNReal.ofReal_zero,
              zero_mul]
  -- each term
  have hterm : ∀ a b, ∫⁻ z in ball (ctr (n := n) (D.pt l)) (D.R l), F a b z ≤
      G.A * ∫⁻ x in tsupport (χ a) ∩ tsupport (χ b), G.D (fun x => sec a x - sec b x) x ∂μ := by
    intro a b
    have hKm : MeasurableSet (tsupport (χ a) ∩ tsupport (χ b)) :=
      ((isClosed_tsupport _).inter (isClosed_tsupport _)).measurableSet
    calc ∫⁻ z in ball (ctr (n := n) (D.pt l)) (D.R l), F a b z
        ≤ ∫⁻ z in ball (ctr (n := n) (D.pt l)) (D.R l), G.A * (F a b z * G.dens l z) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          calc F a b z = 1 * F a b z := (one_mul _).symm
            _ ≤ (G.A * G.dens l z) * F a b z :=
                mul_le_mul_of_nonneg_right (G.one_le_A_mul_dens l z (by rw [← hB]; exact hz)) zero_le
            _ = _ := by ring
      _ = G.A * ∫⁻ x in G.region l, (tsupport (χ a) ∩ tsupport (χ b)).indicator
            (G.D (fun x => sec a x - sec b x)) x ∂μ := by
          rw [lintegral_const_mul' _ _ G.A_ne_top, GluingSystem.region, G.map_measure l _ (hFm a b)]
          rfl
      _ ≤ G.A * ∫⁻ x in tsupport (χ a) ∩ tsupport (χ b), G.D (fun x => sec a x - sec b x) x ∂μ := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [← lintegral_indicator hKm]
          exact setLIntegral_le_lintegral _ _
  calc G.energy l (gluedDatum χ sec)
      ≤ ∫⁻ z in ball (ctr (n := n) (D.pt l)) (D.R l),
          ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M) * ∑ a, ∑ b, F a b z :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M) *
          ∑ a, ∑ b, ∫⁻ z in ball (ctr (n := n) (D.pt l)) (D.R l), F a b z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _ fun a _ =>
          Finset.aemeasurable_fun_sum _ fun b _ => hFm a b]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        exact lintegral_finsetSum' _ fun b _ => hFm a b
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * M) * ∑ a, ∑ b,
          G.A * ∫⁻ x in tsupport (χ a) ∩ tsupport (χ b), G.D (fun x => sec a x - sec b x) x ∂μ := by
        gcongr with a _ b _
        exact hterm a b
    _ = _ := by
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

end SGPT.Trace.OTMargin
