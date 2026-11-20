import SGPT.Trace.OTExt4Grad
import SGPT.Trace.OTMarginDatum
import SGPT.Trace.TwistedL2KahlerLowering

/-!
# Gluing local holomorphic sections with a partition of unity: smoothness and `∂̄` in every chart

Blueprint `claude-ot-ext4.tex`, node `claude-ot-ext4:datum`.  Xia, *Foundations of
pluripotential theory*, q07, proof of `lem:critical-gain-initial-gluing`, third paragraph.

For a finite chart-smooth partition of unity `(η_a)` with `tsupp η_a ⊆ U_a` and sections `F_a`
holomorphic on the open sets `U_a`, the glued section `G = ∑_a η_a F_a` (each term extended by
`0`, `glued`) is smooth in every chart and frame (`isSmoothSectionOn_glued`), and since
`∑_a ∂̄η_a = 0`, `∑_b η_b = 1`,

  `∂̄G = ∑_{a,b} η_b ∂̄η_a (F_a - F_b)`,

so `|⟨∂̄G, v⟩|²_h ≤ D_G · ω(v, iv)` in every chart and frame for
`D_G = N² M ∑_{a,b} 1_{tsupp η_a ∩ tsupp η_b} |F_a - F_b|²_h` (`dbar_glued_le`), where `N` is the
number of pieces and `M` bounds `|∂η_a|²_ω` (`exists_holDerivSq_le_kahlerQuad`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CauchyGreen
  SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (V : HermitianHolomorphicLineBundle.{0, 0} n X)

open Classical in
/-- The section `F` on `U`, extended by `0`. -/
def extSec (U : Set X) (F : (x : X) → V.Fiber x) : (x : X) → V.Fiber x :=
  fun x => if x ∈ U then F x else 0

open Classical in
/-- The glued section `∑_a η_a F_a`, each term extended by `0`. -/
def glued {ι : Type} [Fintype ι] (η : ι → X → ℝ) (U : ι → Set X)
    (F : ι → (x : X) → V.Fiber x) : (x : X) → V.Fiber x :=
  fun x => ∑ i, (η i x : ℂ) • (if x ∈ U i then F i x else 0)

/-- The density `N² M ∑_{a,b} 1_{tsupp η_a ∩ tsupp η_b} |F_a - F_b|²` bounding `|∂̄G|²_ω`. -/
def gluedDensity {ι : Type} [Fintype ι] (M : ℝ) (η : ι → X → ℝ) (U : ι → Set X)
    (F : ι → (x : X) → V.Fiber x) (x : X) : ℝ :=
  (Fintype.card ι : ℝ) ^ 2 * M * ∑ a, ∑ b, (tsupport (η a) ∩ tsupport (η b)).indicator
    (fun x => ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2) x

/-- The coefficient of the extended section `F` on `U` in the chart `c` and frame `e`. -/
def extCoef (c : ComplexChart n X) (e : AtlasFrame V) (U : Set X) (F : (x : X) → V.Fiber x)
    (y : ComplexModel n) : ℂ :=
  e.val.continuousLinearMapAt ℂ (c.val.symm y) (extSec V U F (c.val.symm y))

variable {ι : Type} [Fintype ι] {η : ι → X → ℝ} {U : ι → Set X} {F : ι → (x : X) → V.Fiber x}

/-- The real function `χ ∘ c⁻¹`, as a complex function, vanishes near points outside the
topological support. -/
theorem eventually_ofReal_comp_eq_zero {c : ComplexChart n X} {χ' : X → ℝ} {z : ComplexModel n}
    (hz : z ∈ c.val.target) (hns : c.val.symm z ∉ tsupport χ') :
    ∀ᶠ y in 𝓝 z, ((χ' (c.val.symm y) : ℝ) : ℂ) = 0 := by
  have h1 : ∀ᶠ y in 𝓝 z, χ' (c.val.symm y) = 0 :=
    (c.val.continuousAt_symm hz).eventually (notMem_tsupport_iff_eventuallyEq.mp hns)
  filter_upwards [h1] with y hy; rw [hy, Complex.ofReal_zero]

theorem isOpen_chartFrameDomain (c : ComplexChart n X) (e : AtlasFrame V) :
    IsOpen (chartFrameDomain V c e) :=
  c.val.isOpen_inter_preimage_symm e.val.open_baseSet

/-- The chart coefficient of the glued section is `∑_a η_a coef_a` near points of the
chart-frame domain. -/
theorem chartCoeff_glued_eventuallyEq (c : ComplexChart n X) (e : AtlasFrame V) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain V c e) :
    chartCoeff V c e (glued V η U F) =ᶠ[𝓝 z]
      fun y => ∑ i, ((η i (c.val.symm y) : ℝ) : ℂ) * extCoef V c e (U i) (F i) y := by
  filter_upwards [(isOpen_chartFrameDomain V c e).mem_nhds hz] with y hy
  have hb : c.val.symm y ∈ e.val.baseSet := hy.2
  rw [chartCoeff, frameCoeff, ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hb]
  simp only [glued, map_sum, map_smul, smul_eq_mul, extCoef, extSec]

/-- Each term `η_a coef_a` is smooth, and its `∂̄` is `∂̄η_a · coef_a`. -/
theorem term_spec' (hη : ∀ i, ChartSmooth (n := n) (η i)) (hU : ∀ i, IsOpen (U i))
    (hηU : ∀ i, tsupport (η i) ⊆ U i)
    (hF : ∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber (F i) (U i))
    (c : ComplexChart n X) (e : AtlasFrame V) (i : ι) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain V c e) :
    ContDiffAt ℝ ∞ (fun y => ((η i (c.val.symm y) : ℝ) : ℂ) * extCoef V c e (U i) (F i) y) z ∧
      ∀ v : ComplexModel n, dbarDir v (fun y => ((η i (c.val.symm y) : ℝ) : ℂ) *
        extCoef V c e (U i) (F i) y) z =
        dbarDir v (fun y => ((η i (c.val.symm y) : ℝ) : ℂ)) z * extCoef V c e (U i) (F i) z := by
  have := e.property
  have hzt : z ∈ c.val.target := hz.1
  have hχs : ContDiffAt ℝ ∞ (fun y => ((η i (c.val.symm y) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hη i c).contDiffAt (c.val.open_target.mem_nhds hzt))
  by_cases hzU : c.val.symm z ∈ U i
  · set O := c.val.target ∩ c.val.symm ⁻¹' (U i ∩ e.val.baseSet) with hO
    have hOo : IsOpen O := c.val.isOpen_inter_preimage_symm ((hU i).inter e.val.open_baseSet)
    have hzO : z ∈ O := ⟨hzt, hzU, hz.2⟩
    have hgd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn e.val c (hU i) (hF i)
    have heq : extCoef V c e (U i) (F i) =ᶠ[𝓝 z]
        fun y => e.val.continuousLinearMapAt ℂ (c.val.symm y) (F i (c.val.symm y)) := by
      filter_upwards [hOo.mem_nhds hzO] with y hy
      simp only [extCoef, extSec, if_pos hy.2.1]
    have hgC : ContDiffAt ℝ ∞ (extCoef V c e (U i) (F i)) z :=
      (contDiffAt_real_of_differentiableOn_complex hgd hOo hzO).congr_of_eventuallyEq heq
    have hgD : DifferentiableAt ℂ (extCoef V c e (U i) (F i)) z :=
      (hgd.differentiableAt (hOo.mem_nhds hzO)).congr_of_eventuallyEq heq
    refine ⟨hχs.mul hgC, fun v => ?_⟩
    rw [dbarDir_mul (hχs.differentiableAt (by simp)) (hgC.differentiableAt (by simp)),
      dbarDir_eq_zero_of_differentiableAt hgD, mul_zero, add_zero]
  · have hns : c.val.symm z ∉ tsupport (η i) := fun h => hzU (hηU i h)
    have h0 := eventually_ofReal_comp_eq_zero (c := c) hzt hns
    have heq : (fun y => ((η i (c.val.symm y) : ℝ) : ℂ) * extCoef V c e (U i) (F i) y) =ᶠ[𝓝 z]
        fun _ => 0 := by
      filter_upwards [h0] with y hy; rw [hy, zero_mul]
    refine ⟨contDiffAt_const.congr_of_eventuallyEq heq, fun v => ?_⟩
    have heq' : (fun y => ((η i (c.val.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => 0 := h0
    rw [dbarDir_congr heq, dbarDir_congr heq', dbarDir_const, zero_mul]

/-- **The glued section is smooth** in every chart and frame. -/
theorem isSmoothSectionOn_glued (hη : ∀ i, ChartSmooth (n := n) (η i)) (hU : ∀ i, IsOpen (U i))
    (hηU : ∀ i, tsupport (η i) ⊆ U i)
    (hF : ∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber (F i) (U i)) :
    IsSmoothSectionOn V (glued V η U F) univ := by
  intro c e z hz
  refine ContDiffAt.contDiffWithinAt ?_
  exact (ContDiffAt.sum (s := Finset.univ)
    fun i _ => (term_spec' V hη hU hηU hF c e i hz.1).1).congr_of_eventuallyEq
    (chartCoeff_glued_eventuallyEq V c e hz.1)

/-- `η_a ≤ 1` and `η_a² ≤ 1_{tsupp η_a}`. -/
theorem sq_le_indicator_tsupport {f : X → ℝ} (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (x : X) :
    f x ^ 2 ≤ (tsupport f).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ tsupport f
  · rw [indicator_of_mem hx]; nlinarith [h0 x, h1 x]
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]; norm_num

/-- **The `∂̄` of the glued section in every chart and frame** (FPT:
`∂̄G = ∑_a (∂̄η_a) F_a = ∑_{a,b} η_b ∂̄η_a (F_a - F_b)`). -/
theorem dbar_glued_le (ωb : KahlerBackground n X) (hη : ∀ i, ChartSmooth (n := n) (η i))
    (hη0 : ∀ i x, 0 ≤ η i x) (hη1 : ∀ x, ∑ i, η i x = 1) (hU : ∀ i, IsOpen (U i))
    (hηU : ∀ i, tsupport (η i) ⊆ U i)
    (hF : ∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber (F i) (U i))
    {M : ℝ} (hM : ∀ i, ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target,
      ∀ v : ComplexModel n, holDerivSq (fun y => η i (c.val.symm y)) z v ≤ M * kahlerQuad ωb c z v)
    (c : ComplexChart n X) (e : AtlasFrame V) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain V c e) (v : ComplexModel n) :
    ‖dbarPairing (chartCoeff V c e (glued V η U F)) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
      gluedDensity V M η U F (c.val.symm z) * kahlerQuad ωb c z v := by
  have := e.property
  have hzt : z ∈ c.val.target := hz.1
  set x := c.val.symm z with hx
  set coef : ι → ComplexModel n → ℂ := fun i => extCoef V c e (U i) (F i) with hcoef
  set d : ι → ℂ := fun i => dbarDir v (fun y => ((η i (c.val.symm y) : ℝ) : ℂ)) z with hd
  have hηd : ∀ i, DifferentiableAt ℝ (fun y => ((η i (c.val.symm y) : ℝ) : ℂ)) z := fun i =>
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hη i c).contDiffAt (c.val.open_target.mem_nhds hzt))).differentiableAt (by simp)
  -- `⟨∂̄G, v⟩ = ∑_a d_a coef_a`
  have hpair : dbarPairing (chartCoeff V c e (glued V η U F)) z v = ∑ i, d i * coef i z := by
    rw [dbarPairing_eq_dbarDir, dbarDir_congr (chartCoeff_glued_eventuallyEq V c e hz),
      dbarDir_finset_sum _ fun i _ =>
        ((term_spec' V hη hU hηU hF c e i hz).1).differentiableAt (by simp)]
    exact Finset.sum_congr rfl fun i _ => (term_spec' V hη hU hηU hF c e i hz).2 v
  -- `∑_a d_a = 0`
  have hsumd : ∑ i, d i = 0 := by
    have h1 : (fun y => ∑ i, ((η i (c.val.symm y) : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext y
      rw [← Complex.ofReal_sum, hη1, Complex.ofReal_one]
    have := dbarDir_finset_sum (v := v) (x := z) Finset.univ fun i _ => hηd i
    rw [h1, dbarDir_const] at this
    exact this.symm
  -- the double sum
  have hdouble : ∑ i, d i * coef i z =
      ∑ a, ∑ b, ((η b x : ℝ) : ℂ) * d a * (coef a z - coef b z) := by
    have hη1' : ∑ b, ((η b x : ℝ) : ℂ) = 1 := by rw [← Complex.ofReal_sum, hη1, Complex.ofReal_one]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ a, ∑ b, ((η b x : ℝ) : ℂ) * d a * coef a z = ∑ a, d a * coef a z := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul, hη1', one_mul]
    have e2 : ∑ a, ∑ b, ((η b x : ℝ) : ℂ) * d a * coef b z = 0 := by
      rw [Finset.sum_comm]
      have : ∀ b, ∑ a, ((η b x : ℝ) : ℂ) * d a * coef b z =
          ((η b x : ℝ) : ℂ) * coef b z * ∑ a, d a := fun b => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      simp only [this, hsumd, mul_zero, Finset.sum_const_zero]
    rw [e1, e2, sub_zero]
  rw [hpair, hdouble]
  -- pointwise bounds
  have hη1le : ∀ i y, η i y ≤ 1 := fun i y => SGPT.Trace.OTMargin.χ_le_one' hη0 hη1 i y
  have hdterm : ∀ a, ‖d a‖ ^ 2 ≤ (tsupport (η a)).indicator (fun _ => (1 : ℝ)) x *
      (M * kahlerQuad ωb c z v) := by
    intro a
    by_cases hxa : x ∈ tsupport (η a)
    · rw [indicator_of_mem hxa, one_mul]
      show ‖dbarDir v (fun y => ((η a (c.val.symm y) : ℝ) : ℂ)) z‖ ^ 2 ≤ _
      rw [← dbarPairing_eq_dbarDir,
        norm_dbarPairing_ofReal_sq (((hη a c).contDiffAt (c.val.open_target.mem_nhds hzt)).differentiableAt
          (by simp)) v]
      exact hM a c z hzt v
    · rw [indicator_of_notMem hxa, zero_mul]
      have h0 := eventually_ofReal_comp_eq_zero (c := c) hzt hxa
      have : d a = 0 := by
        show dbarDir v (fun y => ((η a (c.val.symm y) : ℝ) : ℂ)) z = 0
        rw [dbarDir_congr h0, dbarDir_const]
      rw [this, norm_zero]; norm_num
  have hcoefnorm : ∀ a b, ‖coef a z - coef b z‖ ^ 2 * frameNormSq V e x =
      ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2 := by
    intro a b
    rw [SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame e.val hz.2
      (extSec V (U a) (F a) x - extSec V (U b) (F b) x), map_sub, frameNormSq, mul_pow]
    rfl
  have hkq : 0 ≤ kahlerQuad ωb c z v := kahlerQuad_nonneg ωb c hzt v
  have hN := SGPT.Trace.OTMargin.sq_norm_double_sum_le
    (fun a b => ((η b x : ℝ) : ℂ) * d a * (coef a z - coef b z))
  have hfr : 0 ≤ frameNormSq V e x := by rw [frameNormSq]; positivity
  calc ‖∑ a, ∑ b, ((η b x : ℝ) : ℂ) * d a * (coef a z - coef b z)‖ ^ 2 * frameNormSq V e x
      ≤ ((Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b,
          ‖((η b x : ℝ) : ℂ) * d a * (coef a z - coef b z)‖ ^ 2) * frameNormSq V e x :=
        mul_le_mul_of_nonneg_right hN hfr
    _ = (Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b, η b x ^ 2 * ‖d a‖ ^ 2 *
          (‖coef a z - coef b z‖ ^ 2 * frameNormSq V e x) := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
        ring
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ a, ∑ b,
          (tsupport (η b)).indicator (fun _ => (1 : ℝ)) x *
          ((tsupport (η a)).indicator (fun _ => (1 : ℝ)) x * (M * kahlerQuad ωb c z v)) *
          ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum
          fun b _ => ?_) (by positivity)
        rw [hcoefnorm a b]
        refine mul_le_mul_of_nonneg_right (mul_le_mul (sq_le_indicator_tsupport (hη0 b) (hη1le b) x)
          (hdterm a) (sq_nonneg _) ?_) (sq_nonneg _)
        by_cases hb : x ∈ tsupport (η b)
        · rw [indicator_of_mem hb]; norm_num
        · rw [indicator_of_notMem hb]
    _ = gluedDensity V M η U F x * kahlerQuad ωb c z v := by
        rw [gluedDensity]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases ha : x ∈ tsupport (η a) <;> by_cases hb : x ∈ tsupport (η b) <;>
          simp [indicator, ha, hb, mul_comm, mul_assoc, mul_left_comm]

end SGPT.Trace.OTExt4
