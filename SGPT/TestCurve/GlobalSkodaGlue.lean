import SGPT.PSH.GlobalL2Gluing

/-!
# Gluing local holomorphic data with a partition of unity

Blueprint `claude-global-skoda.tex`, node `global-skoda:glue`.

For a gluing system `G` (`SGPT.PSH.GlobalL2.GluingSystem`: a finite chart-ball cover of `X`
adapted to a line bundle `V` and a weight `w`, with local weights `e^{-Ψᵢ - λ|z - zᵢ|²}` and a
partition of unity `χᵢ`) and holomorphic functions `hᵢ` on the middle balls `B(zᵢ, rᵢ)`, the
glued section `glue h = ∑ᵢ χᵢ · (hᵢ ∘ zᵢ) Eᵢ` has smooth coefficients, and its `∂̄`-energy and
its weighted `L²` norms in the charts are bounded by the local weighted `L²` norms
`Eᵢ = ∫_{B(zᵢ, rᵢ)} |hᵢ|² e^{-Ψᵢ - λ|z - zᵢ|²}`:

* `totalEnergy_glue_le`: `N(glue h) ≤ |ι| · (|ι| M) · ∑ᵢ A² Eᵢ`;
* `chartL2_glue_le`: `∫_{B(z_l, r_l)} |coef_l(glue h)|² W_l ≤ |ι| ∑ᵢ A² Eᵢ`.

These are the inputs of the global division step: `h` are the local Skoda quotients, and
`GluingSystem.exists_correction` turns `glue h` into a holomorphic section at distance
`O(1/λ) · N(glue h)`. The section also gives the chart transfers used to integrate over `X`
without global measurability (`lintegral_le_sum_small`, `chartL2_le_lintegral`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {V : X → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  {w : X → ℝ≥0∞} {ι : Type*} [Fintype ι] (G : GluingSystem n X μ V w ι)

/-- The glued section `∑ᵢ χᵢ · (hᵢ ∘ zᵢ) Eᵢ`. -/
def glue (h : ι → ComplexModel n → ℂ) (x : X) : V x :=
  ∑ i, ((G.χ i x : ℝ) : ℂ) • G.localSec i (h i) x

theorem locCoef_glue (h : ι → ComplexModel n → ℂ) (l : ι) :
    G.locCoef l (glue G h) = fun z => ∑ i, ((G.χ i ((G.chart l).symm z) : ℝ) : ℂ) *
      G.locCoef l (G.localSec i (h i)) z := by
  funext z
  simp only [GluingSystem.locCoef, glue, map_sum, map_smul, smul_eq_mul]

variable {G}

/-- The glued section has smooth coefficients. -/
theorem isSmooth_glue {h : ι → ComplexModel n → ℂ}
    (hh : ∀ i, DifferentiableOn ℂ (h i) (ball (G.center i) (G.r i))) : G.IsSmooth (glue G h) := by
  intro l
  rw [locCoef_glue G h l]
  intro z hz
  exact (ContDiffAt.sum fun i _ => (G.term_spec (hh i) hz).1).contDiffWithinAt

/-- `∂̄ coef_l(glue h) = ∑ᵢ ∂̄(χᵢ ∘ z_l⁻¹) · coef_l((hᵢ ∘ zᵢ) Eᵢ)`. -/
theorem dbarDir_locCoef_glue {h : ι → ComplexModel n → ℂ}
    (hh : ∀ i, DifferentiableOn ℂ (h i) (ball (G.center i) (G.r i))) {l : ι}
    {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l)) (e : ComplexModel n) :
    dbarDir e (G.locCoef l (glue G h)) z =
      ∑ i, dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z *
        G.locCoef l (G.localSec i (h i)) z := by
  rw [locCoef_glue G h l, GluingSystem.dbarDir_finset_sum _ fun i _ =>
    ((G.term_spec (hh i) hz).1).differentiableAt (by simp)]
  exact Finset.sum_congr rfl fun i _ => (G.term_spec (hh i) hz).2 e

/-- Pointwise bound for the `∂̄`-energy density of the glued section. -/
theorem dbarNormSq_glue_le {h : ι → ComplexModel n → ℂ}
    (hh : ∀ i, DifferentiableOn ℂ (h i) (ball (G.center i) (G.r i))) {l : ι}
    {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l)) :
    ENNReal.ofReal (dbarNormSq (G.locCoef l (glue G h)) z) * G.W l z ≤
      ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
        (G.inner l i).indicator (fun z => ENNReal.ofReal
          (‖G.locCoef l (G.localSec i (h i)) z‖ ^ 2) * G.W l z) z := by
  set b : ι → ℂ := fun i => G.locCoef l (G.localSec i (h i)) z
  set a : ι → Fin n → ℂ := fun i m =>
    dbarDir (coordVec m) (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z
  have hM0 : 0 ≤ G.M := le_trans (dbarNormSq_nonneg _ z)
    (G.dbar_χ_le (G.cover ((G.chart l).symm z)).choose l z hz)
  have hpt : dbarNormSq (G.locCoef l (glue G h)) z ≤
      ∑ i, (Fintype.card ι : ℝ) * G.M * (G.inner l i).indicator (fun _ => ‖b i‖ ^ 2) z := by
    calc dbarNormSq (G.locCoef l (glue G h)) z
        = ∑ m, ‖∑ i, a i m * b i‖ ^ 2 := by
          unfold dbarNormSq
          exact Finset.sum_congr rfl fun m _ => by rw [dbarDir_locCoef_glue hh hz]
      _ ≤ ∑ m, (Fintype.card ι : ℝ) * ∑ i, ‖a i m‖ ^ 2 * ‖b i‖ ^ 2 := by
          refine Finset.sum_le_sum fun m _ =>
            (GluingSystem.norm_sum_sq_le_card_mul _).trans (le_of_eq ?_)
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, mul_pow]
      _ = ∑ i, (Fintype.card ι : ℝ) *
            (dbarNormSq (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z * ‖b i‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold dbarNormSq
          rw [Finset.sum_mul]
      _ ≤ ∑ i, (Fintype.card ι : ℝ) * G.M * (G.inner l i).indicator (fun _ => ‖b i‖ ^ 2) z := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hχ := G.dbarNormSq_χ_le (i := i) hz
          by_cases hzi : z ∈ G.inner l i
          · rw [indicator_of_mem hzi] at hχ ⊢
            exact mul_le_mul_of_nonneg_right hχ (sq_nonneg _)
          · rw [indicator_of_notMem hzi] at hχ ⊢
            have h0 : dbarNormSq (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z = 0 :=
              le_antisymm hχ (dbarNormSq_nonneg _ z)
            rw [h0, zero_mul, mul_zero]
  calc ENNReal.ofReal (dbarNormSq (G.locCoef l (glue G h)) z) * G.W l z
      ≤ ENNReal.ofReal (∑ i, (Fintype.card ι : ℝ) * G.M *
          (G.inner l i).indicator (fun _ => ‖b i‖ ^ 2) z) * G.W l z :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpt) zero_le
    _ = ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          (G.inner l i).indicator (fun z => ENNReal.ofReal (‖b i‖ ^ 2) * G.W l z) z := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM0)
          (indicator_nonneg (fun _ _ => sq_nonneg _) z)), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hzi : z ∈ G.inner l i
        · rw [indicator_of_mem hzi, indicator_of_mem hzi, ENNReal.ofReal_mul
            (mul_nonneg (Nat.cast_nonneg _) hM0), mul_assoc]
        · rw [indicator_of_notMem hzi, indicator_of_notMem hzi, mul_zero, ENNReal.ofReal_zero,
            zero_mul, mul_zero]

/-- The coefficient of `(hᵢ ∘ zᵢ) Eᵢ` in chart `l` is continuous where `χᵢ` lives. -/
theorem continuousOn_locCoef_localSec {h : ComplexModel n → ℂ} {i : ι}
    (hh : DifferentiableOn ℂ h (ball (G.center i) (G.r i))) (l : ι) :
    ContinuousOn (G.locCoef l (G.localSec i h)) (G.inner l i) :=
  ((G.differentiableOn_locCoef_localSec hh).continuousOn).congr fun _ hz =>
    G.locCoef_localSec_of_mem _ hz

/-- The weighted `L²` norm of `(h ∘ zᵢ) Eᵢ` over the middle region of chart `i`. -/
theorem lintegral_small_localSec_le' {h : ComplexModel n → ℂ} {i : ι}
    (hh : DifferentiableOn ℂ h (ball (G.center i) (G.r i))) :
    ∫⁻ x in G.small i, G.D (G.localSec i h) x ∂μ ≤
      G.A * ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖h z‖ ^ 2) * G.W i z := by
  have hcont : ContinuousOn (G.locCoef i (G.localSec i h)) (ball (G.center i) (G.r i)) :=
    hh.continuousOn.congr fun z hz => G.locCoef_localSec_self _ hz
  refine (G.lintegral_small_le i _ hcont).trans (le_of_eq ?_)
  congr 1
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [G.locCoef_localSec_self _ hz]

variable (G) in
/-- The local weighted `L²` norms `Eᵢ` of the data. -/
def localNorm (h : ι → ComplexModel n → ℂ) (i : ι) : ℝ≥0∞ :=
  ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖h i z‖ ^ 2) * G.W i z

/-- **The `∂̄`-energy of the glued section**, chartwise. -/
theorem energy_glue_le {h : ι → ComplexModel n → ℂ}
    (hh : ∀ i, DifferentiableOn ℂ (h i) (ball (G.center i) (G.r i))) (l : ι) :
    G.energy l (glue G h) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
      ∑ i, G.A * (G.A * localNorm G h i) := by
  calc G.energy l (glue G h)
      ≤ ∫⁻ z in ball (G.center l) (G.R l), ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef l (G.localSec i (h i)) z‖ ^ 2) * G.W l z) z :=
        setLIntegral_mono' measurableSet_ball fun z hz => dbarNormSq_glue_le hh hz
    _ = ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          ∫⁻ z in ball (G.center l) (G.R l), (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef l (G.localSec i (h i)) z‖ ^ 2) * G.W l z) z := by
        rw [lintegral_finsetSum' _ fun i _ =>
          (G.aemeasurable_indicator_inner (continuousOn_locCoef_localSec (hh i) l)).const_mul _]
        exact Finset.sum_congr rfl fun i _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          (G.A * (G.A * localNorm G h i)) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ zero_le
        exact (G.lintegral_inner_le l i _ (continuousOn_locCoef_localSec (hh i) l)).trans
          (mul_le_mul_of_nonneg_left (lintegral_small_localSec_le' (hh i)) zero_le)
    _ = _ := by rw [Finset.mul_sum]

/-- **The total `∂̄`-energy of the glued section.** -/
theorem totalEnergy_glue_le {h : ι → ComplexModel n → ℂ}
    (hh : ∀ i, DifferentiableOn ℂ (h i) (ball (G.center i) (G.r i))) :
    G.totalEnergy (glue G h) ≤ (Fintype.card ι : ℝ≥0∞) *
      (ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) * ∑ i, G.A * (G.A * localNorm G h i)) := by
  calc G.totalEnergy (glue G h) = ∑ l, G.energy l (glue G h) := rfl
    _ ≤ ∑ _l : ι, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          ∑ i, G.A * (G.A * localNorm G h i) := Finset.sum_le_sum fun l _ => energy_glue_le hh l
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The chart `L²` norm of the glued section.** -/
theorem chartL2_glue_le {h : ι → ComplexModel n → ℂ}
    (hh : ∀ i, DifferentiableOn ℂ (h i) (ball (G.center i) (G.r i))) (l : ι) :
    ∫⁻ z in ball (G.center l) (G.r l), ENNReal.ofReal (‖G.locCoef l (glue G h) z‖ ^ 2) *
        G.W l z ≤ (Fintype.card ι : ℝ≥0∞) * ∑ i, G.A * (G.A * localNorm G h i) := by
  have hrR : ball (G.center l) (G.r l) ⊆ ball (G.center l) (G.R l) :=
    ball_subset_ball (G.r_lt_R l).le
  have hpt : ∀ z ∈ ball (G.center l) (G.R l),
      ENNReal.ofReal (‖G.locCoef l (glue G h) z‖ ^ 2) * G.W l z ≤
        ∑ i, (Fintype.card ι : ℝ≥0∞) * (G.inner l i).indicator (fun z => ENNReal.ofReal
          (‖G.locCoef l (G.localSec i (h i)) z‖ ^ 2) * G.W l z) z := by
    intro z hz
    set c : ι → ℂ := fun i => G.locCoef l (G.localSec i (h i)) z
    have hχc : ∀ i, ‖((G.χ i ((G.chart l).symm z) : ℝ) : ℂ) * c i‖ ^ 2 ≤
        (G.inner l i).indicator (fun _ => ‖c i‖ ^ 2) z := by
      intro i
      by_cases hzi : z ∈ G.inner l i
      · rw [indicator_of_mem hzi, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (G.χ_nonneg _ _), mul_pow]
        have h1 : G.χ i ((G.chart l).symm z) ^ 2 ≤ 1 := by
          have := G.χ_le_one i ((G.chart l).symm z)
          have := G.χ_nonneg i ((G.chart l).symm z)
          nlinarith
        nlinarith [sq_nonneg ‖c i‖]
      · rw [indicator_of_notMem hzi, G.χ_eq_zero_of_not_mem hz hzi]
        simp
    have hsum : ‖G.locCoef l (glue G h) z‖ ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i, (G.inner l i).indicator (fun _ => ‖c i‖ ^ 2) z := by
      rw [locCoef_glue G h l]
      exact (GluingSystem.norm_sum_sq_le_card_mul _).trans
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hχc i) (Nat.cast_nonneg _))
    calc ENNReal.ofReal (‖G.locCoef l (glue G h) z‖ ^ 2) * G.W l z
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) *
            ∑ i, (G.inner l i).indicator (fun _ => ‖c i‖ ^ 2) z) * G.W l z :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hsum) zero_le
      _ = ∑ i, (Fintype.card ι : ℝ≥0∞) * (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖c i‖ ^ 2) * G.W l z) z := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun i _ => indicator_nonneg (fun _ _ => sq_nonneg _) z),
            mul_assoc, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hzi : z ∈ G.inner l i
          · rw [indicator_of_mem hzi, indicator_of_mem hzi]
          · rw [indicator_of_notMem hzi, indicator_of_notMem hzi, ENNReal.ofReal_zero, zero_mul]
  calc ∫⁻ z in ball (G.center l) (G.r l), ENNReal.ofReal (‖G.locCoef l (glue G h) z‖ ^ 2) *
        G.W l z
      ≤ ∫⁻ z in ball (G.center l) (G.R l), ENNReal.ofReal (‖G.locCoef l (glue G h) z‖ ^ 2) *
          G.W l z := lintegral_mono_set hrR
    _ ≤ ∫⁻ z in ball (G.center l) (G.R l), ∑ i, (Fintype.card ι : ℝ≥0∞) *
          (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef l (G.localSec i (h i)) z‖ ^ 2) * G.W l z) z :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ∑ i, (Fintype.card ι : ℝ≥0∞) * ∫⁻ z in ball (G.center l) (G.R l),
          (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef l (G.localSec i (h i)) z‖ ^ 2) * G.W l z) z := by
        rw [lintegral_finsetSum' _ fun i _ =>
          (G.aemeasurable_indicator_inner (continuousOn_locCoef_localSec (hh i) l)).const_mul _]
        exact Finset.sum_congr rfl fun i _ => lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
    _ ≤ ∑ i, (Fintype.card ι : ℝ≥0∞) * (G.A * (G.A * localNorm G h i)) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ zero_le
        exact (G.lintegral_inner_le l i _ (continuousOn_locCoef_localSec (hh i) l)).trans
          (mul_le_mul_of_nonneg_left (lintegral_small_localSec_le' (hh i)) zero_le)
    _ = _ := by rw [Finset.mul_sum]

/-! ### Chart transfers -/

/-- The middle region of chart `i`, read in chart `i`, is the middle ball. -/
theorem inner_self_eq (i : ι) : G.inner i i = ball (G.center i) (G.r i) := by
  ext z
  constructor
  · intro hz
    have h2 := hz.2.2
    rwa [mem_preimage, G.chart_symm hz.1] at h2
  · intro hz
    have hzR : z ∈ ball (G.center i) (G.R i) := ball_subset_ball (G.r_lt_R i).le hz
    exact ⟨hzR, G.symm_mem_source hzR, by rw [mem_preimage, G.chart_symm hzR]; exact hz⟩

/-- A chart `L²` norm is controlled by the global weighted `L²` norm. -/
theorem chartL2_le_lintegral (i : ι) (u : (x : X) → V x)
    (hu : ContinuousOn (G.locCoef i u) (ball (G.center i) (G.r i))) :
    ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z ≤
      G.A * ∫⁻ x, G.D u x ∂μ := by
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  have hu' : ContinuousOn (G.locCoef i u) (G.inner i i) := by rw [inner_self_eq]; exact hu
  calc ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z
      = ∫⁻ z in ball (G.center i) (G.R i), (G.inner i i).indicator
          (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) z := by
        rw [inner_self_eq, lintegral_indicator measurableSet_ball,
          Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hrR]
    _ ≤ G.A * ∫⁻ x in G.small i, G.D u x ∂μ := G.lintegral_inner_le i i u hu'
    _ ≤ G.A * ∫⁻ x, G.D u x ∂μ := mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le

/-- The small regions cover `X`: an integral over `X` is at most the sum of the integrals over
the middle regions. -/
theorem lintegral_le_sum_small (F : X → ℝ≥0∞) :
    ∫⁻ x, F x ∂μ ≤ ∑ i, ∫⁻ x in G.small i, F x ∂μ := by
  have hU : (⋃ i, G.small i) = univ := eq_univ_of_forall fun x => by
    obtain ⟨j, hj⟩ := G.cover x
    exact mem_iUnion.mpr ⟨j, G.smaller_subset_small j hj⟩
  calc ∫⁻ x, F x ∂μ = ∫⁻ x in ⋃ i, G.small i, F x ∂μ := by rw [hU, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ x in G.small i, F x ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i, ∫⁻ x in G.small i, F x ∂μ := tsum_fintype _

end SGPT.TestCurve.GlobalSkoda
