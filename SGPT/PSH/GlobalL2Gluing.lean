import SGPT.PSH.GlobalL2LocalSingular
import SGPT.Foundations.Analysis.Pending.WirtingerCalculus
import Mathlib.Algebra.Order.Chebyshev

/-!
# Gluing local `L²` corrections: the Neumann iteration

Blueprint `claude-global-l2:gluing-step`, `claude-global-l2:holomorphic-limit`.

A `GluingSystem` is the data of `claude-global-l2:cover` and `claude-global-l2:local-weights`
for one line bundle `V` (in the application `L^k ⊗ T`) and one global weight `w`
(`e^{-kφ}`): finitely many charts with balls `B(z_i, r'_i) ⊂ B(z_i, r_i) ⊂ B(z_i, R_i)`, frames
`E_i` with coordinate functionals `coef_i`, holomorphic frame and chart transitions, a measure
comparison with Lebesgue measure in the charts, local weights `Ψ_i + λ|z - z_i|²` (`Ψ_i` psh)
with `|u|² w = |coef_i u|² e^{-Ψ_i - λ|z - z_i|²}`, and a smooth partition of unity `χ_i` with
`tsupport χ_i ⊆ B_i(r_i)` and `|∂̄(χ_i ∘ z_l⁻¹)|² ≤ M`.

The Neumann step `GluingSystem.next`: solve `∂̄` locally on every ball with
`localBallCorrection`, glue the local holomorphic approximants with the partition of unity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen

/-- The data of a finite chart-ball cover adapted to a line bundle `V` and a weight `w`
(`claude-global-l2:cover`, `claude-global-l2:local-weights`). -/
structure GluingSystem (n : ℕ) (X : Type*) [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
    (w : X → ℝ≥0∞) (ι : Type*) [Fintype ι] where
  /-- the charts -/
  chart : ι → OpenPartialHomeomorph X (ComplexModel n)
  /-- the centres of the balls -/
  center : ι → ComplexModel n
  /-- the radii `r' < r < R` -/
  r' : ι → ℝ
  r : ι → ℝ
  R : ι → ℝ
  r'_pos : ∀ i, 0 < r' i
  r'_lt_r : ∀ i, r' i < r i
  r_lt_R : ∀ i, r i < R i
  closedBall_subset : ∀ i, closedBall (center i) (R i) ⊆ (chart i).target
  /-- the small balls cover `X` -/
  cover : ∀ x, ∃ i, x ∈ (chart i).source ∧ chart i x ∈ ball (center i) (r' i)
  /-- the coordinate functional of the frame `E_i` -/
  coef : (i : ι) → (x : X) → V x →L[ℂ] ℂ
  /-- the frame `E_i` -/
  frame : ι → (x : X) → V x
  coef_frame : ∀ i x, x ∈ (chart i).source → chart i x ∈ ball (center i) (R i) →
    coef i x (frame i x) = 1
  /-- fibres are lines: `u = coef_i(u) E_i` over the region of chart `i` -/
  eq_coef_smul_frame : ∀ i x (u : V x), x ∈ (chart i).source → chart i x ∈ ball (center i) (R i) →
    u = coef i x u • frame i x
  /-- holomorphic frame transitions -/
  transition_holo : ∀ i l, DifferentiableOn ℂ
    (fun z => coef l ((chart l).symm z) (frame i ((chart l).symm z)))
    {z | z ∈ ball (center l) (R l) ∧ (chart l).symm z ∈ (chart i).source ∧
      chart i ((chart l).symm z) ∈ ball (center i) (R i)}
  /-- holomorphic chart transitions -/
  chart_holo : ∀ i l, DifferentiableOn ℂ (fun z => chart i ((chart l).symm z))
    {z | z ∈ ball (center l) (R l) ∧ (chart l).symm z ∈ (chart i).source ∧
      chart i ((chart l).symm z) ∈ ball (center i) (R i)}
  /-- the density of `μ` in chart `i` -/
  dens : ι → ComplexModel n → ℝ≥0∞
  /-- the comparison constant -/
  A : ℝ≥0∞
  A_ne_top : A ≠ ⊤
  dens_le : ∀ i, ∀ z ∈ ball (center i) (R i), dens i z ≤ A
  one_le_A_mul_dens : ∀ i, ∀ z ∈ ball (center i) (R i), 1 ≤ A * dens i z
  map_measure : ∀ i (f : X → ℝ≥0∞),
    AEMeasurable (fun z => f ((chart i).symm z)) (volume.restrict (ball (center i) (R i))) →
    ∫⁻ x in (chart i).source ∩ chart i ⁻¹' ball (center i) (R i), f x ∂μ =
      ∫⁻ z in ball (center i) (R i), f ((chart i).symm z) * dens i z
  /-- the psh parts of the local weights -/
  Ψ : ι → ComplexModel n → EReal
  Ψ_psh : ∀ i, PlurisubharmonicOn (Ψ i) (ball (center i) (R i))
  /-- the curvature bound `λ` of the local weights -/
  lam : ℝ
  lam_pos : 0 < lam
  density_eq : ∀ i x (u : V x), x ∈ (chart i).source → chart i x ∈ ball (center i) (R i) →
    ENNReal.ofReal (‖u‖ ^ 2) * w x =
      ENNReal.ofReal (‖coef i x u‖ ^ 2) * ballWeight (Ψ i) lam (center i) (chart i x)
  /-- the partition of unity -/
  χ : ι → X → ℝ
  χ_smooth : ∀ i l, ContDiffOn ℝ ∞ (fun z => χ i ((chart l).symm z)) (chart l).target
  χ_nonneg : ∀ i x, 0 ≤ χ i x
  sum_χ : ∀ x, ∑ i, χ i x = 1
  tsupport_χ : ∀ i, tsupport (χ i) ⊆ (chart i).source ∩ chart i ⁻¹' ball (center i) (r i)
  /-- the bound for the cut-off derivatives -/
  M : ℝ
  dbar_χ_le : ∀ i l, ∀ z ∈ ball (center l) (R l),
    dbarNormSq (fun z => ((χ i ((chart l).symm z) : ℝ) : ℂ)) z ≤ M

namespace GluingSystem

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {V : X → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  {w : X → ℝ≥0∞} {ι : Type*} [Fintype ι] (G : GluingSystem n X μ V w ι)

/-! ### Definitions -/

/-- The region `z_i⁻¹ B(z_i, R_i)` of chart `i`. -/
def region (i : ι) : Set X := (G.chart i).source ∩ G.chart i ⁻¹' ball (G.center i) (G.R i)

/-- The middle region `z_i⁻¹ B(z_i, r_i)` of chart `i`. -/
def small (i : ι) : Set X := (G.chart i).source ∩ G.chart i ⁻¹' ball (G.center i) (G.r i)

/-- The small region `z_i⁻¹ B(z_i, r'_i)` of chart `i`; these cover `X`. -/
def smaller (i : ι) : Set X := (G.chart i).source ∩ G.chart i ⁻¹' ball (G.center i) (G.r' i)

/-- The points of the `R_l`-ball of chart `l` lying in the middle region of chart `i`. -/
def inner (l i : ι) : Set (ComplexModel n) :=
  ball (G.center l) (G.R l) ∩ (G.chart l).symm ⁻¹' G.small i

/-- The local weight `e^{-Ψ_i - λ|z - z_i|²}` of chart `i`. -/
def W (i : ι) (z : ComplexModel n) : ℝ≥0∞ := ballWeight (G.Ψ i) G.lam (G.center i) z

/-- The coefficient of a section in chart `i` and frame `E_i`. -/
def locCoef (i : ι) (v : (x : X) → V x) (z : ComplexModel n) : ℂ :=
  G.coef i ((G.chart i).symm z) (v ((G.chart i).symm z))

/-- The frame transition `coef_l(E_i)` in the coordinates of chart `l`. -/
def trans (l i : ι) (z : ComplexModel n) : ℂ :=
  G.coef l ((G.chart l).symm z) (G.frame i ((G.chart l).symm z))

/-- The weighted density `|u|² w` of a section. -/
def D (_G : GluingSystem n X μ V w ι) (u : (x : X) → V x) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖u x‖ ^ 2) * w x

/-- The `∂̄`-energy of a section on the `R_i`-ball of chart `i`. -/
def energy (i : ι) (v : (x : X) → V x) : ℝ≥0∞ :=
  ∫⁻ z in ball (G.center i) (G.R i), ENNReal.ofReal (dbarNormSq (G.locCoef i v) z) * G.W i z

/-- The total `∂̄`-energy `N(v)`. -/
def totalEnergy (v : (x : X) → V x) : ℝ≥0∞ := ∑ i, G.energy i v

/-- A section is smooth for the system if its coefficients are smooth on the `R`-balls. -/
def IsSmooth (v : (x : X) → V x) : Prop :=
  ∀ l, ContDiffOn ℝ ∞ (G.locCoef l v) (ball (G.center l) (G.R l))

open Classical in
/-- The local section `h ∘ z_i · E_i` on the middle region of chart `i`, extended by zero. -/
def localSec (i : ι) (h : ComplexModel n → ℂ) (x : X) : V x :=
  if x ∈ G.small i then h (G.chart i x) • G.frame i x else 0

/-! ### Geometry of the charts -/

theorem ball_subset_target (i : ι) : ball (G.center i) (G.R i) ⊆ (G.chart i).target :=
  ball_subset_closedBall.trans (G.closedBall_subset i)

theorem symm_mem_source {i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center i) (G.R i)) :
    (G.chart i).symm z ∈ (G.chart i).source :=
  (G.chart i).map_target (G.ball_subset_target i hz)

theorem chart_symm {i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center i) (G.R i)) :
    G.chart i ((G.chart i).symm z) = z :=
  (G.chart i).right_inv (G.ball_subset_target i hz)

theorem symm_mem_region {i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center i) (G.R i)) :
    (G.chart i).symm z ∈ G.region i :=
  ⟨G.symm_mem_source hz, by rw [mem_preimage, G.chart_symm hz]; exact hz⟩

theorem isOpen_region (i : ι) : IsOpen (G.region i) :=
  (G.chart i).isOpen_inter_preimage isOpen_ball

theorem isOpen_small (i : ι) : IsOpen (G.small i) :=
  (G.chart i).isOpen_inter_preimage isOpen_ball

theorem isOpen_smaller (i : ι) : IsOpen (G.smaller i) :=
  (G.chart i).isOpen_inter_preimage isOpen_ball

theorem small_subset_region (i : ι) : G.small i ⊆ G.region i :=
  fun _ hx => ⟨hx.1, ball_subset_ball (G.r_lt_R i).le hx.2⟩

theorem smaller_subset_small (i : ι) : G.smaller i ⊆ G.small i :=
  fun _ hx => ⟨hx.1, ball_subset_ball (G.r'_lt_r i).le hx.2⟩

theorem isOpen_inner (l i : ι) : IsOpen (G.inner l i) := by
  have h := (G.chart l).isOpen_inter_preimage_symm (G.isOpen_small i)
  have : G.inner l i = ball (G.center l) (G.R l) ∩
      ((G.chart l).target ∩ (G.chart l).symm ⁻¹' G.small i) := by
    ext z
    simp only [inner, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hz, hs⟩; exact ⟨hz, G.ball_subset_target l hz, hs⟩
    · rintro ⟨hz, -, hs⟩; exact ⟨hz, hs⟩
  rw [this]
  exact isOpen_ball.inter h

theorem inner_subset_overlap (l i : ι) : G.inner l i ⊆
    {z | z ∈ ball (G.center l) (G.R l) ∧ (G.chart l).symm z ∈ (G.chart i).source ∧
      G.chart i ((G.chart l).symm z) ∈ ball (G.center i) (G.R i)} :=
  fun _ hz => ⟨hz.1, hz.2.1, ball_subset_ball (G.r_lt_R i).le hz.2.2⟩

/-- The cut-off `χ_i` vanishes near every point of the `R_l`-ball of chart `l` outside the
middle region of chart `i`. -/
theorem eventually_χ_eq_zero {l i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l))
    (hzi : z ∉ G.inner l i) : ∀ᶠ y in 𝓝 z, G.χ i ((G.chart l).symm y) = 0 := by
  have hns : (G.chart l).symm z ∉ tsupport (G.χ i) := fun h =>
    hzi ⟨hz, G.tsupport_χ i h⟩
  have h1 : ∀ᶠ x in 𝓝 ((G.chart l).symm z), G.χ i x = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hns
  exact ((G.chart l).continuousAt_symm (G.ball_subset_target l hz)).eventually h1

/-! ### Coefficients -/

theorem locCoef_add (i : ι) (u v : (x : X) → V x) :
    G.locCoef i (fun x => u x + v x) = fun z => G.locCoef i u z + G.locCoef i v z := by
  funext z; simp [locCoef]

theorem locCoef_sub (i : ι) (u v : (x : X) → V x) :
    G.locCoef i (fun x => u x - v x) = fun z => G.locCoef i u z - G.locCoef i v z := by
  funext z; simp [locCoef]

theorem locCoef_sum (i : ι) (u : ι → (x : X) → V x) :
    G.locCoef i (fun x => ∑ j, u j x) = fun z => ∑ j, G.locCoef i (u j) z := by
  funext z; simp [locCoef]

theorem locCoef_real_smul (i : ι) (c : X → ℝ) (u : (x : X) → V x) :
    G.locCoef i (fun x => ((c x : ℝ) : ℂ) • u x) =
      fun z => ((c ((G.chart i).symm z) : ℝ) : ℂ) * G.locCoef i u z := by
  funext z; simp [locCoef]

theorem locCoef_localSec_of_mem {l i : ι} (h : ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ G.inner l i) :
    G.locCoef l (G.localSec i h) z = h (G.chart i ((G.chart l).symm z)) * G.trans l i z := by
  have h2 : (G.chart l).symm z ∈ G.small i := hz.2
  simp only [locCoef, localSec]
  rw [if_pos h2, map_smul, smul_eq_mul]
  rfl

theorem locCoef_localSec_of_not_mem {l i : ι} (h : ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ ball (G.center l) (G.R l)) (hzi : z ∉ G.inner l i) :
    G.locCoef l (G.localSec i h) z = 0 := by
  have : (G.chart l).symm z ∉ G.small i := fun h' => hzi ⟨hz, h'⟩
  simp [locCoef, localSec, this]

theorem locCoef_localSec_self {i : ι} (h : ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ ball (G.center i) (G.r i)) : G.locCoef i (G.localSec i h) z = h z := by
  have hzR : z ∈ ball (G.center i) (G.R i) := ball_subset_ball (G.r_lt_R i).le hz
  have hmem : (G.chart i).symm z ∈ G.small i :=
    ⟨G.symm_mem_source hzR, by rw [mem_preimage, G.chart_symm hzR]; exact hz⟩
  simp only [locCoef, localSec, hmem, if_true, map_smul, smul_eq_mul]
  rw [G.coef_frame i _ (G.symm_mem_source hzR) (by rw [G.chart_symm hzR]; exact hzR),
    G.chart_symm hzR, mul_one]

/-- The coefficient of a local section `h ∘ z_i · E_i` in chart `l` is holomorphic where
defined. -/
theorem differentiableOn_locCoef_localSec {l i : ι} {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h (ball (G.center i) (G.r i))) :
    DifferentiableOn ℂ (fun z => h (G.chart i ((G.chart l).symm z)) * G.trans l i z)
      (G.inner l i) := by
  refine DifferentiableOn.mul ?_ ((G.transition_holo i l).mono (G.inner_subset_overlap l i))
  exact hh.comp ((G.chart_holo i l).mono (G.inner_subset_overlap l i)) fun z hz => hz.2.2

theorem locCoef_eventuallyEq_of_mem {l i : ι} (h : ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ G.inner l i) :
    G.locCoef l (G.localSec i h) =ᶠ[𝓝 z]
      fun y => h (G.chart i ((G.chart l).symm y)) * G.trans l i y :=
  Filter.eventually_of_mem ((G.isOpen_inner l i).mem_nhds hz) fun _ hy =>
    G.locCoef_localSec_of_mem h hy

/-! ### Densities in the charts -/

theorem D_chart (i : ι) (u : (x : X) → V x) {z : ComplexModel n}
    (hz : z ∈ ball (G.center i) (G.R i)) :
    G.D u ((G.chart i).symm z) = ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z := by
  rw [D, G.density_eq i _ _ (G.symm_mem_source hz) (by rw [G.chart_symm hz]; exact hz),
    G.chart_symm hz]
  rfl

/-! ### Elementary inequalities -/

theorem norm_sum_sq_le_card_mul (f : ι → ℂ) :
    ‖∑ i, f i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i‖)
  calc ‖∑ i, f i‖ ^ 2 ≤ (∑ i, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa using h2

theorem χ_le_one (i : ι) (x : X) : G.χ i x ≤ 1 := by
  have h := G.sum_χ x
  have : G.χ i x ≤ ∑ j, G.χ j x :=
    Finset.single_le_sum (f := fun j => G.χ j x) (fun j _ => G.χ_nonneg j x) (Finset.mem_univ i)
  linarith

theorem χ_eq_zero_of_not_mem {l i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l))
    (hzi : z ∉ G.inner l i) : G.χ i ((G.chart l).symm z) = 0 :=
  (G.eventually_χ_eq_zero hz hzi).self_of_nhds

theorem contDiffAt_χ {l i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l)) :
    ContDiffAt ℝ ∞ (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z
    ((G.χ_smooth i l).contDiffAt ((G.chart l).open_target.mem_nhds (G.ball_subset_target l hz)))

theorem differentiableAt_χ {l i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l)) :
    DifferentiableAt ℝ (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z :=
  (G.contDiffAt_χ hz).differentiableAt (by simp)

theorem dbarDir_χ_eq_zero_of_not_mem {l i : ι} {z : ComplexModel n}
    (hz : z ∈ ball (G.center l) (G.R l)) (hzi : z ∉ G.inner l i) (e : ComplexModel n) :
    dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z = 0 := by
  rw [dbarDir_congr (g := fun _ => (0 : ℂ))]
  · exact dbarDir_const 0 z
  · filter_upwards [G.eventually_χ_eq_zero hz hzi] with y hy
    rw [hy, Complex.ofReal_zero]

theorem dbarNormSq_χ_le {l i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l)) :
    dbarNormSq (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z ≤
      (G.inner l i).indicator (fun _ => G.M) z := by
  by_cases hzi : z ∈ G.inner l i
  · rw [indicator_of_mem hzi]; exact G.dbar_χ_le i l z hz
  · rw [indicator_of_notMem hzi]
    refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
    rw [G.dbarDir_χ_eq_zero_of_not_mem hz hzi, norm_zero]
    norm_num

/-- `∑_i ∂̄(χ_i ∘ z_l⁻¹) = 0`. -/
theorem sum_dbarDir_χ {l : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center l) (G.R l))
    (e : ComplexModel n) :
    ∑ i, dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z = 0 := by
  have hsum : (fun y => ∑ i, ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
    funext y
    rw [← Complex.ofReal_sum, G.sum_χ, Complex.ofReal_one]
  have key : ∀ s : Finset ι, dbarDir e (fun y => ∑ i ∈ s, ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z
      = ∑ i ∈ s, dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp [dbarDir_const]
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [dbarDir_add (G.differentiableAt_χ hz) (DifferentiableAt.fun_sum fun i _ =>
        G.differentiableAt_χ hz), ih]
  rw [← key Finset.univ, hsum, dbarDir_const]

/-! ### Terms of the glued section -/

/-- The term `(χ_i ∘ z_l⁻¹) · coef_l(h ∘ z_i · E_i)` is smooth on the `R_l`-ball and its `∂̄` is
`∂̄(χ_i ∘ z_l⁻¹) · coef_l(h ∘ z_i · E_i)`. -/
theorem term_spec {l i : ι} {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h (ball (G.center i) (G.r i))) {z : ComplexModel n}
    (hz : z ∈ ball (G.center l) (G.R l)) :
    ContDiffAt ℝ ∞ (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ) *
        G.locCoef l (G.localSec i h) y) z ∧
      ∀ e : ComplexModel n, dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ) *
        G.locCoef l (G.localSec i h) y) z =
        dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z *
          G.locCoef l (G.localSec i h) z := by
  by_cases hzi : z ∈ G.inner l i
  · set g : ComplexModel n → ℂ := fun y => h (G.chart i ((G.chart l).symm y)) * G.trans l i y
    have hg : DifferentiableOn ℂ g (G.inner l i) := G.differentiableOn_locCoef_localSec hh
    have hgC : ContDiffAt ℝ ∞ g z :=
      contDiffAt_real_of_differentiableOn_complex hg (G.isOpen_inner l i) hzi
    have heq : (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ) *
        G.locCoef l (G.localSec i h) y) =ᶠ[𝓝 z]
        fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ) * g y := by
      filter_upwards [G.locCoef_eventuallyEq_of_mem h hzi] with y hy
      rw [hy]
    refine ⟨((G.contDiffAt_χ hz).mul hgC).congr_of_eventuallyEq heq, fun e => ?_⟩
    rw [dbarDir_congr heq, dbarDir_mul (G.differentiableAt_χ hz) (hgC.differentiableAt (by simp)),
      dbarDir_eq_zero_of_differentiableAt
        (hg.differentiableAt ((G.isOpen_inner l i).mem_nhds hzi)), mul_zero, add_zero,
      G.locCoef_localSec_of_mem h hzi]
  · have heq : (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ) *
        G.locCoef l (G.localSec i h) y) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [G.eventually_χ_eq_zero hz hzi] with y hy
      rw [hy, Complex.ofReal_zero, zero_mul]
    refine ⟨contDiffAt_const.congr_of_eventuallyEq heq, fun e => ?_⟩
    rw [dbarDir_congr heq, dbarDir_const, G.dbarDir_χ_eq_zero_of_not_mem hz hzi, zero_mul]

theorem dbarDir_finset_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {κ : Type*}
    (s : Finset κ) {f : κ → E → ℂ} {z e : E} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbarDir e (fun y => ∑ i ∈ s, f i y) z = ∑ i ∈ s, dbarDir e (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dbarDir_const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Finset.forall_mem_insert] at hf
    rw [dbarDir_add hf.1 (DifferentiableAt.fun_sum fun i hi => hf.2 i hi), ih hf.2]

/-! ### Measurability -/

theorem aemeasurable_W (i : ι) : AEMeasurable (G.W i) (volume.restrict (ball (G.center i) (G.R i))) := by
  have hq : QuasiPlurisubharmonicOn (G.Ψ i) (ball (G.center i) (G.R i)) :=
    fun x hx => (G.Ψ_psh i x hx).quasiPlurisubharmonicAt
  have h := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
    (μ := volume) isOpen_ball hq one_ne_zero (f := fun _ => (1 : ℂ)) continuousOn_const
  have h' : AEMeasurable (fun z => multiplierWeight 1 (G.Ψ i z))
      (volume.restrict (ball (G.center i) (G.R i))) :=
    h.congr (Eventually.of_forall fun z => by simp [multiplierDensity])
  have hc : Continuous fun z : ComplexModel n => G.lam * ‖z - G.center i‖ ^ 2 := by fun_prop
  refine (h'.mul ((ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
    hc.neg.aemeasurable)).congr ?_
  refine (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_)
  exact (ballWeight_eq_mul ((G.Ψ_psh i z hz).ne_top) G.lam (G.center i)).symm

theorem aemeasurable_indicator_inner {l i : ι} {F : ComplexModel n → ℂ}
    (hF : ContinuousOn F (G.inner l i)) :
    AEMeasurable ((G.inner l i).indicator fun z => ENNReal.ofReal (‖F z‖ ^ 2) * G.W l z)
      (volume.restrict (ball (G.center l) (G.R l))) := by
  have hm : MeasurableSet (G.inner l i) := (G.isOpen_inner l i).measurableSet
  refine (aemeasurable_indicator_iff hm).mpr ?_
  rw [Measure.restrict_restrict hm, inter_eq_left.mpr (fun z hz => hz.1)]
  refine (ENNReal.measurable_ofReal.comp_aemeasurable
    ((hF.aestronglyMeasurable hm).norm.aemeasurable.pow_const 2)).mul ?_
  exact (G.aemeasurable_W l).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)

/-! ### Transfer of integrals between the charts and `X` -/

theorem indicator_inner_eq {l i : ι} (u : (x : X) → V x) {z : ComplexModel n}
    (hz : z ∈ ball (G.center l) (G.R l)) :
    (G.inner l i).indicator (fun z => ENNReal.ofReal (‖G.locCoef l u z‖ ^ 2) * G.W l z) z =
      (G.small i).indicator (G.D u) ((G.chart l).symm z) := by
  by_cases hzi : z ∈ G.inner l i
  · rw [indicator_of_mem hzi, indicator_of_mem (show (G.chart l).symm z ∈ G.small i from hzi.2),
      G.D_chart l u hz]
  · have : (G.chart l).symm z ∉ G.small i := fun h => hzi ⟨hz, h⟩
    rw [indicator_of_notMem hzi, indicator_of_notMem this]

/-- **(T1)** An integral over the part of the `R_l`-ball lying in the middle region of chart `i`
is controlled by the integral over that region. -/
theorem lintegral_inner_le (l i : ι) (u : (x : X) → V x)
    (hu : ContinuousOn (G.locCoef l u) (G.inner l i)) :
    ∫⁻ z in ball (G.center l) (G.R l),
        (G.inner l i).indicator (fun z => ENNReal.ofReal (‖G.locCoef l u z‖ ^ 2) * G.W l z) z ≤
      G.A * ∫⁻ x in G.small i, G.D u x ∂μ := by
  calc ∫⁻ z in ball (G.center l) (G.R l),
        (G.inner l i).indicator (fun z => ENNReal.ofReal (‖G.locCoef l u z‖ ^ 2) * G.W l z) z
      ≤ ∫⁻ z in ball (G.center l) (G.R l),
          G.A * ((G.small i).indicator (G.D u) ((G.chart l).symm z) * G.dens l z) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        rw [G.indicator_inner_eq u hz]
        calc (G.small i).indicator (G.D u) ((G.chart l).symm z)
            = 1 * (G.small i).indicator (G.D u) ((G.chart l).symm z) := (one_mul _).symm
          _ ≤ (G.A * G.dens l z) * (G.small i).indicator (G.D u) ((G.chart l).symm z) :=
              mul_le_mul_of_nonneg_right (G.one_le_A_mul_dens l z hz) zero_le
          _ = _ := by ring
    _ = G.A * ∫⁻ x in G.region l, (G.small i).indicator (G.D u) x ∂μ := by
        rw [lintegral_const_mul' _ _ G.A_ne_top, region, G.map_measure l _ ?_]
        refine (G.aemeasurable_indicator_inner hu).congr ?_
        exact (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz =>
          G.indicator_inner_eq u hz)
    _ ≤ G.A * ∫⁻ x, (G.small i).indicator (G.D u) x ∂μ :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
    _ = G.A * ∫⁻ x in G.small i, G.D u x ∂μ := by
        rw [lintegral_indicator (G.isOpen_small i).measurableSet]

theorem symm_mem_small_iff {i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center i) (G.R i)) :
    (G.chart i).symm z ∈ G.small i ↔ z ∈ ball (G.center i) (G.r i) := by
  constructor
  · intro h; have := h.2; rwa [mem_preimage, G.chart_symm hz] at this
  · intro h; exact ⟨G.symm_mem_source hz, by rw [mem_preimage, G.chart_symm hz]; exact h⟩

theorem indicator_small_eq {i : ι} (u : (x : X) → V x) {z : ComplexModel n}
    (hz : z ∈ ball (G.center i) (G.R i)) :
    (G.small i).indicator (G.D u) ((G.chart i).symm z) =
      (ball (G.center i) (G.r i)).indicator
        (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) z := by
  by_cases hzr : z ∈ ball (G.center i) (G.r i)
  · rw [indicator_of_mem ((G.symm_mem_small_iff hz).mpr hzr), indicator_of_mem hzr,
      G.D_chart i u hz]
  · rw [indicator_of_notMem (fun h => hzr ((G.symm_mem_small_iff hz).mp h)),
      indicator_of_notMem hzr]

theorem aemeasurable_indicator_ball {i : ι} {F : ComplexModel n → ℂ}
    (hF : ContinuousOn F (ball (G.center i) (G.r i))) :
    AEMeasurable ((ball (G.center i) (G.r i)).indicator
        fun z => ENNReal.ofReal (‖F z‖ ^ 2) * G.W i z)
      (volume.restrict (ball (G.center i) (G.R i))) := by
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  refine (aemeasurable_indicator_iff measurableSet_ball).mpr ?_
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hrR]
  refine (ENNReal.measurable_ofReal.comp_aemeasurable
    ((hF.aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const 2)).mul ?_
  exact (G.aemeasurable_W i).mono_measure (Measure.restrict_mono hrR le_rfl)

/-- **(T2)** The integral over the middle region of chart `i`, in the coordinates of chart `i`. -/
theorem lintegral_small_le (i : ι) (u : (x : X) → V x)
    (hu : ContinuousOn (G.locCoef i u) (ball (G.center i) (G.r i))) :
    ∫⁻ x in G.small i, G.D u x ∂μ ≤
      G.A * ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z := by
  have hsm : MeasurableSet (G.small i) := (G.isOpen_small i).measurableSet
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  calc ∫⁻ x in G.small i, G.D u x ∂μ
      = ∫⁻ x in G.region i, (G.small i).indicator (G.D u) x ∂μ := by
        rw [lintegral_indicator hsm, Measure.restrict_restrict hsm,
          inter_eq_left.mpr (G.small_subset_region i)]
    _ = ∫⁻ z in ball (G.center i) (G.R i),
          (G.small i).indicator (G.D u) ((G.chart i).symm z) * G.dens i z := by
        rw [region, G.map_measure i _ ?_]
        refine (G.aemeasurable_indicator_ball hu).congr ?_
        exact (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz =>
          (G.indicator_small_eq u hz).symm)
    _ ≤ ∫⁻ z in ball (G.center i) (G.R i), G.A * (ball (G.center i) (G.r i)).indicator
          (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have hiff : (G.chart i).symm z ∈ G.small i ↔ z ∈ ball (G.center i) (G.r i) := by
          constructor
          · intro h; have := h.2; rwa [mem_preimage, G.chart_symm hz] at this
          · intro h; exact ⟨G.symm_mem_source hz, by rw [mem_preimage, G.chart_symm hz]; exact h⟩
        by_cases hzr : z ∈ ball (G.center i) (G.r i)
        · rw [indicator_of_mem (hiff.mpr hzr), indicator_of_mem hzr, G.D_chart i u hz, mul_comm]
          exact mul_le_mul_of_nonneg_right (G.dens_le i z hz) zero_le
        · rw [indicator_of_notMem (fun h => hzr (hiff.mp h)), zero_mul]
          exact zero_le
    _ = G.A * ∫⁻ z in ball (G.center i) (G.r i),
          ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z := by
        rw [lintegral_const_mul' _ _ G.A_ne_top, lintegral_indicator measurableSet_ball,
          Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hrR]

/-! ### The Neumann step -/

theorem r_pos (i : ι) : 0 < G.r i := (G.r'_pos i).trans (G.r'_lt_r i)

open Classical in
/-- The local correction in chart `i` (`localBallCorrection`), or `0` if the coefficient of `v`
is not smooth. -/
def stepCoef (v : (x : X) → V x) (i : ι) : ComplexModel n → ℂ :=
  if h : ContDiffOn ℝ ∞ (G.locCoef i v) (ball (G.center i) (G.R i)) then
    Classical.choose (localBallCorrection (G.center i) (G.r i) (G.R i) (G.r_pos i) (G.r_lt_R i)
      G.lam G.lam_pos (G.Ψ i) (G.Ψ_psh i) (G.locCoef i v) h)
  else fun _ => 0

theorem differentiableOn_stepCoef (v : (x : X) → V x) (i : ι) :
    DifferentiableOn ℂ (G.stepCoef v i) (ball (G.center i) (G.r i)) := by
  unfold stepCoef
  split_ifs with h
  · exact (Classical.choose_spec (localBallCorrection (G.center i) (G.r i) (G.R i) (G.r_pos i)
      (G.r_lt_R i) G.lam G.lam_pos (G.Ψ i) (G.Ψ_psh i) (G.locCoef i v) h)).1
  · exact differentiableOn_const 0

theorem stepCoef_le {v : (x : X) → V x} (hv : G.IsSmooth v) (i : ι) :
    ∫⁻ z in ball (G.center i) (G.r i),
        ENNReal.ofReal (‖G.locCoef i v z - G.stepCoef v i z‖ ^ 2) * G.W i z ≤
      ENNReal.ofReal (2 / G.lam) * G.energy i v := by
  unfold stepCoef
  rw [dif_pos (hv i)]
  exact (Classical.choose_spec (localBallCorrection (G.center i) (G.r i) (G.R i) (G.r_pos i)
      (G.r_lt_R i) G.lam G.lam_pos (G.Ψ i) (G.Ψ_psh i) (G.locCoef i v) (hv i))).2

/-- The Neumann step: glue the local corrections with the partition of unity. -/
def next (v : (x : X) → V x) (x : X) : V x :=
  ∑ i, ((G.χ i x : ℝ) : ℂ) • G.localSec i (G.stepCoef v i) x

theorem locCoef_next (v : (x : X) → V x) (l : ι) :
    G.locCoef l (G.next v) = fun z => ∑ i, ((G.χ i ((G.chart l).symm z) : ℝ) : ℂ) *
      G.locCoef l (G.localSec i (G.stepCoef v i)) z := by
  funext z
  simp only [locCoef, next, map_sum, map_smul, smul_eq_mul]

/-- The glued section is smooth for the system. -/
theorem isSmooth_next (v : (x : X) → V x) : G.IsSmooth (G.next v) := by
  intro l
  rw [G.locCoef_next v l]
  intro z hz
  exact (ContDiffAt.sum fun i _ =>
    (G.term_spec (G.differentiableOn_stepCoef v i) hz).1).contDiffWithinAt

/-- The `∂̄` of the glued section: `∂̄ v' = ∑ ∂̄(χ_i ∘ z_l⁻¹) (coef_l(H_i) - coef_l(v))`. -/
theorem dbarDir_locCoef_next (v : (x : X) → V x) {l : ι} {z : ComplexModel n}
    (hz : z ∈ ball (G.center l) (G.R l)) (e : ComplexModel n) :
    dbarDir e (G.locCoef l (G.next v)) z =
      ∑ i, dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z *
        G.locCoef l (fun x => G.localSec i (G.stepCoef v i) x - v x) z := by
  rw [G.locCoef_next v l, dbarDir_finset_sum _ fun i _ =>
    ((G.term_spec (G.differentiableOn_stepCoef v i) hz).1).differentiableAt (by simp)]
  have h0 : ∑ i, dbarDir e (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z *
      G.locCoef l v z = 0 := by
    rw [← Finset.sum_mul, G.sum_dbarDir_χ hz e, zero_mul]
  simp only [G.locCoef_sub, mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
  exact Finset.sum_congr rfl fun i _ => (G.term_spec (G.differentiableOn_stepCoef v i) hz).2 e

/-- Pointwise bound for the `∂̄`-energy density of the glued section. -/
theorem dbarNormSq_next_le (v : (x : X) → V x) {l : ι} {z : ComplexModel n}
    (hz : z ∈ ball (G.center l) (G.R l)) :
    ENNReal.ofReal (dbarNormSq (G.locCoef l (G.next v)) z) * G.W l z ≤
      ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
        (G.inner l i).indicator (fun z => ENNReal.ofReal
          (‖G.locCoef l (fun x => G.localSec i (G.stepCoef v i) x - v x) z‖ ^ 2) * G.W l z) z := by
  set b : ι → ℂ := fun i => G.locCoef l (fun x => G.localSec i (G.stepCoef v i) x - v x) z
  set a : ι → Fin n → ℂ := fun i m =>
    dbarDir (coordVec m) (fun y => ((G.χ i ((G.chart l).symm y) : ℝ) : ℂ)) z
  have hM0 : 0 ≤ G.M := le_trans (dbarNormSq_nonneg _ z) (G.dbar_χ_le (G.cover ((G.chart l).symm z)).choose l z hz)
  have hpt : dbarNormSq (G.locCoef l (G.next v)) z ≤
      ∑ i, (Fintype.card ι : ℝ) * G.M * (G.inner l i).indicator (fun _ => ‖b i‖ ^ 2) z := by
    calc dbarNormSq (G.locCoef l (G.next v)) z
        = ∑ m, ‖∑ i, a i m * b i‖ ^ 2 := by
          unfold dbarNormSq
          exact Finset.sum_congr rfl fun m _ => by rw [G.dbarDir_locCoef_next v hz]
      _ ≤ ∑ m, (Fintype.card ι : ℝ) * ∑ i, ‖a i m‖ ^ 2 * ‖b i‖ ^ 2 := by
          refine Finset.sum_le_sum fun m _ => (norm_sum_sq_le_card_mul _).trans (le_of_eq ?_)
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
  calc ENNReal.ofReal (dbarNormSq (G.locCoef l (G.next v)) z) * G.W l z
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

/-! ### The step estimates -/

theorem continuousOn_locCoef_localSec_sub {v : (x : X) → V x} (hv : G.IsSmooth v) (l i : ι) :
    ContinuousOn (G.locCoef l (fun x => G.localSec i (G.stepCoef v i) x - v x)) (G.inner l i) := by
  rw [G.locCoef_sub]
  refine ContinuousOn.sub ?_ ((hv l).continuousOn.mono fun z hz => hz.1)
  refine ((G.differentiableOn_locCoef_localSec (G.differentiableOn_stepCoef v i)).continuousOn).congr
    fun z hz => G.locCoef_localSec_of_mem _ hz

/-- The local error of the correction in chart `i`, as an integral over the middle region. -/
theorem lintegral_small_localSec_le {v : (x : X) → V x} (hv : G.IsSmooth v) (i : ι) :
    ∫⁻ x in G.small i, G.D (fun x => G.localSec i (G.stepCoef v i) x - v x) x ∂μ ≤
      G.A * (ENNReal.ofReal (2 / G.lam) * G.energy i v) := by
  have hcont : ContinuousOn (G.locCoef i (fun x => G.localSec i (G.stepCoef v i) x - v x))
      (ball (G.center i) (G.r i)) := by
    rw [G.locCoef_sub]
    refine ((G.differentiableOn_stepCoef v i).continuousOn.sub ((hv i).continuousOn.mono
      (ball_subset_ball (G.r_lt_R i).le))).congr fun z hz => ?_
    simp only [G.locCoef_localSec_self _ hz]
    rfl
  refine (G.lintegral_small_le i _ hcont).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
  refine le_trans (le_of_eq ?_) (G.stepCoef_le hv i)
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [G.locCoef_sub, norm_sub_rev, G.locCoef_localSec_self _ hz]

/-- **Energy contraction**, chartwise (`claude-global-l2:gluing-step`). -/
theorem energy_next_le {v : (x : X) → V x} (hv : G.IsSmooth v) (l : ι) :
    G.energy l (G.next v) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
      ∑ i, G.A * (G.A * (ENNReal.ofReal (2 / G.lam) * G.energy i v)) := by
  calc G.energy l (G.next v)
      ≤ ∫⁻ z in ball (G.center l) (G.R l), ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef l (fun x => G.localSec i (G.stepCoef v i) x - v x) z‖ ^ 2) * G.W l z) z :=
        setLIntegral_mono' measurableSet_ball fun z hz => G.dbarNormSq_next_le v hz
    _ = ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          ∫⁻ z in ball (G.center l) (G.R l), (G.inner l i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef l (fun x => G.localSec i (G.stepCoef v i) x - v x) z‖ ^ 2) * G.W l z) z := by
        rw [lintegral_finsetSum' _ fun i _ =>
          (G.aemeasurable_indicator_inner (G.continuousOn_locCoef_localSec_sub hv l i)).const_mul _]
        exact Finset.sum_congr rfl fun i _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ i, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
          (G.A * (G.A * (ENNReal.ofReal (2 / G.lam) * G.energy i v))) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ zero_le
        exact (G.lintegral_inner_le l i _ (G.continuousOn_locCoef_localSec_sub hv l i)).trans
          (mul_le_mul_of_nonneg_left (G.lintegral_small_localSec_le hv i) zero_le)
    _ = _ := by rw [Finset.mul_sum]

/-- The contraction factor of one Neumann step. -/
def kappa : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
    (G.A * (G.A * ENNReal.ofReal (2 / G.lam))))

theorem sum_A_A_energy (v : (x : X) → V x) :
    ∑ i, G.A * (G.A * (ENNReal.ofReal (2 / G.lam) * G.energy i v)) =
      G.A * (G.A * ENNReal.ofReal (2 / G.lam)) * G.totalEnergy v := by
  rw [totalEnergy, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Energy contraction** (`claude-global-l2:gluing-step`). -/
theorem totalEnergy_next_le {v : (x : X) → V x} (hv : G.IsSmooth v) :
    G.totalEnergy (G.next v) ≤ G.kappa * G.totalEnergy v := by
  calc G.totalEnergy (G.next v) ≤ ∑ _l : ι, ENNReal.ofReal ((Fintype.card ι : ℝ) * G.M) *
        (G.A * (G.A * ENNReal.ofReal (2 / G.lam)) * G.totalEnergy v) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← G.sum_A_A_energy v]
        exact G.energy_next_le hv l
    _ = G.kappa * G.totalEnergy v := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, kappa]
        ring

/-- The size of one Neumann step, in every chart. -/
theorem lintegral_sub_next_le {v : (x : X) → V x} (hv : G.IsSmooth v) (j : ι) :
    ∫⁻ z in ball (G.center j) (G.R j),
        ENNReal.ofReal (‖G.locCoef j (fun x => v x - G.next v x) z‖ ^ 2) * G.W j z ≤
      (Fintype.card ι : ℝ≥0∞) * (G.A * (G.A * ENNReal.ofReal (2 / G.lam))) * G.totalEnergy v := by
  have hpt : ∀ z ∈ ball (G.center j) (G.R j),
      ENNReal.ofReal (‖G.locCoef j (fun x => v x - G.next v x) z‖ ^ 2) * G.W j z ≤
        ∑ i, (Fintype.card ι : ℝ≥0∞) * (G.inner j i).indicator (fun z => ENNReal.ofReal
          (‖G.locCoef j (fun x => G.localSec i (G.stepCoef v i) x - v x) z‖ ^ 2) * G.W j z) z := by
    intro z hz
    set b : ι → ℂ := fun i => G.locCoef j (fun x => G.localSec i (G.stepCoef v i) x - v x) z
    have hsum : G.locCoef j (fun x => v x - G.next v x) z =
        ∑ i, ((G.χ i ((G.chart j).symm z) : ℝ) : ℂ) * (-b i) := by
      have h1 : G.locCoef j v z = ∑ i, ((G.χ i ((G.chart j).symm z) : ℝ) : ℂ) * G.locCoef j v z := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, G.sum_χ, Complex.ofReal_one, one_mul]
      rw [G.locCoef_sub, G.locCoef_next]
      dsimp only
      rw [h1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [b, G.locCoef_sub]
      ring
    have hle : ‖G.locCoef j (fun x => v x - G.next v x) z‖ ^ 2 ≤
        ∑ i, (Fintype.card ι : ℝ) * (G.inner j i).indicator (fun _ => ‖b i‖ ^ 2) z := by
      rw [hsum, ← Finset.mul_sum]
      refine (norm_sum_sq_le_card_mul _).trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
      rw [norm_mul, mul_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      by_cases hzi : z ∈ G.inner j i
      · rw [indicator_of_mem hzi]
        have h0 := G.χ_nonneg i ((G.chart j).symm z)
        have h1 := G.χ_le_one i ((G.chart j).symm z)
        have : G.χ i ((G.chart j).symm z) ^ 2 ≤ 1 := by nlinarith
        exact (mul_le_of_le_one_left (sq_nonneg _) this)
      · rw [indicator_of_notMem hzi, G.χ_eq_zero_of_not_mem hz hzi]
        simp
    calc ENNReal.ofReal (‖G.locCoef j (fun x => v x - G.next v x) z‖ ^ 2) * G.W j z
        ≤ ENNReal.ofReal (∑ i, (Fintype.card ι : ℝ) *
            (G.inner j i).indicator (fun _ => ‖b i‖ ^ 2) z) * G.W j z :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle) zero_le
      _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _)
            (indicator_nonneg (fun _ _ => sq_nonneg _) z)), Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hzi : z ∈ G.inner j i
          · rw [indicator_of_mem hzi, indicator_of_mem hzi, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast, mul_assoc]
          · rw [indicator_of_notMem hzi, indicator_of_notMem hzi, mul_zero, ENNReal.ofReal_zero,
              zero_mul, mul_zero]
  calc ∫⁻ z in ball (G.center j) (G.R j),
        ENNReal.ofReal (‖G.locCoef j (fun x => v x - G.next v x) z‖ ^ 2) * G.W j z
      ≤ ∫⁻ z in ball (G.center j) (G.R j), ∑ i, (Fintype.card ι : ℝ≥0∞) *
          (G.inner j i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef j (fun x => G.localSec i (G.stepCoef v i) x - v x) z‖ ^ 2) * G.W j z) z :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ∑ i, (Fintype.card ι : ℝ≥0∞) * ∫⁻ z in ball (G.center j) (G.R j),
          (G.inner j i).indicator (fun z => ENNReal.ofReal
            (‖G.locCoef j (fun x => G.localSec i (G.stepCoef v i) x - v x) z‖ ^ 2) * G.W j z) z := by
        rw [lintegral_finsetSum' _ fun i _ =>
          (G.aemeasurable_indicator_inner (G.continuousOn_locCoef_localSec_sub hv j i)).const_mul _]
        exact Finset.sum_congr rfl fun i _ => lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
    _ ≤ ∑ i, (Fintype.card ι : ℝ≥0∞) * (G.A * (G.A * (ENNReal.ofReal (2 / G.lam) * G.energy i v))) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ zero_le
        exact (G.lintegral_inner_le j i _ (G.continuousOn_locCoef_localSec_sub hv j i)).trans
          (mul_le_mul_of_nonneg_left (G.lintegral_small_localSec_le hv i) zero_le)
    _ = _ := by rw [← Finset.mul_sum, G.sum_A_A_energy v]; ring

/-! ### Telescoping -/

omit [OpensMeasurableSpace X] in
theorem norm_telescope_sq_le (f : ℕ → ℂ) (m k : ℕ) :
    ‖f m - f (m + k)‖ ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ m) *
      ∑ j ∈ Finset.range k, (2 : ℝ) ^ (m + j) * ‖f (m + j) - f (m + j + 1)‖ ^ 2 := by
  have htel : f m - f (m + k) = ∑ j ∈ Finset.range k, (f (m + j) - f (m + j + 1)) := by
    have := Finset.sum_range_sub' (fun j => f (m + j)) k
    simp only [add_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [add_assoc]
  have h1 : ‖f m - f (m + k)‖ ≤ ∑ j ∈ Finset.range k, ‖f (m + j) - f (m + j + 1)‖ := by
    rw [htel]; exact norm_sum_le _ _
  have h2 : (∑ j ∈ Finset.range k, ‖f (m + j) - f (m + j + 1)‖) ^ 2 ≤
      (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j)) *
        ∑ j ∈ Finset.range k, (2 : ℝ) ^ (m + j) * ‖f (m + j) - f (m + j + 1)‖ ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => by positivity)
      (fun j _ => by positivity) fun j _ => le_of_eq ?_
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have h3 : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j) ≤ 2 * (1 / 2 : ℝ) ^ m := by
    have : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j) =
        (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le k) (by positivity)
  calc ‖f m - f (m + k)‖ ^ 2 ≤ (∑ j ∈ Finset.range k, ‖f (m + j) - f (m + j + 1)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2.trans (mul_le_mul_of_nonneg_right h3 (Finset.sum_nonneg fun j _ => by positivity))

omit [OpensMeasurableSpace X] in
/-- **Telescoping**: geometric decay of the steps gives geometric decay of the tails. -/
theorem lintegral_telescope_le {U : Set (ComplexModel n)} {Wt : ComplexModel n → ℝ≥0∞}
    (hW : AEMeasurable Wt (volume.restrict U)) {f : ℕ → ComplexModel n → ℂ}
    (hf : ∀ m, AEStronglyMeasurable (f m) (volume.restrict U)) {B : ℝ≥0∞}
    (h : ∀ m, ∫⁻ z in U, ENNReal.ofReal (‖f m z - f (m + 1) z‖ ^ 2) * Wt z ≤
      B * ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) (m k : ℕ) :
    ∫⁻ z in U, ENNReal.ofReal (‖f m z - f (m + k) z‖ ^ 2) * Wt z ≤
      B * ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ m) := by
  have hmeas : ∀ j, AEMeasurable (fun z => ENNReal.ofReal (‖f j z - f (j + 1) z‖ ^ 2) * Wt z)
      (volume.restrict U) := fun j =>
    (ENNReal.measurable_ofReal.comp_aemeasurable (((hf j).sub (hf (j + 1))).norm.aemeasurable.pow_const
      2)).mul hW
  calc ∫⁻ z in U, ENNReal.ofReal (‖f m z - f (m + k) z‖ ^ 2) * Wt z
      ≤ ∫⁻ z in U, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m) * ∑ j ∈ Finset.range k,
          ENNReal.ofReal ((2 : ℝ) ^ (m + j)) *
            (ENNReal.ofReal (‖f (m + j) z - f (m + j + 1) z‖ ^ 2) * Wt z) := by
        refine lintegral_mono fun z => ?_
        have hpt := norm_telescope_sq_le (fun j => f j z) m k
        calc ENNReal.ofReal (‖f m z - f (m + k) z‖ ^ 2) * Wt z
            ≤ ENNReal.ofReal ((2 * (1 / 2 : ℝ) ^ m) * ∑ j ∈ Finset.range k,
                (2 : ℝ) ^ (m + j) * ‖f (m + j) z - f (m + j + 1) z‖ ^ 2) * Wt z :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpt) zero_le
          _ = _ := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
                (fun j _ => by positivity), mul_assoc, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m) * ∑ j ∈ Finset.range k,
          ENNReal.ofReal ((2 : ℝ) ^ (m + j)) *
            ∫⁻ z in U, ENNReal.ofReal (‖f (m + j) z - f (m + j + 1) z‖ ^ 2) * Wt z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _ fun j _ =>
          (hmeas (m + j)).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun j _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m) * ∑ j ∈ Finset.range k,
          B * ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + j)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) zero_le
        calc ENNReal.ofReal ((2 : ℝ) ^ (m + j)) *
              ∫⁻ z in U, ENNReal.ofReal (‖f (m + j) z - f (m + j + 1) z‖ ^ 2) * Wt z
            ≤ ENNReal.ofReal ((2 : ℝ) ^ (m + j)) * (B * ENNReal.ofReal ((1 / 4 : ℝ) ^ (m + j))) :=
              mul_le_mul_of_nonneg_left (h (m + j)) zero_le
          _ = B * ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + j)) := by
              rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
              norm_num
    _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m) * (B * ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m)) := by
        rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal ?_) zero_le) zero_le
        have : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j) =
            (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
        rw [this, mul_comm]
        exact mul_le_mul_of_nonneg_right (sum_geometric_two_le k) (by positivity)
    _ = B * ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ m) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [show (4 : ℝ) * (1 / 4) ^ m = (2 * (1 / 2) ^ m) * (2 * (1 / 2) ^ m) by
          rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, mul_pow]; ring]

/-! ### The iteration -/

/-- The Neumann iterates `v_m = next^m v₀`. -/
def iter (v₀ : (x : X) → V x) (m : ℕ) : (x : X) → V x := G.next^[m] v₀

theorem iter_succ (v₀ : (x : X) → V x) (m : ℕ) : G.iter v₀ (m + 1) = G.next (G.iter v₀ m) := by
  simp only [iter, Function.iterate_succ_apply']

theorem isSmooth_iter {v₀ : (x : X) → V x} (hv : G.IsSmooth v₀) (m : ℕ) :
    G.IsSmooth (G.iter v₀ m) := by
  cases m with
  | zero => exact hv
  | succ m => rw [iter_succ]; exact G.isSmooth_next _

theorem totalEnergy_iter_le (hκ : G.kappa ≤ ENNReal.ofReal (1 / 4)) {v₀ : (x : X) → V x}
    (hv : G.IsSmooth v₀) (m : ℕ) :
    G.totalEnergy (G.iter v₀ m) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ m) * G.totalEnergy v₀ := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    rw [iter_succ]
    calc G.totalEnergy (G.next (G.iter v₀ m)) ≤ G.kappa * G.totalEnergy (G.iter v₀ m) :=
          G.totalEnergy_next_le (G.isSmooth_iter hv m)
      _ ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal ((1 / 4 : ℝ) ^ m) * G.totalEnergy v₀) :=
          mul_le_mul' hκ ih
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), pow_succ, mul_comm ((1 / 4 : ℝ) ^ m)]

/-! ### Auxiliary facts for the limit -/

omit [OpensMeasurableSpace X] in
theorem norm_sub_sq_le_two (a b c : ℂ) : ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a b c
  nlinarith [norm_nonneg (a - c), norm_nonneg (a - b), norm_nonneg (b - c),
    sq_nonneg (‖a - b‖ - ‖b - c‖)]

omit [OpensMeasurableSpace X] in
/-- `∫ |a - c|² W ≤ 2 ∫ |a - b|² W + 2 ∫ |b - c|² W`. -/
theorem lintegral_sub_sq_le_two {U : Set (ComplexModel n)} {Wt : ComplexModel n → ℝ≥0∞}
    (hW : AEMeasurable Wt (volume.restrict U)) {a b c : ComplexModel n → ℂ}
    (hb : AEStronglyMeasurable (fun z => b z - c z) (volume.restrict U)) :
    ∫⁻ z in U, ENNReal.ofReal (‖a z - c z‖ ^ 2) * Wt z ≤
      2 * (∫⁻ z in U, ENNReal.ofReal (‖a z - b z‖ ^ 2) * Wt z) +
        2 * ∫⁻ z in U, ENNReal.ofReal (‖b z - c z‖ ^ 2) * Wt z := by
  have hm : AEMeasurable (fun z => 2 * (ENNReal.ofReal (‖b z - c z‖ ^ 2) * Wt z))
      (volume.restrict U) :=
    ((ENNReal.measurable_ofReal.comp_aemeasurable (hb.norm.aemeasurable.pow_const 2)).mul hW).const_mul _
  calc ∫⁻ z in U, ENNReal.ofReal (‖a z - c z‖ ^ 2) * Wt z
      ≤ ∫⁻ z in U, (2 * (ENNReal.ofReal (‖a z - b z‖ ^ 2) * Wt z) +
          2 * (ENNReal.ofReal (‖b z - c z‖ ^ 2) * Wt z)) := by
        refine lintegral_mono fun z => ?_
        have h1 : ENNReal.ofReal (‖a z - c z‖ ^ 2) ≤
            2 * ENNReal.ofReal (‖a z - b z‖ ^ 2) + 2 * ENNReal.ofReal (‖b z - c z‖ ^ 2) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          exact ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two _ _ _)
        calc ENNReal.ofReal (‖a z - c z‖ ^ 2) * Wt z
            ≤ (2 * ENNReal.ofReal (‖a z - b z‖ ^ 2) + 2 * ENNReal.ofReal (‖b z - c z‖ ^ 2)) * Wt z :=
              mul_le_mul_of_nonneg_right h1 zero_le
          _ = _ := by ring
    _ = _ := by
        rw [lintegral_add_right' _ hm, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]

omit [OpensMeasurableSpace X] in
/-- Fatou's lemma for pointwise limits of the approximants. -/
theorem lintegral_le_of_tendsto {U : Set (ComplexModel n)} (hU : MeasurableSet U)
    {Wt : ComplexModel n → ℝ≥0∞} (hW : AEMeasurable Wt (volume.restrict U))
    {a G : ComplexModel n → ℂ} {F : ℕ → ComplexModel n → ℂ}
    (hF : ∀ k, AEStronglyMeasurable (fun z => a z - F k z) (volume.restrict U))
    (hlim : ∀ z ∈ U, Tendsto (fun k => F k z) atTop (𝓝 (G z))) {β : ℝ≥0∞}
    (hb : ∀ᶠ k in atTop, ∫⁻ z in U, ENNReal.ofReal (‖a z - F k z‖ ^ 2) * Wt z ≤ β) :
    ∫⁻ z in U, ENNReal.ofReal (‖a z - G z‖ ^ 2) * Wt z ≤ β := by
  have hmeas : ∀ k, AEMeasurable (fun z => ENNReal.ofReal (‖a z - F k z‖ ^ 2) * Wt z)
      (volume.restrict U) := fun k =>
    (ENNReal.measurable_ofReal.comp_aemeasurable ((hF k).norm.aemeasurable.pow_const 2)).mul hW
  calc ∫⁻ z in U, ENNReal.ofReal (‖a z - G z‖ ^ 2) * Wt z
      ≤ ∫⁻ z in U, liminf (fun k => ENNReal.ofReal (‖a z - F k z‖ ^ 2) * Wt z) atTop := by
        refine setLIntegral_mono' hU fun z hz => ?_
        have ht : Tendsto (fun k => ENNReal.ofReal (‖a z - F k z‖ ^ 2)) atTop
            (𝓝 (ENNReal.ofReal (‖a z - G z‖ ^ 2))) :=
          ENNReal.tendsto_ofReal (((tendsto_const_nhds.sub (hlim z hz)).norm).pow 2)
        by_cases h0 : ENNReal.ofReal (‖a z - G z‖ ^ 2) = 0
        · rw [h0, zero_mul]; exact zero_le
        · exact ((ENNReal.Tendsto.mul_const ht (Or.inl h0)).liminf_eq).ge
    _ ≤ liminf (fun k => ∫⁻ z in U, ENNReal.ofReal (‖a z - F k z‖ ^ 2) * Wt z) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ β := liminf_le_of_frequently_le' hb.frequently

theorem W_ne_zero {i : ι} {z : ComplexModel n} (hz : z ∈ ball (G.center i) (G.R i)) :
    G.W i z ≠ 0 := by
  rw [W, ballWeight_eq_mul ((G.Ψ_psh i z hz).ne_top) G.lam (G.center i)]
  refine mul_ne_zero ?_ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  rw [multiplierWeight, Ne, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff, EReal.coe_one, one_mul]
  exact (G.Ψ_psh i z hz).ne_top

/-- The weight is bounded below by positive constants near every point. -/
theorem W_locally_ge {i : ι} {x : ComplexModel n} (hx : x ∈ ball (G.center i) (G.R i)) :
    ∃ ρ > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ y ∈ ball x ρ, ENNReal.ofReal δ ≤ G.W i y := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
  obtain ⟨B, hB0, hB⟩ := (G.Ψ_psh i).exists_nonnegative_compact_upper_bound
    (isCompact_closedBall x (ρ₀ / 2)) ((closedBall_subset_ball (by linarith)).trans hball)
  have hlam := G.lam_pos
  refine ⟨ρ₀ / 2, by positivity, Real.exp (-(B + G.lam * G.R i ^ 2)), Real.exp_pos _, ?_,
    fun y hy => ?_⟩
  · rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hyR : y ∈ ball (G.center i) (G.R i) := hball (ball_subset_ball (by linarith) hy)
  have hyz : ‖y - G.center i‖ ^ 2 ≤ G.R i ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mem_ball_iff_norm.mp hyR).le 2
  have hle : G.Ψ i y + ((G.lam * ‖y - G.center i‖ ^ 2 : ℝ) : EReal) ≤
      ((B + G.lam * G.R i ^ 2 : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add (hB y (ball_subset_closedBall hy))
      (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hyz hlam.le))
  calc ENNReal.ofReal (Real.exp (-(B + G.lam * G.R i ^ 2)))
      = multiplierWeight 1 ((B + G.lam * G.R i ^ 2 : ℝ) : EReal) := by
        rw [multiplierWeight_coe, one_mul]
    _ ≤ G.W i y := multiplierWeight_antitone zero_le_one hle

/-! ### The limit -/

/-- The constant of one step in the coefficients. -/
def cDiff : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (G.A * (G.A * ENNReal.ofReal (2 / G.lam)))

/-- The constant of the final estimate. -/
def K₀ (v₀ : (x : X) → V x) : ℝ≥0∞ :=
  8 * (G.cDiff * G.totalEnergy v₀) + 2 * (ENNReal.ofReal (2 / G.lam) * G.totalEnergy v₀)

theorem cDiff_ne_top : G.cDiff ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top G.A_ne_top
    (ENNReal.mul_ne_top G.A_ne_top ENNReal.ofReal_ne_top))

theorem K₀_ne_top {v₀ : (x : X) → V x} (hE : G.totalEnergy v₀ ≠ ⊤) : G.K₀ v₀ ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top G.cDiff_ne_top hE),
    ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE)⟩

theorem energy_le_totalEnergy (i : ι) (v : (x : X) → V x) : G.energy i v ≤ G.totalEnergy v :=
  Finset.single_le_sum (f := fun i => G.energy i v) (fun _ _ => zero_le) (Finset.mem_univ i)

section Limit

variable {v₀ : (x : X) → V x} (hκ : G.kappa ≤ ENNReal.ofReal (1 / 4)) (hv : G.IsSmooth v₀)
include hκ hv

theorem step_F_le (i : ι) (m : ℕ) :
    ∫⁻ z in ball (G.center i) (G.R i), ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m) z -
        G.locCoef i (G.iter v₀ (m + 1)) z‖ ^ 2) * G.W i z ≤
      (G.cDiff * G.totalEnergy v₀) * ENNReal.ofReal ((1 / 4 : ℝ) ^ m) := by
  have h := G.lintegral_sub_next_le (G.isSmooth_iter hv m) i
  rw [G.locCoef_sub] at h
  rw [iter_succ]
  refine h.trans ?_
  calc (Fintype.card ι : ℝ≥0∞) * (G.A * (G.A * ENNReal.ofReal (2 / G.lam))) *
        G.totalEnergy (G.iter v₀ m)
      ≤ G.cDiff * (ENNReal.ofReal ((1 / 4 : ℝ) ^ m) * G.totalEnergy v₀) :=
        mul_le_mul_of_nonneg_left (G.totalEnergy_iter_le hκ hv m) zero_le
    _ = _ := by ring

theorem approx_le (i : ι) (m : ℕ) :
    ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m) z -
        G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * G.W i z ≤
      (ENNReal.ofReal (2 / G.lam) * G.totalEnergy v₀) * ENNReal.ofReal ((1 / 4 : ℝ) ^ m) := by
  refine (G.stepCoef_le (G.isSmooth_iter hv m) i).trans ?_
  calc ENNReal.ofReal (2 / G.lam) * G.energy i (G.iter v₀ m)
      ≤ ENNReal.ofReal (2 / G.lam) * (ENNReal.ofReal ((1 / 4 : ℝ) ^ m) * G.totalEnergy v₀) :=
        mul_le_mul_of_nonneg_left ((G.energy_le_totalEnergy i _).trans
          (G.totalEnergy_iter_le hκ hv m)) zero_le
    _ = _ := by ring

theorem continuousOn_F (i : ι) (m : ℕ) :
    ContinuousOn (G.locCoef i (G.iter v₀ m)) (ball (G.center i) (G.R i)) :=
  (G.isSmooth_iter hv m i).continuousOn

theorem tail_le (i : ι) (m k : ℕ) :
    ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m) z -
        G.locCoef i (G.iter v₀ (m + k)) z‖ ^ 2) * G.W i z ≤
      (G.cDiff * G.totalEnergy v₀) * ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ m) := by
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  refine lintegral_telescope_le ((G.aemeasurable_W i).mono_measure
    (Measure.restrict_mono hrR le_rfl)) (fun m => ((G.continuousOn_F hκ hv i m).mono hrR).aestronglyMeasurable
      measurableSet_ball) (fun m => ?_) m k
  exact (lintegral_mono_set hrR).trans (G.step_F_le hκ hv i m)

theorem approx_tail_le (i : ι) {m₀ m : ℕ} (hm : m₀ ≤ m) :
    ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m₀) z -
        G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * G.W i z ≤
      G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m₀) := by
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  have hmeas : AEStronglyMeasurable (fun z => G.locCoef i (G.iter v₀ m) z -
      G.stepCoef (G.iter v₀ m) i z) (volume.restrict (ball (G.center i) (G.r i))) :=
    (((G.continuousOn_F hκ hv i m).mono hrR).sub
      (G.differentiableOn_stepCoef _ i).continuousOn).aestronglyMeasurable measurableSet_ball
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hq : ENNReal.ofReal ((1 / 4 : ℝ) ^ (m₀ + k)) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ m₀) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  calc _ ≤ 2 * (∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m₀) z -
          G.locCoef i (G.iter v₀ (m₀ + k)) z‖ ^ 2) * G.W i z) +
        2 * ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i (G.iter v₀ (m₀ + k)) z -
          G.stepCoef (G.iter v₀ (m₀ + k)) i z‖ ^ 2) * G.W i z :=
        lintegral_sub_sq_le_two ((G.aemeasurable_W i).mono_measure
          (Measure.restrict_mono hrR le_rfl)) hmeas
    _ ≤ 2 * ((G.cDiff * G.totalEnergy v₀) * ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ m₀)) +
        2 * ((ENNReal.ofReal (2 / G.lam) * G.totalEnergy v₀) * ENNReal.ofReal ((1 / 4 : ℝ) ^ m₀)) := by
        gcongr
        · exact G.tail_le hκ hv i m₀ k
        · exact (G.approx_le hκ hv i (m₀ + k)).trans (mul_le_mul_of_nonneg_left hq zero_le)
    _ = G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m₀) := by
        rw [ENNReal.ofReal_mul (by norm_num), K₀]
        simp only [ENNReal.ofReal_ofNat]
        ring

theorem exists_limit (hE : G.totalEnergy v₀ ≠ ⊤) (i : ι) :
    ∃ s : ComplexModel n → ℂ, DifferentiableOn ℂ s (ball (G.center i) (G.r i)) ∧
      ∀ m₀, ∫⁻ z in ball (G.center i) (G.r i),
        ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m₀) z - s z‖ ^ 2) * G.W i z ≤
          G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m₀) := by
  set U := ball (G.center i) (G.r i) with hU
  have hrR : U ⊆ ball (G.center i) (G.R i) := ball_subset_ball (G.r_lt_R i).le
  have hUU : (⋃ _ : ℕ, U) = U := iUnion_const U
  set w' : ComplexModel n → ℝ≥0∞ := fun z => min (G.W i z) 1 with hw'
  have hw'm : AEMeasurable w' (volume.restrict U) :=
    ((G.aemeasurable_W i).min aemeasurable_const).mono_measure (Measure.restrict_mono hrR le_rfl)
  have hF0 : ContinuousOn (G.locCoef i (G.iter v₀ 0)) (ball (G.center i) (G.R i)) :=
    G.continuousOn_F hκ hv i 0
  obtain ⟨Ma, hMa⟩ := exists_bound_norm_sq_on_ball (G.r_lt_R i) hF0
  set A' : ℝ≥0∞ := 2 * G.K₀ v₀ + 2 * ∫⁻ z in U, ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2)
    with hA'
  have hA'top : A' ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) (G.K₀_ne_top hE),
    ENNReal.mul_ne_top (by norm_num) (setLIntegral_ball_lt_top_of_bound (M := Ma)
      fun z hz => ENNReal.ofReal_le_ofReal (hMa z hz)).ne⟩
  have hbound : ∀ m, ∫⁻ z in U, ENNReal.ofReal (‖G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * w' z ≤ A' := by
    intro m
    have hm0 := G.approx_tail_le hκ hv i (Nat.zero_le m)
    rw [pow_zero, ENNReal.ofReal_one, mul_one] at hm0
    calc ∫⁻ z in U, ENNReal.ofReal (‖G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * w' z
        ≤ ∫⁻ z in U, (2 * (ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z -
            G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * G.W i z) +
            2 * ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2)) := by
          refine lintegral_mono fun z => ?_
          have h1 : ENNReal.ofReal (‖G.stepCoef (G.iter v₀ m) i z‖ ^ 2) ≤
              2 * ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z - G.stepCoef (G.iter v₀ m) i z‖ ^ 2) +
                2 * ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2) := by
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
            exact ENNReal.ofReal_le_ofReal (norm_sq_le_two_mul _ _)
          calc ENNReal.ofReal (‖G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * w' z
              ≤ (2 * ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z -
                  G.stepCoef (G.iter v₀ m) i z‖ ^ 2) +
                  2 * ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2)) * w' z :=
                mul_le_mul_of_nonneg_right h1 zero_le
            _ = 2 * (ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z -
                  G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * w' z) +
                  2 * (ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2) * w' z) := by ring
            _ ≤ 2 * (ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z -
                  G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * G.W i z) +
                  2 * (ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2) * 1) := by
                gcongr
                · exact min_le_left _ _
                · exact min_le_right _ _
            _ = _ := by rw [mul_one]
      _ = 2 * (∫⁻ z in U, ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z -
            G.stepCoef (G.iter v₀ m) i z‖ ^ 2) * G.W i z) +
            2 * ∫⁻ z in U, ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2) := by
          have hm2 : AEMeasurable (fun z => 2 * ENNReal.ofReal (‖G.locCoef i (G.iter v₀ 0) z‖ ^ 2))
              (volume.restrict U) := (ENNReal.measurable_ofReal.comp_aemeasurable
            (((hF0.mono hrR).aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const
              2)).const_mul _
          rw [lintegral_add_right' _ hm2, lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ A' := by rw [hA']; gcongr
  obtain ⟨ψ, s, hψ, hs, hconv, -, -⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds (N := n) (α := Empty)
      (ι := Empty.elim) (g := Empty.elim) (U := fun _ => U) (fun _ => isOpen_ball) monotone_const
      (w := fun _ => w') (fun _ _ => monotone_const)
      (fun _ => by rw [hUU]; exact hw'm)
      (fun x hx => by
        rw [hUU] at hx
        obtain ⟨ρ, hρ, δ, hδ, hδ1, hle⟩ := G.W_locally_ge (hrR hx)
        exact ⟨ρ, hρ, δ, hδ, fun y hy => le_min (hle y hy) (by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1)⟩)
      (fun m => (G.differentiableOn_stepCoef (G.iter v₀ m) i)) (fun _ e => e.elim) hA'top
      (fun m => by simpa using hbound m)
  rw [hUU] at hs hconv
  refine ⟨s, hs, fun m₀ => ?_⟩
  refine lintegral_le_of_tendsto measurableSet_ball ((G.aemeasurable_W i).mono_measure
    (Measure.restrict_mono hrR le_rfl)) (F := fun k => G.stepCoef (G.iter v₀ (ψ k)) i)
    (fun k => (((G.continuousOn_F hκ hv i m₀).mono hrR).sub
      (G.differentiableOn_stepCoef _ i).continuousOn).aestronglyMeasurable measurableSet_ball)
    (fun z hz => hconv.tendsto_at hz) ?_
  filter_upwards [eventually_ge_atTop m₀] with k hk
  exact G.approx_tail_le hκ hv i (hk.trans (hψ.id_le k))

/-- **Consistency of the local limits** (`claude-global-l2:holomorphic-limit`). -/
theorem localSec_consistent (hE : G.totalEnergy v₀ ≠ ⊤) {s : ι → ComplexModel n → ℂ}
    (hs : ∀ i, DifferentiableOn ℂ (s i) (ball (G.center i) (G.r i)))
    (hsb : ∀ i m₀, ∫⁻ z in ball (G.center i) (G.r i),
        ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m₀) z - s i z‖ ^ 2) * G.W i z ≤
          G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m₀))
    (i l : ι) {x : X} (hxi : x ∈ G.small i) (hxl : x ∈ G.small l) :
    G.localSec i (s i) x = G.localSec l (s l) x := by
  set O : Set (ComplexModel n) := ball (G.center i) (G.r i) ∩ G.inner i l with hO
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  have hOo : IsOpen O := isOpen_ball.inter (G.isOpen_inner i l)
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOR : O ⊆ ball (G.center i) (G.R i) := fun z hz => hz.2.1
  set φ : ComplexModel n → ℂ := fun z => s i z - G.locCoef i (G.localSec l (s l)) z with hφ
  have hSl : ContinuousOn (G.locCoef i (G.localSec l (s l))) (G.inner i l) :=
    ((G.differentiableOn_locCoef_localSec (hs l)).continuousOn).congr
      fun z hz => G.locCoef_localSec_of_mem _ hz
  have hφc : ContinuousOn φ O :=
    ((hs i).continuousOn.mono fun z hz => hz.1).sub (hSl.mono fun z hz => hz.2)
  have hWO : AEMeasurable (G.W i) (volume.restrict O) :=
    (G.aemeasurable_W i).mono_measure (Measure.restrict_mono hOR le_rfl)
  -- the integral of `|φ|² W` over `O` is arbitrarily small
  have hsmall : ∀ m, ∫⁻ z in O, ENNReal.ofReal (‖φ z‖ ^ 2) * G.W i z ≤
      (2 + 2 * (G.A * G.A)) * (G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) := by
    intro m
    have hmeas : AEStronglyMeasurable (fun z => G.locCoef i (G.iter v₀ m) z -
        G.locCoef i (G.localSec l (s l)) z) (volume.restrict O) :=
      (((G.continuousOn_F hκ hv i m).mono hOR).sub (hSl.mono fun z hz => hz.2)).aestronglyMeasurable hOm
    have h1 : ∫⁻ z in O, ENNReal.ofReal (‖s i z - G.locCoef i (G.iter v₀ m) z‖ ^ 2) * G.W i z ≤
        G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m) := by
      refine le_trans ?_ (hsb i m)
      refine (lintegral_mono_set fun z hz => hz.1).trans (le_of_eq ?_)
      refine setLIntegral_congr_fun measurableSet_ball fun z _ => by rw [norm_sub_rev]
    have h2 : ∫⁻ z in O, ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m) z -
        G.locCoef i (G.localSec l (s l)) z‖ ^ 2) * G.W i z ≤
        G.A * G.A * (G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) := by
      calc ∫⁻ z in O, ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m) z -
            G.locCoef i (G.localSec l (s l)) z‖ ^ 2) * G.W i z
          ≤ ∫⁻ z in ball (G.center i) (G.R i), (G.inner i l).indicator (fun z => ENNReal.ofReal
              (‖G.locCoef i (fun x => G.iter v₀ m x - G.localSec l (s l) x) z‖ ^ 2) * G.W i z) z := by
            rw [← lintegral_indicator hOm, ← lintegral_indicator measurableSet_ball]
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ O
            · rw [indicator_of_mem hz, indicator_of_mem (hOR hz), indicator_of_mem hz.2,
                G.locCoef_sub]
            · rw [indicator_of_notMem hz]; exact zero_le
        _ ≤ G.A * ∫⁻ x in G.small l, G.D (fun x => G.iter v₀ m x - G.localSec l (s l) x) x ∂μ :=
            G.lintegral_inner_le i l _ (by
              rw [G.locCoef_sub]
              exact ((G.continuousOn_F hκ hv i m).mono fun z hz => hz.1).sub hSl)
        _ ≤ G.A * (G.A * ∫⁻ z in ball (G.center l) (G.r l), ENNReal.ofReal
              (‖G.locCoef l (fun x => G.iter v₀ m x - G.localSec l (s l) x) z‖ ^ 2) * G.W l z) :=
            mul_le_mul_of_nonneg_left (G.lintegral_small_le l _ (by
              rw [G.locCoef_sub]
              refine (((G.continuousOn_F hκ hv l m).mono (ball_subset_ball (G.r_lt_R l).le)).sub
                (hs l).continuousOn).congr fun z hz => ?_
              simp only [G.locCoef_localSec_self _ hz]
              rfl)) zero_le
        _ = G.A * (G.A * ∫⁻ z in ball (G.center l) (G.r l), ENNReal.ofReal
              (‖G.locCoef l (G.iter v₀ m) z - s l z‖ ^ 2) * G.W l z) := by
            congr 2
            refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
            rw [G.locCoef_sub]
            dsimp only
            rw [G.locCoef_localSec_self _ hz]
        _ ≤ G.A * (G.A * (G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m))) := by
            gcongr; exact hsb l m
        _ = _ := by ring
    calc ∫⁻ z in O, ENNReal.ofReal (‖φ z‖ ^ 2) * G.W i z
        ≤ 2 * (∫⁻ z in O, ENNReal.ofReal (‖s i z - G.locCoef i (G.iter v₀ m) z‖ ^ 2) * G.W i z) +
          2 * ∫⁻ z in O, ENNReal.ofReal (‖G.locCoef i (G.iter v₀ m) z -
            G.locCoef i (G.localSec l (s l)) z‖ ^ 2) * G.W i z :=
          lintegral_sub_sq_le_two hWO hmeas
      _ ≤ 2 * (G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) +
          2 * (G.A * G.A * (G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m))) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun m : ℕ => (2 + 2 * (G.A * G.A)) *
      (G.K₀ v₀ * ENNReal.ofReal ((1 / 4 : ℝ) ^ m))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have h1 := ENNReal.Tendsto.const_mul h0 (Or.inr (G.K₀_ne_top hE))
    rw [mul_zero] at h1
    have h2 := ENNReal.Tendsto.const_mul h1 (a := 2 + 2 * (G.A * G.A))
      (Or.inr (ENNReal.add_ne_top.mpr ⟨(by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.mul_ne_top G.A_ne_top G.A_ne_top)⟩))
    rwa [mul_zero] at h2
  have hzero : ∫⁻ z in O, ENNReal.ofReal (‖φ z‖ ^ 2) * G.W i z = 0 :=
    le_antisymm (ge_of_tendsto' hlim hsmall) zero_le
  have hφm : AEMeasurable (fun z => ENNReal.ofReal (‖φ z‖ ^ 2) * G.W i z) (volume.restrict O) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hφc.aestronglyMeasurable hOm).norm.aemeasurable.pow_const 2)).mul hWO
  have hae : φ =ᵐ[volume.restrict O] fun _ => 0 := by
    have h := (lintegral_eq_zero_iff' hφm).mp hzero
    filter_upwards [h, ae_restrict_mem hOm] with z hz hzO
    rcases mul_eq_zero.mp hz with h0 | h0
    · have : ‖φ z‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h0
      have : ‖φ z‖ = 0 := by nlinarith [norm_nonneg (φ z)]
      exact norm_eq_zero.mp this
    · exact absurd h0 (G.W_ne_zero (hOR hzO))
  have heq := Measure.eqOn_open_of_ae_eq hae hOo hφc continuousOn_const
  -- evaluate at `x`
  have hzx : G.chart i x ∈ O := by
    refine ⟨hxi.2, ball_subset_ball (G.r_lt_R i).le hxi.2, ?_⟩
    rw [mem_preimage, (G.chart i).left_inv hxi.1]; exact hxl
  have hval := heq hzx
  simp only [hφ, sub_eq_zero] at hval
  have hloc : G.locCoef i (G.localSec l (s l)) (G.chart i x) =
      G.coef i x (G.localSec l (s l) x) := by
    have hx' : (G.chart i).symm (G.chart i x) = x := (G.chart i).left_inv hxi.1
    unfold locCoef
    rw [hx']
  rw [hloc] at hval
  have hxreg : G.chart i x ∈ ball (G.center i) (G.R i) := ball_subset_ball (G.r_lt_R i).le hxi.2
  conv_rhs => rw [G.eq_coef_smul_frame i x (G.localSec l (s l) x) hxi.1 hxreg]
  rw [← hval]
  simp only [localSec, if_pos hxi]

end Limit

/-- **Global `L²` correction** (`claude-global-l2:global-correction`, abstract form): if the
contraction factor is at most `1/4`, every section `v` with smooth coefficients and finite
`∂̄`-energy has a correction `S`, given on the middle region of every chart by a holomorphic
coefficient, with `∫ |v - S|² w dμ ≤ |ι| A K₀(v)`, `K₀(v)` a constant multiple of the energy. -/
theorem exists_correction (hκ : G.kappa ≤ ENNReal.ofReal (1 / 4)) {v₀ : (x : X) → V x}
    (hv : G.IsSmooth v₀) (hE : G.totalEnergy v₀ ≠ ⊤) :
    ∃ S : (x : X) → V x,
      (∀ i, ∃ s : ComplexModel n → ℂ, DifferentiableOn ℂ s (ball (G.center i) (G.r i)) ∧
        ∀ x ∈ G.small i, S x = s (G.chart i x) • G.frame i x) ∧
      ∫⁻ x, G.D (fun x => v₀ x - S x) x ∂μ ≤ (Fintype.card ι : ℝ≥0∞) * (G.A * G.K₀ v₀) := by
  choose s hs hsb using G.exists_limit hκ hv hE
  have hcons := G.localSec_consistent hκ hv hE hs hsb
  have hcov : ∀ x, ∃ j, x ∈ G.smaller j := fun x => G.cover x
  choose j hj using hcov
  set S : (x : X) → V x := fun x => G.localSec (j x) (s (j x)) x with hSdef
  have hSi : ∀ i, ∀ x ∈ G.small i, S x = G.localSec i (s i) x := fun i x hx =>
    hcons (j x) i (G.smaller_subset_small _ (hj x)) hx
  refine ⟨S, fun i => ⟨s i, hs i, fun x hx => ?_⟩, ?_⟩
  · rw [hSi i x hx]; simp only [localSec, if_pos hx]
  have hU : (⋃ i, G.smaller i) = univ := eq_univ_of_forall fun x => mem_iUnion.mpr ⟨j x, hj x⟩
  calc ∫⁻ x, G.D (fun x => v₀ x - S x) x ∂μ
      = ∫⁻ x in ⋃ i, G.smaller i, G.D (fun x => v₀ x - S x) x ∂μ := by
        rw [hU, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ x in G.smaller i, G.D (fun x => v₀ x - S x) x ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i, ∫⁻ x in G.smaller i, G.D (fun x => v₀ x - S x) x ∂μ := tsum_fintype _
    _ ≤ ∑ _i : ι, G.A * G.K₀ v₀ := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ∫⁻ x in G.smaller i, G.D (fun x => v₀ x - S x) x ∂μ
            = ∫⁻ x in G.smaller i, G.D (fun x => v₀ x - G.localSec i (s i) x) x ∂μ := by
              refine setLIntegral_congr_fun (G.isOpen_smaller i).measurableSet fun x hx => ?_
              simp only [D, hSi i x (G.smaller_subset_small i hx)]
          _ ≤ ∫⁻ x in G.small i, G.D (fun x => v₀ x - G.localSec i (s i) x) x ∂μ :=
              lintegral_mono_set (G.smaller_subset_small i)
          _ ≤ G.A * ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal
                (‖G.locCoef i (fun x => v₀ x - G.localSec i (s i) x) z‖ ^ 2) * G.W i z :=
              G.lintegral_small_le i _ (by
                rw [G.locCoef_sub]
                refine (((G.continuousOn_F hκ hv i 0).mono (ball_subset_ball (G.r_lt_R i).le)).sub
                  (hs i).continuousOn).congr fun z hz => ?_
                simp only [G.locCoef_localSec_self _ hz]
                rfl)
          _ = G.A * ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal
                (‖G.locCoef i (G.iter v₀ 0) z - s i z‖ ^ 2) * G.W i z := by
              congr 1
              refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
              rw [G.locCoef_sub]
              dsimp only
              rw [G.locCoef_localSec_self _ hz]
              rfl
          _ ≤ G.A * G.K₀ v₀ := by
              have := hsb i 0
              rw [pow_zero, ENNReal.ofReal_one, mul_one] at this
              exact mul_le_mul_of_nonneg_left this zero_le
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GluingSystem

end SGPT.PSH.GlobalL2
