import SGPT.GAGA.H0TubeIntegrals
import SGPT.GAGA.H0ConeSmoothEstimates
import SGPT.GAGA.H0LocalCorrectionC1
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The singular weight of a cone and the weighted energy of the smooth extension


Let `C ⊆ ℂ^m` be a closed cone which is, off the vertex, a complex submanifold of codimension
`r > 0` (`IsLocalGraphAt C r p` for `p ∈ C ∖ {0}`), and let `G_1, …, G_q` be homogeneous
polynomials of degree `d` vanishing on `C`.  The weight is
`Ψ = r log ∑_j |G_j|²` (`coneWeight`), plurisubharmonic on `ℂ^m`.

* `lintegral_ball_infDist_rpow_lt_top`: `dist(·, C)^{2-2r}` is integrable on every ball
  `B(0, R)` (finitely many local graphs on the shell `R/2 ≤ |Z| ≤ R`, and the dyadic scaling
  `Z ↦ 2^{-n} Z`, under which the integral over the `n`-th shell is multiplied by
  `2^{-n(2m + 2 - 2r)}`; this is where `r ≤ m` enters).
* `lintegral_coneWeight_eq_top`: `e^{-Ψ}` is not integrable on any ball around a point of
  `C ∖ {0}` (`|G_j| ≤ L dist(·, C)` near `C`, and `dist(·, C)^{-2r}` is not integrable).
* `lintegral_dbarNormSq_coneWeight_lt_top`: under the Łojasiewicz inequality
  `∑_j |G_j(Z)|² ≥ c |Z|^{2d-2} dist(Z, C)²`, a function `a` with
  `|∂̄a(Z)|² ≤ M |Z|^{2k-4} dist(Z, C)²` has finite energy
  `∫_{B(0,R)} |∂̄a|² e^{-Ψ - |Z|²} < ∞` as soon as `k ≥ (d - 1) r + 2`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.GlobalL2

variable {m : ℕ}

/-! ### Integrability of `dist(·, C)^{2-2r}` on balls -/

/-- `dist(λ Z, C)^s = λ^s dist(Z, C)^s` for a cone `C` and `λ > 0`. -/
theorem infDist_rpow_real_smul {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {lam : ℝ} (hlam : 0 < lam)
    (s : ℝ) (Z : ComplexModel m) :
    infDist (lam • Z) C ^ s = lam ^ s * infDist Z C ^ s := by
  rw [← Complex.coe_smul, infDist_smul_cone hC (Complex.ofReal_ne_zero.mpr hlam.ne'),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam,
    Real.mul_rpow hlam.le infDist_nonneg]

/-- The scaling identity for the integral of `dist(·, C)^s` over a dilated set. -/
theorem lintegral_smul_set_infDist_rpow {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {lam : ℝ} (hlam : 0 < lam)
    (s : ℝ) {A : Set (ComplexModel m)} (hA : MeasurableSet A) :
    ∫⁻ Z in lam • A, ENNReal.ofReal (infDist Z C ^ s) =
      ENNReal.ofReal (lam ^ (2 * m)) * ENNReal.ofReal (lam ^ s) *
        ∫⁻ Z in A, ENNReal.ofReal (infDist Z C ^ s) := by
  set f : ComplexModel m → ℝ≥0∞ := fun Z => ENNReal.ofReal (infDist Z C ^ s) with hfdef
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp ((continuous_infDist_pt C).measurable.pow_const s)
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hAm' : MeasurableSet (lam • A) := hA.const_smul₀ lam
  have hd : Module.finrank ℝ (ComplexModel m) = 2 * m := finrank_real_complexModel m
  -- `∫_A f(λ W) dW = λ^{-2m} ∫_{λA} f`
  have h1 : ∫⁻ W in A, f (lam • W) =
      ENNReal.ofReal ((lam ^ (2 * m))⁻¹) * ∫⁻ Z in lam • A, f Z := by
    have hind : A.indicator (fun W => f (lam • W)) =
        fun W => (lam • A).indicator f (lam • W) := by
      funext W
      by_cases hW : W ∈ A
      · rw [Set.indicator_of_mem hW, Set.indicator_of_mem ((Set.smul_mem_smul_set_iff₀ hlam0 A W).mpr hW)]
      · rw [Set.indicator_of_notMem hW, Set.indicator_of_notMem (fun h => hW ((Set.smul_mem_smul_set_iff₀ hlam0 A W).mp h))]
    rw [← lintegral_indicator hA, hind]
    have hmap := Measure.map_addHaar_smul (volume : Measure (ComplexModel m)) hlam0
    rw [← lintegral_map (hfm.indicator hAm') (measurable_const_smul lam), hmap,
      lintegral_smul_measure, lintegral_indicator hAm', hd]
    congr 2
    rw [abs_of_pos (inv_pos.mpr (pow_pos hlam _))]
  have h2 : ∀ W, f (lam • W) = ENNReal.ofReal (lam ^ s) * f W := by
    intro W
    simp only [hfdef]
    rw [infDist_rpow_real_smul hC hlam, ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
  simp only [h2] at h1
  rw [lintegral_const_mul _ hfm] at h1
  have hpos : ENNReal.ofReal (lam ^ (2 * m)) * ENNReal.ofReal ((lam ^ (2 * m))⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hlam.le _), mul_inv_cancel₀ (pow_ne_zero _ hlam0),
      ENNReal.ofReal_one]
  calc ∫⁻ Z in lam • A, f Z
      = ENNReal.ofReal (lam ^ (2 * m)) * (ENNReal.ofReal ((lam ^ (2 * m))⁻¹) *
          ∫⁻ Z in lam • A, f Z) := by rw [← mul_assoc, hpos, one_mul]
    _ = ENNReal.ofReal (lam ^ (2 * m)) * ENNReal.ofReal (lam ^ s) * ∫⁻ Z in A, f Z := by
        rw [← h1, mul_assoc]

/-- **`dist(·, C)^{2-2r}` is integrable on balls** (`claude-h0-gaga:cone-integrable`). -/
theorem lintegral_ball_infDist_rpow_lt_top {C : Set (ComplexModel m)} (hCc : IsClosed C)
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {r : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    (hgraph : ∀ p ∈ C, p ≠ 0 → IsLocalGraphAt C r p) (R : ℝ) :
    ∫⁻ Z in ball (0 : ComplexModel m) R, ENNReal.ofReal (infDist Z C ^ (2 - 2 * (r : ℝ))) < ⊤ := by
  set s : ℝ := 2 - 2 * (r : ℝ) with hs
  have hs0 : s ≤ 0 := by
    rw [hs]; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  set f : ComplexModel m → ℝ≥0∞ := fun Z => ENNReal.ofReal (infDist Z C ^ s) with hfdef
  rcases le_or_gt R 0 with hR | hR
  · rw [Metric.ball_eq_empty.mpr hR, Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  by_cases hCne : C.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hCne
    refine setLIntegral_ball_lt_top_of_bound (M := 1) fun Z _ => ?_
    rw [hCne, infDist_empty]
    exact ENNReal.ofReal_le_ofReal (Real.zero_rpow_le_one s)
  -- Step 1: the shell `R/2 ≤ |Z| ≤ R`
  set K : Set (ComplexModel m) := closedBall 0 R \ ball 0 (R / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 R).diff isOpen_ball
  have hloc : ∀ q ∈ K, ∃ δ : ℝ, 0 < δ ∧ ∫⁻ Z in ball q δ, f Z < ⊤ := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro h0; apply hq.2; rw [h0]; exact mem_ball_self (by linarith)
    by_cases hqC : q ∈ C
    · exact (hgraph q hqC hq0).exists_lintegral_infDist_rpow_lt_top hqC hr
    · have hd0 : 0 < infDist q C := (hCc.notMem_iff_infDist_pos hCne).mp hqC
      refine ⟨infDist q C / 2, by positivity, ?_⟩
      refine setLIntegral_ball_lt_top_of_bound (M := (infDist q C / 2) ^ s) fun Z hZ => ?_
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hs0)
      have h1 := infDist_le_infDist_add_dist (x := q) (y := Z) (s := C)
      have h2 : dist q Z < infDist q C / 2 := by rw [dist_comm]; exact hZ
      linarith
  choose! δ hδ0 hδfin using hloc
  obtain ⟨T, hTK, hTcov⟩ := hKc.elim_nhds_subcover (fun q => ball q (δ q))
    (fun q hq => ball_mem_nhds q (hδ0 q hq))
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp ((continuous_infDist_pt C).measurable.pow_const s)
  have hKfin : ∫⁻ Z in K, f Z < ⊤ := by
    calc ∫⁻ Z in K, f Z ≤ ∫⁻ Z in ⋃ q : T, ball (q : ComplexModel m) (δ q), f Z := by
          refine lintegral_mono_set fun Z hZ => ?_
          have := hTcov hZ
          simp only [Set.mem_iUnion] at this ⊢
          obtain ⟨q, hq, hZq⟩ := this
          exact ⟨⟨q, hq⟩, hZq⟩
      _ ≤ ∑' q : T, ∫⁻ Z in ball (q : ComplexModel m) (δ q), f Z := lintegral_iUnion_le _ _
      _ = ∑ q : T, ∫⁻ Z in ball (q : ComplexModel m) (δ q), f Z := tsum_fintype _
      _ < ⊤ := ENNReal.sum_lt_top.mpr fun q _ => hδfin q (hTK q q.2)
  -- Step 2: the half-open shell `A`
  set A : Set (ComplexModel m) := {W | R / 2 < ‖W‖ ∧ ‖W‖ ≤ R} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hAK : A ⊆ K := fun W hW =>
    ⟨mem_closedBall_zero_iff.mpr hW.2, fun h => by
      have := mem_ball_zero_iff.mp h; linarith [hW.1]⟩
  set I₀ : ℝ≥0∞ := ∫⁻ Z in A, f Z with hI₀
  have hI₀ : I₀ < ⊤ := lt_of_le_of_lt (lintegral_mono_set hAK) hKfin
  -- Step 3: the dyadic cover of the ball
  have hcov : ball (0 : ComplexModel m) R ⊆ {0} ∪ ⋃ n : ℕ, ((2 : ℝ) ^ n)⁻¹ • A := by
    intro Z hZ
    by_cases hZ0 : Z = 0
    · exact Or.inl hZ0
    right
    have hn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
    have hx : 1 ≤ R / ‖Z‖ := by
      rw [le_div_iff₀ hn, one_mul]; exact (mem_ball_zero_iff.mp hZ).le
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    refine ⟨(2 : ℝ) ^ n • Z, ⟨?_, ?_⟩, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_lt_iff₀ hn, pow_succ] at hn2
      linarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rwa [le_div_iff₀ hn] at hn1
    · show ((2 : ℝ) ^ n)⁻¹ • ((2 : ℝ) ^ n • Z) = Z
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  -- Step 4: summation
  set ρ : ℝ := (1 / 2 : ℝ) ^ ((2 * m : ℕ) + s) with hρ
  have hds : 0 < ((2 * m : ℕ) : ℝ) + s := by
    rw [hs]; push_cast
    have : (r : ℝ) ≤ m := by exact_mod_cast hrm
    linarith
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hds
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ n : ℕ, ∫⁻ Z in ((2 : ℝ) ^ n)⁻¹ • A, f Z = ENNReal.ofReal ρ ^ n * I₀ := by
    intro n
    have hlam : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
    rw [lintegral_smul_set_infDist_rpow hC hlam s hAm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow hρ0]
    congr 2
    have h1 : ((2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := by rw [one_div, inv_pow]
    rw [h1, hρ, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ n) (2 * m), ← Real.rpow_add (by positivity),
      ← Real.rpow_natCast (1 / 2 : ℝ) n, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast ((1 / 2 : ℝ) ^ (((2 * m : ℕ) : ℝ) + s)) n,
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hm : 0 < m := lt_of_lt_of_le hr hrm
  have : Nontrivial (ComplexModel m) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_real_complexModel]; omega
  have hne0 : ∀ᵐ x ∂(volume : Measure (ComplexModel m)), x ≠ 0 := by
    rw [ae_iff]; simp
  have hae : ball (0 : ComplexModel m) R ≤ᵐ[volume] ⋃ n : ℕ, ((2 : ℝ) ^ n)⁻¹ • A := by
    filter_upwards [hne0] with x hx hxb
    exact (hcov hxb).resolve_left hx
  calc ∫⁻ Z in ball (0 : ComplexModel m) R, f Z
      ≤ ∫⁻ Z in ⋃ n : ℕ, ((2 : ℝ) ^ n)⁻¹ • A, f Z := lintegral_mono_set' hae
    _ ≤ ∑' n : ℕ, ∫⁻ Z in ((2 : ℝ) ^ n)⁻¹ • A, f Z := lintegral_iUnion_le _ _
    _ = (∑' n : ℕ, ENNReal.ofReal ρ ^ n) * I₀ := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr hterm
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        refine ENNReal.mul_lt_top ?_ hI₀
        rw [ENNReal.inv_lt_top, tsub_pos_iff_lt]
        exact (ENNReal.ofReal_lt_one).mpr hρ1

/-! ### The singular weight -/

/-- The polynomial functions `Z ↦ G_j(Z)`. -/
def polyFun {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ) (j : Fin q) (Z : ComplexModel m) : ℂ :=
  MvPolynomial.eval (fun i => Z i) (G j)

theorem differentiable_polyFun {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ) (j : Fin q) :
    Differentiable ℂ (polyFun G j) := by
  intro Z
  have h1 : DifferentiableAt ℂ (fun v : Fin m → ℂ => MvPolynomial.eval v (G j))
      ((EuclideanSpace.equiv (Fin m) ℂ) Z) :=
    (AnalyticOnNhd.eval_mvPolynomial (G j) _ (mem_univ _)).differentiableAt
  have h2 := h1.comp Z (EuclideanSpace.equiv (Fin m) ℂ).differentiableAt
  exact h2

/-- The weight `Ψ = r log ∑_j |G_j|²` of the cone. -/
def coneWeight (r : ℕ) {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ) (Z : ComplexModel m) : EReal :=
  ((r : ℝ) : EReal) * generatorLog (polyFun G) Z

theorem plurisubharmonicOn_coneWeight {r : ℕ} (hr : 0 < r) {q : ℕ}
    (G : Fin q → MvPolynomial (Fin m) ℂ) (U : Set (ComplexModel m)) :
    PlurisubharmonicOn (coneWeight r G) U := fun x _ =>
  plurisubharmonicAt_scaled_generatorLog ⟨univ, isOpen_univ, mem_univ x,
    fun j => (differentiable_polyFun G j).differentiableOn⟩ (by exact_mod_cast hr)

theorem coe_nonneg_mul_ne_top {t : ℝ} (ht : 0 ≤ t) {a : EReal} (ha : a ≠ ⊤) :
    (t : EReal) * a ≠ ⊤ := by
  induction a using EReal.rec with
  | bot =>
      rcases ht.lt_or_eq with h | h
      · rw [EReal.coe_mul_bot_of_pos h]; exact bot_ne_top
      · rw [← h]; simp
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl ha

theorem coneWeight_ne_top (r : ℕ) {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ)
    (Z : ComplexModel m) : coneWeight r G Z ≠ ⊤ := by
  refine coe_nonneg_mul_ne_top (Nat.cast_nonneg r) ?_
  unfold generatorLog logNormSq
  rw [Ne, ENNReal.log_eq_top_iff]
  exact ENNReal.ofReal_ne_top

/-- The weight `e^{-Ψ} = (∑_j |G_j|²)^{-r}` where `∑_j |G_j|² > 0`. -/
theorem multiplierWeight_coneWeight_of_pos (r : ℕ) {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ)
    {Z : ComplexModel m} (hpos : 0 < generatorNormSq (polyFun G) Z) :
    multiplierWeight 1 (coneWeight r G Z) =
      ENNReal.ofReal ((generatorNormSq (polyFun G) Z ^ r)⁻¹) := by
  unfold coneWeight generatorLog logNormSq
  rw [generatorVector_norm_sq, ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul,
    multiplierWeight_coe, one_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hpos]

theorem multiplierWeight_coneWeight_of_eq_zero {r : ℕ} (hr : 0 < r) {q : ℕ}
    (G : Fin q → MvPolynomial (Fin m) ℂ) {Z : ComplexModel m}
    (h0 : generatorNormSq (polyFun G) Z = 0) : multiplierWeight 1 (coneWeight r G Z) = ⊤ := by
  unfold coneWeight generatorLog logNormSq
  rw [generatorVector_norm_sq, h0, ENNReal.ofReal_zero, ENNReal.log_zero,
    EReal.coe_mul_bot_of_pos (by exact_mod_cast hr)]
  exact multiplierWeight_bot one_pos

/-! ### Non-integrability of `e^{-Ψ}` along `C` -/

/-- **`e^{-Ψ}` is not integrable near `C ∖ {0}`** (`claude-h0-gaga:weight`). -/
theorem lintegral_coneWeight_eq_top {C : Set (ComplexModel m)} (hCc : IsClosed C) {r : ℕ}
    (hr : 0 < r) {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ)
    (hGC : ∀ j, ∀ Z ∈ C, polyFun G j Z = 0) {p : ComplexModel m} (hpC : p ∈ C)
    (hgraph : IsLocalGraphAt C r p) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ Z in ball p δ, multiplierWeight 1 (coneWeight r G Z) = ⊤ := by
  have hCne : C.Nonempty := ⟨p, hpC⟩
  -- Lipschitz bounds for the generators on `closedBall p 2`
  have hLip : ∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (polyFun G j) (closedBall p 2) := by
    intro j
    have hcd : ContDiffOn ℝ 1 (polyFun G j) (closedBall p 2) :=
      (((contDiffOn_of_differentiableOn_complex (differentiable_polyFun G j).differentiableOn
        isOpen_univ).restrict_scalars ℝ).of_le (WithTop.coe_le_coe.mpr le_top)).mono
          (subset_univ _)
    exact hcd.exists_lipschitzOnWith one_ne_zero (convex_closedBall p 2)
      (isCompact_closedBall p 2)
  choose K hK using hLip
  set L : ℝ := ∑ j, (K j : ℝ) ^ 2 with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hupper : ∀ Z ∈ ball p 1, generatorNormSq (polyFun G) Z ≤ (L + 1) * infDist Z C ^ 2 := by
    intro Z hZ
    obtain ⟨Z', hZ'C, hZ'd⟩ := hCc.exists_infDist_eq_dist hCne Z
    have hZZ' : dist Z Z' ≤ dist Z p := hZ'd ▸ infDist_le_dist_of_mem hpC
    have hZp : dist Z p < 1 := hZ
    have hZ2 : Z ∈ closedBall p 2 := by
      rw [mem_closedBall]; linarith
    have hZ'2 : Z' ∈ closedBall p 2 := by
      rw [mem_closedBall]
      linarith [dist_triangle Z' Z p, dist_comm Z Z']
    have hj : ∀ j, ‖polyFun G j Z‖ ^ 2 ≤ (K j : ℝ) ^ 2 * infDist Z C ^ 2 := by
      intro j
      have h1 : ‖polyFun G j Z - polyFun G j Z'‖ ≤ K j * ‖Z - Z'‖ :=
        (hK j).norm_sub_le hZ2 hZ'2
      rw [hGC j Z' hZ'C, sub_zero, ← dist_eq_norm, ← hZ'd] at h1
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc generatorNormSq (polyFun G) Z = ∑ j, ‖polyFun G j Z‖ ^ 2 := rfl
      _ ≤ ∑ j, (K j : ℝ) ^ 2 * infDist Z C ^ 2 := Finset.sum_le_sum fun j _ => hj j
      _ = L * infDist Z C ^ 2 := by rw [hL, Finset.sum_mul]
      _ ≤ (L + 1) * infDist Z C ^ 2 := by nlinarith [sq_nonneg (infDist Z C)]
  set κ : ℝ := ((L + 1) ^ r)⁻¹ with hκ
  have hκ0 : 0 < κ := by positivity
  have hlower : ∀ Z ∈ ball p 1, ENNReal.ofReal (κ * infDist Z C ^ (-(2 * (r : ℝ)))) ≤
      multiplierWeight 1 (coneWeight r G Z) := by
    intro Z hZ
    rcases (generatorNormSq_nonneg (polyFun G) Z).lt_or_eq with hpos | h0
    · rw [multiplierWeight_coneWeight_of_pos r G hpos]
      have hZC : Z ∉ C := by
        intro hZC
        have : generatorNormSq (polyFun G) Z = 0 := by
          simp [generatorNormSq, hGC _ Z hZC]
        linarith
      have hD : 0 < infDist Z C := (hCc.notMem_iff_infDist_pos hCne).mp hZC
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hupper Z hZ
      have h2 : generatorNormSq (polyFun G) Z ^ r ≤ ((L + 1) * infDist Z C ^ 2) ^ r :=
        pow_le_pow_left₀ hpos.le h1 r
      have h3 : infDist Z C ^ (-(2 * (r : ℝ))) = ((infDist Z C ^ 2) ^ r)⁻¹ := by
        rw [Real.rpow_neg hD.le, ← pow_mul, ← Real.rpow_natCast]
        push_cast; ring_nf
      rw [h3, hκ, ← mul_inv, ← mul_pow]
      exact inv_anti₀ (pow_pos hpos r) h2
    · rw [multiplierWeight_coneWeight_of_eq_zero hr G h0.symm]
      exact le_top
  have htube := hgraph.lintegral_infDist_rpow_eq_top hCc hpC hr (lt_min hδ one_pos)
  have hbig : ⊤ ≤ ∫⁻ Z in ball p δ, multiplierWeight 1 (coneWeight r G Z) := by
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal κ *
          ∫⁻ Z in ball p (min δ 1), ENNReal.ofReal (infDist Z C ^ (-(2 * (r : ℝ)))) := by
          rw [htube, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hκ0).ne']
      _ = ∫⁻ Z in ball p (min δ 1), ENNReal.ofReal (κ * infDist Z C ^ (-(2 * (r : ℝ)))) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun Z => ?_
          rw [ENNReal.ofReal_mul hκ0.le]
      _ ≤ ∫⁻ Z in ball p (min δ 1), multiplierWeight 1 (coneWeight r G Z) :=
          setLIntegral_mono' isOpen_ball.measurableSet fun Z hZ =>
            hlower Z (ball_subset_ball (min_le_right _ _) hZ)
      _ ≤ ∫⁻ Z in ball p δ, multiplierWeight 1 (coneWeight r G Z) :=
          lintegral_mono_set (ball_subset_ball (min_le_left _ _))
  exact top_le_iff.mp hbig

/-! ### Finite energy of the smooth extension -/

/-- **Finite weighted energy** (`claude-h0-gaga:weight`): under the Łojasiewicz inequality
`∑_j |G_j(Z)|² ≥ c |Z|^{2d-2} dist(Z, C)²` and `k ≥ (d - 1) r + 2`, every `a` with
`|∂̄a(Z)|² ≤ M |Z|^{2k-4} dist(Z, C)²` has `∫_{B(0,R)} |∂̄a|² e^{-Ψ - |Z|²} < ∞`. -/
theorem lintegral_dbarNormSq_coneWeight_lt_top {C : Set (ComplexModel m)} (hCc : IsClosed C)
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {r : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    (hgraph : ∀ p ∈ C, p ≠ 0 → IsLocalGraphAt C r p) {q : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ)
    {d : ℕ} {c : ℝ} (hc : 0 < c)
    (hLoj : ∀ Z : ComplexModel m,
      c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2 ≤ generatorNormSq (polyFun G) Z)
    {k : ℕ} (hk : (d - 1) * r + 2 ≤ k) {a : ComplexModel m → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (ha : ∀ Z : ComplexModel m, dbarNormSq a Z ≤ M * ‖Z‖ ^ (2 * k - 4) * infDist Z C ^ 2)
    (R : ℝ) :
    ∫⁻ Z in ball (0 : ComplexModel m) R,
      ENNReal.ofReal (dbarNormSq a Z) * ballWeight (coneWeight r G) 1 0 Z < ⊤ := by
  set e : ℕ := 2 * k - 4 - 2 * (d - 1) * r with he
  have hesum : 2 * k - 4 = e + 2 * (d - 1) * r := by
    have h1 : 2 * (d - 1) * r = 2 * ((d - 1) * r) := by ring
    rw [he, h1]
    rw [h1] at he
    omega
  set K : ℝ := M * (c ^ r)⁻¹ * max R 1 ^ e with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ Z ∈ ball (0 : ComplexModel m) R,
      ENNReal.ofReal (dbarNormSq a Z) * ballWeight (coneWeight r G) 1 0 Z ≤
        ENNReal.ofReal (K * infDist Z C ^ (2 - 2 * (r : ℝ))) := by
    intro Z hZ
    rcases (dbarNormSq_nonneg a Z).lt_or_eq with hpos | h0
    swap
    · rw [← h0, ENNReal.ofReal_zero, zero_mul]; exact zero_le
    -- `∂̄a(Z) ≠ 0` forces `dist(Z, C) > 0`
    have hD : 0 < infDist Z C := by
      rcases (infDist_nonneg (x := Z) (s := C)).lt_or_eq with h | h
      · exact h
      · have := ha Z; rw [← h] at this; simp at this; linarith
    have hN : 0 < ‖Z‖ := by
      have hCne : C.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, infDist_empty] at hD
        exact lt_irrefl _ hD
      obtain ⟨p, hp⟩ := hCne
      have h0C : (0 : ComplexModel m) ∈ C := by simpa using hC 0 p hp
      rcases (norm_nonneg Z).lt_or_eq with h | h
      · exact h
      · have hZ0 : Z = 0 := norm_eq_zero.mp h.symm
        rw [hZ0, infDist_zero_of_mem h0C] at hD
        exact absurd hD (lt_irrefl _)
    have hS : 0 < generatorNormSq (polyFun G) Z :=
      lt_of_lt_of_le (by positivity) (hLoj Z)
    have hw : ballWeight (coneWeight r G) 1 0 Z ≤
        ENNReal.ofReal ((generatorNormSq (polyFun G) Z ^ r)⁻¹) := by
      rw [ballWeight_eq_mul (coneWeight_ne_top r G Z), multiplierWeight_coneWeight_of_pos r G hS]
      calc ENNReal.ofReal ((generatorNormSq (polyFun G) Z ^ r)⁻¹) *
            ENNReal.ofReal (Real.exp (-(1 * ‖Z - 0‖ ^ 2)))
          ≤ ENNReal.ofReal ((generatorNormSq (polyFun G) Z ^ r)⁻¹) * 1 := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖Z - 0‖]))
        _ = _ := mul_one _
    calc ENNReal.ofReal (dbarNormSq a Z) * ballWeight (coneWeight r G) 1 0 Z
        ≤ ENNReal.ofReal (M * ‖Z‖ ^ (2 * k - 4) * infDist Z C ^ 2) *
            ENNReal.ofReal (((c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2) ^ r)⁻¹) := by
          gcongr
          · exact ha Z
          · refine hw.trans (ENNReal.ofReal_le_ofReal ?_)
            exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (hLoj Z) r)
      _ = ENNReal.ofReal (M * ‖Z‖ ^ (2 * k - 4) * infDist Z C ^ 2 *
            ((c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2) ^ r)⁻¹) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (K * infDist Z C ^ (2 - 2 * (r : ℝ))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          set D := infDist Z C with hDdef
          set N := ‖Z‖ with hNdef
          have hD2 : D ^ (2 - 2 * (r : ℝ)) = D ^ 2 / (D ^ 2) ^ r := by
            rw [Real.rpow_sub hD, ← pow_mul, Real.rpow_two, ← Real.rpow_natCast D (2 * r)]
            push_cast; ring_nf
          have hEq : M * N ^ (2 * k - 4) * D ^ 2 * ((c * N ^ (2 * (d - 1)) * D ^ 2) ^ r)⁻¹ =
              M * (c ^ r)⁻¹ * N ^ e * D ^ (2 - 2 * (r : ℝ)) := by
            rw [hD2, hesum, pow_add, mul_pow, mul_pow, ← pow_mul]
            have hNe : N ^ (2 * (d - 1) * r) ≠ 0 := pow_ne_zero _ hN.ne'
            have hcr : c ^ r ≠ 0 := pow_ne_zero _ hc.ne'
            have hDr : (D ^ 2) ^ r ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hD.ne')
            field_simp
          rw [hEq, hK]
          have he' : N ^ e ≤ max R 1 ^ e :=
            pow_le_pow_left₀ (norm_nonneg _) ((mem_ball_zero_iff.mp hZ).le.trans (le_max_left _ _)) e
          have hrest : 0 ≤ M * (c ^ r)⁻¹ * D ^ (2 - 2 * (r : ℝ)) := by positivity
          calc M * (c ^ r)⁻¹ * N ^ e * D ^ (2 - 2 * (r : ℝ))
              = (M * (c ^ r)⁻¹ * D ^ (2 - 2 * (r : ℝ))) * N ^ e := by ring
            _ ≤ (M * (c ^ r)⁻¹ * D ^ (2 - 2 * (r : ℝ))) * max R 1 ^ e :=
                mul_le_mul_of_nonneg_left he' hrest
            _ = M * (c ^ r)⁻¹ * max R 1 ^ e * D ^ (2 - 2 * (r : ℝ)) := by ring
  calc ∫⁻ Z in ball (0 : ComplexModel m) R,
        ENNReal.ofReal (dbarNormSq a Z) * ballWeight (coneWeight r G) 1 0 Z
      ≤ ∫⁻ Z in ball (0 : ComplexModel m) R, ENNReal.ofReal (K * infDist Z C ^ (2 - 2 * (r : ℝ))) :=
        setLIntegral_mono' isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal K *
          ∫⁻ Z in ball (0 : ComplexModel m) R, ENNReal.ofReal (infDist Z C ^ (2 - 2 * (r : ℝ))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun Z => ?_
        rw [ENNReal.ofReal_mul hK0]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_ball_infDist_rpow_lt_top hCc hC hr hrm hgraph R)

end SGPT.GAGA.H0
