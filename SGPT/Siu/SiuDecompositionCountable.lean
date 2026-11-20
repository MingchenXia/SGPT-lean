import SGPT.Siu.SiuDecompositionLimits
import SGPT.Siu.SiuDecompositionPrimeDivisors

/-!
# Only countably many prime divisors carry positive Lelong number

Source: the proof of Siu's decomposition `eq:Siudec` ("`{E_i}` is a countable collection of prime
divisors"); Xia, *Foundations of pluripotential theory*, `thm:siu-divisorial-decomposition`,
Step 2.  We prove countability by a mass argument instead of the irreducible-component argument
of FPT:

* `currentLelong_eq_zero_of_chartSpanCurrent_eq_zero`: Lelong numbers are local in the current:
  if all readings of `T` on strongly positive test forms supported in an open chart set `U`
  vanish, then `ν(T, x) = 0` on `U` (the zero function is a local potential of `T` there).
* `chartSpanCurrent_eq_zero_of_trace`: a positive current whose trace annihilates a nonnegative
  test function `φ` vanishes on the tests supported in `{φ > 0}` (its coefficients are measures
  dominated by the trace measure).
* `exists_bump_pos_primeDivisorCurrent`: hence `[D]` has positive trace on every chart ball
  meeting `D`, since `ν([D], x) ≥ 1` on `D`.
* `countable_of_finset_dominated`: if `T - c ∑_{D ∈ F} [D] ≥ 0` for every finite set `F` of
  prime divisors from a family `𝒟` (`c > 0`), then `𝒟` is countable: testing against countably
  many bumps (finitely many charts, rational centres and radii), each bump sees only finitely
  many divisors of `𝒟` with trace at least `1/(l+1)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal ContDiff

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open LocalProductCurrents StronglyPositiveForms
open ActualAnalyticCurrentLocalDensity
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open SquaredLogLelongSourceNormalization

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-! ### Locality of Lelong numbers -/

theorem tsupport_monoCLM_subset {Ω U : Opens (ComplexModel (m + 1))} (hU : U ≤ Ω)
    (ψ : 𝓓(U, ℝ)) : tsupport (TestFunction.monoCLM ℝ ψ : 𝓓(Ω, ℝ)) ⊆ U := by
  have h : ((TestFunction.monoCLM ℝ ψ : 𝓓(Ω, ℝ)) : ComplexModel (m + 1) → ℝ) = ψ := by
    have h' := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤) (Ω₂ := Ω) ψ
    simpa only [le_refl, hU, and_self, ↓reduceIte] using h'
  rw [h]
  exact ψ.tsupport_subset

theorem localQuasiPshPotentialOn_zero (U : Opens (ComplexModel (m + 1))) :
    LocalQuasiPshPotentialOn (fun _ : ComplexModel (m + 1) => (0 : EReal)) (U : Set _) := by
  refine ⟨U.isOpen,
    fun x _ => (plurisubharmonicAt_const 0 EReal.zero_ne_top x).quasiPlurisubharmonicAt, ?_⟩
  intro x hx V _ hxV
  exact ⟨x, ⟨hx, hxV⟩, EReal.zero_ne_bot⟩

theorem ddC_regularLocalQuasiPsh_zero (U : Opens (ComplexModel (m + 1)))
    (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)) :
    ddC (ActualQuasiPshPotentialSmoothCompatibility.regularLocalQuasiPsh
      (localQuasiPshPotentialOn_zero U)) w φ = 0 := by
  have hzero : ActualQuasiPshPotentialSmoothCompatibility.regularLocalQuasiPsh
      (localQuasiPshPotentialOn_zero U) = 0 := by
    ext ψ
    rw [ActualQuasiPshPotentialSmoothCompatibility.regularLocalQuasiPsh, regularDistribution_apply]
    simp
  have hw : w = ![w 0, w 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hzero, hw, ddC_apply]
  simp

/-- **Lelong numbers are local in the current.**  If every reading of `T` on strongly positive
test forms supported in an open subset `U` of a chart vanishes, then `ν(T, x) = 0` on `U`. -/
theorem currentLelong_eq_zero_of_chartSpanCurrent_eq_zero
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (e : ComplexChart (m + 1) M) (U : Opens (ComplexModel (m + 1))) (hU : U ≤ chartTarget e)
    (hvan : ∀ (γ : formSpan (m + 1) m) (ψ : 𝓓(chartTarget e, ℝ)),
      tsupport ψ ⊆ U → chartSpanCurrent T e γ ψ = 0)
    {p : M} (hp : p ∈ e.val.source) (hpU : e.val p ∈ U) :
    currentLelong T hT p = 0 := by
  have hread := isOriginalCurrentSourceReader_currentLelong T hT e U hU _
    (localQuasiPshPotentialOn_zero U) (by
      intro w φ
      obtain ⟨γ, hγ⟩ := exists_formSpan_coefficient (m := m) w
      rw [coefficients_eq_chartSpanCurrent hT.2.1 e hγ, ddC_regularLocalQuasiPsh_zero]
      exact hvan γ _ (tsupport_monoCLM_subset hU φ)) p hp hpU
  rw [hread]
  exact SGPT.Okounkov.squaredLogLelongNumber_zero (n := m + 1) (X := ComplexModel (m + 1)) _

/-- A positive local current whose trace annihilates a nonnegative test function `φ` vanishes on
every test function supported in `{φ > 0}`. -/
theorem chartSpanCurrent_eq_zero_of_trace {U : Opens (ComplexModel (m + 1))}
    {P : LocalProductCurrent (m + 1) U m} (hP : IsPositive P) {φ : 𝓓(U, ℝ)}
    (hφ : ∀ x, 0 ≤ φ x) (h0 : P (kahlerPower (m + 1) m) φ = 0) {B : Set (ComplexModel (m + 1))}
    (hB : ∀ x ∈ B, 0 < φ x) (γ : formSpan (m + 1) m) {ψ : 𝓓(U, ℝ)} (hψ : tsupport ψ ⊆ B) :
    P γ ψ = 0 := by
  set μ := hP.traceMeasure
  have hint : Integrable (fun x => φ x) μ := by
    have h := hP.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
      (w := fun _ => (1 : ℝ)) aestronglyMeasurable_const ⟨1, fun _ _ => by simp⟩
    simpa only [mul_one] using h
  have hae : (fun x => φ x) =ᵐ[μ] 0 := by
    rw [← integral_eq_zero_iff_of_nonneg (fun x => hφ x) hint, hP.integral_traceMeasure]
    exact h0
  have hBnull : ∀ᵐ x ∂μ, x ∉ B := by
    filter_upwards [hae] with x hx hxB
    have := hB x hxB
    rw [hx] at this
    exact lt_irrefl _ this
  rw [hP.apply_eq_integral_density γ ψ]
  apply integral_eq_zero_of_ae
  filter_upwards [hBnull] with x hx
  have : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψ h))
  simp [this]

/-! ### Bumps -/

open Classical in
/-- A nonnegative smooth bump in a chart, positive exactly on the ball `B(q, r)` (zero when the
closed ball is not inside the chart target). -/
def chartBump (e : ComplexChart (m + 1) M) (q : ComplexModel (m + 1)) (r : ℝ) :
    𝓓(chartTarget e, ℝ) :=
  if h : 0 < r ∧ closedBall q r ⊆ e.val.target then
    let b : ContDiffBump q := ⟨r / 2, r, half_pos h.1, half_lt_self h.1⟩
    { toFun := b
      contDiff' := b.contDiff
      hasCompactSupport' := b.hasCompactSupport
      tsupport_subset' := by
        rw [b.tsupport_eq]
        exact h.2 }
  else 0

omit [IsComplexManifold (m + 1) M] in
theorem chartBump_nonneg (e : ComplexChart (m + 1) M) (q : ComplexModel (m + 1)) (r : ℝ)
    (x : ComplexModel (m + 1)) : 0 ≤ chartBump e q r x := by
  unfold chartBump
  split_ifs with h
  · exact ContDiffBump.nonneg _
  · exact le_rfl

omit [IsComplexManifold (m + 1) M] in
theorem chartBump_pos (e : ComplexChart (m + 1) M) {q : ComplexModel (m + 1)} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall q r ⊆ e.val.target) {x : ComplexModel (m + 1)}
    (hx : x ∈ ball q r) : 0 < chartBump e q r x := by
  unfold chartBump
  rw [dif_pos ⟨hr, hsub⟩]
  exact ContDiffBump.pos_of_mem_ball _ hx

/-- **`[D]` has positive trace on every chart ball meeting `D`.** -/
theorem chartSpanCurrent_primeDivisorCurrent_bump_pos [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (e : ComplexChart (m + 1) M)
    {q : ComplexModel (m + 1)} {r : ℝ} (hr : 0 < r) (hsub : closedBall q r ⊆ e.val.target)
    {x : M} (hxD : x ∈ D.val) (hxs : x ∈ e.val.source) (hxB : e.val x ∈ ball q r) :
    0 < chartSpanCurrent (primeDivisorCurrent D) e (kahlerPower (m + 1) m) (chartBump e q r) := by
  have hD := isClosedPositiveCurrent_primeDivisorCurrent D
  have hpos := isPositive_chartSpanCurrent _ hD.2.2 e
  rcases (hpos.positiveDistribution_trace _ (chartBump_nonneg e q r)).lt_or_eq with h | h
  · exact h
  exfalso
  let U : Opens (ComplexModel (m + 1)) := ⟨ball q r, isOpen_ball⟩
  have hU : U ≤ chartTarget e := fun z hz => hsub (ball_subset_closedBall hz)
  have hzero := currentLelong_eq_zero_of_chartSpanCurrent_eq_zero hD e U hU
    (fun γ ψ hψ => chartSpanCurrent_eq_zero_of_trace hpos (chartBump_nonneg e q r) h.symm
      (fun z hz => chartBump_pos e hr hsub hz) γ hψ) hxs hxB
  have hone := one_le_currentLelong_primeDivisorCurrent D hxD
  rw [hzero] at hone
  exact absurd hone (by norm_num)

/-! ### Countability -/

theorem chartSpanCurrent_sum {ι : Type*} (F : Finset ι)
    (A : ι → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (e : ComplexChart (m + 1) M)
    (γ : formSpan (m + 1) m) (φ : 𝓓(chartTarget e, ℝ)) :
    chartSpanCurrent (∑ i ∈ F, A i) e γ φ = ∑ i ∈ F, chartSpanCurrent (A i) e γ φ := by
  classical
  induction F using Finset.induction_on with
  | empty => rfl
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      rfl

theorem chartSpanCurrent_smul (c : ℝ) (A : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) (γ : formSpan (m + 1) m) (φ : 𝓓(chartTarget e, ℝ)) :
    chartSpanCurrent (c • A) e γ φ = c * chartSpanCurrent A e γ φ := rfl

/-- **Countability.**  Let `T` be a closed positive current and `c > 0`.  If
`T - c ∑_{D ∈ F} [D]` is positive for every finite set `F` of prime divisors taken from `𝒟`,
then `𝒟` is countable. -/
theorem countable_of_finset_dominated [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) {c : ℝ} (hc : 0 < c)
    (𝒟 : Set (SGPT.PSH.GeometricPrimeCarrier (m + 1) M))
    (hdom : ∀ F : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) M), (↑F : Set _) ⊆ 𝒟 →
      IsFullPositive (T - ∑ D ∈ F, c • primeDivisorCurrent D)) :
    𝒟.Countable := by
  classical
  -- finitely many charts cover `M`
  obtain ⟨xs, hxs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (complexChartAt (n := m + 1) x).val.source)
    (fun x => (complexChartAt (n := m + 1) x).val.open_source)
    (fun x _ => mem_iUnion.2 ⟨x, mem_complexChartAt_source x⟩)
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense (ComplexModel (m + 1))
  let κp : formSpan (m + 1) m := kahlerPower (m + 1) m
  let I := xs × S × ℕ × ℕ
  let test : I → ℝ := fun i =>
    chartSpanCurrent T (complexChartAt (n := m + 1) (i.1 : M)) κp
      (chartBump (complexChartAt (n := m + 1) (i.1 : M)) i.2.1 (1 / ((i.2.2.1 : ℝ) + 1)))
  let fib : I → Set (SGPT.PSH.GeometricPrimeCarrier (m + 1) M) := fun i =>
    {D | D ∈ 𝒟 ∧ 1 / ((i.2.2.2 : ℝ) + 1) ≤
      chartSpanCurrent (primeDivisorCurrent D) (complexChartAt (n := m + 1) (i.1 : M)) κp
        (chartBump (complexChartAt (n := m + 1) (i.1 : M)) i.2.1 (1 / ((i.2.2.1 : ℝ) + 1)))}
  -- every divisor of `𝒟` lies in some fibre
  have hcover : 𝒟 ⊆ ⋃ i : I, fib i := by
    intro D hD
    obtain ⟨x, hxD⟩ := D.nonempty
    obtain ⟨y, hyxs, hxy⟩ : ∃ y ∈ xs, x ∈ (complexChartAt (n := m + 1) y).val.source := by
      have := hxs (mem_univ x)
      simpa only [mem_iUnion, exists_prop] using this
    set e := complexChartAt (n := m + 1) y
    have hxt : e.val x ∈ e.val.target := e.val.map_source hxy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.val.open_target _ hxt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
    set r : ℝ := 1 / ((k : ℝ) + 1)
    have hr : 0 < r := by positivity
    obtain ⟨q, hqS, hq⟩ := hSdense.exists_mem_open (isOpen_ball (x := e.val x) (ε := r))
      ⟨_, mem_ball_self hr⟩
    have hxB : e.val x ∈ ball q r := by rw [mem_ball_comm]; exact hq
    have hsub : closedBall q r ⊆ e.val.target := by
      intro z hz
      apply hball
      rw [mem_ball]
      calc dist z (e.val x) ≤ dist z q + dist q (e.val x) := dist_triangle _ _ _
        _ < r + r := add_lt_add_of_le_of_lt (mem_closedBall.mp hz) (mem_ball.mp hq)
        _ < ε := by linarith
    have hpos := chartSpanCurrent_primeDivisorCurrent_bump_pos D e hr hsub hxD hxy hxB
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hpos
    refine mem_iUnion.2 ⟨⟨⟨y, hyxs⟩, ⟨q, hqS⟩, k, l⟩, hD, ?_⟩
    exact hl.le
  -- every fibre is finite
  have hfin : ∀ i : I, (fib i).Finite := by
    intro i
    by_contra hinf
    obtain ⟨N, hN⟩ := exists_nat_gt (test i * ((i.2.2.2 : ℝ) + 1) / c)
    obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have hF𝒟 : (↑F : Set _) ⊆ 𝒟 := fun D hD => (hFsub hD).1
    set e := complexChartAt (n := m + 1) (i.1 : M)
    set φ := chartBump e i.2.1 (1 / ((i.2.2.1 : ℝ) + 1))
    have hpos := (isPositive_chartSpanCurrent _ (hdom F hF𝒟) e).positiveDistribution_trace φ
      (chartBump_nonneg e _ _)
    rw [chartSpanCurrent_sub] at hpos
    change 0 ≤ chartSpanCurrent T e κp φ -
      chartSpanCurrent (∑ D ∈ F, c • primeDivisorCurrent D) e κp φ
      at hpos
    rw [chartSpanCurrent_sum] at hpos
    simp only [chartSpanCurrent_smul] at hpos
    have hlow : ∑ D ∈ F, c * (1 / ((i.2.2.2 : ℝ) + 1)) ≤
        ∑ D ∈ F, c * chartSpanCurrent (primeDivisorCurrent D) e κp φ :=
      Finset.sum_le_sum fun D hD => mul_le_mul_of_nonneg_left (hFsub hD).2 hc.le
    rw [Finset.sum_const, hFcard, nsmul_eq_mul] at hlow
    have hl1 : (0 : ℝ) < (i.2.2.2 : ℝ) + 1 := by positivity
    have htest : test i = chartSpanCurrent T e κp φ := rfl
    have h1 : (N : ℝ) * (c * (1 / ((i.2.2.2 : ℝ) + 1))) ≤ test i := by linarith
    have h2 : test i * ((i.2.2.2 : ℝ) + 1) / c < N := hN
    rw [div_lt_iff₀ hc] at h2
    have h3 : (N : ℝ) * c ≤ test i * ((i.2.2.2 : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_right h1 hl1.le
      rwa [mul_assoc, mul_assoc, one_div, inv_mul_cancel₀ hl1.ne', mul_one] at this
    linarith
  have hIcount : Countable I := by
    have : Countable S := hScount.to_subtype
    infer_instance
  exact (Set.countable_iUnion fun i => (hfin i).countable).mono hcover

end SGPT.Siu
