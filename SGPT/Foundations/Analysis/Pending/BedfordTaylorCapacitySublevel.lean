import SGPT.Foundations.Analysis.Pending.BedfordTaylorNonCharging
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity

set_option autoImplicit false

/-!
# Sublevel sets of a plurisubharmonic function have small relative capacity

Let `ψ` be a plurisubharmonic function, `ψ ≢ -∞`, on a connected neighbourhood of a closed ball
`B̄(z₀, 3R)`.  Then the open sets `{ψ < -k} ∩ B(z₀, R/2)` have relative Monge--Ampère capacity
`O(1/k)` in any open `Ω ⊇ B̄(z₀, 5R)`:

  `c({ψ < -k} ∩ B(z₀, R/2), Ω) ≤ A / (S + k)`   (`exists_relCapacity_sublevel_le`),

with `A`, `S > 0` independent of `k`.  This is the Chern--Levine--Nirenberg estimate for an
unbounded plurisubharmonic weight, *uniform over the competitors* `-1 ≤ v ≤ 0` of the relative
capacity (Bedford--Taylor 1982, Prop. 3.6 / Błocki's lecture notes, Prop. 2.2.4; Demailly,
*Complex analytic and differential geometry*, III.3.11).  In particular a locally pluripolar set
has relative *outer* capacity zero near every point (`tendsto_relCapacity_sublevel`).

*Proof.*  The estimate `exists_sublevel_measure_bound` repeats the argument of
`BedfordTaylor.measure_poleSet_inter_ball_eq_zero`, but keeps track of the constant: for smooth
slots bounded by `M` on `B̄(z₀, 2R)`, the CLN estimate for the truncated weight `max(ψ, -k)`
(`exists_cln_constant_weight`, constant depending on `z₀, R, M` only) bounds the limit measure of
the open set `{ψ < -k} ∩ B(z₀, R/2)` by `C ∫_{B(z₀,R)} (S - ψ) / (S + k)`.  For a competitor `v`
of `c(·, Ω)`, the Bedford--Taylor measure is the limit of the densities of ANY decreasing smooth
approximation `f_l ↓ v` on `B(z₀, 4R)`; since `-1 ≤ v ≤ 0`, Dini's argument
(`IsDecApprox.eventually_le_of_lt`) makes a tail of `f_l` bounded by `1` on `B̄(z₀, 2R)`, so
`M = 1` serves every competitor at once.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- **CLN for an unbounded weight, with an explicit constant.**  For smooth plurisubharmonic
slots bounded by `M` on `B̄(z₀, 2R)` whose mixed densities converge weakly to `μ` on `U ⊇ B̄(z₀, 3R)`,
`μ({ψ < -k} ∩ B(z₀, R/2)) ≤ A / (S + k)`, with `A`, `S` depending only on `z₀, R, M, ψ`. -/
theorem exists_sublevel_measure_bound (z₀ : ComplexModel n) {R M : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) {V : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hVc : IsPreconnected V) (hψ : PlurisubharmonicOn ψ V) (hne : ∃ a ∈ V, ψ a ≠ ⊥)
    (hbV : closedBall z₀ (3 * R) ⊆ V) :
    ∃ A S : ℝ, 0 < S ∧ ∀ (U : Opens (ComplexModel n)) (F : Fin n → ℕ → ComplexModel n → ℝ)
      (μ : Measure (ComplexModel n)), (∀ i l, IsSmoothPsdOn U (F i l)) →
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤) → TendstoMixed U F μ →
      closedBall z₀ (3 * R) ⊆ U →
      (∀ i l, ∀ z ∈ closedBall z₀ (2 * R), |F i l z| ≤ M) →
      ∀ k : ℕ, μ (ball z₀ (R / 2) ∩ {z | ψ z < ((-(k : ℝ) : ℝ) : EReal)}) ≤
        ENNReal.ofReal (A / (S + k)) := by
  classical
  set Ω' : Opens (ComplexModel n) := ⟨ball z₀ (3 * R), isOpen_ball⟩
  have hψ' : PlurisubharmonicOn ψ Ω' := fun x hx ↦ hψ x (hbV (ball_subset_closedBall hx))
  set U2 : Opens (ComplexModel n) := ⟨ball z₀ (5 * R / 2), isOpen_ball⟩
  have hU2rc : RelativelyCompactIn U2 Ω' :=
    ⟨(isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))⟩
  have hU2Ω' : U2 ≤ Ω' := subset_closure.trans hU2rc.2
  have h2U2 : closedBall z₀ (2 * R) ⊆ U2 := closedBall_subset_ball (by linarith)
  obtain ⟨C, hC0, hC⟩ := exists_cln_constant_weight z₀ hR hM
  -- an upper bound for `ψ` and its integrability on the ball
  obtain ⟨S₀, hS₀, hψS₀⟩ := hψ'.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z₀ R) (closedBall_subset_ball (by linarith))
  set S : ℝ := S₀ + 1 with hSdef
  have hS : 0 < S := by positivity
  have hIψ : IntegrableOn (fun z ↦ (ψ z).toReal) (ball z₀ R) :=
    ((hψ.locallyIntegrableOn_toReal volume hVc hne).integrableOn_compact_subset
      ((closedBall_subset_closedBall (by linarith)).trans hbV)
      (isCompact_closedBall z₀ R)).mono_set ball_subset_closedBall
  have hfin : ∀ᵐ z ∂volume.restrict (ball z₀ R), ψ z ≠ ⊤ ∧ ψ z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset
      (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hbV))
      (hψ.ae_finite volume hVc hne)
  set I := ∫ z in ball z₀ R, (S - (ψ z).toReal)
  have : IsFiniteMeasure (volume.restrict (ball z₀ R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine ⟨C * I, S, hS, fun U F μ hFs0 hμf hT hball hFM k ↦ ?_⟩
  have hU2U : U2 ≤ U := fun z hz ↦ hball (ball_subset_closedBall (hU2Ω' hz))
  have hcb (r : ℝ) (hr : r ≤ 3 * R) : closedBall z₀ r ⊆ U :=
    (closedBall_subset_closedBall hr).trans hball
  have hSk : 0 < S + k := by positivity
  set w := truncationReal ψ k with hw_def
  have hw : IsLocallyBoundedPshOn Ω' w := truncationReal_isLocallyBoundedPshOn hψ' k
  obtain ⟨G, hG0⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hw hU2rc
  have hG : IsDecApprox U2 w G := isDecApprox_of_isDecreasingApproximation hw hU2Ω' hG0
  have hwcoe (z : ComplexModel n) (hz : z ∈ Ω') : (w z : EReal) = truncation ψ k z :=
    coe_truncationReal hψ' k hz
  have hwS (z : ComplexModel n) (hz : z ∈ closedBall z₀ R) : w z < S := by
    have hzΩ : z ∈ Ω' := closedBall_subset_ball (by linarith) hz
    have : (w z : EReal) ≤ (S₀ : EReal) := by
      rw [hwcoe z hzΩ]
      exact max_le (hψS₀ z hz) (EReal.coe_le_coe_iff.mpr (by
        linarith [Nat.cast_nonneg (α := ℝ) k]))
    have := EReal.coe_le_coe_iff.mp this
    simp only [hSdef]; linarith
  have hFs (l : ℕ) (i : Fin n) : IsSmoothPsdOn U2 (F i l) :=
    ⟨(hFs0 i l).1.mono hU2U, fun z hz ↦ (hFs0 i l).2 z (hU2U hz)⟩
  have hcln (l : ℕ) := hC U2 (fun i ↦ F i l) w G S h2U2 (hFs l) (fun i ↦ hFM i l) hG hwS
  -- comparison of the weight integral with the integral of `ψ`
  have hwI : ∫ z in ball z₀ R, (S - w z) ≤ I := by
    have h1 : IntegrableOn (fun z ↦ S - w z) (ball z₀ R) := by
      simpa using hG.integrableOn_sub_mul isOpen_ball.measurableSet
        ((isCompact_closedBall z₀ R).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall)
        (closure_ball_subset_closedBall.trans
          ((closedBall_subset_closedBall (by linarith)).trans h2U2))
        (continuousOn_const (c := (1 : ℝ))) S
    refine integral_mono_ae h1 ((integrable_const S).sub hIψ) ?_
    filter_upwards [hfin, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzb
    have hzΩ : z ∈ Ω' := ball_subset_ball (by linarith) hzb
    have : (ψ z).toReal ≤ w z := by
      change (ψ z).toReal ≤ (truncation ψ k z).toReal
      exact EReal.toReal_le_toReal (le_max_left _ _) hz.2 (truncation_ne_top hψ' k hzΩ)
    show S - w z ≤ S - (ψ z).toReal
    linarith
  -- the open set where `ψ < -k`
  set O := ball z₀ (R / 2) ∩ {z | ψ z < ((-(k : ℝ) : ℝ) : EReal)} with hO_def
  have hOo : IsOpen O := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    have hzV : z ∈ V := hbV (ball_subset_closedBall
      (ball_subset_ball (by linarith) hz.1))
    exact inter_mem (isOpen_ball.mem_nhds hz.1)
      ((hψ z hzV).upperSemicontinuousAt _ hz.2)
  have hOcl : closure O ⊆ closedBall z₀ (R / 2) :=
    (closure_mono inter_subset_left).trans closure_ball_subset_closedBall
  have hOc : IsCompact (closure O) :=
    (isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure hOcl
  refine measure_le_of_tendstoMixed_of_isOpen hμf hT hOo hOc
    (hOcl.trans (hcb _ (by linarith))) fun φ hφ hφ01 hφO l ↦ ?_
  set D := mixedDensity (fun i ↦ F i l) with hD_def
  have hDc : ContinuousOn D U2 := continuousOn_mixedDensity fun i ↦ (hFs l i).1
  have hD0 (z : ComplexModel n) (hz : z ∈ U2) : 0 ≤ D z :=
    mixedDensity_nonneg fun i ↦ (hFs l i).2 z hz
  have hB2c : IsCompact (closure (ball z₀ (R / 2))) :=
    (isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hB2U : closure (ball z₀ (R / 2)) ⊆ U2 :=
    closure_ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans h2U2)
  have hstep1 : ∫ z, φ z * D z = ∫ z in ball z₀ (R / 2), φ z * D z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      rw [hφO z fun h ↦ hz h.1, zero_mul]).symm
  have hint1 : IntegrableOn (fun z ↦ φ z * D z) (ball z₀ (R / 2)) :=
    integrableOn_of_continuousOn_closure hB2c hB2U (hφ.continuousOn.mul hDc)
  have hint2 : IntegrableOn (fun z ↦ (S - w z) * D z / (S + k)) (ball z₀ (R / 2)) :=
    (hG.integrableOn_sub_mul isOpen_ball.measurableSet hB2c hB2U hDc S).div_const _
  have hstep2 : ∫ z in ball z₀ (R / 2), φ z * D z ≤
      ∫ z in ball z₀ (R / 2), (S - w z) * D z / (S + k) := by
    refine setIntegral_mono_on hint1 hint2 isOpen_ball.measurableSet fun z hz ↦ ?_
    have hzU2 : z ∈ U2 := h2U2 (closedBall_subset_closedBall (by linarith)
      (ball_subset_closedBall hz))
    have hDz := hD0 z hzU2
    by_cases hzO : z ∈ O
    · have hwz : w z = -(k : ℝ) := by
        change (truncation ψ k z).toReal = _
        rw [truncation, max_eq_right hzO.2.le, EReal.toReal_coe]
      rw [hwz, show (S - -(k : ℝ)) * D z / (S + k) = D z by field_simp; ring]
      exact mul_le_of_le_one_left hDz (hφ01 z).2
    · rw [hφO z hzO, zero_mul]
      have := hwS z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))
      exact div_nonneg (mul_nonneg (by linarith) hDz) hSk.le
  rw [hstep1]
  refine hstep2.trans ?_
  rw [integral_div]
  refine div_le_div_of_nonneg_right ((hcln l).trans ?_) hSk.le
  exact mul_le_mul_of_nonneg_left hwI hC0

/-- **Sublevel sets of a plurisubharmonic function have relative capacity `O(1/k)`**, uniformly
over the competitors: for `Ω ⊇ B̄(z₀, 5R)` and `ψ ≢ -∞` plurisubharmonic on a preconnected
`V ⊇ B̄(z₀, 3R)`, `c({ψ < -k} ∩ B(z₀, R/2), Ω) ≤ A / (S + k)`. -/
theorem exists_relCapacity_sublevel_le (z₀ : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {Ω : Opens (ComplexModel n)} (hΩ : closedBall z₀ (5 * R) ⊆ Ω)
    {V : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hVc : IsPreconnected V) (hψ : PlurisubharmonicOn ψ V) (hne : ∃ a ∈ V, ψ a ≠ ⊥)
    (hbV : closedBall z₀ (3 * R) ⊆ V) :
    ∃ A S : ℝ, 0 < S ∧ ∀ k : ℕ,
      relCapacity Ω (ball z₀ (R / 2) ∩ {z | ψ z < ((-(k : ℝ) : ℝ) : EReal)}) ≤
        ENNReal.ofReal (A / (S + k)) := by
  classical
  obtain ⟨A, S, hS, hbound⟩ :=
    exists_sublevel_measure_bound z₀ hR zero_le_one hVc hψ hne hbV
  refine ⟨A, S, hS, fun k ↦ relCapacity_le_of_forall fun v hv hb ↦ ?_⟩
  have hμ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure_spec Ω v hv
  set μ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω v hv
  set U : Opens (ComplexModel n) := ⟨ball z₀ (4 * R), isOpen_ball⟩ with hUdef
  have hU : RelativelyCompactIn U Ω :=
    ⟨(isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans
        ((closedBall_subset_closedBall (by linarith)).trans hΩ)⟩
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  obtain ⟨f, hf⟩ := (hμ.2.2.2 U hU).1
  have hT0 := (hμ.2.2.2 U hU).2 f hf
  have hG : IsDecApprox U v f := isDecApprox_of_isDecreasingApproximation hv hUΩ hf
  have h2U : closedBall z₀ (2 * R) ⊆ U := closedBall_subset_ball (by linarith)
  obtain ⟨l₀, hl₀⟩ := hG.eventually_le_of_lt (isCompact_closedBall z₀ (2 * R)) h2U
    (S := 1) fun z hz ↦ lt_of_le_of_lt (hb z (hUΩ (h2U hz))).2 zero_lt_one
  have hlow : ∀ l, ∀ z ∈ U, v z ≤ f l z := fun l z hz ↦
    (hf.2.1 z hz).le_of_tendsto (hf.2.2 z hz) l
  set F : Fin n → ℕ → ComplexModel n → ℝ := fun _ l ↦ f (l + l₀) with hFdef
  have hFs : ∀ i l, IsSmoothPsdOn U (F i l) := fun _ l ↦ hG.1 (l + l₀)
  have hT : TendstoMixed U F μ := by
    intro φ hφ hφc hφU
    refine ((hT0 φ hφ hφc hφU).comp (tendsto_add_atTop_nat l₀)).congr fun j ↦ ?_
    simp only [Function.comp_apply, hFdef]
    rw [(smoothMeasure_test_integral (hf.1 (j + l₀)) φ hφ hφc hφU).2.2,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
        simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]]
    simp only [mixedDensity_diagonal]
  have hFM : ∀ i l, ∀ z ∈ closedBall z₀ (2 * R), |F i l z| ≤ 1 := by
    intro i l z hz
    refine abs_le.mpr ⟨?_, hl₀ (l + l₀) (Nat.le_add_left _ _) z hz⟩
    exact (hb z (hUΩ (h2U hz))).1.trans (hlow (l + l₀) z (h2U hz))
  exact hbound U F μ hFs (fun K hK hKU ↦ hμ.2.2.1 K hK (hKU.trans hUΩ)) hT
    (closedBall_subset_ball (by linarith)) hFM k

/-- The relative capacity of the sublevel sets tends to zero. -/
theorem tendsto_relCapacity_sublevel (z₀ : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {Ω : Opens (ComplexModel n)} (hΩ : closedBall z₀ (5 * R) ⊆ Ω)
    {V : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hVc : IsPreconnected V) (hψ : PlurisubharmonicOn ψ V) (hne : ∃ a ∈ V, ψ a ≠ ⊥)
    (hbV : closedBall z₀ (3 * R) ⊆ V) :
    Tendsto (fun k : ℕ ↦
      relCapacity Ω (ball z₀ (R / 2) ∩ {z | ψ z < ((-(k : ℝ) : ℝ) : EReal)})) atTop (𝓝 0) := by
  obtain ⟨A, S, hS, hle⟩ := exists_relCapacity_sublevel_le z₀ hR hΩ hVc hψ hne hbV
  have ht : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (A / (S + k))) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ ↦ A / (S + k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ S tendsto_natCast_atTop_atTop)
    simpa using ENNReal.tendsto_ofReal this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ zero_le) hle

/-- The sublevel set `{ψ < -k} ∩ B(z₀, r)` of a function plurisubharmonic on `V ⊇ B(z₀, r)` is
open (upper semicontinuity). -/
theorem isOpen_ball_inter_sublevel {z₀ : ComplexModel n} {r : ℝ} {V : Set (ComplexModel n)}
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ V) (hbV : ball z₀ r ⊆ V)
    (c : EReal) : IsOpen (ball z₀ r ∩ {z | ψ z < c}) := by
  refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
  exact inter_mem (isOpen_ball.mem_nhds hz.1) ((hψ z (hbV hz.1)).upperSemicontinuousAt _ hz.2)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
