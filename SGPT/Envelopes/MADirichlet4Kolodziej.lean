import SGPT.Envelopes.MADirichlet4Barrier

/-!
# Kołodziej's theorem: the limit lies above the barrier

Xia, *Foundations of pluripotential theory* (FPT), Steps 2 and 3 of the proof of
`thm:compact-bounded-subsolution-ball-dirichlet`, for a bounded open set `Q` (a polydisk in the
application).

Let `α` be a finite measure carried by a compact `K ⊆ Q` and `W` a bounded plurisubharmonic
function with `-B ≤ W ≤ 0` and `(ddᶜW)ⁿ ≥ α` on `Q` (the barrier of `exists_barrier`). Let
`U_j ∈ ℰ₀(Q)` with Monge–Ampère measures `μ_j` carried by a fixed compact `K₀ ⊆ Q`, `μ_j → α`
weakly, `e₁(U_j) ≤ C`, and satisfying the self-integral convergence of the truncations
(`tendsto_lintegral_convDensity_abs_sub` for the convolution approximants). If a subsequence
`U_{σ_k}` converges in `L¹_loc(Q)` to a plurisubharmonic `v`, then `W ≤ v` on `Q`
(`coe_le_of_approximants`); in particular `v` is bounded.

*Proof* (FPT). For `ε > 0` put `W_ε = W + ε(|z|² - M')` (`|z|² ≤ M'` on `Q`), so
`(ddᶜW_ε)ⁿ ≥ α + cₙεⁿ dV` (MA-DIR `ma_add_normSq_ge`). For a level `δ` and `s > 0`, the comparison
principle gives `(ddᶜW_ε)ⁿ{U_j < W_ε - δ} ≤ μ_j{U_j < W_ε - δ}`. With the truncations at a large
level `T`, `a_j = max(U_j, -T)`, `b_T = max(v, -T)`:
`{v < W_ε - δ - s} ∩ L ⊆ {U_j < W_ε - δ} ∪ (L ∩ {|a_j - b_T| > s/2})` and
`{U_j < W_ε - δ} ⊆ {b_T - W_ε < -δ + s} ∪ {U_j < -T} ∪ {a_j < b_T - s}`. The terms are controlled
by: the fixed-measure continuity (`tendsto_integral_abs_sub_of_localL1`) for
`(ddᶜW_ε)ⁿ|_L`; `μ_j{U_j < -T} ≤ C/T`; the self-integral convergence; and the capacity-controlled
weak convergence for the quasi-continuous weight `b_T - W_ε` (`eventually_measure_lt_le`). Hence
`α{v < W_ε - δ - s} + cₙεⁿ vol({v < W_ε - δ - s} ∩ L) ≤ α{v ≤ W_ε - δ + 2s}`; letting `s ↓ 0` at a
level `δ` with `α{v = W_ε - δ} = 0` gives `vol{v < W_ε - δ} = 0`, so `v ≥ W_ε - δ` everywhere;
then `δ ↓ 0` and `ε ↓ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-! ### Truncations of extended-real limits -/

/-- Truncation is `1`-Lipschitz for TN's canonical extended distance. -/
theorem ofReal_abs_max_sub_le (x : ℝ) (y : EReal) (T : ℝ) :
    ENNReal.ofReal |max x (-T) - (max y ((-T : ℝ) : EReal)).toReal| ≤
      canonicalERealAbsDiff (x : EReal) y := by
  induction y using EReal.rec with
  | bot => rw [canonicalERealAbsDiff_bot_right (EReal.coe_ne_bot x)]; exact le_top
  | top =>
    have : canonicalERealAbsDiff (x : EReal) ⊤ = ⊤ := by
      simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    rw [this]; exact le_top
  | coe y =>
    rw [canonicalERealAbsDiff_coe_coe, ← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe]
    exact ENNReal.ofReal_le_ofReal (abs_max_sub_max_le_abs x y (-T))

/-- The truncation `max(v, -T)` of a plurisubharmonic function, as a real function. -/
def truncReal (v : ComplexModel n → EReal) (T : ℝ) (z : ComplexModel n) : ℝ :=
  (max (v z) ((-T : ℝ) : EReal)).toReal

theorem coe_truncReal {Q : Opens (ComplexModel n)} {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Q) (T : ℝ) {z : ComplexModel n} (hz : z ∈ Q) :
    (truncReal v T z : EReal) = max (v z) ((-T : ℝ) : EReal) := by
  refine EReal.coe_toReal ?_ ?_
  · exact max_ne_top ((hv z hz).ne_top) (EReal.coe_ne_top _)
  · exact ne_of_gt ((EReal.bot_lt_coe _).trans_le (le_max_right _ _))

theorem neg_le_truncReal (v : ComplexModel n → EReal) {T : ℝ} (z : ComplexModel n)
    (hz : v z ≠ ⊤) : -T ≤ truncReal v T z := by
  rw [truncReal]
  have h1 : max (v z) ((-T : ℝ) : EReal) ≠ ⊤ := max_ne_top hz (EReal.coe_ne_top _)
  have := EReal.toReal_le_toReal (le_max_right (v z) ((-T : ℝ) : EReal)) (EReal.coe_ne_bot _) h1
  simpa using this

theorem isLocallyBoundedPshOn_truncReal {Q : Opens (ComplexModel n)} {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Q) (T : ℝ) : IsLocallyBoundedPshOn Q (truncReal v T) := by
  have hmax : PlurisubharmonicOn (fun z => max (v z) ((-T : ℝ) : EReal)) Q :=
    hv.max fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x
  refine ⟨fun x hx => (hmax x hx).congr ?_, fun z hz => ?_⟩
  · filter_upwards [Q.isOpen.mem_nhds hx] with y hy
    exact (coe_truncReal hv T hy).symm
  · obtain ⟨r, hr, hrQ⟩ := Metric.isOpen_iff.mp Q.isOpen z hz
    obtain ⟨C, hC0, hC⟩ := hv.exists_nonnegative_compact_upper_bound (isCompact_closedBall z (r / 2))
      ((closedBall_subset_ball (by linarith)).trans hrQ)
    refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by positivity),
      (ball_subset_ball (by linarith)).trans hrQ, max C |T|, fun y hy => ?_⟩
    have hyQ : y ∈ (Q : Set (ComplexModel n)) := hrQ (ball_subset_ball (by linarith) hy)
    have hlow := neg_le_truncReal v y (hv y hyQ).ne_top (T := T)
    have hup : truncReal v T y ≤ max C (-T) := by
      have h := coe_truncReal hv T hyQ
      have h2 : (truncReal v T y : EReal) ≤ ((max C (-T) : ℝ) : EReal) := by
        rw [h, EReal.coe_strictMono.monotone.map_max]
        exact max_le_max (hC y (ball_subset_closedBall hy)) le_rfl
      exact EReal.coe_le_coe_iff.mp h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [le_abs_self T, le_max_right C |T|]
    · exact hup.trans (max_le_max le_rfl (neg_le_abs T))

/-- Canonical `L¹_loc` convergence passes to the real truncations. -/
theorem tendsto_lintegral_truncReal {Q : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {v : ComplexModel n → EReal}
    (hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, canonicalERealAbsDiff (f k x : EReal) (v x)) atTop (𝓝 0))
    (T : ℝ) : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |max (f k x) (-T) - truncReal v T x|) atTop
        (𝓝 0) := fun L hL hLQ =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim L hL hLQ) (fun _ => bot_le)
    fun k => lintegral_mono fun x => ofReal_abs_max_sub_le (f k x) (v x) T

/-- Quasi-continuity is a property of the values on `D`. -/
theorem IsQuasiContinuousOn.congr {D : Opens (ComplexModel n)} {f g : ComplexModel n → ℝ}
    (hf : IsQuasiContinuousOn D f) (h : EqOn f g D) : IsQuasiContinuousOn D g := by
  intro L hL hLD ε hε
  obtain ⟨G, hG, hc, hfc⟩ := hf L hL hLD ε hε
  exact ⟨G, hG, hc, hfc.congr fun x hx => (h (hLD hx.1)).symm⟩

/-! ### The approximation hypotheses -/

/-- The properties of a sequence of approximants used in Kołodziej's theorem (FPT
`prop:canonical-grid-energy-control`, `thm:canonical-grid-self-integral-convergence`): `U_j ∈ ℰ₀(Q)`
on a bounded `Q`, Monge–Ampère measures carried by a fixed compact subset and converging weakly
to `α`, bounded energies `e₁`, and the self-integral convergence of the truncations. -/
structure IsKolodziejApprox (Q : Opens (ComplexModel n)) (α : Measure (ComplexModel n))
    (U : ℕ → ComplexModel n → ℝ) : Prop where
  bounded : Bornology.IsBounded (Q : Set (ComplexModel n))
  cegrell : ∀ j, IsCegrellE0 Q (U j)
  carrier : ∃ K₀ : Set (ComplexModel n), IsCompact K₀ ∧ K₀ ⊆ Q ∧
    ∀ j, canonicalBedfordTaylorMeasure Q (U j) (cegrell j).psh K₀ᶜ = 0
  weak : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
    Tendsto (fun j => ∫ x, h x ∂canonicalBedfordTaylorMeasure Q (U j) (cegrell j).psh) atTop
      (𝓝 (∫ x, h x ∂α))
  energy : ∃ C : ℝ, ∀ j, (localEnergy Q 1 (U j) (cegrell j).psh).toReal ≤ C
  selfIntegral : ∀ T : ℝ, 0 < T → ∀ σ : ℕ → ℕ, StrictMono σ → ∀ b : ComplexModel n → ℝ,
    IsLocallyBoundedPshOn Q b →
    (∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |max (U (σ k) x) (-T) - b x|) atTop (𝓝 0)) →
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal |max (U (σ k) x) (-T) - b x|
      ∂canonicalBedfordTaylorMeasure Q (U (σ k)) (cegrell (σ k)).psh) atTop (𝓝 0)

/-- The capacity modulus of the approximants (MA-DIR3 `ma_le_relCapacity_add_of_localEnergy_le`):
uniformly in `j`, `μ_j(E)` is small when `Cap_Q(E)` is small. -/
theorem IsKolodziejApprox.modulus (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox Q α U)
    {r : ℝ} (hr : 0 < r) : ∃ η : ℝ≥0∞, 0 < η ∧ ∀ j, ∀ E : Set (ComplexModel n), E ⊆ Q →
      relCapacity Q E < η →
        canonicalBedfordTaylorMeasure Q (U j) (hA.cegrell j).psh E ≤ ENNReal.ofReal r := by
  obtain ⟨C, hC⟩ := hA.energy
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hC 0)
  set T : ℝ := 2 * C / r + 1 with hTdef
  have hT : 0 < T := by positivity
  have hCT : C / T ≤ r / 2 := by
    rw [div_le_iff₀ hT, hTdef]
    have : r / 2 * (2 * C / r + 1) = C + r / 2 := by field_simp
    rw [this]; linarith
  have hTn : 0 < T ^ n := pow_pos hT n
  refine ⟨ENNReal.ofReal (r / 2 / T ^ n), ENNReal.ofReal_pos.mpr (by positivity),
    fun j E hEQ hE => ?_⟩
  have h := ma_le_relCapacity_add_of_localEnergy_le hn hA.bounded hA.cegrell hC j hT hEQ
  refine h.trans ?_
  calc ENNReal.ofReal (T ^ n) * relCapacity Q E + ENNReal.ofReal (C / T)
      ≤ ENNReal.ofReal (T ^ n) * ENNReal.ofReal (r / 2 / T ^ n) + ENNReal.ofReal (r / 2) :=
        add_le_add (mul_le_mul_right hE.le _) (ENNReal.ofReal_le_ofReal hCT)
    _ = ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := by
        rw [← ENNReal.ofReal_mul hTn.le, mul_div_cancel₀ _ hTn.ne']
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- Canonical measures on `Q` are carried by `Q`. -/
theorem canonicalBedfordTaylorMeasure_compl {Q : Opens (ComplexModel n)} {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Q φ) :
    canonicalBedfordTaylorMeasure Q φ hφ (Q : Set (ComplexModel n))ᶜ = 0 :=
  (isBTLimit_canonicalBedfordTaylorMeasure hφ).1

/-- **The single-scale estimate** of FPT's Steps 2 and 3: for a bounded psh `V` with
`-B ≤ V ≤ 0` (later `V = W_ε`), levels `0 < δ < 1`, `0 < s < 1/4`, a compact `L ⊆ Q` and
`η > 0`, `(ddᶜV)ⁿ({v < V - δ - s} ∩ L) ≤ α{v ≤ V - δ + 2s} + η`. -/
theorem measure_sublevel_inter_le (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKQ : K ⊆ Q) (hαK : α Kᶜ = 0) {U : ℕ → ComplexModel n → ℝ}
    (hA : IsKolodziejApprox Q α U) {V : ComplexModel n → ℝ} (hV : IsLocallyBoundedPshOn Q V)
    {B : ℝ} (hB : 0 ≤ B) (hVb : ∀ z ∈ Q, -B ≤ V z ∧ V z ≤ 0) {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Q) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, canonicalERealAbsDiff (U (σ k) x : EReal) (v x)) atTop (𝓝 0))
    {δ s η : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) (hs1 : s < 1 / 4) (hη : 0 < η)
    {L : Set (ComplexModel n)} (hL : IsCompact L) (hLQ : L ⊆ Q) :
    canonicalBedfordTaylorMeasure Q V hV
        ({z | z ∈ Q ∧ v z < ((V z - δ - s : ℝ) : EReal)} ∩ L) ≤
      α {z | z ∈ Q ∧ v z ≤ ((V z - δ + 2 * s : ℝ) : EReal)} + ENNReal.ofReal η := by
  classical
  obtain ⟨K₀, hK₀, hK₀Q, hμK⟩ := hA.carrier
  obtain ⟨C, hC⟩ := hA.energy
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hC 0)
  set μ : ℕ → Measure (ComplexModel n) :=
    fun j => canonicalBedfordTaylorMeasure Q (U j) (hA.cegrell j).psh with hμdef
  have hQm : MeasurableSet (Q : Set (ComplexModel n)) := Q.isOpen.measurableSet
  have hμfin : ∀ j, IsFiniteMeasure (μ j) := fun j => ⟨by
    rw [← measure_add_measure_compl hK₀.measurableSet, hμK j, add_zero]
    exact (isBTLimit_canonicalBedfordTaylorMeasure (hA.cegrell j).psh).2.1 K₀ hK₀ hK₀Q⟩
  -- the truncation level
  set T : ℝ := B + 2 + 4 * C / η with hTdef
  have hT : 0 < T := by positivity
  have hTB : B + 2 ≤ T := by rw [hTdef]; have : 0 ≤ 4 * C / η := by positivity
                             linarith
  have hCT : C / T ≤ η / 4 := by
    rcases eq_or_lt_of_le hC0 with h | h
    · rw [← h, zero_div]; positivity
    · rw [div_le_iff₀ hT]
      have : 4 * C / η ≤ T := by rw [hTdef]; linarith
      have h2 : η / 4 * (4 * C / η) = C := by field_simp
      nlinarith
  set a : ℕ → ComplexModel n → ℝ := fun k z => max (U (σ k) z) (-T) with hadef
  set bT : ComplexModel n → ℝ := truncReal v T with hbTdef
  have hbT : IsLocallyBoundedPshOn Q bT := isLocallyBoundedPshOn_truncReal hv T
  have hconst : IsLocallyBoundedPshOn Q fun _ => (-T : ℝ) := by
    simpa using IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_zero Q) (-T)
  have ha : ∀ k, IsLocallyBoundedPshOn Q (a k) := fun k =>
    IsLocallyBoundedPshOn.max (hA.cegrell (σ k)).psh hconst
  have haT : ∀ k, ∀ z ∈ Q, |a k z| ≤ T := fun k z hz => by
    refine abs_le.mpr ⟨le_max_right _ _, max_le ?_ (by linarith)⟩
    exact ((hA.cegrell (σ k)).nonpos z hz).trans hT.le
  have hab := tendsto_lintegral_truncReal hlim T
  -- (E3) the self-integral convergence
  have hE3 := hA.selfIntegral T hT σ hσ bT hbT hab
  -- (E5) the fixed-measure continuity for `(ddᶜV)ⁿ|_L`
  set νV := canonicalBedfordTaylorMeasure Q V hV with hνVdef
  set νL := νV.restrict L with hνLdef
  have hνLfin : IsFiniteMeasure νL := ⟨by
    rw [hνLdef, Measure.restrict_apply_univ]
    exact (isBTLimit_canonicalBedfordTaylorMeasure hV).2.1 L hL hLQ⟩
  have hcapnull : CapacityNull Q νL := capacityNull_of_le_ma hV hB
    (fun z hz => ⟨(hVb z hz).1, by linarith [(hVb z hz).2]⟩)
    (Measure.restrict_le_self.trans Measure.restrict_le_self)
  have hE5 := tendsto_integral_abs_sub_of_localL1 ha hbT haT hab hcapnull
  -- (E4) the capacity-controlled weak convergence for the weight `b_T - V`
  set f : ComplexModel n → ℝ := fun z => (Q : Set (ComplexModel n)).indicator bT z -
    (Q : Set (ComplexModel n)).indicator V z with hfdef
  have hfm : Measurable f := (measurable_indicator_of_plurisubharmonicOn hbT.1).sub
    (measurable_indicator_of_plurisubharmonicOn hV.1)
  have hfq : IsQuasiContinuousOn Q f :=
    ((isQuasiContinuousOn_of_isLocallyBoundedPshOn hbT).sub
      (isQuasiContinuousOn_of_isLocallyBoundedPshOn hV)).congr fun z hz => by
        simp [hfdef, indicator_of_mem hz]
  have hE4 := eventually_measure_lt_le (μ := fun k => μ (σ k)) (ν := α) (hK₀.union hK)
    (union_subset hK₀Q hKQ) (fun k => measure_mono_null (compl_subset_compl.mpr subset_union_left)
      (hμK (σ k))) (measure_mono_null (compl_subset_compl.mpr subset_union_right) hαK)
    (fun h hc hk => (hA.weak h hc hk).comp hσ.tendsto_atTop)
    (fun r hr => by
      obtain ⟨η', hη', h'⟩ := hA.modulus hn hr
      exact ⟨η', hη', fun k => h' (σ k)⟩) hfm hfq (-δ + s) hs (ε := η / 4) (by positivity)
  -- choose one large index
  have hev3 : ∀ᶠ k in atTop, ENNReal.ofReal (1 / s) *
      ∫⁻ x, ENNReal.ofReal |a k x - bT x| ∂μ (σ k) < ENNReal.ofReal (η / 4) := by
    have h := ENNReal.Tendsto.const_mul hE3 (a := ENNReal.ofReal (1 / s)) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h
    exact (tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.mpr (by positivity))
  have hev5 : ∀ᶠ k in atTop, ∫ x in (Q : Set (ComplexModel n)), |a k x - bT x| ∂νL <
      s / 2 * (η / 4) := (tendsto_order.1 hE5).2 _ (by positivity)
  obtain ⟨k, hk3, hk4, hk5⟩ := (hev3.and (hE4.and hev5)).exists
  set j := σ k with hjdef
  have hUj := (hA.cegrell j).psh
  -- (E2) the deep sublevel set
  have hE2 : μ j {z | z ∈ Q ∧ U j z < -T} ≤ ENNReal.ofReal (η / 4) := by
    have h := ma_sublevel_le_localEnergy hUj (p := 1) (s := T) one_pos hT
    have hE : localEnergy Q 1 (U j) hUj ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_toReal ((hA.cegrell j).localEnergy_ne_top zero_le_one)]
      exact ENNReal.ofReal_le_ofReal (hC j)
    refine h.trans ((mul_le_mul_right hE _).trans ?_)
    rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_neg_one, inv_mul_eq_div]
    exact ENNReal.ofReal_le_ofReal hCT
  -- (E3') the shallow set
  have hE3' : μ j {z | a k z < bT z - s} ≤ ENNReal.ofReal (η / 4) := by
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal |a k x - bT x|) (μ j) := by
      have h1 : μ j = (μ j).restrict Q :=
        (Measure.restrict_eq_self_of_ae_mem ((measure_eq_zero_iff_ae_notMem.mp
          (canonicalBedfordTaylorMeasure_compl hUj)).mono fun x hx => by simpa using hx)).symm
      rw [h1]
      exact (continuous_abs.measurable.comp_aemeasurable
        ((aemeasurable_of_isLocallyBoundedPshOn (ha k) (μ j)).sub
          (aemeasurable_of_isLocallyBoundedPshOn hbT (μ j)))).ennreal_ofReal
    have hcheb := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal s)
    have hsub : {z | a k z < bT z - s} ⊆ {x | ENNReal.ofReal s ≤ ENNReal.ofReal |a k x - bT x|} :=
      fun z hz => ENNReal.ofReal_le_ofReal (by
        have : a k z < bT z - s := hz
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith)
    calc μ j {z | a k z < bT z - s}
        ≤ μ j {x | ENNReal.ofReal s ≤ ENNReal.ofReal |a k x - bT x|} := measure_mono hsub
      _ = ENNReal.ofReal (1 / s) * (ENNReal.ofReal s *
            μ j {x | ENNReal.ofReal s ≤ ENNReal.ofReal |a k x - bT x|}) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div,
            inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (1 / s) * ∫⁻ x, ENNReal.ofReal |a k x - bT x| ∂μ j :=
          mul_le_mul_right hcheb _
      _ ≤ ENNReal.ofReal (η / 4) := hk3.le
  -- (E5') the fixed measure
  set S5 : Set (ComplexModel n) := {z | s / 2 < |a k z - bT z|} with hS5def
  have hE5' : νV (L ∩ S5) ≤ ENNReal.ofReal (η / 4) := by
    have hm : νL.restrict Q = νL := by
      rw [hνLdef, Measure.restrict_restrict hQm, inter_eq_right.mpr hLQ]
    have hi : Integrable (fun x => |a k x - bT x|) (νL.restrict Q) :=
      ((integrable_of_isLocallyBoundedPshOn (ν := νL) (ha k) (haT k)).sub
        (integrable_of_isLocallyBoundedPshOn (ν := νL) hbT
          (abs_le_of_localL1 ha hbT haT hab))).abs
    have hcheb := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun x => abs_nonneg (a k x - bT x)) hi (s / 2)
    have hreal : (νL.restrict Q).real {x | s / 2 ≤ |a k x - bT x|} ≤ η / 4 := by
      have h1 := hcheb.trans hk5.le
      have h2 : 0 < s / 2 := by positivity
      nlinarith
    calc νV (L ∩ S5) = νL S5 := by
          rw [hνLdef, Measure.restrict_apply' hL.measurableSet, inter_comm]
      _ ≤ νL {x | s / 2 ≤ |a k x - bT x|} :=
          measure_mono fun x hx => (show s / 2 < |a k x - bT x| from hx).le
      _ = (νL.restrict Q) {x | s / 2 ≤ |a k x - bT x|} := by rw [hm]
      _ = ENNReal.ofReal ((νL.restrict Q).real {x | s / 2 ≤ |a k x - bT x|}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (η / 4) := ENNReal.ofReal_le_ofReal hreal
  -- (E6) the comparison principle
  have hVδ : IsLocallyBoundedPshOn Q fun z => V z + -δ := IsLocallyBoundedPshOn.add_const hV (-δ)
  have hE6 : νV {z | z ∈ Q ∧ U j z < V z + -δ} ≤ μ j {z | z ∈ Q ∧ U j z < V z + -δ} := by
    have h := SGPT.PSH.BookDeepDomination.measure_lt_le_of_boundary hn hA.bounded hUj hVδ
      (fun ζ hζ η' hη' => by
        filter_upwards [((hA.cegrell j).tendsto_frontier ζ hζ).eventually
          (Ioi_mem_nhds (show -η' < (0 : ℝ) by linarith)), self_mem_nhdsWithin] with z hz hzQ
        have := (hVb z hzQ).2
        have hz' : -η' < U j z := hz
        linarith)
      (isBTLimit_canonicalBedfordTaylorMeasure hUj) (isBTLimit_canonicalBedfordTaylorMeasure hVδ)
    rwa [canonicalBedfordTaylorMeasure_add_const hV (-δ) hVδ] at h
  -- the set inclusions
  have hE7 : {z | z ∈ Q ∧ v z < ((V z - δ - s : ℝ) : EReal)} ∩ L ⊆
      {z | z ∈ Q ∧ U j z < V z + -δ} ∪ (L ∩ S5) := by
    rintro z ⟨⟨hzQ, hz⟩, hzL⟩
    by_cases hU : U j z < V z + -δ
    · exact Or.inl ⟨hzQ, hU⟩
    · refine Or.inr ⟨hzL, ?_⟩
      have hU' : V z - δ ≤ U j z := by linarith [not_lt.mp hU]
      have haz : a k z = U j z := max_eq_left (by linarith [(hVb z hzQ).1])
      have hbz : bT z < V z - δ - s := by
        have h1 : (bT z : EReal) < ((V z - δ - s : ℝ) : EReal) := by
          rw [hbTdef, coe_truncReal hv T hzQ]
          exact max_lt hz (EReal.coe_lt_coe_iff.mpr (by linarith [(hVb z hzQ).1]))
        exact EReal.coe_lt_coe_iff.mp h1
      show s / 2 < |a k z - bT z|
      rw [haz, abs_of_pos (by linarith)]
      linarith
  have hE8 : {z | z ∈ Q ∧ U j z < V z + -δ} ⊆
      ({z | f z < -δ + s} ∪ {z | z ∈ Q ∧ U j z < -T}) ∪ {z | a k z < bT z - s} := by
    rintro z ⟨hzQ, hz⟩
    by_cases hT' : U j z < -T
    · exact Or.inl (Or.inr ⟨hzQ, hT'⟩)
    · have haz : a k z = U j z := max_eq_left (not_lt.mp hT')
      by_cases hab' : a k z < bT z - s
      · exact Or.inr hab'
      · refine Or.inl (Or.inl ?_)
        show (Q : Set (ComplexModel n)).indicator bT z - (Q : Set (ComplexModel n)).indicator V z <
          -δ + s
        rw [indicator_of_mem hzQ, indicator_of_mem hzQ]
        linarith [not_lt.mp hab']
  have hE9 : α {z | f z ≤ -δ + s + s} ≤ α {z | z ∈ Q ∧ v z ≤ ((V z - δ + 2 * s : ℝ) : EReal)} := by
    refine (measure_le_inter_add_sdiff α _ K).trans ?_
    rw [measure_mono_null (fun z hz => hz.2 : {z | f z ≤ -δ + s + s} \ K ⊆ Kᶜ) hαK, add_zero]
    refine measure_mono fun z hz => ⟨hKQ hz.2, ?_⟩
    have hzQ := hKQ hz.2
    have h1 : f z = bT z - V z := by simp [hfdef, indicator_of_mem hzQ]
    have h2 : bT z ≤ V z - δ + 2 * s := by have := hz.1; simp only [mem_ofPred_eq] at this; linarith
    calc v z ≤ max (v z) ((-T : ℝ) : EReal) := le_max_left _ _
      _ = (bT z : EReal) := (coe_truncReal hv T hzQ).symm
      _ ≤ ((V z - δ + 2 * s : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr h2
  -- assembly
  calc νV ({z | z ∈ Q ∧ v z < ((V z - δ - s : ℝ) : EReal)} ∩ L)
      ≤ νV ({z | z ∈ Q ∧ U j z < V z + -δ} ∪ (L ∩ S5)) := measure_mono hE7
    _ ≤ νV {z | z ∈ Q ∧ U j z < V z + -δ} + νV (L ∩ S5) := measure_union_le _ _
    _ ≤ μ j {z | z ∈ Q ∧ U j z < V z + -δ} + ENNReal.ofReal (η / 4) := add_le_add hE6 hE5'
    _ ≤ (μ j {z | f z < -δ + s} + μ j {z | z ∈ Q ∧ U j z < -T} + μ j {z | a k z < bT z - s}) +
          ENNReal.ofReal (η / 4) := by
        exact add_le_add ((measure_mono hE8).trans ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl))) le_rfl
    _ ≤ ((α {z | f z ≤ -δ + s + s} + ENNReal.ofReal (η / 4)) + ENNReal.ofReal (η / 4) +
          ENNReal.ofReal (η / 4)) + ENNReal.ofReal (η / 4) := by
        gcongr
    _ ≤ α {z | z ∈ Q ∧ v z ≤ ((V z - δ + 2 * s : ℝ) : EReal)} + ENNReal.ofReal η := by
        have h4 : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
            ENNReal.ofReal (η / 4) = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
        calc ((α {z | f z ≤ -δ + s + s} + ENNReal.ofReal (η / 4)) + ENNReal.ofReal (η / 4) +
              ENNReal.ofReal (η / 4)) + ENNReal.ofReal (η / 4)
            = α {z | f z ≤ -δ + s + s} + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
              ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)) := by ring
          _ ≤ _ := by rw [h4]; exact add_le_add hE9 le_rfl
/-- Comparison with the truncation above the truncation level. -/
theorem lt_coe_iff_truncReal {Q : Opens (ComplexModel n)} {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Q) {T : ℝ} {z : ComplexModel n} (hz : z ∈ Q) {r : ℝ}
    (hr : -T < r) : v z < (r : EReal) ↔ truncReal v T z < r := by
  rw [← EReal.coe_lt_coe_iff, coe_truncReal hv T hz, max_lt_iff]
  exact ⟨fun h => ⟨h, EReal.coe_lt_coe_iff.mpr hr⟩, fun h => h.1⟩

theorem le_coe_iff_truncReal {Q : Opens (ComplexModel n)} {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Q) {T : ℝ} {z : ComplexModel n} (hz : z ∈ Q) {r : ℝ}
    (hr : -T < r) : v z ≤ (r : EReal) ↔ truncReal v T z ≤ r := by
  rw [← EReal.coe_le_coe_iff, coe_truncReal hv T hz, max_le_iff]
  exact ⟨fun h => ⟨h, EReal.coe_le_coe_iff.mpr hr.le⟩, fun h => h.1⟩

/-- **Kołodziej's theorem, the barrier step** (FPT, Steps 2 and 3 of the proof of
`thm:compact-bounded-subsolution-ball-dirichlet`): an `L¹_loc` limit `v` of a subsequence of
approximants lies above every barrier `W` with `(ddᶜW)ⁿ ≥ α`, `-B ≤ W ≤ 0`. -/
theorem coe_le_of_approximants (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKQ : K ⊆ Q) (hαK : α Kᶜ = 0) {U : ℕ → ComplexModel n → ℝ}
    (hA : IsKolodziejApprox Q α U) {W : ComplexModel n → ℝ} (hW : IsLocallyBoundedPshOn Q W)
    {B : ℝ} (hB : 0 ≤ B) (hWb : ∀ z ∈ Q, -B ≤ W z ∧ W z ≤ 0)
    (hWα : α.restrict Q ≤ canonicalBedfordTaylorMeasure Q W hW) {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Q) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, canonicalERealAbsDiff (U (σ k) x : EReal) (v x)) atTop (𝓝 0)) :
    ∀ z ∈ Q, (W z : EReal) ≤ v z := by
  classical
  have hQm : MeasurableSet (Q : Set (ComplexModel n)) := Q.isOpen.measurableSet
  obtain ⟨ρ₀, hρ₀⟩ := hA.bounded.subset_closedBall 0
  set M' : ℝ := ρ₀ ^ 2 with hM'def
  have hM' : ∀ z ∈ Q, ‖z‖ ^ 2 ≤ M' := fun z hz => by
    have h := hρ₀ hz
    rw [mem_closedBall, dist_zero_right] at h
    exact pow_le_pow_left₀ (norm_nonneg z) h 2
  have hstep : ∀ ε : ℝ, 0 < ε → ∀ z ∈ Q, ((W z + ε * (‖z‖ ^ 2 - M') : ℝ) : EReal) ≤ v z := by
    intro ε hε
    set Wε : ComplexModel n → ℝ := fun z => W z + ε * (‖z‖ ^ 2 - M') with hWεdef
    have hWε : IsLocallyBoundedPshOn Q Wε := by
      have h := IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_linComb hW
        (isLocallyBoundedPshOn_zero Q) zero_le_one le_rfl hε.le) (-(ε * M'))
      have heq : (fun z => 1 * W z + 0 * (fun _ => (0 : ℝ)) z + ε * ‖z‖ ^ 2 + -(ε * M')) = Wε := by
        funext z; simp only [hWεdef]; ring
      rwa [heq] at h
    set Bε : ℝ := B + ε * M' with hBεdef
    have hM'0 : 0 ≤ M' := sq_nonneg _
    have hBε : 0 ≤ Bε := by positivity
    have hWεb : ∀ z ∈ Q, -Bε ≤ Wε z ∧ Wε z ≤ 0 := fun z hz => by
      have h1 := hM' z hz
      have h2 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
      constructor
      · simp only [hWεdef, hBεdef]; nlinarith [(hWb z hz).1]
      · simp only [hWεdef]; nlinarith [(hWb z hz).2]
    have hνε := ma_add_normSq_ge hn hW hε M' hWε
    set c : ℝ≥0∞ := ENNReal.ofReal (mongeAmpereConst n * ε ^ n) with hcdef
    have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (mul_pos mongeAmpereConst_pos (pow_pos hε n))).ne'
    -- levels
    set T₀ : ℝ := Bε + 2 with hT₀def
    set g : ComplexModel n → ℝ := fun z => (Q : Set (ComplexModel n)).indicator (truncReal v T₀) z -
      (Q : Set (ComplexModel n)).indicator Wε z with hgdef
    have hgm : Measurable g :=
      (measurable_indicator_of_plurisubharmonicOn (isLocallyBoundedPshOn_truncReal hv T₀).1).sub
        (measurable_indicator_of_plurisubharmonicOn hWε.1)
    have hgQ : ∀ z ∈ Q, g z = truncReal v T₀ z - Wε z := fun z hz => by
      simp [hgdef, indicator_of_mem hz]
    obtain ⟨t, -, htpos, htlim, htnull⟩ := exists_antitone_level_null (Ω := Q) (α := α)
      (fun K' _ _ => measure_lt_top α K') hgm.neg
    have hlevel : ∀ k, t k < 1 → ∀ z ∈ Q, ((Wε z - t k : ℝ) : EReal) ≤ v z := by
      intro k hk1
      set δ : ℝ := t k with hδdef
      have hδ : 0 < δ := htpos k
      -- the sets
      set A : ℝ → Set (ComplexModel n) := fun s => {z | z ∈ Q ∧ v z < ((Wε z - δ - s : ℝ) : EReal)}
        with hAdef
      set Bs : ℝ → Set (ComplexModel n) :=
        fun s => {z | z ∈ Q ∧ v z ≤ ((Wε z - δ + s : ℝ) : EReal)} with hBsdef
      have hBs_eq : ∀ s, 0 ≤ s → s < 1 → Bs s = {z | z ∈ Q ∧ g z ≤ -δ + s} := by
        intro s hs0 hs1
        ext z
        refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
        · rw [hgQ z hz.1]
          have := (le_coe_iff_truncReal hv hz.1 (T := T₀) (r := Wε z - δ + s)
            (by linarith [(hWεb z hz.1).1])).mp hz.2
          linarith
        · have h2 : g z ≤ -δ + s := hz.2
          rw [hgQ z hz.1] at h2
          exact (le_coe_iff_truncReal hv hz.1 (T := T₀) (r := Wε z - δ + s)
            (by linarith [(hWεb z hz.1).1])).mpr (by linarith)
      have hA0_eq : A 0 = {z | z ∈ Q ∧ g z < -δ} := by
        ext z
        refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
        · rw [hgQ z hz.1]
          have := (lt_coe_iff_truncReal hv hz.1 (T := T₀) (r := Wε z - δ - 0)
            (by linarith [(hWεb z hz.1).1])).mp hz.2
          linarith
        · have h2 : g z < -δ := hz.2
          rw [hgQ z hz.1] at h2
          exact (lt_coe_iff_truncReal hv hz.1 (T := T₀) (r := Wε z - δ - 0)
            (by linarith [(hWεb z hz.1).1])).mpr (by linarith)
      have hnullδ : α {z | z ∈ Q ∧ g z = -δ} = 0 := by
        refine measure_mono_null (fun z hz => ?_) (htnull k)
        refine ⟨hz.1, ?_⟩
        have h2 : g z = -δ := hz.2
        show -g z = t k
        rw [h2]; ring
      -- the single-scale estimate, for every compact `L ⊇ K`
      set sm : ℕ → ℝ := fun m => 1 / (8 * ((m : ℝ) + 1)) with hsmdef
      have hsm0 : ∀ m, 0 < sm m := fun m => by positivity
      have hsm1 : ∀ m, sm m < 1 / 4 := fun m => by
        simp only [hsmdef]
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
      have hsmanti : Antitone sm := fun m m' hmm' => by
        simp only [hsmdef]
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
        linarith
      have hsmlim : Tendsto sm atTop (𝓝 0) := by
        simp only [hsmdef]
        exact tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num)
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
      have hvolL : ∀ L : Set (ComplexModel n), IsCompact L → K ⊆ L → L ⊆ Q →
          volume (A 0 ∩ L) = 0 := by
        intro L hL hKL hLQ
        have hineq : ∀ m, α (A (sm m)) + c * volume (A (sm m) ∩ L) ≤ α (Bs (2 * sm m)) := by
          intro m
          have hup : canonicalBedfordTaylorMeasure Q Wε hWε (A (sm m) ∩ L) ≤ α (Bs (2 * sm m)) := by
            refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
            have h := measure_sublevel_inter_le hn hK hKQ hαK hA hWε hBε hWεb hv hσ hlim hδ hk1
              (hsm0 m) (hsm1 m) (η := η) (by exact_mod_cast hη) hL hLQ
            simpa only [ENNReal.ofReal_coe_nnreal] using h
          have hlow : α (A (sm m)) + c * volume (A (sm m) ∩ L) ≤
              canonicalBedfordTaylorMeasure Q Wε hWε (A (sm m) ∩ L) := by
            have h1 := Measure.le_iff'.mp ((add_le_add hWα le_rfl).trans hνε) (A (sm m) ∩ L)
            have hAQ : A (sm m) ∩ L ⊆ Q := fun z hz => hz.1.1
            rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply' hQm,
              Measure.restrict_apply' hQm, inter_eq_left.mpr hAQ, smul_eq_mul] at h1
            refine le_trans (add_le_add ?_ le_rfl) h1
            refine (measure_le_inter_add_sdiff α _ L).trans ?_
            rw [measure_mono_null (fun z hz => fun h => hz.2 (hKL h) : A (sm m) \ L ⊆ Kᶜ) hαK,
              add_zero]
          exact hlow.trans hup
        -- pass to the limit `m → ∞`
        have hAmono : Monotone fun m => A (sm m) := fun m m' hmm' z hz =>
          ⟨hz.1, hz.2.trans_le (EReal.coe_le_coe_iff.mpr (by linarith [hsmanti hmm']))⟩
        have hAunion : (⋃ m, A (sm m)) = A 0 := by
          ext z
          simp only [mem_iUnion]
          refine ⟨fun ⟨m, hm⟩ => ⟨hm.1, hm.2.trans_le (EReal.coe_le_coe_iff.mpr (by
            linarith [hsm0 m]))⟩, fun hz => ?_⟩
          obtain ⟨hzQ, hz⟩ := hz
          obtain ⟨q, hq1, hq2⟩ := EReal.exists_between_coe_real hz
          have hgap : 0 < Wε z - δ - 0 - q := by
            have := EReal.coe_lt_coe_iff.mp hq2; linarith
          obtain ⟨m, hm⟩ := ((tendsto_order.1 hsmlim).2 _ hgap).exists
          exact ⟨m, hzQ, hq1.trans (EReal.coe_lt_coe_iff.mpr (by linarith))⟩
        have hBanti : Antitone fun m => Bs (2 * sm m) := fun m m' hmm' z hz =>
          ⟨hz.1, hz.2.trans (EReal.coe_le_coe_iff.mpr (by linarith [hsmanti hmm']))⟩
        have hBinter : (⋂ m, Bs (2 * sm m)) = Bs 0 := by
          ext z
          simp only [mem_iInter]
          refine ⟨fun hz => ⟨(hz 0).1, ?_⟩, fun hz m => ⟨hz.1, hz.2.trans
            (EReal.coe_le_coe_iff.mpr (by linarith [hsm0 m]))⟩⟩
          have h1 : ∀ m, v z ≤ ((Wε z - δ + 2 * sm m : ℝ) : EReal) := fun m => (hz m).2
          have h2 : Tendsto (fun m => ((Wε z - δ + 2 * sm m : ℝ) : EReal)) atTop
              (𝓝 ((Wε z - δ + 0 : ℝ) : EReal)) := by
            refine (continuous_coe_real_ereal.tendsto _).comp ?_
            simpa using (tendsto_const_nhds (x := Wε z - δ)).add (hsmlim.const_mul 2)
          exact ge_of_tendsto h2 (Eventually.of_forall h1)
        have hBmeas : ∀ m, MeasurableSet (Bs (2 * sm m)) := fun m => by
          rw [hBs_eq _ (by linarith [hsm0 m]) (by linarith [hsm1 m])]
          exact hQm.inter (measurableSet_le hgm measurable_const)
        have hlimA : Tendsto (fun m => α (A (sm m))) atTop (𝓝 (α (A 0))) := by
          rw [← hAunion]; exact tendsto_measure_iUnion_atTop hAmono
        have hlimV : Tendsto (fun m => volume (A (sm m) ∩ L)) atTop (𝓝 (volume (A 0 ∩ L))) := by
          rw [← hAunion, iUnion_inter]
          exact tendsto_measure_iUnion_atTop fun m m' hmm' => inter_subset_inter_left _ (hAmono hmm')
        have hlimB : Tendsto (fun m => α (Bs (2 * sm m))) atTop (𝓝 (α (Bs 0))) := by
          rw [← hBinter]
          exact tendsto_measure_iInter_atTop (fun m => (hBmeas m).nullMeasurableSet) hBanti
            ⟨0, measure_ne_top _ _⟩
        have hlimit : α (A 0) + c * volume (A 0 ∩ L) ≤ α (Bs 0) :=
          le_of_tendsto_of_tendsto' (hlimA.add (ENNReal.Tendsto.const_mul hlimV (Or.inr
            (by rw [hcdef]; exact ENNReal.ofReal_ne_top)))) hlimB hineq
        have hB0 : α (Bs 0) ≤ α (A 0) + 0 := by
          rw [← hnullδ]
          refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
          rcases lt_or_eq_of_le hz.2 with hlt | heq
          · exact Or.inl ⟨hz.1, by simpa using hlt⟩
          · refine Or.inr ⟨hz.1, ?_⟩
            rw [hgQ z hz.1]
            have h1 := (le_coe_iff_truncReal hv hz.1 (T := T₀) (r := Wε z - δ + 0)
              (by linarith [(hWεb z hz.1).1])).mp hz.2
            have h2 : ¬ truncReal v T₀ z < Wε z - δ - 0 := fun h =>
              (lt_irrefl _) (heq ▸ (lt_coe_iff_truncReal hv hz.1 (T := T₀) (r := Wε z - δ - 0)
                (by linarith [(hWεb z hz.1).1])).mpr h |>.trans_le (by simp))
            linarith [not_lt.mp h2]
        have hcancel : c * volume (A 0 ∩ L) ≤ 0 :=
          (ENNReal.add_le_add_iff_left (measure_ne_top α _)).mp (hlimit.trans hB0)
        exact (mul_eq_zero.mp (le_antisymm hcancel bot_le)).resolve_left hc
      -- almost everywhere, then everywhere
      have hae : ∀ᵐ z ∂volume.restrict Q, ((Wε z - δ : ℝ) : EReal) ≤ v z := by
        refine ae_restrict_of_forall_compact fun K' hK' hK'Q => ?_
        have h0 := hvolL (K ∪ K') (hK.union hK') subset_union_left (union_subset hKQ hK'Q)
        have hnull : volume.restrict K' (A 0) = 0 := by
          rw [Measure.restrict_apply' hK'.measurableSet]
          exact measure_mono_null (inter_subset_inter_right _ subset_union_right) h0
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull,
          ae_restrict_mem hK'.measurableSet] with z hz hzK
        by_contra hlt
        exact hz ⟨hK'Q hzK, by simpa using not_le.mp hlt⟩
      have hpsh : PlurisubharmonicOn (fun z => ((Wε z - δ : ℝ) : EReal)) Q := by
        have := (IsLocallyBoundedPshOn.add_const hWε (-δ)).1
        simpa only [← sub_eq_add_neg] using this
      exact hpsh.le_of_ae_le Q.isOpen hv.upperSemicontinuousOn volume hae
    intro z hz
    have hev : ∀ᶠ k in atTop, ((Wε z - t k : ℝ) : EReal) ≤ v z :=
      ((tendsto_order.1 htlim).2 1 one_pos).mono fun k hk => hlevel k hk z hz
    have hconv : Tendsto (fun k => ((Wε z - t k : ℝ) : EReal)) atTop (𝓝 ((Wε z - 0 : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp ((tendsto_const_nhds).sub htlim)
    have h := le_of_tendsto hconv hev
    rw [sub_zero] at h
    exact h
  intro z hz
  have hconv : Tendsto (fun m : ℕ => ((W z + (1 / ((m : ℝ) + 1)) * (‖z‖ ^ 2 - M') : ℝ) : EReal))
      atTop (𝓝 ((W z + 0 * (‖z‖ ^ 2 - M') : ℝ) : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    exact tendsto_const_nhds.add ((tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul tendsto_const_nhds)
  have h := le_of_tendsto' hconv fun m => hstep _ (by positivity) z hz
  simpa using h

end SGPT.Envelopes.MADirichlet
