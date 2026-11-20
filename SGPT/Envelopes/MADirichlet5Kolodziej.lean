import SGPT.Envelopes.MADirichlet5Capacity

/-!
# Kołodziej's theorem on polydisks

Xia, *Foundations of pluripotential theory* (FPT), `thm:compact-bounded-subsolution-ball-dirichlet`
(Kołodziej), on a polydisk `Q = a + R·P` instead of a ball: let `α` be a finite measure carried by
a compact `K ⊆ Q` with `α ≤ (ddᶜw)ⁿ` on `Q` for a bounded plurisubharmonic `w`. Then there is a
unique bounded plurisubharmonic `u` on `Q` with `(ddᶜu)ⁿ = α` and boundary values `0`; it is the
largest bounded plurisubharmonic `v` with `(ddᶜv)ⁿ ≥ α` and `limsup v ≤ 0` at `∂Q`
(`exists_kolodziej_polydisk`).

MA-DIR4 (`exists_approximants_bounded_limit`) produced the bounded limit `u` of a subsequence of
the convolution approximants `U_j` (`IsKolodziejApprox`). Here we identify its Monge–Ampère measure
(`ma_eq_of_approximants`), following FPT `thm:canonical-grid-capacity-convergence` and the last
step of the proof of Kołodziej's theorem:

* `tendsto_relCapacity_lt_sub_of_approximants`: `Cap_Q{U_j < u - δ} → 0`, from the capacity of
  sublevel sets (`pow_mul_relCapacity_le`, applied to the truncation `max(U_j, -T)`) and the
  self-integral convergence `∫ |max(U_j, -T) - u| d(ddᶜU_j)ⁿ → 0`;
* `tendsto_relCapacity_add_lt_of_localL1`: `Cap_Q(L ∩ {U_j > u + δ}) → 0` for compact `L ⊆ Q`,
  from quasi-continuity of `u` and Hartogs' lemma;
* hence `max(U_j, -T) → u` in capacity on every open `V ⊆ Q` (`exists_relCapacity_inter_le`), so
  `(ddᶜ max(U_j, -T))ⁿ → (ddᶜu)ⁿ` weakly (`tendsto_integral_mixed_of_relCapacity`), while
  `(ddᶜ max(U_j, -T))ⁿ` and `(ddᶜU_j)ⁿ` differ by at most `2 e₁(U_j)/T` in total variation
  (`IsCegrellE0.truncation`) and `(ddᶜU_j)ⁿ → α`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- `|max(a, -T) - b| ≤ |a - b|` when `b ≥ -T`. -/
theorem abs_max_neg_sub_le {a b T : ℝ} (hb : -T ≤ b) : |max a (-T) - b| ≤ |a - b| := by
  rcases le_total a (-T) with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left h]

/-- Monge–Ampère measures of `ℰ₀` functions are finite. -/
theorem IsCegrellE0.isFiniteMeasure {D : Opens (ComplexModel n)} {φ : ComplexModel n → ℝ}
    (hφ : IsCegrellE0 D φ) : IsFiniteMeasure (canonicalBedfordTaylorMeasure D φ hφ.psh) := by
  refine ⟨(measure_univ_le_add_compl (D : Set (ComplexModel n))).trans_lt ?_⟩
  rw [(isBTLimit_canonicalBedfordTaylorMeasure hφ.psh).1, add_zero]
  exact hφ.mass_lt_top

/-- Two finite measures which agree on `G` integrate a function bounded by `C` to values at
distance at most `C (ν₁(Gᶜ) + ν₂(Gᶜ))`. -/
theorem abs_integral_sub_le_of_restrict_eq {X : Type*} [MeasurableSpace X] {ν₁ ν₂ : Measure X}
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] {G : Set X} (hG : MeasurableSet G)
    (heq : ν₁.restrict G = ν₂.restrict G) {φ : X → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) :
    |∫ x, φ x ∂ν₁ - ∫ x, φ x ∂ν₂| ≤ C * ((ν₁ Gᶜ).toReal + (ν₂ Gᶜ).toReal) := by
  have hint : ∀ (ν : Measure X) [IsFiniteMeasure ν], Integrable φ ν := fun ν _ =>
    (integrable_const C).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hsplit : ∀ (ν : Measure X) [IsFiniteMeasure ν],
      ∫ x, φ x ∂ν = ∫ x, φ x ∂(ν.restrict G) + ∫ x, φ x ∂(ν.restrict Gᶜ) := fun ν _ => by
    rw [← integral_add_measure (hint ν).restrict (hint ν).restrict,
      Measure.restrict_add_restrict_compl hG]
  have hbound : ∀ (ν : Measure X) [IsFiniteMeasure ν],
      |∫ x, φ x ∂(ν.restrict Gᶜ)| ≤ C * (ν Gᶜ).toReal := fun ν _ => by
    have h := norm_integral_le_of_norm_le_const (μ := ν.restrict Gᶜ) (f := φ) (C := C)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
    rw [Real.norm_eq_abs] at h
    simpa [Measure.real, Measure.restrict_apply_univ] using h
  rw [hsplit ν₁, hsplit ν₂, heq]
  calc |∫ x, φ x ∂(ν₂.restrict G) + ∫ x, φ x ∂(ν₁.restrict Gᶜ) -
        (∫ x, φ x ∂(ν₂.restrict G) + ∫ x, φ x ∂(ν₂.restrict Gᶜ))|
      = |∫ x, φ x ∂(ν₁.restrict Gᶜ) - ∫ x, φ x ∂(ν₂.restrict Gᶜ)| := by ring_nf
    _ ≤ |∫ x, φ x ∂(ν₁.restrict Gᶜ)| + |∫ x, φ x ∂(ν₂.restrict Gᶜ)| := abs_sub _ _
    _ ≤ C * (ν₁ Gᶜ).toReal + C * (ν₂ Gᶜ).toReal := add_le_add (hbound ν₁) (hbound ν₂)
    _ = C * ((ν₁ Gᶜ).toReal + (ν₂ Gᶜ).toReal) := by ring

/-- **Convergence in capacity, the lower half** (FPT `thm:canonical-grid-capacity-convergence`,
for a bounded limit): `Cap_Q{U_{σ k} < u - δ} → 0`. -/
theorem tendsto_relCapacity_lt_sub_of_approximants (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox Q α U)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Q u) {B : ℝ}
    (hub : ∀ z ∈ Q, -B ≤ u z ∧ u z ≤ 0) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (σ k) x - u x|) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => relCapacity Q {z | z ∈ Q ∧ U (σ k) z < u z - δ}) atTop (𝓝 0) := by
  classical
  set T : ℝ := |B| + δ + 1 with hTdef
  have hT : 0 < T := by positivity
  have huT : ∀ z ∈ Q, -T + δ < u z := fun z hz => by
    have := (hub z hz).1; have := le_abs_self B; rw [hTdef]; linarith
  choose hφT hloc _hmass hFeq _hFle _hEle using fun k => (hA.cegrell (σ k)).truncation hn hA.bounded hT one_pos
  set μ : ℕ → Measure (ComplexModel n) := fun k =>
    canonicalBedfordTaylorMeasure Q (U (σ k)) (hA.cegrell (σ k)).psh with hμdef
  set ν : ℕ → Measure (ComplexModel n) := fun k =>
    canonicalBedfordTaylorMeasure Q _ (hφT k).psh with hνdef
  set W : ℕ → ComplexModel n → ℝ := fun k z => max (U (σ k) z) (-T) with hWdef
  -- the self-integral convergence
  have hself := hA.selfIntegral T hT σ hσ u hu fun L hL hLQ => by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim L hL hLQ)
      (fun _ => zero_le) fun k => setLIntegral_mono' hL.measurableSet fun x hx => ?_
    exact ENNReal.ofReal_le_ofReal (abs_max_neg_sub_le (by linarith [huT x (hLQ hx)]))
  -- the key estimate
  set c : ℝ≥0∞ := ENNReal.ofReal (δ / 2) ^ n with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hctop : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hkey : ∀ k, c * relCapacity Q {z | z ∈ Q ∧ U (σ k) z < u z - δ} ≤
      2 * ((ENNReal.ofReal (δ / 2))⁻¹ *
        ∫⁻ x, ENNReal.ofReal |max (U (σ k) x) (-T) - u x| ∂μ k) := by
    intro k
    set E : Set (ComplexModel n) := {z | z ∈ Q ∧ W k z < u z - δ / 2} with hEdef
    -- the sublevel set is relatively compact
    obtain ⟨hKc, hKcQ⟩ := exists_isCompact_sublevel hA.bounded
      (hA.cegrell (σ k)).tendsto_frontier (s := δ / 2) (by positivity)
    have hsub : E ⊆ closure {z | z ∈ Q ∧ U (σ k) z ≤ -(δ / 2)} := by
      rintro z ⟨hzQ, hz⟩
      refine subset_closure ⟨hzQ, ?_⟩
      have h1 : W k z < -(δ / 2) := by linarith [(hub z hzQ).2]
      exact (le_max_left _ _).trans h1.le
    have hcap := pow_mul_relCapacity_le hn (hφT k).psh hu (δ / 2) (t := δ / 2) (by positivity)
      hKc hKcQ hsub
    have hset : {z | z ∈ Q ∧ W k z < u z - δ / 2 - δ / 2} =
        {z | z ∈ Q ∧ U (σ k) z < u z - δ} := by
      ext z
      simp only [mem_ofPred_eq, hWdef]
      refine and_congr_right fun hzQ => ?_
      have h1 := huT z hzQ
      constructor
      · intro h; have := le_max_left (U (σ k) z) (-T); linarith
      · intro h
        rcases le_total (U (σ k) z) (-T) with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; linarith
    rw [hset] at hcap
    -- `ν(E) ≤ 2 μ(E)`
    set G : Set (ComplexModel n) := {z | z ∈ Q ∧ -T < U (σ k) z} with hGdef
    set F : Set (ComplexModel n) := {z | z ∈ Q ∧ U (σ k) z ≤ -T} with hFdef
    have hGm : MeasurableSet G := measurableSet_superlevel (hA.cegrell (σ k)).psh (-T)
    have hFE : F ⊆ E := by
      rintro z ⟨hzQ, hz⟩
      refine ⟨hzQ, ?_⟩
      simp only [hWdef, max_eq_right hz]
      linarith [huT z hzQ]
    have hEsplit : E ⊆ (E ∩ G) ∪ F := by
      intro z hz
      by_cases h : -T < U (σ k) z
      · exact Or.inl ⟨hz, hz.1, h⟩
      · exact Or.inr ⟨hz.1, not_lt.mp h⟩
    have hνE : ν k E ≤ 2 * μ k E := by
      calc ν k E ≤ ν k ((E ∩ G) ∪ F) := measure_mono hEsplit
        _ ≤ ν k (E ∩ G) + ν k F := measure_union_le _ _
        _ = μ k (E ∩ G) + μ k F := by
            congr 1
            · rw [← Measure.restrict_apply' hGm, ← Measure.restrict_apply' hGm]
              exact congrArg (fun m : Measure (ComplexModel n) => m E) (hloc k)
            · exact hFeq k
        _ ≤ μ k E + μ k E := add_le_add (measure_mono inter_subset_left) (measure_mono hFE)
        _ = 2 * μ k E := by rw [two_mul]
    -- Chebyshev
    have hμQ : (μ k).restrict Q = μ k := Measure.restrict_eq_self_of_ae_mem
      (ae_iff.mpr (isBTLimit_canonicalBedfordTaylorMeasure (hA.cegrell (σ k)).psh).1)
    have hfm : AEMeasurable (fun x => ENNReal.ofReal |max (U (σ k) x) (-T) - u x|)
        ((μ k).restrict Q) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (continuous_abs.measurable.comp_aemeasurable
          ((aemeasurable_of_isLocallyBoundedPshOn (hφT k).psh (μ k)).sub
            (aemeasurable_of_isLocallyBoundedPshOn hu (μ k))))
    have hcheb := mul_meas_ge_le_lintegral₀ hfm (ENNReal.ofReal (δ / 2))
    rw [hμQ] at hcheb
    have hEsub : E ⊆ {x | ENNReal.ofReal (δ / 2) ≤
        ENNReal.ofReal |max (U (σ k) x) (-T) - u x|} := by
      rintro z ⟨-, hz⟩
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_sub_comm]
      exact (le_abs_self _).trans' (by simp only [hWdef] at hz; linarith)
    have hμE : μ k E ≤ (ENNReal.ofReal (δ / 2))⁻¹ *
        ∫⁻ x, ENNReal.ofReal |max (U (σ k) x) (-T) - u x| ∂μ k := by
      refine (ENNReal.mul_le_iff_le_inv (ENNReal.ofReal_pos.mpr (by positivity)).ne'
        ENNReal.ofReal_ne_top).mp ?_
      exact (mul_le_mul' le_rfl (measure_mono hEsub)).trans hcheb
    calc c * relCapacity Q {z | z ∈ Q ∧ U (σ k) z < u z - δ} ≤ ν k E := hcap
      _ ≤ 2 * μ k E := hνE
      _ ≤ _ := mul_le_mul' le_rfl hμE
  -- conclusion
  have hlim0 : Tendsto (fun k => c⁻¹ * (2 * ((ENNReal.ofReal (δ / 2))⁻¹ *
      ∫⁻ x, ENNReal.ofReal |max (U (σ k) x) (-T) - u x| ∂μ k))) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hself
      (Or.inr (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)).ne'))
      (a := (ENNReal.ofReal (δ / 2))⁻¹)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top) (a := 2)
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.inv_ne_top.mpr hc0)) (a := c⁻¹)
    simpa using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0 (fun _ => zero_le)
    fun k => ?_
  exact (ENNReal.mul_le_iff_le_inv hc0 hctop).mp (hkey k)

/-- **Convergence in capacity, the upper half**: if `f_j → v` in `L¹_loc(Q)` (all plurisubharmonic,
`v` locally bounded), then `Cap_Q(L ∩ {f_j > v + δ}) → 0` for every compact `L ⊆ Q` and `δ > 0`
(quasi-continuity of `v` and Hartogs' lemma). -/
theorem tendsto_relCapacity_add_lt_of_localL1 {Q : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hf : ∀ j, IsLocallyBoundedPshOn Q (f j)) (hv : IsLocallyBoundedPshOn Q v)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Q →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {L : Set (ComplexModel n)} (hL : IsCompact L) (hLQ : L ⊆ Q) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => relCapacity Q (L ∩ {z | v z + δ < f j z})) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, hr0, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  obtain ⟨G, hGo, hGcap, hcont⟩ := isQuasiContinuousOn_of_isLocallyBoundedPshOn hv L hL hLQ r hrpos
  set L' : Set (ComplexModel n) := L \ G with hL'def
  have hL' : IsCompact L' := hL.diff hGo
  -- local control at each point of `L'`
  have hloc : ∀ x ∈ L', ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ j in atTop, ∀ y ∈ L' ∩ ball x ρ, f j y ≤ v y + δ := by
    intro x hx
    obtain ⟨r₁, hr₁, hr₁c⟩ := Metric.continuousWithinAt_iff.mp (hcont x hx) (δ / 3) (by positivity)
    obtain ⟨r₂, hr₂, hr₂f⟩ := eventually_le_on_ball_of_localL1 hf hv hlim (hLQ hx.1)
      (c := v x + δ / 3) (by linarith)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
    filter_upwards [hr₂f] with j hj y ⟨hyL, hyx⟩
    have h1 := hj y (ball_subset_ball (min_le_right _ _) hyx)
    have h2 := hr₁c hyL (lt_of_lt_of_le (mem_ball.mp hyx) (min_le_left _ _))
    rw [Real.dist_eq] at h2
    have h3 := (abs_lt.mp h2).1
    linarith
  choose! ρ hρ hρj using hloc
  obtain ⟨t, htL', htfin, hcover⟩ := hL'.elim_finite_subcover_image (b := L')
    (c := fun x => ball x (ρ x)) (fun _ _ => isOpen_ball)
    (fun x hx => mem_iUnion₂.mpr ⟨x, hx, mem_ball_self (hρ x hx)⟩)
  have hev : ∀ᶠ j in atTop, ∀ x ∈ t, ∀ y ∈ L' ∩ ball x (ρ x), f j y ≤ v y + δ :=
    (Filter.eventually_all_finite htfin).mpr fun x hx => hρj x (htL' hx)
  filter_upwards [hev] with j hj
  refine le_trans ?_ hrε.le
  refine (relCapacity_mono ?_).trans hGcap.le
  rintro z ⟨hzL, hz⟩
  by_contra hzG
  have hzL' : z ∈ L' := ⟨hzL, hzG⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hzL')
  have := hj x hxt z ⟨hzL', hzx⟩
  exact absurd hz (not_lt.mpr this)

/-- **Convergence in capacity of the approximants** (FPT `thm:canonical-grid-capacity-convergence`
for a bounded limit, convolution variant): `Cap_Q(L ∩ {|U_{σ k} - u| > a}) → 0` for every compact
`L ⊆ Q` and `a > 0`. -/
theorem tendsto_relCapacity_abs_sub_of_approximants (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox Q α U)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Q u) {B : ℝ}
    (hub : ∀ z ∈ Q, -B ≤ u z ∧ u z ≤ 0) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (σ k) x - u x|) atTop (𝓝 0))
    {L : Set (ComplexModel n)} (hL : IsCompact L) (hLQ : L ⊆ Q) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k => relCapacity Q (L ∩ {z | a < |U (σ k) z - u z|})) atTop (𝓝 0) := by
  have h1 := tendsto_relCapacity_lt_sub_of_approximants hn hA hu hub hσ hlim ha
  have h2 := tendsto_relCapacity_add_lt_of_localL1 (f := fun k => U (σ k))
    (fun k => (hA.cegrell (σ k)).psh) hu hlim hL hLQ ha
  have h3 : Tendsto (fun k => relCapacity Q {z | z ∈ Q ∧ U (σ k) z < u z - a} +
      relCapacity Q (L ∩ {z | u z + a < U (σ k) z})) atTop (𝓝 0) := by
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
    fun k => (relCapacity_mono ?_).trans (relCapacity_union_le _ _ _)
  rintro z ⟨hzL, hz⟩
  have hz' : a < |U (σ k) z - u z| := hz
  rcases lt_abs.mp hz' with h | h
  · exact Or.inr ⟨hzL, show u z + a < U (σ k) z by linarith⟩
  · exact Or.inl ⟨hLQ hzL, show U (σ k) z < u z - a by linarith⟩

/-- **The limit solves the equation** (FPT, the end of the proof of
`thm:compact-bounded-subsolution-ball-dirichlet`): a bounded `L¹_loc` limit `u` of a subsequence of
approximants with the properties `IsKolodziejApprox Q α U` satisfies `(ddᶜu)ⁿ = α`. -/
theorem ma_eq_of_approximants (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} [IsFiniteMeasure α] (hαQ : α (Q : Set (ComplexModel n))ᶜ = 0)
    {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox Q α U)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Q u) {B : ℝ}
    (hub : ∀ z ∈ Q, -B ≤ u z ∧ u z ≤ 0) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hlim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (σ k) x - u x|) atTop (𝓝 0)) :
    canonicalBedfordTaylorMeasure Q u hu = α := by
  classical
  obtain ⟨C, hC⟩ := hA.energy
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hC 0)
  -- the integral identity for test functions supported in `Q`
  have hint : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (Q : Set (ComplexModel n)) →
      ∫ z, φ z ∂canonicalBedfordTaylorMeasure Q u hu = ∫ z, φ z ∂α := by
    intro φ hφ hφc hφQ
    obtain ⟨Cφ, hCφ⟩ := hφ.bounded_above_of_compact_support hφc
    have hCφ' : ∀ x, |φ x| ≤ Cφ := fun x => by rw [← Real.norm_eq_abs]; exact hCφ x
    have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hCφ' 0)
    -- the estimate at a truncation level `T`
    have hT : ∀ T : ℝ, |B| + 1 ≤ T →
        |∫ z, φ z ∂canonicalBedfordTaylorMeasure Q u hu - ∫ z, φ z ∂α| ≤ Cφ * (2 * (C / T)) := by
      intro T hBT
      have hT0 : 0 < T := by linarith [abs_nonneg B]
      have huT : ∀ z ∈ Q, -T ≤ u z := fun z hz => by
        have := (hub z hz).1; have := le_abs_self B; linarith
      choose hφT hloc _hmass hFeq hFle _hEle using
        fun k => (hA.cegrell (σ k)).truncation hn hA.bounded hT0 one_pos
      set μ : ℕ → Measure (ComplexModel n) := fun k =>
        canonicalBedfordTaylorMeasure Q (U (σ k)) (hA.cegrell (σ k)).psh with hμdef
      set ν : ℕ → Measure (ComplexModel n) := fun k =>
        canonicalBedfordTaylorMeasure Q _ (hφT k).psh with hνdef
      -- (a) the truncations converge in capacity, hence weakly
      have hcap : ∀ (i : Fin n) (V : Opens (ComplexModel n)), V ≤ Q →
          ∀ T' : Set (ComplexModel n), IsCompact T' → T' ⊆ V → ∀ a : ℝ, 0 < a →
          Tendsto (fun k => relCapacity V {z | z ∈ T' ∧
            a < |(fun _ : Fin n => fun z => max (U (σ k) z) (-T)) i z -
              (fun _ : Fin n => u) i z|}) atTop (𝓝 0) := by
        intro i V hVQ T' hT' hT'V a ha
        have h := tendsto_relCapacity_of_le_opens hVQ hA.bounded hT' hT'V
          (tendsto_relCapacity_abs_sub_of_approximants hn hA hu hub hσ hlim hT'
            (hT'V.trans hVQ) ha)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
          fun k => relCapacity_mono ?_
        rintro z ⟨hzT, hz⟩
        exact ⟨hzT, lt_of_lt_of_le hz (abs_max_neg_sub_le (huT z (hVQ (hT'V hzT))))⟩
      have hweakT := tendsto_integral_mixed_of_relCapacity hφc.isCompact hφQ
        (u := fun k _ => fun z => max (U (σ k) z) (-T)) (v := fun _ => u)
        (fun k _ => (hφT k).psh) (fun _ => hu) hT0.le
        (fun k _ z hz => ⟨le_max_right _ _, (max_le ((hA.cegrell (σ k)).nonpos z hz)
          (by linarith)).trans hT0.le⟩)
        (fun _ z hz => ⟨huT z hz, (hub z hz).2.trans hT0.le⟩) hcap hφ hφc subset_rfl
      simp only [canonicalMixedBedfordTaylorMeasure_diagonal] at hweakT
      -- (b) the approximants converge weakly to `α`
      have hweak : Tendsto (fun k => ∫ z, φ z ∂μ k) atTop (𝓝 (∫ z, φ z ∂α)) :=
        (hA.weak φ hφ hφc).comp hσ.tendsto_atTop
      -- (c) the truncation changes the measures by at most `2C/T`
      have hdiff : ∀ k, |∫ z, φ z ∂ν k - ∫ z, φ z ∂μ k| ≤ Cφ * (2 * (C / T)) := by
        intro k
        have := (hφT k).isFiniteMeasure
        have := (hA.cegrell (σ k)).isFiniteMeasure
        set G : Set (ComplexModel n) := {z | z ∈ Q ∧ -T < U (σ k) z} with hGdef
        set F : Set (ComplexModel n) := {z | z ∈ Q ∧ U (σ k) z ≤ -T} with hFdef
        have hGm : MeasurableSet G := measurableSet_superlevel (hA.cegrell (σ k)).psh (-T)
        have hGc : Gᶜ ⊆ (Q : Set (ComplexModel n))ᶜ ∪ F := by
          intro z hz
          by_cases hzQ : z ∈ Q
          · exact Or.inr ⟨hzQ, not_lt.mp fun h => hz ⟨hzQ, h⟩⟩
          · exact Or.inl hzQ
        have hE : localEnergy Q 1 (U (σ k)) (hA.cegrell (σ k)).psh ≤ ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_toReal ((hA.cegrell (σ k)).localEnergy_ne_top zero_le_one)]
          exact ENNReal.ofReal_le_ofReal (hC (σ k))
        have hμF : μ k F ≤ ENNReal.ofReal (C / T) := by
          refine (hFle k).trans ?_
          rw [Real.rpow_neg_one, div_eq_mul_inv, mul_comm C, ENNReal.ofReal_mul (by positivity)]
          exact mul_le_mul' le_rfl hE
        have hbd : ∀ m : Measure (ComplexModel n), m (Q : Set (ComplexModel n))ᶜ = 0 →
            m F ≤ ENNReal.ofReal (C / T) → (m Gᶜ).toReal ≤ C / T := by
          intro m hm hmF
          refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
          calc m Gᶜ ≤ m ((Q : Set (ComplexModel n))ᶜ ∪ F) := measure_mono hGc
            _ ≤ m (Q : Set (ComplexModel n))ᶜ + m F := measure_union_le _ _
            _ ≤ ENNReal.ofReal (C / T) := by rw [hm, zero_add]; exact hmF
        have h1 := abs_integral_sub_le_of_restrict_eq hGm (hloc k) hφ.measurable hCφ'
        have h2 : (ν k Gᶜ).toReal ≤ C / T := hbd _
          (isBTLimit_canonicalBedfordTaylorMeasure (hφT k).psh).1 (by rw [hFeq k]; exact hμF)
        have h3 : (μ k Gᶜ).toReal ≤ C / T := hbd _
          (isBTLimit_canonicalBedfordTaylorMeasure (hA.cegrell (σ k)).psh).1 hμF
        calc |∫ z, φ z ∂ν k - ∫ z, φ z ∂μ k| ≤ Cφ * ((ν k Gᶜ).toReal + (μ k Gᶜ).toReal) := h1
          _ ≤ Cφ * (2 * (C / T)) := by
              apply mul_le_mul_of_nonneg_left _ hCφ0; linarith
      -- (d) pass to the limit
      have hlimd := ((hweakT.sub hweak).abs)
      exact le_of_tendsto' hlimd hdiff
    -- let `T → ∞`
    set d := |∫ z, φ z ∂canonicalBedfordTaylorMeasure Q u hu - ∫ z, φ z ∂α| with hddef
    have hd : d ≤ 0 := by
      have hlimT : Tendsto (fun m : ℕ => Cφ * (2 * (C / (|B| + 1 + m)))) atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := C)).div_atTop
          (tendsto_atTop_add_const_left _ (|B| + 1) tendsto_natCast_atTop_atTop)
        simpa using (h.const_mul 2).const_mul Cφ
      exact ge_of_tendsto' hlimT fun m => hT _ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hd0 : d = 0 := le_antisymm hd (abs_nonneg _)
    rw [hddef, abs_eq_zero, sub_eq_zero] at hd0
    exact hd0
  -- from integrals to measures
  have hMAfin : ∀ K, IsCompact K → K ⊆ Q → canonicalBedfordTaylorMeasure Q u hu K < ⊤ :=
    fun K hK hKQ => (isBTLimit_canonicalBedfordTaylorMeasure hu).2.1 K hK hKQ
  have hαfin : ∀ K, IsCompact K → K ⊆ Q → α K < ⊤ := fun K _ _ => measure_lt_top α K
  have h1 := restrict_le_of_tendsto_integral (Ω := Q) hMAfin (μ := fun _ => canonicalBedfordTaylorMeasure Q u hu)
    (ν := α) (fun _ => hMAfin) hαfin (fun _ => Measure.restrict_le_self)
    (fun φ hφ hφc hφQ => by rw [hint φ hφ hφc hφQ]; exact tendsto_const_nhds)
  have h2 := restrict_le_of_tendsto_integral (Ω := Q) hαfin (μ := fun _ => α)
    (ν := canonicalBedfordTaylorMeasure Q u hu) (fun _ => hαfin) hMAfin
    (fun _ => Measure.restrict_le_self)
    (fun φ hφ hφc hφQ => by rw [hint φ hφ hφc hφQ]; exact tendsto_const_nhds)
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr
    (isBTLimit_canonicalBedfordTaylorMeasure hu).1)] at h1
  rw [Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hαQ)] at h2
  exact le_antisymm h1 h2

/-- **Kołodziej's theorem on polydisks** (FPT `thm:compact-bounded-subsolution-ball-dirichlet`,
on `Q = a + R·P` instead of a ball): let `α` be a finite measure carried by a compact `K ⊆ Q` with
`α ≤ (ddᶜw)ⁿ` on `Q` for a plurisubharmonic `w` with `b ≤ w ≤ b + M`. Then there is a bounded
plurisubharmonic `u ∈ ℰ₀(Q)` with `(ddᶜu)ⁿ = α`, `-(M + 1) ≤ u ≤ 0` and boundary values `0`; it is
the largest bounded plurisubharmonic `v` with `(ddᶜv)ⁿ ≥ α` and `limsup v ≤ 0` at `∂Q`, and the
unique bounded plurisubharmonic solution with boundary values `0`. -/
theorem exists_kolodziej_polydisk (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R) (hαK : α Kᶜ = 0) {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw) :
    ∃ (u : ComplexModel n → ℝ) (hu : IsCegrellE0 (polydiskAtOpens a R) u),
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) u hu.psh = α ∧
      (∀ z ∈ polydiskAt a R, -(M + 1) ≤ u z ∧ u z ≤ 0) ∧
      (∀ v : ComplexModel n → ℝ, ∀ hv : IsLocallyBoundedPshOn (polydiskAtOpens a R) v,
        α.restrict (polydiskAt a R) ≤ canonicalBedfordTaylorMeasure (polydiskAtOpens a R) v hv →
        (∀ ζ ∈ frontier (polydiskAt a R), ∀ δ > 0, ∀ᶠ z in 𝓝[polydiskAt a R] ζ, v z < δ) →
        ∀ z ∈ polydiskAt a R, v z ≤ u z) ∧
      (∀ v : ComplexModel n → ℝ, ∀ hv : IsLocallyBoundedPshOn (polydiskAtOpens a R) v,
        canonicalBedfordTaylorMeasure (polydiskAtOpens a R) v hv = α →
        (∀ ζ ∈ frontier (polydiskAt a R), Tendsto v (𝓝[polydiskAt a R] ζ) (𝓝 0)) →
        ∀ z ∈ polydiskAt a R, v z = u z) := by
  obtain ⟨r, hr, χ, U, hA, σ, u, -, -, -, hσ, hu, hub, hbd, hlim⟩ :=
    exists_approximants_bounded_limit hn a hR α hK hKQ hαK hw hM hwb hα
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hαQ : α (Q : Set (ComplexModel n))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hKQ) hαK
  have hMA : canonicalBedfordTaylorMeasure Q u hu = α :=
    ma_eq_of_approximants hn hαQ hA hu (B := M + 1) hub hσ hlim
  have hE0 : IsCegrellE0 Q u :=
    { psh := hu
      bddBelow := ⟨M + 1, fun z hz => (hub z hz).1⟩
      nonpos := fun z hz => (hub z hz).2
      tendsto_frontier := hbd
      mass_lt_top := by rw [hMA]; exact measure_lt_top α _ }
  refine ⟨u, hE0, hMA, hub, fun v hv hαv hvbd => ?_, fun v hv hvMA hvbd => ?_⟩
  · refine le_of_ma_le_of_le_ma hn hA.bounded hu hv (fun ζ hζ δ hδ => ?_)
      (α := α) (measure_lt_top α _) hMA.le hαv
    have h1 := hvbd ζ hζ (δ / 2) (by positivity)
    have h2 := (hbd ζ hζ).eventually (Ioi_mem_nhds (show -(δ / 2) < 0 by linarith))
    filter_upwards [h1, h2] with z hz1 hz2
    have : -(δ / 2) < u z := hz2
    linarith
  · have hfin : canonicalBedfordTaylorMeasure Q v hv (Q : Set (ComplexModel n)) < ⊤ := by
      rw [hvMA]; exact measure_lt_top α _
    refine eq_of_ma_eq hn hA.bounded hv hu (fun ζ hζ δ hδ => ?_) hfin (hvMA.trans hMA.symm)
    have h := ((hvbd ζ hζ).sub (hbd ζ hζ)).eventually
      (Metric.ball_mem_nhds (0 - 0 : ℝ) hδ)
    filter_upwards [h] with z hz
    simpa [Real.dist_eq] using hz

end SGPT.Envelopes.MADirichlet
