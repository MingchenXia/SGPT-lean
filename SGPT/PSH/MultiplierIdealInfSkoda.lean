import SGPT.Okounkov.TranscendentalSkodaTheorem
import SGPT.Okounkov.TranscendentalSkodaAlgebra
import SGPT.PSH.CanonicalGrowthManifold
import SGPT.PSH.AnalyticGeneratorAlgebra
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

/-!
# Multiplier ideals versus `𝓘_∞` for analytic singularities (`lma:IandIinf`)

Source: `lma:IandIinf` of the chapter *Plurisubharmonic functions* (section *Analytic
singularities*): let `X` be compact and `φ ∈ QPSH(X)` a potential with analytic singularities.
For every `ε > 0` there is `k₀ > 0` such that for every `k ≥ k₀`,

  `𝓘(k(1 + ε)φ) ⊆ 𝓘_∞(kφ)`.

* `𝓘(ψ)` is the multiplier ideal `multiplierIdeal 1 ψ` (book convention `|f|² e^{-ψ}`,
  `def:pshfunctions:L1122`); `𝓘_∞(ψ)` is `SGPT.PSH.inftyIdeal ψ`, germs `f` with
  `log |f|² ≤ ψ + C` near the point (`def:Iinfty`).
* "Analytic singularities" (`def:neatanasing`) is the SGPT predicate
  `(VariableComplexAtlas.ofFixedModel n M).HasRationalAnalyticChartType φ`: in every holomorphic
  chart, near every point, `φ = c log ∑ |f_j|² + R` with `c ∈ ℚ_{>0}`, `f_j` holomorphic and `R`
  bounded. The quasi-plurisubharmonicity of `φ` is not used.

## Proof

The book's proof uses strong openness and the sharp Briançon–Skoda theorem to get the local
inclusion `𝓘(λφ)_x ⊆ 𝓘_∞((λ - n/c)_+ φ)_x`. We use instead Skoda's division theorem in the form
proved by the Okounkov SKODA package
(`SGPT.Okounkov.TranscendentalSkoda.multiplierIdeal_add_eq_pow_mul`,
`𝓘((k + m)ψ)_x = J^k 𝓘(mψ)_x` for `ψ = log ∑ |g_j|²` and integers `m ≥ n`), which needs no strong
openness and gives the slightly weaker local inclusion
`𝓘(λφ)_x ⊆ 𝓘_∞((k'/c) φ)_x` for every integer `k'` with `n + k' ≤ λc`
(`exists_logNormSq_le_of_multiplierIntegrableAt`, `mem_inftyIdeal_of_mem_multiplierIdeal`).
For `λ = s(1 + ε)` and `k' = ⌈sc⌉` this is enough as soon as `s ≥ (n + 1)/(cε)`. The coefficient
`c` of a presentation near `x` is kept for all points of a neighbourhood of `x` by transporting
the presentation through the chart changes, and compactness gives finitely many such
neighbourhoods, hence a uniform `k₀`. In dimension `0` Skoda's theorem is not needed.

* `exists_multiplierIdeal_le_inftyIdeal` — `lma:IandIinf`, real multiples `s ≥ s₀`;
* `lma_IandIinf` — `lma:IandIinf` for integers `k ≥ k₀`, the book's statement.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.MultiplierIdealInf

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.TranscendentalSkoda

/-! ### Extended-real arithmetic -/

/-- For `0 < q ≤ p` and `a ≤ A` (`A ≥ 0`): `p a ≤ q a + (p - q) A`. -/
theorem coe_mul_le_coe_mul_add {p q A : ℝ} (hq : 0 < q) (hqp : q ≤ p) {a : EReal}
    (ha : a ≤ (A : EReal)) :
    (p : EReal) * a ≤ (q : EReal) * a + (((p - q) * A : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos (hq.trans_le hqp)]
    exact bot_le
  | coe a =>
    have ha' : a ≤ A := EReal.coe_le_coe_iff.mp ha
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith
  | top => exact absurd ha (by simp)

/-- `t (x + b) = t x + t b` for a real `t > 0` and a real `b`. -/
theorem coe_mul_add_coe {t : ℝ} (ht : 0 < t) (x : EReal) (b : ℝ) :
    (t : EReal) * (x + (b : EReal)) = (t : EReal) * x + ((t * b : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos ht]
  | coe x => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos ht, EReal.top_add_coe]

/-- `log ‖x‖² ≤ log A` when `‖x‖² ≤ A`, `A > 0`. -/
theorem logNormSq_le_log {E : Type*} [NormedAddCommGroup E] {x : E} {A : ℝ} (hA : 0 < A)
    (hx : ‖x‖ ^ 2 ≤ A) : logNormSq x ≤ (Real.log A : EReal) := by
  rw [← ENNReal.log_ofReal_of_pos hA]
  exact ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hx)

/-! ### Scaling the weight -/

/-- Scaling the weight is scaling the exponent: `𝓘(c · (t w)) = 𝓘((ct) w)` for `t > 0`. -/
theorem multiplierIntegrableAt_coe_mul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] {μ : Measure E} {w : E → EReal} {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {f : E → ℂ} {z : E} :
    MultiplierIntegrableAt (fun y => (t : EReal) * w y) c f z μ ↔
      MultiplierIntegrableAt w (c * t) f z μ := by
  have hdens : multiplierDensity (fun y => (t : EReal) * w y) c f =
      multiplierDensity w (c * t) f := by
    funext y
    simp only [multiplierDensity, multiplierWeight]
    rw [← mul_assoc, ← EReal.coe_mul]
  unfold MultiplierIntegrableAt WeightedL2On
  rw [hdens]
  exact ⟨fun ⟨_, h⟩ => ⟨mul_pos hc ht, h⟩, fun ⟨_, h⟩ => ⟨hc, h⟩⟩

/-! ### The local inclusion -/

section Local

variable {n r : ℕ}

theorem norm_le_norm_generatorVector (f : Fin r → ComplexModel n → ℂ) (z : ComplexModel n)
    (j : Fin r) : ‖f j z‖ ≤ ‖generatorVector f z‖ :=
  PiLp.norm_apply_le (generatorVector f z) j

theorem norm_prod_le_pow (f : Fin r → ComplexModel n → ℂ) (z : ComplexModel n) {k : ℕ}
    (β : Fin k → Fin r) : ‖∏ i, f (β i) z‖ ≤ ‖generatorVector f z‖ ^ k := by
  rw [norm_prod]
  calc ∏ i, ‖f (β i) z‖ ≤ ∏ _i : Fin k, ‖generatorVector f z‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => norm_le_norm_generatorVector f z (β i))
    _ = ‖generatorVector f z‖ ^ k := by simp

/-- Dimension zero: every point is isolated, and integrability at the point forces
`F = 0` or `ψ ≠ -∞` there. -/
theorem exists_logNormSq_le_of_multiplierIntegrableAt_zero {f : Fin r → ComplexModel 0 → ℂ}
    {z₀ : ComplexModel 0} {u : ComplexModel 0 → EReal} {c : ℝ} (hc : 0 < c)
    {b : ComplexModel 0 → ℝ}
    (hu : u =ᶠ[𝓝 z₀] fun z => (c : EReal) * generatorLog f z + (b z : EReal))
    {t : ℝ} {F : ComplexModel 0 → ℂ} (hF : MultiplierIntegrableAt u t F z₀ volume) (k : ℕ) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 z₀, logNormSq (F z) ≤ (k : EReal) * generatorLog f z + (C : EReal) := by
  have hss : ∀ z : ComplexModel 0, z = z₀ := fun z => by
    ext i
    exact i.elim0
  by_cases hF0 : F z₀ = 0
  · refine ⟨0, Eventually.of_forall fun z => ?_⟩
    rw [hss z, hF0]
    simp
  obtain ⟨ht, U, hU, hzU, -, -, hint⟩ := hF
  have hUuniv : U = univ := eq_univ_of_forall fun z => by rw [hss z]; exact hzU
  have hconst : ∀ z ∈ U, multiplierDensity u t F z = multiplierDensity u t F z₀ :=
    fun z _ => by rw [hss z]
  rw [setLIntegral_congr_fun hU.measurableSet hconst, setLIntegral_const] at hint
  have hvol : volume U ≠ 0 := (hU.measure_pos volume ⟨z₀, hzU⟩).ne'
  have hdens : multiplierDensity u t F z₀ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_mul hvol] at hint
    exact lt_irrefl _ hint
  have hψ : generatorLog f z₀ ≠ ⊥ := by
    intro hbot
    apply hdens
    have hu0 : u z₀ = ⊥ := by
      rw [hu.self_of_nhds]
      show (c : EReal) * generatorLog f z₀ + (b z₀ : EReal) = ⊥
      rw [hbot, EReal.coe_mul_bot_of_pos hc]
      simp
    rw [multiplierDensity, hu0, multiplierWeight_bot ht]
    refine ENNReal.mul_top ?_
    simpa [ENNReal.ofReal_eq_zero, not_le] using hF0
  have hψt : generatorLog f z₀ ≠ ⊤ := logNormSq_ne_top _
  have hFb : logNormSq (F z₀) ≠ ⊥ := by simpa using hF0
  have hFt : logNormSq (F z₀) ≠ ⊤ := logNormSq_ne_top _
  obtain ⟨p, hp⟩ : ∃ p : ℝ, generatorLog f z₀ = (p : EReal) :=
    ⟨_, (EReal.coe_toReal hψt hψ).symm⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, logNormSq (F z₀) = (q : EReal) :=
    ⟨_, (EReal.coe_toReal hFt hFb).symm⟩
  refine ⟨q - k * p, Eventually.of_forall fun z => ?_⟩
  rw [hss z, hp, hq, ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  linarith

/-- **Local form of `lma:IandIinf`.** Near `z₀ ∈ ℂⁿ` let `u = c log ∑ |f_j|² + b` with `f_j`
holomorphic, `c > 0` and `b` bounded. If `|F|² e^{-t u}` is integrable near `z₀` and `k` is an
integer with `n + k ≤ tc`, then `log |F|² ≤ k log ∑ |f_j|² + C` near `z₀`. The proof is Skoda's
division theorem `𝓘((k + n)ψ) = J^k 𝓘(nψ)` for `ψ = log ∑ |f_j|²`. -/
theorem exists_logNormSq_le_of_multiplierIntegrableAt {f : Fin r → ComplexModel n → ℂ}
    {z₀ : ComplexModel n} (hf : HolomorphicGeneratorsAt f z₀) {u : ComplexModel n → EReal}
    {c : ℝ} (hc : 0 < c) {b : ComplexModel n → ℝ} (hb : BoundedRealGermAt b z₀)
    (hu : u =ᶠ[𝓝 z₀] fun z => (c : EReal) * generatorLog f z + (b z : EReal))
    {t : ℝ} {F : ComplexModel n → ℂ} (hF : MultiplierIntegrableAt u t F z₀ volume)
    {k : ℕ} (hk : ((n + k : ℕ) : ℝ) ≤ t * c) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 z₀, logNormSq (F z) ≤ (k : EReal) * generatorLog f z + (C : EReal) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact exists_logNormSq_le_of_multiplierIntegrableAt_zero hc hu hF k
  have ht : 0 < t := hF.1
  -- Step 1: `F ∈ 𝓘((k + n) ψ)`
  obtain ⟨B, -, hB⟩ := hb
  have hpsh := Pending.plurisubharmonicAt_scaled_generatorLog hf hc
  have hmore : MoreSingularAt u (fun z => (c : EReal) * generatorLog f z) z₀ := by
    refine ⟨B, ?_⟩
    filter_upwards [hu, hB] with z hz hBz
    rw [hz]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_of_abs_le hBz))
  have h1 := Pending.multiplierIntegrableAt_of_moreSingularAt hpsh.quasiPlurisubharmonicAt
    hmore hF
  have h2 : MultiplierIntegrableAt (generatorLog f) (t * c) F z₀ volume :=
    (multiplierIntegrableAt_coe_mul_iff ht hc).mp h1
  have hpos : (0 : ℝ) < ((k + n : ℕ) : ℝ) := by
    have : 0 < k + n := by omega
    exact_mod_cast this
  have h3 : MultiplierIntegrableAt (generatorLog f) ((k + n : ℕ) : ℝ) F z₀ volume :=
    Pending.multiplierIntegrableAt_of_exponent_le
      (quasiPlurisubharmonicAt_generatorLog hf) hpos
      (by rw [add_comm k n]; exact hk) h2
  -- Step 2: Skoda's division theorem
  obtain ⟨h, hh, hFeq⟩ :=
    (multiplierIdeal_add_eq_pow_mul n r hn f z₀ hf n k le_rfl F).mp h3
  -- Step 3: `|F| ≤ K' |f|^k` near `z₀`
  have hcont : ∀ β, ContinuousAt (h β) z₀ := fun β => by
    obtain ⟨-, U, hU, hzU, hhol, -⟩ := hh β
    exact (hhol.differentiableAt (hU.mem_nhds hzU)).continuousAt
  set H : ℝ := ∑ β, (‖h β z₀‖ + 1) with hH
  have hHb : ∀ᶠ z in 𝓝 z₀, ∀ β, ‖h β z‖ ≤ H := by
    rw [eventually_all]
    intro β
    filter_upwards [(hcont β).norm.eventually (gt_mem_nhds (lt_add_one ‖h β z₀‖))] with z hz
    exact hz.le.trans (Finset.single_le_sum (f := fun β => ‖h β z₀‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ β))
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ => by positivity
  set N : ℝ := (Fintype.card (Fin k → Fin r) : ℝ) * H with hN
  set K : ℝ := N ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨Real.log K, ?_⟩
  filter_upwards [hFeq, hHb] with z hz hHz
  set v := generatorVector f z with hv
  have hnorm : ‖F z‖ ≤ N * ‖v‖ ^ k := by
    rw [hz]
    calc ‖∑ β, (∏ i, f (β i) z) * h β z‖ ≤ ∑ β, ‖(∏ i, f (β i) z) * h β z‖ := norm_sum_le _ _
      _ ≤ ∑ _β : Fin k → Fin r, ‖v‖ ^ k * H := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_prod_le_pow f z β) (hHz β) (norm_nonneg _) (by positivity)
      _ = N * ‖v‖ ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hN]
          ring
  have hsq : ‖F z‖ ^ 2 ≤ K * (‖v‖ ^ 2) ^ k := by
    calc ‖F z‖ ^ 2 ≤ (N * ‖v‖ ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = N ^ 2 * (‖v‖ ^ 2) ^ k := by ring
      _ ≤ K * (‖v‖ ^ 2) ^ k :=
          mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
  -- Step 4: logarithms
  calc logNormSq (F z) = ENNReal.log (ENNReal.ofReal (‖F z‖ ^ 2)) := rfl
    _ ≤ ENNReal.log (ENNReal.ofReal (K * (‖v‖ ^ 2) ^ k)) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hsq)
    _ = ENNReal.log (ENNReal.ofReal K) + ENNReal.log (ENNReal.ofReal (‖v‖ ^ 2) ^ k) := by
        rw [ENNReal.ofReal_mul hKpos.le, ENNReal.ofReal_pow (by positivity), ENNReal.log_mul_add]
    _ = (Real.log K : EReal) + (k : EReal) * generatorLog f z := by
        rw [ENNReal.log_ofReal_of_pos hKpos, ENNReal.log_pow]
        rfl
    _ = (k : EReal) * generatorLog f z + (Real.log K : EReal) := add_comm _ _

end Local

/-! ### The inclusion at a point of a complex manifold -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`𝓘(tφ)_y ⊆ 𝓘_∞(sφ)_y` from one presentation.** Let `e` be a holomorphic chart and `V` an
open set on which `φ = c log ∑ |f_j|² + b` in the coordinates of `e`, with `f_j`
holomorphic on `V`, `c > 0` and `|b| ≤ B`. For `y` with `e y ∈ V`, reals `t, s > 0` and an
integer `k'` with `sc ≤ k'` and `n + k' ≤ tc`, every germ of `𝓘(tφ)` at `y` lies in `𝓘_∞(sφ)`.
The presentation is transported to the preferred chart at `y` by the chart change. -/
theorem mem_inftyIdeal_of_mem_multiplierIdeal {φ : M → EReal} (e : ComplexChart n M)
    {V : Set (ComplexModel n)} (hV : IsOpen V) {r : ℕ}
    {f : Fin r → ComplexModel n → ℂ} (hf : ∀ j, DifferentiableOn ℂ (f j) V) {c : ℝ}
    (hc : 0 < c) {b : ComplexModel n → ℝ} {B : ℝ} (hB : ∀ z ∈ V, |b z| ≤ B)
    (hφ : ∀ z ∈ V, chartFunction φ e z = (c : EReal) * generatorLog f z + (b z : EReal))
    {y : M} (hy : y ∈ e.val.source) (hyV : e.val y ∈ V) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {k' : ℕ} (hsk : s * c ≤ k') (hk : ((n + k' : ℕ) : ℝ) ≤ t * c) {g : M → ℂ}
    (hg : (multiplierIdeal (n := n) 1 (fun x => (t : EReal) * φ x)).mem y g) :
    (SGPT.PSH.inftyIdeal (n := n) (fun x => (s : EReal) * φ x)).mem y g := by
  set ey := complexChartAt (n := n) y with hey
  set τ := chartTransition ey e with hτ
  have hyey : y ∈ ey.val.source := mem_complexChartAt_source y
  set z₀ := ey.val y with hz₀
  have hz₀τ : z₀ ∈ τ.source := by
    simp only [hτ, chartTransition, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      mem_preimage]
    refine ⟨ey.val.map_source hyey, ?_⟩
    rw [hz₀, ey.val.left_inv hyey]
    exact hy
  have hτz₀ : τ z₀ = e.val y := by
    simp only [hτ, chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hz₀,
      ey.val.left_inv hyey]
  set U' := τ.source ∩ τ ⁻¹' V with hU'
  have hU'open : IsOpen U' := τ.isOpen_inter_preimage hV
  have hz₀U' : z₀ ∈ U' := ⟨hz₀τ, by rw [mem_preimage, hτz₀]; exact hyV⟩
  have hτdiff : ∀ z ∈ τ.source, DifferentiableAt ℂ τ z := fun z hz =>
    (HolomorphicMaps.chartTransition_contDiffAt ey e hz).differentiableAt (by simp)
  -- the transported presentation
  set f' : Fin r → ComplexModel n → ℂ := fun j z => f j (τ z) with hf'
  have hf'hol : HolomorphicGeneratorsAt f' z₀ :=
    ⟨U', hU'open, hz₀U', fun j z hz =>
      ((hf j (τ z) hz.2).comp z (hτdiff z hz.1).differentiableWithinAt (fun w hw => hw.2))⟩
  have hgen : ∀ z, generatorLog f' z = generatorLog f (τ z) := fun _ => rfl
  have hpres : ∀ z ∈ U', chartFunction φ ey z =
      (c : EReal) * generatorLog f' z + (b (τ z) : EReal) := by
    intro z hz
    have hzsrc : ey.val.symm z ∈ e.val.source := by
      have := hz.1
      simp only [hτ, chartTransition, OpenPartialHomeomorph.trans_source, mem_inter_iff,
        mem_preimage] at this
      exact this.2
    have h1 : chartFunction φ ey z = chartFunction φ e (τ z) := by
      simp only [chartFunction, hτ, chartTransition, OpenPartialHomeomorph.coe_trans,
        Function.comp_apply, e.val.left_inv hzsrc]
    rw [h1, hφ _ hz.2, hgen]
  have hpresev : chartFunction φ ey =ᶠ[𝓝 z₀]
      fun z => (c : EReal) * generatorLog f' z + (b (τ z) : EReal) :=
    eventually_of_mem (hU'open.mem_nhds hz₀U') hpres
  have hb' : BoundedRealGermAt (fun z => b (τ z)) z₀ :=
    ⟨max B 0, le_max_right _ _, eventually_of_mem (hU'open.mem_nhds hz₀U')
      fun z hz => (hB _ hz.2).trans (le_max_left _ _)⟩
  -- the integrability in the chart at `y`
  have hint : MultiplierIntegrableAt (chartFunction φ ey) t (fun z => g (ey.val.symm z)) z₀
      volume := by
    have h := hg.2
    have h' : MultiplierIntegrableAt (fun z => (t : EReal) * chartFunction φ ey z) 1
        (fun z => g (ey.val.symm z)) z₀ volume := h
    have := (multiplierIntegrableAt_coe_mul_iff one_pos ht).mp h'
    rwa [one_mul] at this
  obtain ⟨C, hC⟩ := exists_logNormSq_le_of_multiplierIntegrableAt hf'hol hc hb' hpresev hint hk
  -- an upper bound for `log ∑ |f'_j|²` near `z₀`
  have hvcont : ContinuousAt (generatorVector f') z₀ := by
    obtain ⟨U, hU, hzU, hfU⟩ := hf'hol
    have hc' : ∀ j, ContinuousAt (f' j) z₀ := fun j =>
      ((hfU j).differentiableAt (hU.mem_nhds hzU)).continuousAt
    exact (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr hc')
  set A' : ℝ := ‖generatorVector f' z₀‖ ^ 2 + 1 with hA'
  have hA'pos : 0 < A' := by positivity
  have hψbd : ∀ᶠ z in 𝓝 z₀, generatorLog f' z ≤ ((max (Real.log A') 0 : ℝ) : EReal) := by
    have hsqcont : ContinuousAt (fun z => ‖generatorVector f' z‖ ^ 2) z₀ :=
      (continuous_norm.continuousAt.comp hvcont).pow 2
    filter_upwards [hsqcont.eventually (gt_mem_nhds (lt_add_one (‖generatorVector f' z₀‖ ^ 2)))]
      with z hz
    exact (logNormSq_le_log hA'pos hz.le).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  set A : ℝ := max (Real.log A') 0 with hA
  -- the logarithmic bound on the manifold
  refine SGPT.PSH.mem_inftyIdeal_iff_log_bound.mpr ⟨hg.1, ?_⟩
  refine ⟨C + (k' - s * c) * A + s * max B 0, ?_⟩
  have hev : ∀ᶠ y' in 𝓝 y, ey.val y' ∈ U' ∧
      logNormSq (g (ey.val.symm (ey.val y'))) ≤
        (k' : EReal) * generatorLog f' (ey.val y') + (C : EReal) ∧
      generatorLog f' (ey.val y') ≤ (A : EReal) :=
    have hmem : ∀ᶠ z in 𝓝 z₀, z ∈ U' := hU'open.mem_nhds hz₀U'
    (ey.val.continuousAt hyey).eventually (hmem.and (hC.and hψbd))
  filter_upwards [hev, ey.val.open_source.mem_nhds hyey] with y' ⟨hy'U, hlog, hψy'⟩ hy'src
  rw [ey.val.left_inv hy'src] at hlog
  have hφy' : φ y' = (c : EReal) * generatorLog f' (ey.val y') + (b (τ (ey.val y')) : EReal) := by
    have := hpres _ hy'U
    simp only [chartFunction, ey.val.left_inv hy'src] at this
    exact this
  set X := generatorLog f' (ey.val y') with hX
  set β := b (τ (ey.val y')) with hβ
  have hβB : -(s * max B 0) ≤ s * β := by
    have h1 : |β| ≤ max B 0 := (hB _ hy'U.2).trans (le_max_left _ _)
    have h2 := neg_abs_le β
    nlinarith
  have hstep1 :
      (k' : EReal) * X ≤ ((s * c : ℝ) : EReal) * X + (((k' - s * c) * A : ℝ) : EReal) := by
    have := coe_mul_le_coe_mul_add (p := (k' : ℝ)) (q := s * c) (A := A) (mul_pos hs hc) hsk hψy'
    simpa only [EReal.coe_natCast] using this
  have hsφ : (s : EReal) * φ y' = ((s * c : ℝ) : EReal) * X + ((s * β : ℝ) : EReal) := by
    rw [hφy', coe_mul_add_coe hs, ← mul_assoc, ← EReal.coe_mul]
  rw [hsφ]
  calc logNormSq (g y') ≤ (k' : EReal) * X + (C : EReal) := hlog
    _ ≤ (((s * c : ℝ) : EReal) * X + (((k' - s * c) * A : ℝ) : EReal)) + (C : EReal) :=
        add_le_add hstep1 le_rfl
    _ = ((s * c : ℝ) : EReal) * X + (((k' - s * c) * A + C : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
    _ ≤ ((s * c : ℝ) : EReal) * X + (((s * β) + (C + (k' - s * c) * A + s * max B 0) : ℝ) :
          EReal) := by
        refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
        linarith
    _ = ((s * c : ℝ) : EReal) * X + ((s * β : ℝ) : EReal) +
          ((C + (k' - s * c) * A + s * max B 0 : ℝ) : EReal) := by
        rw [EReal.coe_add (s * β) (C + (k' - s * c) * A + s * max B 0)]
        exact (add_assoc _ _ _).symm

/-- **`lma:IandIinf`, real multiples.** Let `M` be a compact complex manifold and `φ` a function
with analytic singularities (`def:neatanasing`). For every `ε > 0` there is `s₀ > 0` such that
`𝓘(s(1 + ε)φ) ⊆ 𝓘_∞(sφ)` for every real `s ≥ s₀`. -/
theorem exists_multiplierIdeal_le_inftyIdeal [CompactSpace M] {φ : M → EReal}
    (hφ : (VariableComplexAtlas.ofFixedModel n M).HasRationalAnalyticChartType φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
      (multiplierIdeal (n := n) 1 (fun x => ((s * (1 + ε) : ℝ) : EReal) * φ x)).Le
        (SGPT.PSH.inftyIdeal (n := n) (fun x => (s : EReal) * φ x)) := by
  -- a presentation near every point, in the preferred chart
  have hloc : ∀ x : M, ∃ (c : ℝ) (V : Set (ComplexModel n)) (r : ℕ)
      (f : Fin r → ComplexModel n → ℂ) (b : ComplexModel n → ℝ) (B : ℝ),
      0 < c ∧ IsOpen V ∧ (complexChartAt (n := n) x).val x ∈ V ∧ (∀ j, DifferentiableOn ℂ (f j) V) ∧
      (∀ z ∈ V, |b z| ≤ B) ∧
      ∀ z ∈ V, chartFunction φ (complexChartAt (n := n) x) z =
        (c : EReal) * generatorLog f z + (b z : EReal) := by
    intro x
    set e := complexChartAt (n := n) x
    have hx : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    obtain ⟨c, r, f, hc, ⟨U, hU, hxU, hfU⟩, b, ⟨B, -, hB⟩, heq⟩ := hφ e (e.val x) hx
    obtain ⟨W, hWsub, hW, hxW⟩ := _root_.mem_nhds_iff.mp (hB.and heq)
    refine ⟨c, W ∩ U ∩ e.val.target, r, f, b, B, by exact_mod_cast hc,
      (hW.inter hU).inter e.val.open_target, ⟨⟨hxW, hxU⟩, hx⟩,
      fun j => (hfU j).mono fun z hz => hz.1.2, fun z hz => (hWsub hz.1.1).1,
      fun z hz => (hWsub hz.1.1).2⟩
  choose c V r f b B hc hV hxV hf hB hpres using hloc
  -- finitely many neighbourhoods cover `M`
  set O : M → Set M := fun x =>
    (complexChartAt (n := n) x).val.source ∩ (complexChartAt (n := n) x).val ⁻¹' V x with hO
  have hOopen : ∀ x, IsOpen (O x) := fun x =>
    (complexChartAt (n := n) x).val.isOpen_inter_preimage (hV x)
  have hxO : ∀ x, x ∈ O x := fun x => ⟨mem_complexChartAt_source x, hxV x⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover O hOopen
    (fun x _ => mem_iUnion.mpr ⟨x, hxO x⟩)
  set s₀ : ℝ := (T.sup fun x => ⌈((n : ℝ) + 1) / (c x * ε)⌉₊ : ℕ) + 1 with hs₀
  refine ⟨s₀, by positivity, fun s hs => ?_⟩
  intro y g hg
  obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.mp (hT (mem_univ y))
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hcx := hc x
  have hbig : ((n : ℝ) + 1) / (c x * ε) < s := by
    have h1 : ((n : ℝ) + 1) / (c x * ε) ≤ ⌈((n : ℝ) + 1) / (c x * ε)⌉₊ := Nat.le_ceil _
    have h2 : (⌈((n : ℝ) + 1) / (c x * ε)⌉₊ : ℝ) ≤
        (T.sup fun x => ⌈((n : ℝ) + 1) / (c x * ε)⌉₊ : ℕ) := by
      exact_mod_cast Finset.le_sup (f := fun x => ⌈((n : ℝ) + 1) / (c x * ε)⌉₊) hxT
    linarith
  set k' : ℕ := ⌈s * c x⌉₊ with hk'
  have hsk : s * c x ≤ k' := Nat.le_ceil _
  have hk'lt : (k' : ℝ) < s * c x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk : ((n + k' : ℕ) : ℝ) ≤ s * (1 + ε) * c x := by
    have hcε : 0 < c x * ε := mul_pos hcx hε
    have h1 : (n : ℝ) + 1 < s * (c x * ε) := by
      have := (div_lt_iff₀ hcε).mp hbig
      linarith
    push_cast
    nlinarith
  exact mem_inftyIdeal_of_mem_multiplierIdeal (complexChartAt (n := n) x) (hV x) (hf x) hcx
    (hB x) (hpres x) hyx.1 hyx.2 (by positivity) hs0 hsk hk hg

/-- **`lma:IandIinf`.** Let `M` be a compact complex manifold and `φ` a function with analytic
singularities (`def:neatanasing`; `φ ∈ QPSH(X)` is not needed). For every `ε > 0` there is an
integer `k₀ > 0` such that `𝓘(k(1 + ε)φ) ⊆ 𝓘_∞(kφ)` for every integer `k ≥ k₀`. -/
theorem lma_IandIinf [CompactSpace M] {φ : M → EReal}
    (hφ : (VariableComplexAtlas.ofFixedModel n M).HasRationalAnalyticChartType φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      (multiplierIdeal (n := n) 1 (fun x => ((k * (1 + ε) : ℝ) : EReal) * φ x)).Le
        (SGPT.PSH.inftyIdeal (n := n) (fun x => (k : EReal) * φ x)) := by
  obtain ⟨s₀, hs₀, h⟩ := exists_multiplierIdeal_le_inftyIdeal hφ hε
  refine ⟨⌈s₀⌉₊, Nat.ceil_pos.mpr hs₀, fun k hk => ?_⟩
  have hle : s₀ ≤ k := (Nat.le_ceil s₀).trans (by exact_mod_cast hk)
  have := h k hle
  simpa only [EReal.coe_natCast] using this

end Manifold

end SGPT.PSH.MultiplierIdealInf
