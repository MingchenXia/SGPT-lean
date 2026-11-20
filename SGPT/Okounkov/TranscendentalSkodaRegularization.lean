import SGPT.Okounkov.TranscendentalSkodaL2Statements
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.WeightedL2ExtensionLimit

/-!
# Skoda's theorem: the division step from the surjective case

Blueprint `claude-tok-skoda`, node `skoda:division-step`:
`SurjectiveSkodaStatement → SkodaDivisionStatement`.

Let `f ∈ 𝓘((ℓ + 1)φ)_x`, `φ = log ∑ |gᵢ|²`, `ℓ ≥ n`. Strong openness gives `p > ℓ` with
`f ∈ 𝓘((p + 1)φ)_x`. On a ball `D` around `x` the regularized tuples
`G^δ = (g₁, …, g_r, √δ)` have no common zeros and `|G^δ|² = |g|² + δ ≥ |g|²`, so Skoda's division
for surjective tuples gives `H^δ` holomorphic on a fixed neighbourhood `U` of `x` with
`f = ∑ gᵢ H^δᵢ + √δ H^δ_{r+1}` and `∫_U |H^δ|² (|g|² + δ)^{-p}` bounded independently of `δ`.
Montel's theorem and Fatou's lemma (TN `exists_subseq_differentiableOn_extension_of_weighted_bounds`)
give limits `hᵢ` along a common subsequence `δ_k → 0` with `f = ∑ gᵢ hᵢ` and
`∫_U |hᵢ|² |g|^{-2p} < ∞`, so `hᵢ ∈ 𝓘(pφ)_x ⊆ 𝓘(ℓφ)_x`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set Metric SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal

variable {n r : ℕ}

/-! ### Subsequences -/

/-- A finite family of subsequence-stable properties, each of which can be achieved by passing
to a further subsequence, holds simultaneously along one subsequence. -/
theorem exists_strictMono_forall_of_fintype {ι : Type*} [Fintype ι]
    (P : ι → (ℕ → ℕ) → Prop)
    (hP : ∀ i (φ ψ : ℕ → ℕ), P i φ → StrictMono ψ → P i (φ ∘ ψ))
    (hex : ∀ i (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i φ := by
  classical
  have key : ∀ s : Finset ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ s, P i φ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun k => k, fun _ _ h => h, by simp⟩
    | insert a s _ ih =>
      obtain ⟨φ, hφ, hs⟩ := ih
      obtain ⟨ψ, hψ, ha⟩ := hex a φ hφ
      refine ⟨φ ∘ ψ, hφ.comp hψ, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha
      · exact hP i φ ψ (hs i hi) hψ
  obtain ⟨φ, hφ, h⟩ := key Finset.univ
  exact ⟨φ, hφ, fun i => h i (Finset.mem_univ i)⟩

/-- A subsequence of a locally uniformly convergent sequence converges locally uniformly to the
same limit. -/
theorem tendstoLocallyUniformlyOn_comp_strictMono {α β : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ℕ → α → β} {f : α → β} {s : Set α}
    (h : TendstoLocallyUniformlyOn F f atTop s) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    TendstoLocallyUniformlyOn (fun k => F (ψ k)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hψ.tendsto_atTop.eventually hev⟩

/-! ### The regularized tuple -/

/-- The regularized tuple `(g₁, …, g_r, √δ)`. -/
def regTuple (g : Fin r → ComplexModel n → ℂ) (δ : ℝ) : Fin (r + 1) → ComplexModel n → ℂ :=
  Fin.snoc (α := fun _ => ComplexModel n → ℂ) g fun _ => ((Real.sqrt δ : ℝ) : ℂ)

theorem generatorNormSq_regTuple (g : Fin r → ComplexModel n → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (z : ComplexModel n) : generatorNormSq (regTuple g δ) z = generatorNormSq g z + δ := by
  simp only [generatorNormSq, regTuple, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg δ),
    Real.sq_sqrt hδ]

theorem sum_regTuple_mul (g : Fin r → ComplexModel n → ℂ) (δ : ℝ)
    (H : Fin (r + 1) → ComplexModel n → ℂ) (z : ComplexModel n) :
    ∑ i, regTuple g δ i z * H i z =
      ∑ i : Fin r, g i z * H i.castSucc z + ((Real.sqrt δ : ℝ) : ℂ) * H (Fin.last r) z := by
  simp [regTuple, Fin.sum_univ_castSucc]

theorem differentiableOn_regTuple {g : Fin r → ComplexModel n → ℂ} {D : Set (ComplexModel n)}
    (hg : ∀ i, DifferentiableOn ℂ (g i) D) (δ : ℝ) (i : Fin (r + 1)) :
    DifferentiableOn ℂ (regTuple g δ i) D := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [regTuple, differentiableOn_const]
  · simpa [regTuple] using hg j

/-! ### Weights -/

/-- `(|g|² + δ)^{-q} ≤ e^{-qφ}` for `q > 0`, `δ > 0` (including the poles of `φ`). -/
theorem ofReal_rpow_le_multiplierWeight (g : Fin r → ComplexModel n → ℂ) {q δ : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (z : ComplexModel n) :
    ENNReal.ofReal ((generatorNormSq g z + δ) ^ (-q)) ≤ multiplierWeight q (generatorLog g z) := by
  by_cases hz : ∃ j, g j z ≠ 0
  · have hS : 0 < generatorNormSq g z := by
      obtain ⟨j, hj⟩ := hz
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
        (f := fun j => ‖g j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    rw [generatorLog_of_nonzero hz, multiplierWeight_coe]
    apply ENNReal.ofReal_le_ofReal
    rw [show -(q * Real.log (generatorNormSq g z)) = Real.log (generatorNormSq g z) * (-q) by ring,
      ← Real.rpow_def_of_pos hS]
    exact Real.rpow_le_rpow_of_nonpos hS (by linarith) (by linarith)
  · push Not at hz
    rw [(generatorLog_eq_bot_iff g z).mpr hz, multiplierWeight_bot hq]
    exact le_top

/-- `e^{-qφ} ≤ sup_k (|g|² + δ_k)^{-q}` for `δ_k = 1/(k+1)`. -/
theorem multiplierWeight_le_iSup (g : Fin r → ComplexModel n → ℂ) {q : ℝ} (hq : 0 < q)
    (z : ComplexModel n) :
    multiplierWeight q (generatorLog g z) ≤
      ⨆ k : ℕ, ENNReal.ofReal ((generatorNormSq g z + 1 / ((k : ℝ) + 1)) ^ (-q)) := by
  have hδ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hz : ∃ j, g j z ≠ 0
  · have hS : 0 < generatorNormSq g z := by
      obtain ⟨j, hj⟩ := hz
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
        (f := fun j => ‖g j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    rw [generatorLog_of_nonzero hz, multiplierWeight_coe]
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal
        ((generatorNormSq g z + 1 / ((k : ℝ) + 1)) ^ (-q))) atTop
        (𝓝 (ENNReal.ofReal (generatorNormSq g z ^ (-q)))) := by
      apply ENNReal.tendsto_ofReal
      have h1 : Tendsto (fun k : ℕ => generatorNormSq g z + 1 / ((k : ℝ) + 1)) atTop
          (𝓝 (generatorNormSq g z)) := by simpa using tendsto_const_nhds.add hδ
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hS.ne')).tendsto.comp h1
    rw [show Real.exp (-(q * Real.log (generatorNormSq g z))) = generatorNormSq g z ^ (-q) by
      rw [Real.rpow_def_of_pos hS]; ring_nf]
    exact le_of_tendsto' hlim fun k => le_iSup (fun k : ℕ => ENNReal.ofReal
      ((generatorNormSq g z + 1 / ((k : ℝ) + 1)) ^ (-q))) k
  · push Not at hz
    rw [(generatorLog_eq_bot_iff g z).mpr hz, multiplierWeight_bot hq]
    have hS0 : generatorNormSq g z = 0 := by simp [generatorNormSq, hz]
    simp only [hS0, zero_add]
    rw [top_le_iff, iSup_eq_top]
    intro b hb
    -- `(1/(k+1))^{-q} = (k+1)^q → ∞`
    have hlarge : Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ q) atTop atTop :=
      (tendsto_rpow_atTop hq).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    obtain ⟨k, hk⟩ := (hlarge.eventually_gt_atTop b.toReal).exists
    refine ⟨k, ?_⟩
    have heq : (1 / ((k : ℝ) + 1)) ^ (-q) = ((k : ℝ) + 1) ^ q := by
      rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
    rw [heq]
    calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb.ne).symm
      _ < ENNReal.ofReal (((k : ℝ) + 1) ^ q) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hk

/-- `e^{-ℓφ} ≤ M^{p-ℓ} e^{-pφ}` where `|g|² ≤ M`, for `0 < ℓ ≤ p`. -/
theorem multiplierWeight_le_mul_of_le (g : Fin r → ComplexModel n → ℂ) {ℓ p M : ℝ}
    (hℓ : 0 < ℓ) (hℓp : ℓ ≤ p) (hM : 0 < M) {z : ComplexModel n}
    (hzM : generatorNormSq g z ≤ M) :
    multiplierWeight ℓ (generatorLog g z) ≤
      ENNReal.ofReal (M ^ (p - ℓ)) * multiplierWeight p (generatorLog g z) := by
  by_cases hz : ∃ j, g j z ≠ 0
  · have hS : 0 < generatorNormSq g z := by
      obtain ⟨j, hj⟩ := hz
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
        (f := fun j => ‖g j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    rw [generatorLog_of_nonzero hz, multiplierWeight_coe, multiplierWeight_coe,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set S := generatorNormSq g z
    have e1 : Real.exp (-(ℓ * Real.log S)) = S ^ (p - ℓ) * Real.exp (-(p * Real.log S)) := by
      rw [Real.rpow_def_of_pos hS, ← Real.exp_add]; ring_nf
    rw [e1]
    gcongr
  · push Not at hz
    rw [(generatorLog_eq_bot_iff g z).mpr hz, multiplierWeight_bot hℓ, multiplierWeight_bot
      (lt_of_lt_of_le hℓ hℓp), ENNReal.mul_top (by positivity)]

/-! ### The division step -/

/-- **The division step from the surjective case** (`skoda:division-step`). -/
theorem skodaDivisionStatement_of_surjective (hSK : SurjectiveSkodaStatement) :
    SkodaDivisionStatement := by
  intro n r hn g x hg ℓ hℓ f hf
  obtain ⟨V, hVo, hxV, hgV⟩ := hg
  -- strong openness
  have hpsh : PlurisubharmonicOn (generatorLog g) V := by
    intro y hy
    have h := SGPT.Foundations.Analysis.Pending.plurisubharmonicAt_scaled_generatorLog
      ⟨V, hVo, hy, hgV⟩ one_pos
    have heq : (fun y => ((1 : ℝ) : EReal) * generatorLog g y) = generatorLog g := by
      funext y; simp
    rwa [heq] at h
  obtain ⟨c', hc'lt, hfc'⟩ :=
    SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier.exists_gt_multiplierIntegrableAt
      hVo hpsh hxV hf
  set p : ℝ := c' - 1 with hpdef
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hℓp : (ℓ : ℝ) < p := by
    have : ((ℓ + 1 : ℕ) : ℝ) = ℓ + 1 := by push_cast; ring
    rw [this] at hc'lt; linarith
  have hnp : (n : ℝ) < p := lt_of_le_of_lt (by exact_mod_cast hℓ) hℓp
  have hp0 : 0 < p := lt_of_lt_of_le hℓpos hℓp.le
  rw [show c' = p + 1 by ring] at hfc'
  obtain ⟨-, V₁, hV₁o, hxV₁, hfhol, hfL2⟩ := hfc'
  -- the ball
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hVo.inter hV₁o) x ⟨hxV, hxV₁⟩
  set ρ : ℝ := ε / 4 with hρ
  have hρpos : 0 < ρ := by positivity
  have hcl : closedBall x (2 * ρ) ⊆ V ∩ V₁ :=
    (closedBall_subset_ball (by linarith)).trans hεsub
  set D := ball x (2 * ρ) with hD
  have hDV : D ⊆ V := ball_subset_closedBall.trans (hcl.trans inter_subset_left)
  have hDV₁ : D ⊆ V₁ := ball_subset_closedBall.trans (hcl.trans inter_subset_right)
  set S := generatorNormSq g with hS
  have hScont : ContinuousOn S V := by
    rw [hS]
    have : generatorNormSq g = fun y => ∑ j, ‖g j y‖ ^ 2 := rfl
    rw [this]
    exact continuousOn_finsetSum _ fun j _ => ((hgV j).continuousOn.norm).pow 2
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x (2 * ρ)).exists_bound_of_continuousOn
    (hScont.mono (hcl.trans inter_subset_left))
  set M : ℝ := max M₀ 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hSM : ∀ z ∈ D, S z ≤ M := fun z hz => by
    have h := hM₀ z (ball_subset_closedBall hz)
    rw [Real.norm_of_nonneg (generatorNormSq_nonneg g z)] at h
    exact h.trans (le_max_left _ _)
  -- Skoda's division for the regularized tuples
  obtain ⟨U, hUo, hKU, hUD, hU⟩ := hSK n hn D isOpen_ball (convex_ball x _) isBounded_ball
    (closedBall x ρ) (isCompact_closedBall x ρ) (closedBall_subset_ball (by linarith)) p hnp
  have hxU : x ∈ U := hKU (mem_closedBall_self hρpos.le)
  set A₀ : ℝ≥0∞ := ∫⁻ z in V₁, multiplierDensity (generatorLog g) (p + 1) f z with hA₀
  have hA₀ : A₀ ≠ ⊤ := hfL2.2.ne
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hIδ : ∀ k, (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 *
      generatorNormSq (regTuple g (δ k)) z ^ (-(p + 1)))) ≤ A₀ := by
    intro k
    calc (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 *
          generatorNormSq (regTuple g (δ k)) z ^ (-(p + 1))))
        ≤ ∫⁻ z in D, multiplierDensity (generatorLog g) (p + 1) f z := by
          refine lintegral_mono fun z => ?_
          rw [generatorNormSq_regTuple g (hδpos k).le, ENNReal.ofReal_mul (sq_nonneg _),
            multiplierDensity]
          gcongr
          exact ofReal_rpow_le_multiplierWeight g (by linarith) (hδpos k) z
      _ ≤ A₀ := lintegral_mono_set hDV₁
  have hex : ∀ k, ∃ H : Fin (r + 1) → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, regTuple g (δ k) i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) *
        generatorNormSq (regTuple g (δ k)) z ^ (-p)) ≤
        ENNReal.ofReal (2 + 2 * n / (p - n)) * A₀ := by
    intro k
    have hpos : ∀ z ∈ D, 0 < generatorNormSq (regTuple g (δ k)) z := fun z _ => by
      rw [generatorNormSq_regTuple g (hδpos k).le]
      exact add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) (hδpos k)
    obtain ⟨H, hH, hHeq, hHb⟩ := hU (r + 1) (regTuple g (δ k))
      (differentiableOn_regTuple (fun j => (hgV j).mono hDV) _) hpos f (hfhol.mono hDV₁)
      (ne_top_of_le_ne_top hA₀ (hIδ k))
    exact ⟨H, hH, hHeq, hHb.trans (by gcongr; exact hIδ k)⟩
  choose H hHhol hHeq hHbd using hex
  set C : ℝ≥0∞ := ENNReal.ofReal (2 + 2 * n / (p - n)) * A₀ with hC
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA₀
  set w : ℕ → ComplexModel n → ℝ≥0∞ := fun k z => ENNReal.ofReal ((S z + δ k) ^ (-p)) with hw
  have hwmono : ∀ z, Monotone fun k => w k z := by
    intro z k l hkl
    apply ENNReal.ofReal_le_ofReal
    have hδ : δ l ≤ δ k := by
      simp only [hδdef]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
    exact Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z)
      (hδpos l)) (by linarith) (by linarith)
  have hwmeas : ∀ k, AEMeasurable (w k) (volume.restrict (⋃ _k : ℕ, U)) := by
    intro k
    rw [iUnion_const]
    have hc : ContinuousOn (fun z => (S z + δ k) ^ (-p)) U := by
      refine ContinuousOn.rpow_const ((hScont.mono (hUD.trans hDV)).add continuousOn_const)
        fun z _ => Or.inl ?_
      exact (add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) (hδpos k)).ne'
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hUo.measurableSet
  have hlow : ∀ z ∈ ⋃ _k : ℕ, U, ∃ r > 0, ∃ δ' : ℝ, 0 < δ' ∧
      ∀ y ∈ ball z r, ENNReal.ofReal δ' ≤ w 0 y := by
    intro z hz
    rw [iUnion_const] at hz
    obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hUo z hz
    refine ⟨r₀, hr₀, (M + 1) ^ (-p), by positivity, fun y hy => ?_⟩
    apply ENNReal.ofReal_le_ofReal
    have hyD : y ∈ D := hUD (hr₀U hy)
    simp only [hδdef, Nat.cast_zero, zero_add, div_one]
    exact Real.rpow_le_rpow_of_nonpos (by linarith [generatorNormSq_nonneg g y])
      (by linarith [hSM y hyD]) (by linarith)
  have hbound : ∀ i k, ∫⁻ z in U, ENNReal.ofReal (‖H k i z‖ ^ 2) * w k z ≤ C := by
    intro i k
    refine le_trans (lintegral_mono fun z => ?_) (hHbd k)
    rw [generatorNormSq_regTuple g (hδpos k).le, hw]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by
      linarith [generatorNormSq_nonneg g z, hδpos k]) _)
    exact Finset.single_le_sum (f := fun i => ‖H k i z‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- a common convergent subsequence for the first `r` components
  set P : Fin r → (ℕ → ℕ) → Prop := fun i φ => ∃ h : ComplexModel n → ℂ,
    DifferentiableOn ℂ h U ∧ TendstoLocallyUniformlyOn (fun k => H (φ k) i.castSucc) h atTop U ∧
    ∫⁻ z in U, ENNReal.ofReal (‖h z‖ ^ 2) * ⨆ k, w k z ≤ C with hPdef
  have hPsub : ∀ i (φ ψ : ℕ → ℕ), P i φ → StrictMono ψ → P i (φ ∘ ψ) := by
    rintro i φ ψ ⟨h, hh, hconv, hb⟩ hψ
    exact ⟨h, hh, tendstoLocallyUniformlyOn_comp_strictMono hconv hψ, hb⟩
  have hPex : ∀ i (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (φ ∘ ψ) := by
    intro i φ hφ
    have hwm' : ∀ z ∈ ⋃ _k : ℕ, U, Monotone fun k => w (φ k) z :=
      fun z _ _ _ hab => hwmono z (hφ.monotone hab)
    have hlow' : ∀ z ∈ ⋃ _k : ℕ, U, ∃ r > 0, ∃ δ' : ℝ, 0 < δ' ∧
        ∀ y ∈ ball z r, ENNReal.ofReal δ' ≤ w (φ 0) y := by
      intro z hz
      obtain ⟨r₀, hr₀, δ', hδ', hl⟩ := hlow z hz
      exact ⟨r₀, hr₀, δ', hδ', fun y hy => (hl y hy).trans (hwmono y (Nat.zero_le _))⟩
    obtain ⟨ψ, G₀, hψ, hG₀, hconv, -, hb⟩ :=
      SGPT.Foundations.Analysis.Pending.exists_subseq_differentiableOn_extension_of_weighted_bounds
        (α := Empty) (ι := Empty.elim) (g := Empty.elim) (U := fun _ => U) (fun _ => hUo)
        (fun _ _ _ => le_rfl) (w := fun k => w (φ k)) hwm' (fun k => hwmeas (φ k)) hlow'
        (F := fun k => H (φ k) i.castSucc) (fun k => hHhol (φ k) i.castSucc)
        (fun _ a => a.elim) hCtop (fun k => hbound i.castSucc (φ k))
    rw [iUnion_const] at hG₀ hconv hb
    refine ⟨ψ, hψ, G₀, hG₀, hconv, le_trans (lintegral_mono fun z => ?_) hb⟩
    gcongr
    exact hwmono z (hφ.id_le _)
  obtain ⟨φ, hφ, hPφ⟩ := exists_strictMono_forall_of_fintype P hPsub hPex
  choose h hhol hconv hhb using hPφ
  -- the limit identity
  have hlimit : ∀ z ∈ U, f z = ∑ i, g i z * h i z := by
    intro z hz
    have hk : ∀ k, f z = ∑ i : Fin r, g i z * H (φ k) i.castSucc z +
        ((Real.sqrt (δ (φ k)) : ℝ) : ℂ) * H (φ k) (Fin.last r) z := fun k => by
      rw [hHeq (φ k) z hz, sum_regTuple_mul]
    have h1 : Tendsto (fun k => ∑ i : Fin r, g i z * H (φ k) i.castSucc z) atTop
        (𝓝 (∑ i, g i z * h i z)) :=
      tendsto_finsetSum _ fun i _ => ((hconv i).tendsto_at hz).const_mul (g i z)
    -- the last component stays bounded at `z`
    obtain ⟨r₀, hr₀, δ', hδ', hl⟩ := hlow z (by rw [iUnion_const]; exact hz)
    obtain ⟨r₁, hr₁, M', hM'⟩ :=
      SGPT.Foundations.Analysis.Pending.exists_eventually_norm_le_of_weighted_bounds
        (U := fun _ => U) (fun _ => hUo) (fun _ _ _ => le_rfl) (w := w)
        (fun y _ => hwmono y) (F := fun k => H k (Fin.last r)) (fun k => hHhol k (Fin.last r))
        hCtop (fun k => hbound (Fin.last r) k) (by rw [iUnion_const]; exact hz) hr₀ hδ' hl
    have hbdd : IsBoundedUnder (· ≤ ·) atTop
        ((fun w => ‖w‖) ∘ fun k => H (φ k) (Fin.last r) z) := by
      refine ⟨M', ?_⟩
      have := hφ.tendsto_atTop.eventually hM'
      simp only [eventually_map]
      filter_upwards [this] with k hk
      exact hk.2 z (mem_ball_self hr₁)
    have hsq : Tendsto (fun k => ((Real.sqrt (δ (φ k)) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((Real.continuous_sqrt.tendsto 0).comp (hδ0.comp hφ.tendsto_atTop))
      rw [Real.sqrt_zero] at this
      have h' := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h'
      exact h'
    have h2 := hsq.zero_mul_isBoundedUnder_le hbdd
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact tendsto_nhds_unique (tendsto_const_nhds.congr hk) h3
  -- the limits lie in `𝓘(ℓφ)_x`
  have hmem : ∀ i, MultiplierIntegrableAt (generatorLog g) (ℓ : ℝ) (h i) x volume := by
    intro i
    refine ⟨hℓpos, U, hUo, hxU, hhol i, aemeasurable_multiplierDensity_generatorLog hUo
      (fun j => (hgV j).continuousOn.mono (hUD.trans hDV)) hℓpos.ne' (hhol i).continuousOn, ?_⟩
    calc (∫⁻ z in U, multiplierDensity (generatorLog g) ℓ (h i) z)
        ≤ ∫⁻ z in U, ENNReal.ofReal (M ^ (p - ℓ)) *
            (ENNReal.ofReal (‖h i z‖ ^ 2) * ⨆ k, w k z) := by
          refine setLIntegral_mono' hUo.measurableSet fun z hz => ?_
          rw [multiplierDensity, mul_left_comm]
          gcongr
          exact (multiplierWeight_le_mul_of_le g hℓpos hℓp.le hMpos (hSM z (hUD hz))).trans
            (by gcongr; exact multiplierWeight_le_iSup g hp0 z)
      _ = ENNReal.ofReal (M ^ (p - ℓ)) *
            ∫⁻ z in U, ENNReal.ofReal (‖h i z‖ ^ 2) * ⨆ k, w k z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_of_le_of_lt (hhb i) (lt_top_iff_ne_top.mpr hCtop))
  exact ⟨h, hmem, Filter.eventually_of_mem (hUo.mem_nhds hxU) hlimit⟩

end SGPT.Okounkov.TranscendentalSkoda
