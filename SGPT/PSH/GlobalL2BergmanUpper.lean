import SGPT.PSH.GlobalL2BergmanLower
import SGPT.PSH.MultiplierIdealInfSkoda
import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes

/-!
# The upper bound of `prop:Bergman_approx`

Blueprint `claude-ot-ext.tex`, nodes `claude-ot-ext:bergman-upper`, `claude-ot-ext:bergman-approx`.
Source `prop:Bergman_approx` (`chapter_pshfunctions.tex` 1944--1993).  For the Bergman sequence

`φ_k = (1/k) log sup { |s|²_{h^k ⊗ h_T} : s ∈ H⁰(X, L^k ⊗ T), ∫_X |s|²_{h^k ⊗ h_T} e^{-kφ} ω^n ≤ 1 }`

(`bergmanSeq`, lane S62) and a potential `φ` with analytic singularities, we prove the second
inequality `φ_k ⪯ α_k φ` with `α_k ∈ (0,1)` strictly increasing to `1`, and assemble the whole
proposition with S62's first inequality (`bergmanSeq_lower`).

The book's proof: the unit ball of `H⁰(X, L^k ⊗ T ⊗ I(kφ))` (the sections of finite norm) lies in
`H⁰(X, L^k ⊗ T ⊗ I_∞(α_k k φ))` by `lma:IandIinf`, and finite dimension makes the constant uniform.
Here:

* `exists_logNormSq_le_of_inftyIdeal`: a section whose coefficients lie in `I_∞(u)` at every point
  satisfies `log |s|² ≤ u + C` on all of `X` (compactness);
* `exists_norm_le_of_weighted_lintegral_le`: the weighted `L²` unit ball is bounded for the sup
  norm (`H⁰` is finite dimensional; Fatou and the positivity of `ω^n` on open sets);
* `exists_uniform_logNormSq_le`: a finite-dimensional space of sections each satisfying
  `log |s|² ≤ u + C_s` satisfies one such bound uniformly on bounded sets (coordinates in a basis);
* `bergmanSeq_le_of_le_inftyIdeal`: if `I(kφ) ⊆ I_∞(sφ)` then `φ_k ≤ (s/k) φ + C`;
* `bergmanSeq_upper`: the second inequality, by a diagonal choice in `lma:IandIinf`
  (`SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal`, lane S49);
* `prop_Bergman_approx`: both inequalities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.TensorDictionaryDraft
  SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

/-! ### Elementary facts -/

/-- A local upper bound `f ≤ g + C` near every point of a compact space is global. -/
theorem exists_global_bound_of_local {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (f g : Y → EReal) (h : ∀ x, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, f y ≤ g y + (C : EReal)) :
    ∃ C : ℝ, ∀ y, f y ≤ g y + (C : EReal) := by
  classical
  choose C hC using h
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => {y | f y ≤ g y + (C x : EReal)})
    (fun x _ => hC x)
  refine ⟨∑ x ∈ t, |C x|, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  refine le_trans hyx (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hxt)

/-- `log ‖v‖² ≤ a` iff `‖v‖² ≤ e^a` (in `ℝ≥0∞`). -/
theorem logNormSq_le_iff {E : Type*} [NormedAddCommGroup E] (v : E) (a : EReal) :
    logNormSq v ≤ a ↔ ENNReal.ofReal (‖v‖ ^ 2) ≤ EReal.exp a := by
  rw [logNormSq, ← ENNReal.log_le_log_iff, EReal.log_exp]

/-- The weight `e^{-cφ}` never vanishes where `φ < +∞`, for `c ≥ 0`. -/
theorem multiplierWeight_ne_zero_of_ne_top {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊤) :
    multiplierWeight c a ≠ 0 := by
  rw [multiplierWeight, Ne, EReal.exp_eq_zero_iff]
  intro h
  have h' : (c : EReal) * a = ⊤ := by
    rw [← neg_neg ((c : EReal) * a), h]
    rfl
  rcases hc.lt_or_eq with hc | hc
  · induction a using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos hc] at h'; exact absurd h' (by simp)
    | coe a => rw [← EReal.coe_mul] at h'; exact absurd h' (EReal.coe_ne_top _)
    | top => exact ha rfl
  · rw [← hc, EReal.coe_zero, zero_mul] at h'
    exact absurd h' (by simp)

/-! ### Sections of a line bundle on a compact manifold -/

section Sections

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] [ContinuousFiberNorm V]

/-- Evaluation of holomorphic sections at a point, as a linear map. -/
def sectionEval (y : X) : HolomorphicSections (n := n) V →ₗ[ℂ] V y where
  toFun s := s y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Global logarithmic bound from `I_∞`.**  If at every point the coefficient of `s` in the
preferred frame lies in `I_∞(u)`, i.e. `log |s_e|² ≤ u + C` near the point, then
`log |s|² ≤ u + C'` on all of the compact manifold `X`. -/
theorem exists_logNormSq_le_of_inftyIdeal [CompactSpace X] {u : X → EReal}
    (s : HolomorphicSections (n := n) V)
    (hs : ∀ x, (SGPT.PSH.inftyIdeal (n := n) u).mem x
      (sectionCoefficient V (preferredOriginalFrame V x).val s)) :
    ∃ C : ℝ, ∀ y, logNormSq (s y) ≤ u y + (C : EReal) := by
  apply exists_global_bound_of_local
  intro x
  obtain ⟨-, C, hC⟩ := SGPT.PSH.mem_inftyIdeal_iff_log_bound.mp (hs x)
  set e := trivializationAt ℂ V x with he
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
  have hcont : ContinuousAt (frameNorm V e) x :=
    (frameNorm_continuousOn V e).continuousAt (e.open_baseSet.mem_nhds hx)
  set B : ℝ := frameNorm V e x + 1 with hB
  have hB0 : 0 < B := by
    have : 0 ≤ frameNorm V e x := norm_nonneg _
    linarith
  refine ⟨C + Real.log (B ^ 2), ?_⟩
  filter_upwards [hC, e.open_baseSet.mem_nhds hx,
    hcont.eventually (gt_mem_nhds (lt_add_one (frameNorm V e x)))] with y hy hyb hyB
  have hn := norm_eq_coefficient_mul_frameNorm V e s hyb
  have hfy : 0 ≤ frameNorm V e y := norm_nonneg _
  have hle : ‖s y‖ ^ 2 ≤ ‖sectionCoefficient V e s y‖ ^ 2 * B ^ 2 := by
    rw [hn, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfy hyB.le 2) (by positivity)
  calc logNormSq (s y) ≤ ENNReal.log (ENNReal.ofReal
        (‖sectionCoefficient V e s y‖ ^ 2 * B ^ 2)) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hle)
    _ = logNormSq (sectionCoefficient V e s y) + (Real.log (B ^ 2) : EReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.log_mul_add,
          ENNReal.log_ofReal_of_pos (x := B ^ 2) (by positivity)]
        rfl
    _ ≤ (u y + (C : EReal)) + (Real.log (B ^ 2) : EReal) := add_le_add hy le_rfl
    _ = u y + ((C + Real.log (B ^ 2) : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]

variable [MeasurableSpace X] [BorelSpace X]

/-- **The weighted `L²` unit ball is bounded.**  For a measure charging every nonempty open set
and a measurable weight `w > 0`, the sections with `∫ |s|² w dμ ≤ 1` have bounded sup norm.
(`H⁰` is finite dimensional, so the unit sphere is compact; on it the weighted integral is lower
semicontinuous by Fatou's lemma and positive.) -/
theorem exists_norm_le_of_weighted_lintegral_le [CompactSpace X] (μ : Measure X)
    [μ.IsOpenPosMeasure] {w : X → ℝ≥0∞} (hw : Measurable w) (hw0 : ∀ y, w y ≠ 0) :
    ∃ R : ℝ, ∀ s : HolomorphicSections (n := n) V,
      ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * w y ∂μ ≤ 1 → ‖s‖ ≤ R := by
  have := holomorphicSections_finiteDimensional (n := n) V
  have := FiniteDimensional.proper ℂ (HolomorphicSections (n := n) V)
  set Q : HolomorphicSections (n := n) V → ℝ≥0∞ :=
    fun s => ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * w y ∂μ with hQ
  have hmeas : ∀ s : HolomorphicSections (n := n) V,
      Measurable (fun y => ENNReal.ofReal (‖s y‖ ^ 2) * w y) := fun s =>
    (ENNReal.continuous_ofReal.comp ((sectionNormMap V s).continuous.pow 2)).measurable.mul hw
  have hQsmul : ∀ (c : ℂ) (s : HolomorphicSections (n := n) V),
      Q (c • s) = ENNReal.ofReal (‖c‖ ^ 2) * Q s := by
    intro c s
    simp only [hQ]
    rw [← lintegral_const_mul _ (hmeas s)]
    refine lintegral_congr fun y => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    change ‖c • s y‖ ^ 2 = _
    rw [norm_smul, mul_pow]
  by_contra hne
  push Not at hne
  choose s hsQ hsR using fun j : ℕ => hne ((j : ℝ) + 1)
  have hspos : ∀ j, 0 < ‖s j‖ := fun j => lt_trans (by positivity) (hsR j)
  set t : ℕ → HolomorphicSections (n := n) V := fun j => ((‖s j‖⁻¹ : ℝ) : ℂ) • s j with ht
  have htn : ∀ j, ‖t j‖ = 1 := by
    intro j
    rw [ht, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hspos j)),
      inv_mul_cancel₀ (hspos j).ne']
  have htQ : ∀ j, Q (t j) ≤ ENNReal.ofReal (((j : ℝ) + 1) ^ 2)⁻¹ := by
    intro j
    rw [ht, hQsmul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hspos j))]
    calc ENNReal.ofReal (‖s j‖⁻¹ ^ 2) * Q (s j) ≤ ENNReal.ofReal (‖s j‖⁻¹ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (hsQ j) zero_le
      _ = ENNReal.ofReal (‖s j‖⁻¹ ^ 2) := mul_one _
      _ ≤ ENNReal.ofReal (((j : ℝ) + 1) ^ 2)⁻¹ := by
          apply ENNReal.ofReal_le_ofReal
          rw [inv_pow]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (hsR j).le 2)
  -- a convergent subsequence on the unit sphere
  obtain ⟨t₀, ht₀, ψ, hψ, hlim⟩ := (isCompact_sphere (0 : HolomorphicSections (n := n) V) 1).tendsto_subseq
    (x := t) (fun j => by rw [mem_sphere_zero_iff_norm]; exact htn j)
  rw [mem_sphere_zero_iff_norm] at ht₀
  -- Fatou
  have hpt : ∀ y, ENNReal.ofReal (‖t₀ y‖ ^ 2) * w y ≤
      liminf (fun j => ENNReal.ofReal (‖t (ψ j) y‖ ^ 2) * w y) atTop := by
    intro y
    have hev : Tendsto (fun j => ‖t (ψ j) y‖) atTop (𝓝 ‖t₀ y‖) := by
      have h1 : Tendsto (fun j => ‖t (ψ j) - t₀‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp hlim
      have h2 : ∀ j, |‖t (ψ j) y‖ - ‖t₀ y‖| ≤ ‖t (ψ j) - t₀‖ := by
        intro j
        refine (abs_norm_sub_norm_le _ _).trans ?_
        have := norm_apply_le_sectionSize V (t (ψ j) - t₀) y
        exact this
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by
        rw [Real.norm_eq_abs]; exact h2 j) h1
    have hev2 : Tendsto (fun j => ENNReal.ofReal (‖t (ψ j) y‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖t₀ y‖ ^ 2))) :=
      ENNReal.tendsto_ofReal (hev.pow 2)
    by_cases h0 : ENNReal.ofReal (‖t₀ y‖ ^ 2) = 0
    · rw [h0, zero_mul]; exact zero_le
    · exact ((ENNReal.Tendsto.mul_const hev2 (Or.inl h0)).liminf_eq).ge
  have hQ0 : Q t₀ = 0 := by
    apply le_antisymm _ zero_le
    calc Q t₀ ≤ ∫⁻ y, liminf (fun j => ENNReal.ofReal (‖t (ψ j) y‖ ^ 2) * w y) atTop ∂μ :=
          lintegral_mono hpt
      _ ≤ liminf (fun j => Q (t (ψ j))) atTop := lintegral_liminf_le (fun j => hmeas _)
      _ ≤ liminf (fun j => ENNReal.ofReal (((ψ j : ℝ) + 1) ^ 2)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall fun j => htQ (ψ j))
      _ = 0 := by
          apply Tendsto.liminf_eq
          rw [← ENNReal.ofReal_zero]
          apply ENNReal.tendsto_ofReal
          have hψt : Tendsto (fun j => (ψ j : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
          have : Tendsto (fun j => ((ψ j : ℝ) + 1) ^ 2) atTop atTop :=
            (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ 1 hψt)
          exact this.inv_tendsto_atTop
  -- a section vanishing almost everywhere vanishes
  have hae : ∀ᵐ y ∂μ, ENNReal.ofReal (‖t₀ y‖ ^ 2) * w y = 0 :=
    (lintegral_eq_zero_iff (hmeas t₀)).mp hQ0
  have hopen : IsOpen {y | 0 < ‖t₀ y‖} := isOpen_lt continuous_const (sectionNormMap V t₀).continuous
  have hnull : μ {y | 0 < ‖t₀ y‖} = 0 := by
    apply measure_mono_null _ (ae_iff.mp hae)
    intro y hy hzero
    rcases mul_eq_zero.mp hzero with h | h
    · rw [ENNReal.ofReal_eq_zero] at h
      have : 0 < ‖t₀ y‖ ^ 2 := pow_pos hy 2
      linarith
    · exact hw0 y h
  have hempty := (hopen.measure_eq_zero_iff μ).mp hnull
  have hzero : t₀ = 0 := by
    apply (sectionSize_eq_zero_iff V t₀).mp
    apply le_antisymm _ (sectionSize_nonneg V t₀)
    apply (sectionSize_le_iff V t₀ le_rfl).mpr
    intro y
    by_contra hy
    push Not at hy
    have : y ∈ {y | 0 < ‖t₀ y‖} := hy
    rw [hempty] at this
    exact this
  rw [hzero, norm_zero] at ht₀
  exact zero_ne_one ht₀

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem sectionEval_apply (y : X) (s : HolomorphicSections (n := n) V) :
    sectionEval V y s = s y := rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Uniform logarithmic bound on bounded sets.**  If every section of a subspace `W` of the
(finite-dimensional) space of holomorphic sections satisfies `log |s|² ≤ u + C_s`, then one
constant works for all `s ∈ W` of sup norm at most `R`: write `s` in a basis of `W`; the
coordinates are continuous linear functionals. -/
theorem exists_uniform_logNormSq_le [CompactSpace X] {u : X → EReal}
    (W : Submodule ℂ (HolomorphicSections (n := n) V))
    (hW : ∀ s ∈ W, ∃ C : ℝ, ∀ y, logNormSq (s y) ≤ u y + (C : EReal)) (R : ℝ) :
    ∃ C : ℝ, ∀ s ∈ W, ‖s‖ ≤ R → ∀ y, logNormSq (s y) ≤ u y + (C : EReal) := by
  classical
  have := holomorphicSections_finiteDimensional (n := n) V
  set b := Module.finBasis ℂ W with hb
  set N := Module.finrank ℂ W with hN
  choose C hC using fun i : Fin N => hW (b i) (b i).2
  set K : Fin N → ℝ := fun i => ‖LinearMap.toContinuousLinearMap (b.coord i)‖ with hK
  set A : ℝ := (N : ℝ) * ∑ i, (K i * |R|) ^ 2 + 1 with hA
  have hA0 : 0 < A := by positivity
  set Cm : ℝ := ∑ i, |C i| with hCm
  refine ⟨Cm + Real.log A, fun s hs hsR y => ?_⟩
  set s' : W := ⟨s, hs⟩ with hs'
  -- the expansion in the basis
  have hy : s y = ∑ i, (b.repr s' i) • ((b i : HolomorphicSections (n := n) V) y) := by
    have h1 := congrArg (fun t : W => sectionEval V y (t : HolomorphicSections (n := n) V))
      (b.sum_repr s')
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, sectionEval_apply] at h1
    exact h1.symm
  -- the coordinates are bounded
  have hcoord : ∀ i, ‖b.repr s' i‖ ≤ K i * |R| := by
    intro i
    have h1 : ‖b.repr s' i‖ ≤ K i * ‖s'‖ := by
      have := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm s'
      rwa [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply] at this
    have h2 : ‖s'‖ ≤ |R| := (show ‖s'‖ = ‖s‖ from rfl) ▸ hsR.trans (le_abs_self R)
    exact h1.trans (mul_le_mul_of_nonneg_left h2
      (norm_nonneg (LinearMap.toContinuousLinearMap (b.coord i))))
  -- the pointwise bound
  have hnorm : ‖s y‖ ≤ ∑ i, (K i * |R|) * ‖(b i : HolomorphicSections (n := n) V) y‖ := by
    rw [hy]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _)
  have hsq : ‖s y‖ ^ 2 ≤ ∑ i, ((N : ℝ) * (K i * |R|) ^ 2) *
      ‖(b i : HolomorphicSections (n := n) V) y‖ ^ 2 := by
    calc ‖s y‖ ^ 2 ≤ (∑ i, (K i * |R|) * ‖(b i : HolomorphicSections (n := n) V) y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ (Finset.univ.card : ℝ) * ∑ i, ((K i * |R|) *
            ‖(b i : HolomorphicSections (n := n) V) y‖) ^ 2 := by
          exact sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun i => (K i * |R|) * ‖(b i : HolomorphicSections (n := n) V) y‖)
      _ = ∑ i, ((N : ℝ) * (K i * |R|) ^ 2) * ‖(b i : HolomorphicSections (n := n) V) y‖ ^ 2 := by
          rw [Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have hbi : ∀ i, ENNReal.ofReal (‖(b i : HolomorphicSections (n := n) V) y‖ ^ 2) ≤
      EReal.exp (u y + (Cm : EReal)) := by
    intro i
    refine ((logNormSq_le_iff _ _).mp (hC i y)).trans (EReal.exp_monotone ?_)
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  rw [logNormSq_le_iff]
  calc ENNReal.ofReal (‖s y‖ ^ 2)
      ≤ ENNReal.ofReal (∑ i, ((N : ℝ) * (K i * |R|) ^ 2) *
          ‖(b i : HolomorphicSections (n := n) V) y‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = ∑ i, ENNReal.ofReal ((N : ℝ) * (K i * |R|) ^ 2) *
          ENNReal.ofReal (‖(b i : HolomorphicSections (n := n) V) y‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (by positivity)
    _ ≤ ∑ i, ENNReal.ofReal ((N : ℝ) * (K i * |R|) ^ 2) * EReal.exp (u y + (Cm : EReal)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbi i) zero_le
    _ = ENNReal.ofReal (∑ i, (N : ℝ) * (K i * |R|) ^ 2) * EReal.exp (u y + (Cm : EReal)) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    _ ≤ ENNReal.ofReal A * EReal.exp (u y + (Cm : EReal)) := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        rw [hA, ← Finset.mul_sum]
        linarith
    _ = EReal.exp (u y + ((Cm + Real.log A : ℝ) : EReal)) := by
        rw [EReal.coe_add, ← add_assoc, EReal.exp_add (u y + (Cm : EReal)), EReal.exp_coe,
          Real.exp_log hA0, mul_comm]

end Sections

/-! ### The Bergman sequence -/

section Bergman

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- **`φ_k ≤ (s/k) φ + C` from `I(kφ) ⊆ I_∞(sφ)`.**  Every section of the weighted unit ball lies in
`H⁰(X, L^k ⊗ T ⊗ I(kφ))`, hence its coefficients lie in `I_∞(sφ)`; the unit ball is bounded and
`H⁰` is finite dimensional, so `|s|²_{h^k ⊗ h_T} ≤ e^{C} e^{sφ}` uniformly on it. -/
theorem bergmanSeq_le_of_le_inftyIdeal [CompactSpace X] (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) {k : ℕ} (hk : 0 < k) {s : ℝ}
    (hI : (multiplierIdeal (n := n) 1 (fun x => ((k : ℝ) : EReal) * φ x)).Le
      (SGPT.PSH.inftyIdeal (n := n) (fun x => (s : EReal) * φ x))) :
    ∃ C : ℝ, ∀ x, bergmanSeq ωb L T φ k x ≤ ((s / k : ℝ) : EReal) * φ x + (C : EReal) := by
  set V := (twistedPower L T k).Fiber with hV
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ : IsSmoothPositiveVolume (n := n) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hwm : Measurable (fun y => multiplierWeight (k : ℝ) (φ y)) :=
    measurable_originalMultiplierWeight hφ.1.upperSemicontinuous.measurable _
  have hw0 : ∀ y, multiplierWeight (k : ℝ) (φ y) ≠ 0 := fun y =>
    multiplierWeight_ne_zero_of_ne_top (Nat.cast_nonneg k) (hφ.1.ne_top y)
  obtain ⟨R, hR⟩ := exists_norm_le_of_weighted_lintegral_le (n := n) V μ hwm hw0
  set W := fullHolomorphicIdealSections (n := n) V (sourceDegreeMultiplierIdeal (n := n) k φ)
    with hW
  have hWb : ∀ t ∈ W, ∃ C : ℝ, ∀ y, logNormSq (t y) ≤ (s : EReal) * φ y + (C : EReal) := by
    intro t ht
    apply exists_logNormSq_le_of_inftyIdeal V t
    intro x
    exact hI x _ (((fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) V _
      (sourceDegreeMultiplierIdeal_isCoherent k hφ) t).mp ht) x)
  obtain ⟨C, hC⟩ := exists_uniform_logNormSq_le V W hWb R
  refine ⟨C / k, fun x => ?_⟩
  have hsup : (⨆ t : twistedSections L T k,
      ⨆ (_ : ∫⁻ y, ENNReal.ofReal (‖t y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤ 1),
        ENNReal.ofReal (‖t x‖ ^ 2)) ≤ EReal.exp ((s : EReal) * φ x + (C : EReal)) := by
    refine iSup₂_le fun t ht => ?_
    have htW : t ∈ W := (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) V k hφ t
      hμ).mpr (lt_of_le_of_lt ht ENNReal.one_lt_top)
    exact (logNormSq_le_iff _ _).mp (hC t htW (hR t ht) x)
  have hlog := ENNReal.log_monotone hsup
  rw [EReal.log_exp] at hlog
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold bergmanSeq
  calc ((1 / (k : ℝ) : ℝ) : EReal) * ENNReal.log (⨆ t : twistedSections L T k,
        ⨆ (_ : ∫⁻ y, ENNReal.ofReal (‖t y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
          ∂(IntegrationCurrent.kahlerVolume ωb) ≤ 1), ENNReal.ofReal (‖t x‖ ^ 2))
      ≤ ((1 / (k : ℝ) : ℝ) : EReal) * ((s : EReal) * φ x + (C : EReal)) :=
        mul_le_mul_of_nonneg_left hlog (EReal.coe_nonneg.mpr (by positivity))
    _ = ((s / k : ℝ) : EReal) * φ x + ((C / k : ℝ) : EReal) := by
        rw [MultiplierIdealInf.coe_mul_add_coe (by positivity), ← mul_assoc, ← EReal.coe_mul]
        have h1 : 1 / (k : ℝ) * s = s / k := by ring
        have h2 : 1 / (k : ℝ) * C = C / k := by ring
        rw [h1, h2]

/-- `a₀ φ + C ≤ a φ + (C + (a₀ - a) M)` for `0 < a ≤ a₀` and `φ ≤ M` (`M ≥ 0` real). -/
theorem coe_mul_add_le_coe_mul_add {a a₀ M C : ℝ} (ha : 0 < a) (haa : a ≤ a₀) {e : EReal}
    (he : e ≤ (M : EReal)) :
    (a₀ : EReal) * e + (C : EReal) ≤ (a : EReal) * e + ((C + (a₀ - a) * M : ℝ) : EReal) := by
  induction e using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (ha.trans_le haa), EReal.bot_add]; exact bot_le
  | coe r =>
    have hr : r ≤ M := EReal.coe_le_coe_iff.mp he
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    nlinarith
  | top => exact absurd he (by simp)

/-- A quasi-psh function on a compact manifold is bounded above by a nonnegative constant. -/
theorem exists_nonneg_upper_bound [CompactSpace X] {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, φ x ≤ (M : EReal) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨0, le_rfl, fun x => isEmptyElim x⟩
  obtain ⟨x₀, -, hx₀⟩ := (hφ.1.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
    univ_nonempty isCompact_univ
  refine ⟨max (φ x₀).toReal 0, le_max_right _ _, fun x => (hx₀ (mem_univ x)).trans ?_⟩
  by_cases hb : φ x₀ = ⊥
  · rw [hb]; exact bot_le
  · rw [← EReal.coe_toReal (hφ.1.ne_top x₀) hb]
    exact EReal.coe_le_coe_iff.mpr (by rw [EReal.toReal_coe]; exact le_max_left _ _)

/-- **The second inequality of `prop:Bergman_approx`**: for `φ` quasi-psh with analytic
singularities (`def:neatanasing`) there are `α_k ∈ (0,1)`, strictly increasing to `1`, and `k₀`
such that `φ_k ⪯ α_k φ`, i.e. `φ_k ≤ α_k φ + C_k`, for every `k ≥ k₀`.  The book takes
`α_k = (1 - n/(ck))_+`; we choose `α_k` diagonally from `lma:IandIinf` (for `ε_j = 1/(j+1)`,
`I(k φ) ⊆ I_∞(k φ/(1 + ε_j))` for `k ≥ k_j`) and multiply by `(k+1)/(k+2)` to make it strictly
increasing, using `φ ≤ M`. -/
theorem bergmanSeq_upper [CompactSpace X] (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (hφan : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).HasRationalAnalyticChartType φ) :
    ∃ α : ℕ → ℝ, StrictMono α ∧ (∀ k, 0 < α k ∧ α k < 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ C : ℝ, ∀ x : X,
        bergmanSeq ωb L T φ k x ≤ ((α k : ℝ) : EReal) * φ x + (C : EReal) := by
  classical
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hε
  have hεpos : ∀ j, 0 < ε j := fun j => by positivity
  choose s₀ hs₀ hS using fun j : ℕ =>
    SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal (n := n) hφan (hεpos j)
  -- thresholds, made strictly increasing
  set Tj : ℕ → ℕ := fun j => ⌈s₀ j * (1 + ε j)⌉₊ with hTj
  set T' : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), (Tj i + 1) with hT'
  have hT'succ : ∀ j, T' (j + 1) = T' j + (Tj (j + 1) + 1) := fun j => by
    simp only [hT', Finset.sum_range_succ]
  have hT'mono : StrictMono T' := strictMono_nat_of_lt_succ fun j => by rw [hT'succ]; omega
  have hTT' : ∀ j, Tj j ≤ T' j := by
    intro j
    cases j with
    | zero => simp [hT']
    | succ j => rw [hT'succ]; omega
  -- the index `J k`: the largest `j` with `T' j ≤ k`
  set J : ℕ → ℕ := fun k => Nat.findGreatest (fun j => T' j ≤ k) k with hJ
  have hJmono : Monotone J := fun k k' hkk' =>
    Nat.findGreatest_mono (fun _ hj => le_trans hj hkk') hkk'
  have hJspec : ∀ k, T' 0 ≤ k → T' (J k) ≤ k := fun k hk =>
    Nat.findGreatest_spec (P := fun j => T' j ≤ k) (Nat.zero_le k) hk
  have hJtend : Tendsto J atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro m
    exact ⟨T' m, fun k hk =>
      Nat.le_findGreatest (P := fun j => T' j ≤ k) ((hT'mono.id_le m).trans hk) hk⟩
  -- the exponents
  set α₀ : ℕ → ℝ := fun k => 1 / (1 + ε (J k)) with hα₀
  set r : ℕ → ℝ := fun k => ((k : ℝ) + 1) / ((k : ℝ) + 2) with hr
  set α : ℕ → ℝ := fun k => α₀ k * r k with hα
  have hα₀pos : ∀ k, 0 < α₀ k := fun k => by have := hεpos (J k); positivity
  have hα₀le : ∀ k, α₀ k ≤ 1 := fun k => by
    rw [hα₀, div_le_one (by have := hεpos (J k); positivity)]
    linarith [hεpos (J k)]
  have hrpos : ∀ k, 0 < r k := fun k => by positivity
  have hrlt : ∀ k, r k < 1 := fun k => by rw [hr, div_lt_one (by positivity)]; linarith
  have hα₀mono : Monotone α₀ := by
    intro k k' hkk'
    have hj := hJmono hkk'
    simp only [hα₀, hε]
    apply one_div_le_one_div_of_le (by positivity)
    have : (1 : ℝ) / ((J k' : ℝ) + 1) ≤ 1 / ((J k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
    linarith
  have hrmono : StrictMono r := by
    intro k k' hkk'
    have hk : (k : ℝ) < k' := by exact_mod_cast hkk'
    simp only [hr]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hαmono : StrictMono α := fun k k' hkk' =>
    calc α k = α₀ k * r k := rfl
      _ ≤ α₀ k' * r k := mul_le_mul_of_nonneg_right (hα₀mono hkk'.le) (hrpos k).le
      _ < α₀ k' * r k' := mul_lt_mul_of_pos_left (hrmono hkk') (hα₀pos k')
  have hαbd : ∀ k, 0 < α k ∧ α k < 1 := fun k =>
    ⟨mul_pos (hα₀pos k) (hrpos k),
      (mul_le_of_le_one_left (hrpos k).le (hα₀le k)).trans_lt (hrlt k)⟩
  have hεtend : Tendsto (fun k => ε (J k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => ε j) atTop (𝓝 0) := by
      simp only [hε]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hJtend
  have hα₀tend : Tendsto α₀ atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hεtend).inv₀ (by norm_num)
    simpa [hα₀, one_div] using this
  have hrtend : Tendsto r atTop (𝓝 1) := by
    have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun k => ?_
      simp only [Function.comp_apply]
      push_cast
      ring
    have h1 : Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h2
    rw [sub_zero] at h1
    refine h1.congr fun k => ?_
    simp only [hr]
    field_simp
    ring
  have hαtend : Tendsto α atTop (𝓝 1) := by
    have := hα₀tend.mul hrtend
    rwa [mul_one] at this
  obtain ⟨M, hM0, hM⟩ := exists_nonneg_upper_bound hφ
  refine ⟨α, hαmono, hαbd, hαtend, T' 0 + 1, fun k hk => ?_⟩
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
  have hJk := hJspec k (by omega)
  set j := J k with hjdef
  have h1ε : 0 < 1 + ε j := by have := hεpos j; linarith
  set s : ℝ := k / (1 + ε j) with hs
  have hss₀ : s₀ j ≤ s := by
    rw [hs, le_div_iff₀ h1ε]
    have h1 : s₀ j * (1 + ε j) ≤ (Tj j : ℝ) := Nat.le_ceil _
    have h2 : (Tj j : ℝ) ≤ k := by exact_mod_cast (hTT' j).trans hJk
    linarith
  have hI := hS j s hss₀
  have hsk : s * (1 + ε j) = k := by rw [hs]; field_simp
  rw [hsk] at hI
  obtain ⟨C, hC⟩ := bergmanSeq_le_of_le_inftyIdeal ωb L T hφ hk0 hI
  have hsk' : s / k = α₀ k := by
    show (k : ℝ) / (1 + ε j) / k = 1 / (1 + ε j)
    field_simp
  rw [hsk'] at hC
  refine ⟨C + (α₀ k - α k) * M, fun x => (hC x).trans ?_⟩
  exact coe_mul_add_le_coe_mul_add (hαbd k).1
    (mul_le_of_le_one_right (hα₀pos k).le (hrlt k).le) (hM x)

/-- **`prop:Bergman_approx`.**  Let `(L, h)` be a Hermitian line bundle with smooth metric,
`θ = c₁(L, h)`, `(T, h_T)` a Hermitian line bundle with smooth metric, `ω` a Kähler form, and
`φ ∈ PSH(X, θ)` with analytic singularities such that `θ_φ` is a Kähler current.  For the Bergman
sequence `φ_k` of `eq:Bergman_seq_def` (`bergmanSeq`) there are `α_k ∈ (0,1)`, strictly increasing
with limit `1`, and `k₀` such that `φ ⪯ φ_k ⪯ α_k φ` for all `k ≥ k₀`. -/
theorem prop_Bergman_approx [CompactSpace X] (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hφan : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).HasRationalAnalyticChartType φ) :
    ∃ α : ℕ → ℝ, StrictMono α ∧ (∀ k, 0 < α k ∧ α k < 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        (∃ c : ℝ, ∀ x : X, φ x ≤ bergmanSeq ωb L T φ k x + (c : EReal)) ∧
        (∃ C : ℝ, ∀ x : X, bergmanSeq ωb L T φ k x ≤ ((α k : ℝ) : EReal) * φ x + (C : EReal)) := by
  have hq : IsGlobalQuasiPshPotential (n := n) φ := by
    obtain ⟨ω', h⟩ := hφ
    exact h.quasiPshPotential
  obtain ⟨α, hαmono, hαbd, hαtend, k₁, hup⟩ := bergmanSeq_upper ωb L T hq hφan
  obtain ⟨k₂, hlow⟩ := bergmanSeq_preceq ωb L T hL hT θ hθ hφ
  exact ⟨α, hαmono, hαbd, hαtend, max k₁ k₂, fun k hk =>
    ⟨hlow k (le_of_max_le_right hk), hup k (le_of_max_le_left hk)⟩⟩

end Bergman

end SGPT.PSH.GlobalL2
