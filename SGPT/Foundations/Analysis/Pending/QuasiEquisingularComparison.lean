import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.IEnvelopeCompetitors
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim

set_option autoImplicit false

/-!
# Comparing quasi-equisingular approximations

Quasi-equisingular approximations (Xia, *Singularities in global pluripotential theory* (SGPT),
Definition 1.6.4; `FirstPass.QuasiEquisingularApproximation.IsQuasiEquisingularApproximation`)
are determined by their target only up to bounded functions.  This file records what does and
what does not survive that ambiguity.

* **Finite shifts** (`IsQuasiEquisingularApproximation.add_const`): adding to the `k`-th term a
  constant `a_k ≥ 0` with `a_k ↓ 0` gives another quasi-equisingular approximation of the same
  potential.  Also `IsQuasiEquisingularApproximation.mono_error`: the errors may be enlarged.
* **Comparison without a constant fails** (`exists_quasiEquisingularApproximation_not_le`; blueprint
  `trace:qe-comparison`, Xia Proposition 1.6.3, `xia-sgpt:page-0050`): on a nonempty compact Kähler
  manifold, `u_j = 0` and `v_k = 1 / (k + 1)` approximate `0` (background `ω`), and
  `v_k ≤ (1 - ε) u_j` holds for no `ε`, `j`, `k`.  The comparison holds only up to a constant.
* **Pointwise compatible order fails** (`not_exists_quasiEquisingularApproximations_le`; blueprint
  `trace:qe-compatible-order`, Xia p. 0280): `ψ + 1 ≼_I ψ`, yet no approximations `φ_j ↓ ψ + 1`,
  `ψ_j ↓ ψ` satisfy `φ_j ≤ ψ_j` for every `j`, since the limit would give `ψ + 1 ≤ ψ`.
* **Compatible order up to bounded functions**
  (`exists_quasiEquisingularApproximations_moreSingular_ofType`,
  `exists_quasiEquisingularApproximations_moreSingular`): if `φ ≼_I ψ`, Demailly's approximations
  of types `(2^{-k}, I(2^k φ))` and `(2^{-k}, I(2^k ψ))` can be taken with one common error
  sequence, and then `φ_k ≤ ψ_k + C_k` for every `k`.  This is Xia's argument (p. 0280): the ideal
  inclusion `I(2^k φ) ⊆ I(2^k ψ)` compares the two weights up to `O(1)`
  (`IdealWeightComparison.moreSingularOn_univ_of_le`).
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularComparison

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation
  FirstPass.GlobalAnalyticSingularities FirstPass.HolomorphicIdealSheaves FirstPass.IEnvelope

noncomputable section

/-! ### Finite shifts -/

section Shifts

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Adding a real constant to the weight does not change local multiplier integrability. -/
theorem multiplierIntegrableAt_chartFunction_add_const_iff {φ : M → EReal} (a : ℝ)
    (e : ComplexChart n M) (c : ℝ) (f : ComplexModel n → ℂ) (z : ComplexModel n)
    [MeasurableSpace (ComplexModel n)] (μ : Measure (ComplexModel n)) :
    MultiplierIntegrableAt (chartFunction (fun x => φ x + (a : EReal)) e) c f z μ ↔
      MultiplierIntegrableAt (chartFunction φ e) c f z μ := by
  have hfun : chartFunction (fun x => φ x + (a : EReal)) e =
      fun y => chartFunction φ e y - ((-a : ℝ) : EReal) := by
    funext y
    simp only [chartFunction, EReal.coe_neg, sub_eq_add_neg, neg_neg]
  rw [hfun]
  constructor
  · rintro ⟨hc, U, hU, hzU, hhol, hint⟩
    exact ⟨hc, U, hU, hzU, hhol, (weightedL2On_sub_const_iff (-a)).mp hint⟩
  · rintro ⟨hc, U, hU, hzU, hhol, hint⟩
    exact ⟨hc, U, hU, hzU, hhol, (weightedL2On_sub_const_iff (-a)).mpr hint⟩

/-- A multiplier-ideal inclusion is unchanged when a real constant is added on the left. -/
theorem multiplierIdealIncluded_add_const_left {φ ψ : M → EReal} {d c : ℝ}
    (h : MultiplierIdealIncluded (n := n) φ d ψ c) (a : ℝ) :
    MultiplierIdealIncluded (n := n) (fun x => φ x + (a : EReal)) d ψ c := by
  intro e z hz f hf hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  exact h e z hz f hf ((multiplierIntegrableAt_chartFunction_add_const_iff a e d f z _).mp hmem)

/-- Adding a real constant preserves the chartwise analytic singularity type. -/
theorem hasManifoldAnalyticSingularityType_add_const {u : M → EReal}
    (hu : HasManifoldAnalyticSingularityType (n := n) u) (a : ℝ) :
    HasManifoldAnalyticSingularityType (n := n) (fun x => u x + (a : EReal)) := by
  intro e z hz
  obtain ⟨c, N, f, hc, hgen, b, ⟨C, hC0, hC⟩, heq⟩ := hu e z hz
  refine ⟨c, N, f, hc, hgen, fun y => b y + a, ⟨C + |a|, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hC] with y hy
    exact (abs_add_le _ _).trans (add_le_add hy le_rfl)
  · filter_upwards [heq] with y hy
    change u (e.val.symm y) + (a : EReal) = _
    have hy' : u (e.val.symm y) = _ := hy
    rw [hy', EReal.coe_add, add_assoc]

/-- A real constant has analytic singularity type in every chart (one generator `1`). -/
theorem hasManifoldAnalyticSingularityType_const (a : ℝ) :
    HasManifoldAnalyticSingularityType (n := n) (fun _ : M => (a : EReal)) := by
  intro e z _
  refine ⟨1, 1, fun _ _ => 1, by norm_num,
    ⟨univ, isOpen_univ, mem_univ z, fun _ => differentiableOn_const 1⟩, fun _ => a,
    ⟨|a|, abs_nonneg a, Eventually.of_forall fun _ => le_rfl⟩, Eventually.of_forall fun y => ?_⟩
  have hlog : generatorLog (fun (_ : Fin 1) (_ : ComplexModel n) => (1 : ℂ)) y = 0 := by
    rw [generatorLog_of_nonzero ⟨0, one_ne_zero⟩]
    simp [generatorNormSq]
  change (a : EReal) = _
  simp only [hlog, mul_zero, zero_add]

variable [IsComplexManifold n M]

/-- **Finite shifts of a quasi-equisingular approximation.**  If `(u_k)` is a
quasi-equisingular approximation of `u` and `a_k ≥ 0` decreases to `0`, then `(u_k + a_k)` is
one too, with the same errors. -/
theorem IsQuasiEquisingularApproximation.add_const {omega : KahlerBackground n M}
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) {a : ℕ → ℝ}
    (ha : NonnegativeDecreasesToZero a) :
    IsQuasiEquisingularApproximation omega θ u ε (fun k x => uSeq k x + (a k : EReal)) := by
  refine ⟨h.target, h.error, fun k => (h.term k).add_const (a k),
    fun k => hasManifoldAnalyticSingularityType_add_const (h.term_hasAnalyticSingularityType k) _,
    ⟨fun x i j hij => add_le_add (h.term_antitone x hij) (EReal.coe_le_coe_iff.mpr (ha.2.1 hij)),
      fun x => ?_⟩, fun c d hc hcd => ?_⟩
  · have ha' : Tendsto (fun k => (a k : EReal)) atTop (𝓝 (0 : EReal)) := by
      simpa using EReal.tendsto_coe.mpr ha.2.2
    have hlim := (h.term_tendsto x).prodMk_nhds ha'
    have hcont := EReal.continuousAt_add (p := (u x, (0 : EReal))) (Or.inr (by simp))
      (Or.inr (by simp))
    have h2 : Tendsto (fun p : EReal × EReal => p.1 + p.2) (𝓝 (u x, (0 : EReal))) (𝓝 (u x)) := by
      simpa using hcont.tendsto
    exact h2.comp hlim
  · filter_upwards [h.eventually_multiplierIdealIncluded hc hcd] with k hk
    exact multiplierIdealIncluded_add_const_left hk (a k)

/-- **Enlarging the errors.**  A quasi-equisingular approximation with errors `ε` is one with any
larger errors `ε' ≥ ε` that still decrease to `0`. -/
theorem IsQuasiEquisingularApproximation.mono_error {omega : KahlerBackground n M}
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {ε ε' : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hε' : NonnegativeDecreasesToZero ε') (hle : ∀ k, ε k ≤ ε' k) :
    IsQuasiEquisingularApproximation omega θ u ε' uSeq := by
  refine ⟨h.target, hε', fun k => ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hsemi : ((ε' k - ε k) • omega.form).val.IsSemipositive :=
    RestrictedMassEnvelopeMonotone.kahler_smul_isSemipositive omega (sub_nonneg.mpr (hle k))
  have h' := LocalPotentials.isThetaPshPotential_add_of_semipositive (h.term k) hsemi
  have hform : θ + ε k • omega.form + (ε' k - ε k) • omega.form = θ + ε' k • omega.form := by
    rw [add_assoc, ← add_smul, add_sub_cancel]
  rwa [hform] at h'

end Shifts

/-! ### Comparison without a constant fails (`trace:qe-comparison`) -/

section Comparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The comparison of quasi-equisingular approximations needs a constant** (blueprint
`trace:qe-comparison`, Xia SGPT, Proposition 1.6.3, `xia-sgpt:page-0050`).  On a nonempty
compact Kähler manifold, with background `θ = ω`, the sequences `u_j = 0` and `v_k = 1 / (k + 1)`
are quasi-equisingular approximations of `0`, and for no real `δ` and no `j, k` does
`v_k ≤ (1 - δ) u_j` hold (it fails at every point).  So "`v_k ≤ (1 - ε) u_j` for `k ≥ k₀`" is
false as written; it can hold only up to an additive constant. -/
theorem exists_quasiEquisingularApproximation_not_le [Nonempty M]
    (omega : KahlerBackground n M) :
    ∃ (u : M → EReal) (ε ε' : ℕ → ℝ) (uSeq vSeq : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega omega.form u ε uSeq ∧
      IsQuasiEquisingularApproximation omega omega.form u ε' vSeq ∧
      ∀ (δ : ℝ) (j k : ℕ) (x : M), ¬ vSeq k x ≤ ((1 - δ : ℝ) : EReal) * uSeq j x := by
  have hu : IsThetaPshPotential omega.form.val (fun _ : M => ((0 : ℝ) : EReal)) := by
    simpa using (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hconst := isQuasiEquisingularApproximation_const omega omega.form hu
    (hasManifoldAnalyticSingularityType_const (n := n) 0)
  have ha : NonnegativeDecreasesToZero (fun k : ℕ => 1 / ((k : ℝ) + 1)) :=
    ⟨fun k => by positivity,
      fun i j hij => one_div_le_one_div_of_le (by positivity)
        (by have h' : (i : ℝ) ≤ j := by exact_mod_cast hij
            linarith),
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  refine ⟨_, _, _, _, _, hconst, IsQuasiEquisingularApproximation.add_const hconst ha,
    fun δ j k x hle => ?_⟩
  have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have h0 : ((1 - δ : ℝ) : EReal) * ((0 : ℝ) : EReal) = ((0 : ℝ) : EReal) := by
    rw [← EReal.coe_mul, mul_zero]
  change ((0 : ℝ) : EReal) + ((1 / ((k : ℝ) + 1) : ℝ) : EReal) ≤
    ((1 - δ : ℝ) : EReal) * ((0 : ℝ) : EReal) at hle
  rw [h0, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
  linarith

end Comparison

/-! ### Compatible order (`trace:qe-compatible-order`) -/

section CompatibleOrder

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Pointwise order passes to pointwise limits of quasi-equisingular approximations. -/
theorem le_of_decreasesPointwiseTo {X : Type*} {φSeq ψSeq : ℕ → X → EReal} {φ ψ : X → EReal}
    (hφ : DecreasesPointwiseTo φSeq φ) (hψ : DecreasesPointwiseTo ψSeq ψ)
    (h : ∀ k x, φSeq k x ≤ ψSeq k x) (x : X) : φ x ≤ ψ x :=
  le_of_tendsto_of_tendsto' (hφ.2 x) (hψ.2 x) fun k => h k x

/-- **Quasi-equisingular approximations cannot be ordered pointwise in general** (blueprint
`trace:qe-compatible-order`, Xia SGPT, p. 0280).  For a theta-PSH potential `ψ` on a nonempty
manifold, `ψ + 1 ≼_I ψ` (the multiplier ideals coincide), but no quasi-equisingular
approximations `φ_k` of `ψ + 1` and `ψ_k` of `ψ`, in any backgrounds, satisfy `φ_k ≤ ψ_k` for every
`k`: the limit would give `ψ + 1 ≤ ψ`. -/
theorem not_exists_quasiEquisingularApproximations_le [Nonempty M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {ψ : M → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) :
    IOrderOnManifold (n := n) (fun x => ψ x + ((1 : ℝ) : EReal)) ψ ∧
      ¬ ∃ (ε ε' : ℕ → ℝ) (φSeq ψSeq : ℕ → M → EReal),
        IsQuasiEquisingularApproximation omega θ (fun x => ψ x + ((1 : ℝ) : EReal)) ε φSeq ∧
        IsQuasiEquisingularApproximation omega θ ψ ε' ψSeq ∧ ∀ k x, φSeq k x ≤ ψSeq k x := by
  constructor
  · have h := (iEquivalentOnManifold_sub_const (n := n) ψ (-1)).1
    have hfun : (fun x => ψ x - ((-1 : ℝ) : EReal)) = fun x => ψ x + ((1 : ℝ) : EReal) := by
      funext x
      simp only [EReal.coe_neg, sub_eq_add_neg, neg_neg]
    rwa [hfun] at h
  · rintro ⟨ε, ε', φSeq, ψSeq, hφ, hψ', hle⟩
    obtain ⟨x⟩ := ‹Nonempty M›
    obtain ⟨y, -, hy⟩ := hψ.2 x univ isOpen_univ (mem_univ x)
    have htop : ψ y ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top y
    have h := le_of_decreasesPointwiseTo hφ.decreasesPointwise hψ'.decreasesPointwise hle y
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ψ y = r := ⟨(ψ y).toReal, (EReal.coe_toReal htop hy).symm⟩
    simp only [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    linarith

/-- In dimension `0` any potential with no pole is bounded below on a compact manifold, so every
theta-PSH potential is more singular than any other. -/
theorem moreSingularOn_univ_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] [CompactSpace M]
    {θ : SmoothRealForm 0 M 2} {φ ψ : M → EReal} (hφ : IsThetaPshPotential θ φ)
    (hψ : IsThetaPshPotential θ ψ) : MoreSingularOn φ ψ univ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, fun x => isEmptyElim x⟩
  have : DiscreteTopology M :=
    discreteTopology_iff_isOpen_singleton.mpr
      FiniteGeodesicsFullMassAnyDim.isOpen_singleton_of_dim_zero
  have : Finite M := finite_of_compact_of_discrete
  obtain ⟨C, hC⟩ := hφ.exists_global_upper_bound
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min ψ
  have hbot : ψ x₀ ≠ ⊥ := FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hψ x₀
  have htop : ψ x₀ ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top x₀
  refine ⟨C - (ψ x₀).toReal, fun x _ => (hC x).trans ?_⟩
  calc (C : EReal) = ((ψ x₀).toReal : EReal) + ((C - (ψ x₀).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
    _ = ψ x₀ + ((C - (ψ x₀).toReal : ℝ) : EReal) := by rw [EReal.coe_toReal htop hbot]
    _ ≤ ψ x + ((C - (ψ x₀).toReal : ℝ) : EReal) := add_le_add (hx₀ x) le_rfl

/-- **Compatible quasi-equisingular approximations, up to bounded functions** (corrected form of
blueprint `trace:qe-compatible-order`; Xia SGPT, proof of Proposition 8.2.1 (1), p. 0280).  On a
compact Kähler manifold of positive dimension, if `φ ≼_I ψ` are theta-PSH, Demailly's
quasi-equisingular approximations of types `(2^{-k}, I(2^k φ))` and `(2^{-k}, I(2^k ψ))` can be
taken with one common error sequence, and then `φ_k ≤ ψ_k + C_k` for every `k`. -/
theorem exists_quasiEquisingularApproximations_moreSingular_ofType (hn : 0 < n) [CompactSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ ψ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (h : IOrderOnManifold (n := n) φ ψ) :
    ∃ (ε : ℕ → ℝ) (φSeq ψSeq : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ φ ε φSeq ∧
      IsQuasiEquisingularApproximation omega θ ψ ε ψSeq ∧
      (∀ k, HasAnalyticSingularitiesOfType (n := n) (φSeq k) (((2 ^ k : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := n) ((2 ^ k : ℕ) : ℝ) φ)) ∧
      (∀ k, HasAnalyticSingularitiesOfType (n := n) (ψSeq k) (((2 ^ k : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := n) ((2 ^ k : ℕ) : ℝ) ψ)) ∧
      ∀ k, MoreSingularOn (φSeq k) (ψSeq k) univ := by
  obtain ⟨ε₁, φSeq, hφq, hφt⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType hn omega θ
      hφ
  obtain ⟨ε₂, ψSeq, hψq, hψt⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType hn omega θ
      hψ
  have hε : NonnegativeDecreasesToZero (fun k => max (ε₁ k) (ε₂ k)) := by
    refine ⟨fun k => le_max_of_le_left (hφq.error_nonneg k), fun i j hij => max_le_max
      (hφq.error_antitone hij) (hψq.error_antitone hij), ?_⟩
    simpa using hφq.error_tendsto.max hψq.error_tendsto
  refine ⟨_, φSeq, ψSeq,
    IsQuasiEquisingularApproximation.mono_error hφq hε fun k => le_max_left _ _,
    IsQuasiEquisingularApproximation.mono_error hψq hε fun k => le_max_right _ _, hφt, hψt,
    fun k => ?_⟩
  have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  exact IdealWeightComparison.moreSingularOn_univ_of_le (hφt k) (hψt k)
    (PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold h hpos)

/-- **Compatible quasi-equisingular approximations, up to bounded functions, in every dimension**
(corrected form of blueprint `trace:qe-compatible-order`).  On a compact Kähler manifold, if
`φ ≼_I ψ` are theta-PSH, they have quasi-equisingular approximations with one common error
sequence and `φ_k ≤ ψ_k + C_k` for every `k`.  In dimension `0` the constant sequences work. -/
theorem exists_quasiEquisingularApproximations_moreSingular [CompactSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ ψ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (h : IOrderOnManifold (n := n) φ ψ) :
    ∃ (ε : ℕ → ℝ) (φSeq ψSeq : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ φ ε φSeq ∧
      IsQuasiEquisingularApproximation omega θ ψ ε ψSeq ∧
      ∀ k, MoreSingularOn (φSeq k) (ψSeq k) univ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨c₁, 𝔞₁, h₁⟩ := DemaillyApproximationAnalyticType.hasAnalyticSingularities_of_dim_zero hφ
    obtain ⟨c₂, 𝔞₂, h₂⟩ := DemaillyApproximationAnalyticType.hasAnalyticSingularities_of_dim_zero hψ
    exact ⟨_, _, _, isQuasiEquisingularApproximation_const omega θ hφ
      h₁.hasManifoldAnalyticSingularityType, isQuasiEquisingularApproximation_const omega θ hψ
      h₂.hasManifoldAnalyticSingularityType, fun _ => moreSingularOn_univ_of_dim_zero hφ hψ⟩
  · obtain ⟨ε, φSeq, ψSeq, hφq, hψq, -, -, hle⟩ :=
      exists_quasiEquisingularApproximations_moreSingular_ofType hn omega θ hφ hψ h
    exact ⟨ε, φSeq, ψSeq, hφq, hψq, hle⟩

end CompatibleOrder

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularComparison
