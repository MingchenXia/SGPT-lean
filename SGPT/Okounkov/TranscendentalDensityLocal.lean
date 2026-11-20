import SGPT.Okounkov.TranscendentalSkodaManifoldStatement
import SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import SGPT.Foundations.Analysis.Pending.IdealWeightProducts
import SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers

/-!
# The singularity type of the gentle approximations of a potential with analytic singularities

Source: blueprint node `tok:density`, the central computation of its proof (DRWNXZ Lemma 3.1,
via Skoda's theorem `tok:ext-skoda`).

Let `Φ` be quasi-plurisubharmonic on a complex manifold of dimension `n > 0`, with
`Φ = log ∑ᵢ |gᵢ|² + O(1)` on an open set `U₀ ∋ x` (`gᵢ` holomorphic on `U₀`). Let `m ≥ n`,
`k > 0`, `K = k + m`, and let `v` and `w` have analytic singularities of types
`(1/K, 𝓘(KΦ))` and `(1/m, 𝓘(mΦ))` (for instance two terms of the gentle quasi-equisingular
approximation of `Φ`, `tok:sing-decrease` (a)). Skoda's theorem
`𝓘(KΦ)_x = J_x^k 𝓘(mΦ)_x` (`J = (g₁, …, g_r)`) shows that the products `g^β h_l`
(`|β| = k`, `h_l` local generators of `𝓘(mΦ)`) generate `𝓘(KΦ)` at `x`; hence near `x`

`v = (1/K) log ∑ |g^β h_l|² + O(1) = (k/K) Φ + (m/K) w + O(1)`

(`sameSingularityTypeAt_of_manifoldSkoda`). This is the identity
`φ_K = (k/K) φ + (1/K) ψ + O(1)` of the proof of `tok:density`, with `ψ = m w` (the potential of
`tok:ideal-potential` for the multiplier ideal `𝓘(mΦ)`, here produced by the approximation itself).

Skoda's theorem enters as the hypothesis `ManifoldSkodaStatement` (the manifold form published by
the SKODA package); the results of this file are conditional on it.

## Main results

* `UnitLogPresentedAt`: `Φ = log ∑ |gᵢ|² + O(1)` near `x` with holomorphic `gᵢ`.
* `ereal_combo_identity`: the extended-real identity behind the computation.
* `dominatedAt_fintype_sum`: domination is stable under finite sums over any finite type.
* `sameSingularityTypeAt_of_manifoldSkoda`: the local comparison (conditional on Skoda).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalDensity

open Set Filter
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending.IdealWeightComparison
open SGPT.Foundations.Analysis.Pending.IdealWeightProducts
open SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers
open SGPT.Okounkov.TranscendentalSkoda

section Presentation

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- `Φ = log ∑ᵢ |gᵢ|² + O(1)` near `x`: on an open neighbourhood `U` of `x`, with `gᵢ`
holomorphic on `U` and a bounded real remainder. (Analytic singularities of type `(1, (g))`
near `x`; this is the hypothesis of `ManifoldSkodaStatement`.) -/
def UnitLogPresentedAt (Φ : X → EReal) (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ (r : ℕ) (g : Fin r → X → ℂ),
    (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U) ∧
      ∃ (R : X → ℝ) (C : ℝ), (∀ y ∈ U, |R y| ≤ C) ∧
        ∀ y ∈ U, Φ y = generatorLog g y + (R y : EReal)

end Presentation

/-! ### Extended-real arithmetic -/

/-- The identity `(k/K)(A + R₀) + (m/K)((1/m) B + R') = (1/K)(k A + B) + ((k/K) R₀ + (m/K) R')`
for `A, B ∈ [-∞, ∞)`, `K = k + m`, `k, m > 0`. -/
theorem ereal_combo_identity {A B : EReal} (hA : A ≠ ⊤) (hB : B ≠ ⊤) {k m : ℕ} (hk : 0 < k)
    (hm : 0 < m) (R₀ R' : ℝ) :
    ((((k : ℝ) / ((k + m : ℕ) : ℝ)) : ℝ) : EReal) * (A + (R₀ : EReal)) +
        ((((m : ℝ) / ((k + m : ℕ) : ℝ)) : ℝ) : EReal) *
          ((((m : ℝ)⁻¹ : ℝ) : EReal) * B + (R' : EReal)) =
      (((((k + m : ℕ) : ℝ))⁻¹ : ℝ) : EReal) * (((k : ℝ) : EReal) * A + B) +
        ((((k : ℝ) / ((k + m : ℕ) : ℝ)) * R₀ + ((m : ℝ) / ((k + m : ℕ) : ℝ)) * R' : ℝ) :
          EReal) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hKR : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by push_cast; linarith
  have h1 : (0 : ℝ) < (k : ℝ) / ((k + m : ℕ) : ℝ) := div_pos hkR hKR
  have h2 : (0 : ℝ) < (m : ℝ) / ((k + m : ℕ) : ℝ) := div_pos hmR hKR
  have h3 : (0 : ℝ) < (((k + m : ℕ) : ℝ))⁻¹ := inv_pos.mpr hKR
  have h4 : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  induction A using EReal.rec with
  | bot =>
      rw [EReal.bot_add, EReal.coe_mul_bot_of_pos h1, EReal.bot_add,
        EReal.coe_mul_bot_of_pos hkR, EReal.bot_add, EReal.coe_mul_bot_of_pos h3, EReal.bot_add]
  | top => exact absurd rfl hA
  | coe a =>
      induction B using EReal.rec with
      | bot =>
          rw [EReal.coe_mul_bot_of_pos h4, EReal.bot_add, EReal.coe_mul_bot_of_pos h2,
            EReal.add_bot, EReal.add_bot, EReal.coe_mul_bot_of_pos h3, EReal.bot_add]
      | top => exact absurd rfl hB
      | coe b =>
          simp only [← EReal.coe_add, ← EReal.coe_mul]
          congr 1
          field_simp
          ring

/-! ### Domination along finite sums -/

section Dominated

variable {X : Type*} [TopologicalSpace X]

/-- A germ which is, near `x`, a finite sum (over any finite type) of germs dominated by `g`
is dominated by `g`. -/
theorem dominatedAt_fintype_sum {P : ℕ} {g : Fin P → X → ℂ} {x : X} {ι : Type*} [Fintype ι]
    {s : ι → X → ℂ} {v : X → ℂ} (hs : ∀ i, DominatedAt g x (s i))
    (heq : v =ᶠ[𝓝 x] fun y => ∑ i, s i y) : DominatedAt g x v := by
  classical
  let e := Fintype.equivFin ι
  refine DominatedAt.sum (a := fun _ _ => (1 : ℂ)) (s := fun t => s (e.symm t))
    (fun _ => continuousAt_const) (fun t => hs (e.symm t)) ?_
  filter_upwards [heq] with y hy
  rw [hy]
  simp only [one_mul]
  exact (Fintype.sum_equiv e (fun i => s i y) (fun t => s (e.symm t) y)
    (fun i => by simp)).trans rfl

end Dominated

/-! ### The local comparison -/

section Local

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- The zero germ lies in every multiplier ideal of positive level. -/
theorem multiplierIdeal_mem_zero {c : ℝ} (hc : 0 < c) (Φ : X → EReal) (x : X) :
    (multiplierIdeal (n := n) c Φ).mem x (fun _ => 0) :=
  ⟨holomorphicAt_const 0, multiplierIntegrableAt_zero _ hc _ _⟩

/-- **The singularity type of a gentle approximant** (the central step of `tok:density`,
conditional on Skoda's theorem `ManifoldSkodaStatement`). Let `Φ` be quasi-psh with
`Φ = log ∑ |gᵢ|² + R₀` on an open `U₀ ∋ x`, `m ≥ n > 0`, `k > 0`, `K = k + m`, and let `v`, `w`
have analytic singularities of types `(1/K, 𝓘(KΦ))` and `(1/m, 𝓘(mΦ))`. Then near `x`,
`v = (k/K) Φ + (m/K) w + O(1)`. -/
theorem sameSingularityTypeAt_of_manifoldSkoda (hS : ManifoldSkodaStatement.{u}) (hn : 0 < n)
    {Φ : X → EReal} (hΦ : ManifoldQuasiPlurisubharmonic (n := n) Φ) {x : X} {U₀ : Set X}
    (hU₀ : IsOpen U₀) (hx₀ : x ∈ U₀) {r : ℕ} {g : Fin r → X → ℂ}
    (hg : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U₀)
    {R₀ : X → ℝ} {C₀ : ℝ} (hR₀ : ∀ y ∈ U₀, |R₀ y| ≤ C₀)
    (hΦeq : ∀ y ∈ U₀, Φ y = generatorLog g y + (R₀ y : EReal))
    {k m : ℕ} (hk : 0 < k) (hm : n ≤ m) {v w : X → EReal}
    (hv : HasAnalyticSingularitiesOfType (n := n) v (((k + m : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((k + m : ℕ) : ℝ) Φ))
    (hw : HasAnalyticSingularitiesOfType (n := n) w (((m : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) (m : ℝ) Φ)) :
    SameSingularityTypeAt v (fun y => ((((k : ℝ) / ((k + m : ℕ) : ℝ)) : ℝ) : EReal) * Φ y +
      ((((m : ℝ) / ((k + m : ℕ) : ℝ)) : ℝ) : EReal) * w y) x := by
  classical
  have hmpos : 0 < m := lt_of_lt_of_le hn hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  obtain ⟨-, -, hvloc⟩ := hv
  obtain ⟨U, hU, hxU, P, H, hHd, hHiff, R, C, hRC, hveq⟩ := hvloc x
  obtain ⟨-, -, hwloc⟩ := hw
  obtain ⟨U', hU', hxU', P', H', hH'd, hH'iff, R', C', hR'C', hweq⟩ := hwloc x
  have hsk : ∀ f : X → ℂ, ((multiplierIdeal (n := n) ((k + m : ℕ) : ℝ) Φ).mem x f ↔
      ManifoldMemPowMulMultiplier (n := n) g k (m : ℝ) Φ x f) :=
    fun f => hS n X hn Φ hΦ r g U₀ hU₀ hg R₀ C₀ hR₀ hΦeq x hx₀ m k hm f
  set T := tensorPowerFamily g k with hT
  set Q := mulFamily T H' with hQ
  -- every generator of `𝓘(KΦ)` at `x` is dominated by the products `g^β h_l`
  have hdom1 : ∀ l, DominatedAt Q x (H l) := by
    intro l
    obtain ⟨h, hh, heq⟩ := (hsk (H l)).mp (mem_of_isPresentation hU hxU hHd hHiff l)
    refine dominatedAt_fintype_sum (s := fun β z => (∏ i, g (β i) z) * h β z) (fun β => ?_) heq
    have h1 : DominatedAt T x (fun z => ∏ i, g (β i) z) := by
      refine dominatedAt_of_eq ⟨Fintype.equivFin (Fin k → Fin r) β, ?_⟩
      funext z
      simp [hT, tensorPowerFamily]
    have h2 : DominatedAt H' x (h β) := dominatedAt_of_isInSpanAt ((hH'iff x hxU' (h β)).mp (hh β))
    exact dominatedAt_mul h1 h2
  -- every product `g^β h_l` lies in `𝓘(KΦ)` at `x`, hence is dominated by its generators
  have hdom2 : ∀ t, DominatedAt H x (Q t) := by
    intro t
    set β := (Fintype.equivFin (Fin k → Fin r)).symm (finProdFinEquiv.symm t).1 with hβ
    set j := (finProdFinEquiv.symm t).2 with hj
    have hH'j := mem_of_isPresentation hU' hxU' hH'd hH'iff j
    have hmemK : (multiplierIdeal (n := n) ((k + m : ℕ) : ℝ) Φ).mem x
        (fun z => (∏ i, g (β i) z) * H' j z) := by
      refine (hsk _).mpr ⟨fun β' => if β' = β then H' j else fun _ => 0, fun β' => ?_, ?_⟩
      · by_cases hβ' : β' = β
        · simpa [hβ'] using hH'j
        · simpa [hβ'] using multiplierIdeal_mem_zero hmR Φ x
      · refine Eventually.of_forall fun z => ?_
        dsimp only
        rw [Finset.sum_eq_single β]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hb
          exact absurd (Finset.mem_univ β) hb
    have hQt : Q t = fun z => (∏ i, g (β i) z) * H' j z := by
      funext z
      simp [hQ, mulFamily, hT, tensorPowerFamily, hβ, hj]
    rw [hQt]
    exact dominatedAt_of_isInSpanAt ((hHiff x hxU _).mp hmemK)
  have hlog1 : MoreSingularAt (generatorLog H) (generatorLog Q) x :=
    moreSingularAt_generatorLog_of_forall_dominatedAt hdom1
  have hlog2 : MoreSingularAt (generatorLog Q) (generatorLog H) x :=
    moreSingularAt_generatorLog_of_forall_dominatedAt hdom2
  -- the two presentations
  have hKR : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by positivity
  have hcK : (0 : ℝ) < (((k + m : ℕ) : ℝ))⁻¹ := inv_pos.mpr hKR
  have hcastK : (((((k + m : ℕ) : ℚ)⁻¹ : ℚ) : ℝ)) = (((k + m : ℕ) : ℝ))⁻¹ := by push_cast; ring
  have hcastm : (((((m : ℕ) : ℚ)⁻¹ : ℚ) : ℝ)) = ((m : ℝ))⁻¹ := by push_cast; ring
  have hveq' : ∀ᶠ y in 𝓝 x, v y =
      (((((k + m : ℕ) : ℝ))⁻¹ : ℝ) : EReal) * generatorLog H y + (R y : EReal) :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => by rw [hveq y hy, hcastK]
  have hcombo : ∀ᶠ y in 𝓝 x,
      ((((k : ℝ) / ((k + m : ℕ) : ℝ)) : ℝ) : EReal) * Φ y +
          ((((m : ℝ) / ((k + m : ℕ) : ℝ)) : ℝ) : EReal) * w y =
        (((((k + m : ℕ) : ℝ))⁻¹ : ℝ) : EReal) * generatorLog Q y +
          ((((k : ℝ) / ((k + m : ℕ) : ℝ)) * R₀ y + ((m : ℝ) / ((k + m : ℕ) : ℝ)) * R' y : ℝ) :
            EReal) := by
    filter_upwards [hU₀.mem_nhds hx₀, hU'.mem_nhds hxU'] with y hy₀ hy'
    rw [hΦeq y hy₀, hweq y hy', hcastm, hQ, generatorLog_mulFamily, hT,
      generatorLog_tensorPowerFamily]
    exact ereal_combo_identity (generatorLog_ne_top _ _) (generatorLog_ne_top _ _) hk hmpos _ _
  have hk1 : (0 : ℝ) ≤ (k : ℝ) / ((k + m : ℕ) : ℝ) := by positivity
  have hm1 : (0 : ℝ) ≤ (m : ℝ) / ((k + m : ℕ) : ℝ) := by positivity
  have hRup : ∀ᶠ y in 𝓝 x, ((k : ℝ) / ((k + m : ℕ) : ℝ)) * R₀ y +
      ((m : ℝ) / ((k + m : ℕ) : ℝ)) * R' y ≤
      ((k : ℝ) / ((k + m : ℕ) : ℝ)) * C₀ + ((m : ℝ) / ((k + m : ℕ) : ℝ)) * C' := by
    filter_upwards [hU₀.mem_nhds hx₀, hU'.mem_nhds hxU'] with y hy₀ hy'
    have h1 := (abs_le.mp (hR₀ y hy₀)).2
    have h2 := (abs_le.mp (hR'C' y hy')).2
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hk1) (mul_le_mul_of_nonneg_left h2 hm1)
  have hRlo : ∀ᶠ y in 𝓝 x, -(((k : ℝ) / ((k + m : ℕ) : ℝ)) * C₀ +
      ((m : ℝ) / ((k + m : ℕ) : ℝ)) * C') ≤ ((k : ℝ) / ((k + m : ℕ) : ℝ)) * R₀ y +
      ((m : ℝ) / ((k + m : ℕ) : ℝ)) * R' y := by
    filter_upwards [hU₀.mem_nhds hx₀, hU'.mem_nhds hxU'] with y hy₀ hy'
    have h1 := (abs_le.mp (hR₀ y hy₀)).1
    have h2 := (abs_le.mp (hR'C' y hy')).1
    nlinarith [mul_le_mul_of_nonneg_left h1 hk1, mul_le_mul_of_nonneg_left h2 hm1]
  have hRvup : ∀ᶠ y in 𝓝 x, R y ≤ C :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => (abs_le.mp (hRC y hy)).2
  have hRvlo : ∀ᶠ y in 𝓝 x, -C ≤ R y :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => (abs_le.mp (hRC y hy)).1
  exact ⟨moreSingularAt_of_moreSingularAt_generatorLog hcK hveq' hcombo hRvup hRlo hlog1,
    moreSingularAt_of_moreSingularAt_generatorLog hcK hcombo hveq' hRup hRvlo hlog2⟩

end Local

end SGPT.Okounkov.TranscendentalDensity
