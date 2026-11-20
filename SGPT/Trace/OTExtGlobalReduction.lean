import SGPT.Trace.OTExtAlongOpenness
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling

/-!
# From `thm:OT_ext` to the global extension along a quasi-equisingular approximation

Blueprint `claude-ot2.tex`, nodes `claude-ot2:existence`, `claude-ot2:sections-mono`,
`claude-ot2:reduction`.

The proof of `thm:OT_ext_global` (`chapter_trace.tex` 537--558) uses `thm:OT_ext` only for the
*existence* of an extension, only for potentials with analytic singularities (multiples of the
terms of a quasi-equisingular approximation), and always with a margin in the exponent.  This file
isolates that use:

* `OTExtExistenceAlong`: the existence part of `thm:OT_ext` (no `L²` bound);
  `OTExtAlong.existence`: `thm:OT_ext` implies it; `otExtExistenceAlong_of_dim_zero`;
* `OTExtMarginExistenceAlong`: the existence part with a margin, for potentials `ψ` with analytic
  singularities whose restriction to `W` is quasi-psh: sections of `𝓘(k t ψ|_W)`, `t > 1`, extend to
  sections of `𝓘(k ψ)`.  `OTExtExistenceAlong.margin`, `OTExtAlong.marginExistence`: it is implied
  by the previous ones; `OTExtMarginExistenceStatement`: it, for all data (the open analytic input
  of `thm:OT_ext_global`), and `otExtMarginExistenceStatement_of_otExtStatement`;
* `fullHolomorphicIdealSections_mono`: `H⁰(X, V ⊗ 𝓐) ⊆ H⁰(X, V ⊗ 𝓑)` when `𝓐 ⊆ 𝓑`;
* `exists_extension_of_iOrder` (**the book's argument**): let `(Φ_q)` be a quasi-equisingular
  approximation of `φ` in `PSH(X, θ - 3δω)` with `Φ_q|_W` psh with respect to some form on `W`,
  and `u` an `η`-psh function on the compact submanifold `W` with `u ≼_𝓘 Φ_q|_W` for every `q`.
  If the margin existence part holds for `δ`, then there is `k₀` such that for all `k ≥ k₀` every
  `s ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ 𝓘(k u))` extends to `s̃ ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(k φ))`.

  Proof as in the book: uniform strong openness along `W` gives `c > k` with `s ∈ 𝓘(c u)` (shrunk
  so that `c/k ≤ 1 + δ/D`, `-θ + Dω ≥ 0`); the `𝓘`-order gives `s ∈ 𝓘(c Φ_q|_W)`; for rational
  `d ∈ (k, c)` and `ψ = (d/k) Φ_q` we have `ψ ∈ PSH(X, θ - δω)` once `ε_q ≤ δ`, and
  `s ∈ 𝓘(k t ψ|_W)` with `t = c/d > 1`; the margin existence part gives
  `s̃ ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(kψ)) = H⁰(X, L^k ⊗ T ⊗ 𝓘(d Φ_q))`; and `𝓘(d Φ_q) ⊆ 𝓘(k φ)` for `q`
  large by quasi-equisingularity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.TensorDictionaryDraft
  SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2

/-! ### Monotonicity of `H⁰(X, V ⊗ 𝓐)` in the ideal sheaf -/

section Mono

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]

/-- `H⁰(X, V ⊗ 𝓐) ⊆ H⁰(X, V ⊗ 𝓑)` for ideal sheaves `𝓐 ⊆ 𝓑`. -/
theorem fullHolomorphicIdealSections_mono {A B : GermIdeal n X} (h : A.Le B) :
    fullHolomorphicIdealSections (n := n) V A ≤ fullHolomorphicIdealSections (n := n) V B := by
  intro s hs e x hx
  refine Ideal.span_mono ?_ (hs e x hx)
  rintro g ⟨f, hf, hA, rfl⟩
  exact ⟨f, hf, h _ _ hA, rfl⟩

end Mono

/-! ### Scalings of multiplier ideals -/

section Scaling

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]

/-- `𝓘(1 · (c u)) = 𝓘(c u)` for `c > 0` (the convention of `sourceDegreeMultiplierIdeal` and of
`IsAlongMultiplierSection` against the native exponent). -/
theorem mem_multiplierIdeal_one_coe_mul_iff {c : ℝ} (hc : 0 < c) (u : Z → EReal) (y : Z)
    (g : Z → ℂ) :
    (multiplierIdeal (n := k) 1 (fun w => (c : EReal) * u w)).mem y g ↔
      (multiplierIdeal (n := k) c u).mem y g :=
  and_congr_right fun _ => multiplierIntegrableAt_scaled_one_iff _ hc _ _ _

/-- `k · (t u) = (k t) u` in `EReal` for real `k, t`. -/
theorem coe_mul_coe_mul (a b : ℝ) (x : EReal) :
    (a : EReal) * ((b : EReal) * x) = ((a * b : ℝ) : EReal) * x := by
  rw [← mul_assoc, ← EReal.coe_mul]

/-- A positive multiple of a value different from `⊥` is different from `⊥`. -/
theorem coe_mul_ne_bot {t : ℝ} (ht : 0 < t) {x : EReal} (hx : x ≠ ⊥) : (t : EReal) * x ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => rw [EReal.coe_mul_top_of_pos ht]; exact top_ne_bot
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

end Scaling

/-! ### The existence part of `thm:OT_ext` -/

section Existence

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **The existence part of `thm:OT_ext`** for fixed data (`OTExtAlong` without the `L²` bound):
there is `k₀` such that for all `k ≥ k₀`, all `φ ∈ PSH(X, θ - δω)` with `φ|_W ≢ -∞` and all
`s ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ 𝓘(kφ|_W))` there is `s̃ ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` with
`s̃|_W = s`.  This is all that the proof of `thm:OT_ext_global` uses of `thm:OT_ext`. -/
def OTExtExistenceAlong (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (θ : ClosedRealOneOneForm n X) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (δ : ℝ) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
  ∀ φ : X → EReal, IsThetaPshPotential (θ - δ • ωb.form).val φ → (∃ y ∈ W, φ y ≠ ⊥) →
  ∀ s : (y : W) → (twistedPower L T k).Fiber y,
    IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) (k : ℝ) (fun y : W => φ y) s →
  ∃ s' : twistedSections L T k,
    s' ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k φ) ∧
    ∀ y : W, s' y = s y

/-- `thm:OT_ext` (with its `L²` bound) implies its existence part. -/
theorem OTExtAlong.existence {ωb : KahlerBackground n X}
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {W : Set X}
    {m : ℕ} {hW : IsClosedConnectedSubmanifold n W m} {δ : ℝ}
    (h : OTExtAlong ωb L T θ hW δ) : OTExtExistenceAlong ωb L T θ hW δ := by
  obtain ⟨k₀, C, -, hext⟩ := h
  refine ⟨k₀, fun k hk φ hφ hne s hs => ?_⟩
  obtain ⟨s', hs'mem, hs'eq, -⟩ := hext k hk φ hφ hne s hs
  exact ⟨s', hs'mem, hs'eq⟩

/-- The existence part of `thm:OT_ext` holds when `dim Y = 0` (from `otExtAlong_of_dim_zero`). -/
theorem otExtExistenceAlong_of_dim_zero (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : SGPT.PSH.GlobalL2.IsOwnFirstChernForm L θ) {W : Set X}
    (hW : IsClosedConnectedSubmanifold n W 0) {δ : ℝ} (hδ : 0 < δ) :
    OTExtExistenceAlong ωb L T θ hW δ :=
  OTExtAlong.existence (otExtAlong_of_dim_zero ωb L T hL hT θ hθ hW hδ)

end Existence

/-! ### The existence part with a margin, for analytic singularities -/

section Margin

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **The existence part of `thm:OT_ext` with a margin, for potentials with analytic
singularities** — exactly what the proof of `thm:OT_ext_global` consumes: there is `k₀` such that
for all `k ≥ k₀`, all `ψ ∈ PSH(X, θ - δω)` with analytic singularity type whose restriction to `W`
is quasi-psh and `≢ -∞`, all `t > 1` and all `s ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ 𝓘(k t ψ|_W))` there is
`s̃ ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(kψ))` with `s̃|_W = s`.  It follows from `OTExtExistenceAlong`
(`OTExtExistenceAlong.margin`), and is weaker. -/
def OTExtMarginExistenceAlong (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (θ : ClosedRealOneOneForm n X)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) (δ : ℝ) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
  ∀ ψ : X → EReal, IsThetaPshPotential (θ - δ • ωb.form).val ψ →
    HasManifoldAnalyticSingularityType (n := n) ψ →
    ManifoldQuasiPlurisubharmonic (n := m) (fun y : W => ψ y) → (∃ y ∈ W, ψ y ≠ ⊥) →
  ∀ t : ℝ, 1 < t → ∀ s : (y : W) → (twistedPower L T k).Fiber y,
    IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) ((k : ℝ) * t)
      (fun y : W => ψ y) s →
  ∃ s' : twistedSections L T k,
    s' ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k ψ) ∧
    ∀ y : W, s' y = s y

/-- The existence part of `thm:OT_ext` implies its margin version. -/
theorem OTExtExistenceAlong.margin {ωb : KahlerBackground n X}
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {W : Set X}
    {m : ℕ} {hW : IsClosedConnectedSubmanifold n W m} {δ : ℝ}
    (h : OTExtExistenceAlong ωb L T θ hW δ) : OTExtMarginExistenceAlong ωb L T θ hW δ := by
  let hkm := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel m) W := chartedSpace hkm hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hkm hW.2.2
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨max k₀ 1, fun k hk ψ hψ _ hψq hne t ht s hs => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkt : (k : ℝ) ≤ k * t := le_mul_of_one_le_right hkpos.le ht.le
  refine hk₀ k (le_of_max_le_left hk) ψ hψ hne s ?_
  exact IsAlongMultiplierSection.of_le (twistedPower L T k).Fiber (hkpos.trans_le hkt) hkpos
    (fun y g hg => mem_multiplierIdeal_of_exponent_le hψq hkpos hkt hg) hs

/-- `thm:OT_ext` implies the margin version of its existence part. -/
theorem OTExtAlong.marginExistence {ωb : KahlerBackground n X}
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {W : Set X}
    {m : ℕ} {hW : IsClosedConnectedSubmanifold n W m} {δ : ℝ}
    (h : OTExtAlong ωb L T θ hW δ) : OTExtMarginExistenceAlong ωb L T θ hW δ :=
  (OTExtAlong.existence h).margin

variable (n X) in
/-- **The open analytic input of `thm:OT_ext_global`**: the margin version of the existence part of
`thm:OT_ext` (`OTExtMarginExistenceAlong`) for all data.  It is implied by `thm:OT_ext`
(`OTExtStatement`) and holds when `dim Y = 0`. -/
def OTExtMarginExistenceStatement : Prop :=
  ∀ (ωb : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X),
    IsSourceSmoothHermitianMetric L → IsSourceSmoothHermitianMetric T →
  ∀ θ : ClosedRealOneOneForm n X, SGPT.PSH.GlobalL2.IsOwnFirstChernForm L θ →
  ∀ (W : Set X) (m : ℕ) (hW : IsClosedConnectedSubmanifold n W m) (δ : ℝ), 0 < δ →
    OTExtMarginExistenceAlong ωb L T θ hW δ

/-- `thm:OT_ext ⇒ OTExtMarginExistenceStatement`. -/
theorem otExtMarginExistenceStatement_of_otExtStatement (h : OTExtStatement n X) :
    OTExtMarginExistenceStatement n X :=
  fun ωb L T hL hT θ hθ W m hW δ hδ => OTExtAlong.marginExistence (h ωb L T hL hT θ hθ W m hW δ hδ)

end Margin

/-! ### The reduction -/

section Reduction

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- The form inequality behind `t Φ_q ∈ PSH(X, θ - δω)`: if `-θ + Dω ≥ 0`, `D > 0`,
`1 ≤ t`, `(t - 1) D ≤ δ` and `ε ≤ δ`, then `(θ - δω) - t(θ - 3δω + εω) ≥ 0`. -/
theorem isSemipositive_sub_smul_background (ωb : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {D δ t ε : ℝ}
    (hD : (-θ + D • ωb.form).val.IsSemipositive) (ht : 1 ≤ t) (htD : (t - 1) * D ≤ δ)
    (hε : ε ≤ δ) (hδ : 0 < δ) :
    ((θ - δ • ωb.form) - t • (θ - (3 * δ) • ωb.form + ε • ωb.form)).val.IsSemipositive := by
  have hsplit : (θ - δ • ωb.form) - t • (θ - (3 * δ) • ωb.form + ε • ωb.form) =
      (t - 1) • (-θ + D • ωb.form) +
        (3 * t * δ - δ - t * ε - (t - 1) * D) • ωb.form := by
    module
  rw [hsplit]
  refine UniformPerturbedKahlerLowerBound.isSemipositive_add
    (KahlerDomination.isSemipositive_smul hD (by linarith))
    (KahlerDomination.isSemipositive_smul ωb.isSemipositive ?_)
  nlinarith

/-- **The book's proof of `thm:OT_ext_global`, abstracted** (`chapter_trace.tex` 537--558).
Let `(Φ_q)` be a quasi-equisingular approximation of `φ` in `PSH(X, θ - 3δω)`, `W` a closed
connected submanifold such that every restriction `Φ_q|_W` is `β_q`-psh on `W`, and `u` an
`η`-psh function on `W` with `u ≼_𝓘 Φ_q|_W` for every `q`.  If the margin existence part of
`thm:OT_ext` holds for `δ`, then there is `k₀` such that for every `k ≥ k₀` every
`s ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ 𝓘(k u))` extends to some `s̃ ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(k φ))`. -/
theorem exists_extension_of_iOrder (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (θ : ClosedRealOneOneForm n X)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) {δ : ℝ} (hδ : 0 < δ)
    (hOT : OTExtMarginExistenceAlong ωb L T θ hW δ)
    {φ : X → EReal} {ε : ℕ → ℝ} {Φ : ℕ → X → EReal}
    (hqea : IsQuasiEquisingularApproximation ωb (θ - (3 * δ) • ωb.form) φ ε Φ) :
    let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    (∀ q, ∃ β : ClosedRealOneOneForm m W, IsThetaPshPotential β.val (fun y : W => Φ q y.1)) →
    ∀ {η : SmoothRealForm m W 2} {u : W → EReal}, ThetaPlurisubharmonic η u →
      (∀ q, IOrderOnManifold (n := m) u (fun y : W => Φ q y.1)) →
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ s : (y : W) → (twistedPower L T k).Fiber y,
        IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) (k : ℝ) u s →
        ∃ s' : twistedSections L T k,
          s' ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
            (sourceDegreeMultiplierIdeal (n := n) k φ) ∧
          ∀ y : W, s' y = s y := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  intro hβ η u hu hI
  obtain ⟨k₀, hk₀⟩ := hOT
  obtain ⟨D, hD, hDsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωb (-θ)
  have hι := contMDiff_val hk hW.2.2
  refine ⟨max k₀ 1, fun k hk' s hs => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk'
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  -- uniform strong openness along `W`, then shrink the exponent
  obtain ⟨c', hkc', hs'⟩ := IsAlongMultiplierSection.exists_gt (twistedPower L T k).Fiber hι hu
    hkpos hs
  set c'' : ℝ := min c' (k + k * δ / D) with hc''
  have hkc'' : (k : ℝ) < c'' := lt_min hkc' (by
    have : 0 < k * δ / D := by positivity
    linarith)
  have hc''pos : 0 < c'' := hkpos.trans hkc''
  have hs'' : IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) c'' u s :=
    IsAlongMultiplierSection.of_le (twistedPower L T k).Fiber (hkpos.trans hkc') hc''pos
      (fun y g hg => mem_multiplierIdeal_of_exponent_le hu.quasiPlurisubharmonic hc''pos
        (min_le_left _ _) hg) hs'
  -- a rational exponent `d ∈ (k, c'')`
  obtain ⟨d, hkd, hdc⟩ := exists_rat_btwn hkc''
  have hdpos : (0 : ℝ) < d := hkpos.trans hkd
  -- choose the stage `q`
  have hεev : ∀ᶠ q in atTop, ε q ≤ δ :=
    (hqea.error_tendsto.eventually (Iic_mem_nhds hδ))
  obtain ⟨q, hqε, hqinc⟩ := (hεev.and (hqea.eventually_multiplierIdealIncluded hkpos hkd)).exists
  -- `s ∈ H⁰(W, 𝓘(c'' Φ_q|_W))`
  have hsq : IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) c''
      (fun y : W => Φ q y.1) s :=
    IsAlongMultiplierSection.of_le (twistedPower L T k).Fiber hc''pos hc''pos
      (PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold (hI q) hc''pos) hs''
  -- the potential `ψ = r Φ_q`, `r = d/k` rational, and the margin `t = c''/d`
  set r : ℚ := d / k with hr
  have hrR : ((r : ℚ) : ℝ) = (d : ℝ) / k := by rw [hr]; push_cast; ring
  have hrpos : (0 : ℝ) < (r : ℝ) := by rw [hrR]; exact div_pos hdpos hkpos
  have hkr : (k : ℝ) * (r : ℝ) = d := by rw [hrR]; field_simp
  set t : ℝ := c'' / d with ht
  have ht1 : 1 < t := by rw [ht, one_lt_div hdpos]; exact hdc
  set ψ : X → EReal := fun x => ((r : ℝ) : EReal) * Φ q x with hψ
  have hψk : (fun x => ((k : ℝ) : EReal) * ψ x) = fun x => ((d : ℝ) : EReal) * Φ q x := by
    funext x
    rw [hψ, coe_mul_coe_mul, hkr]
  have hψkt : (fun x => (((k : ℝ) * t : ℝ) : EReal) * ψ x) = fun x => (c'' : EReal) * Φ q x := by
    funext x
    rw [hψ, coe_mul_coe_mul]
    congr 2
    rw [ht, hrR]
    field_simp
  -- `ψ ∈ PSH(X, θ - δω)`
  have hψpsh : IsThetaPshPotential (θ - δ • ωb.form).val ψ := by
    have h1 := PotentialMassComparison.isThetaPshPotential_smul (hqea.term q) hrpos
    have hr1 : 1 ≤ (r : ℝ) := by
      rw [hrR, le_div_iff₀ hkpos, one_mul]
      exact hkd.le
    have hrD : ((r : ℝ) - 1) * D ≤ δ := by
      have hle : (d : ℝ) ≤ k + k * δ / D := hdc.le.trans (min_le_right _ _)
      have : (r : ℝ) - 1 ≤ δ / D := by
        rw [hrR, sub_le_iff_le_add, div_le_iff₀ hkpos]
        calc (d : ℝ) ≤ k + k * δ / D := hle
          _ = (δ / D + 1) * k := by field_simp; ring
      calc ((r : ℝ) - 1) * D ≤ δ / D * D := mul_le_mul_of_nonneg_right this hD.le
        _ = δ := by field_simp
    have hsemi := isSemipositive_sub_smul_background ωb θ hDsemi hr1 hrD hqε hδ
    have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h1 hsemi
    rwa [add_sub_cancel] at h2
  -- analytic singularities and the restriction to `W`
  have hψan : HasManifoldAnalyticSingularityType (n := n) ψ := fun e z hz =>
    QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul
      (hqea.term_hasAnalyticSingularityType q e z hz) (by exact_mod_cast hrpos)
  obtain ⟨β, hβq⟩ := hβ q
  have hψW : IsThetaPshPotential ((r : ℝ) • β).val (fun y : W => ψ y) :=
    PotentialMassComparison.isThetaPshPotential_smul hβq hrpos
  have hψne : ∃ y ∈ W, ψ y ≠ ⊥ := by
    obtain ⟨x₀, hx₀⟩ := hW.2.1.nonempty
    obtain ⟨y, -, hy⟩ := hψW.2 ⟨x₀, hx₀⟩ univ isOpen_univ (mem_univ _)
    exact ⟨y.1, y.2, hy⟩
  have hsψ : IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) ((k : ℝ) * t)
      (fun y : W => ψ y) s := by
    intro y
    have h := hsq y
    have hfun : (fun w : W => (((k : ℝ) * t : ℝ) : EReal) * ψ w) =
        fun w : W => (c'' : EReal) * Φ q w :=
      funext fun w => congrFun hψkt w
    rw [hfun]
    exact h
  obtain ⟨s', hs'mem, hs'eq⟩ := hk₀ k (le_of_max_le_left hk') ψ hψpsh hψan
    hψW.1.quasiPlurisubharmonic hψne t ht1 s hsψ
  refine ⟨s', ?_, hs'eq⟩
  -- `𝓘(kψ) = 𝓘(d Φ_q) ⊆ 𝓘(kφ)`
  have hle : (sourceDegreeMultiplierIdeal (n := n) k ψ).Le
      (sourceDegreeMultiplierIdeal (n := n) k φ) := by
    intro x g hg
    have h1 : (multiplierIdeal (n := n) 1 (fun x => ((d : ℝ) : EReal) * Φ q x)).mem x g := by
      have := hg
      simp only [sourceDegreeMultiplierIdeal] at this
      rwa [hψk] at this
    have h2 := (mem_multiplierIdeal_one_coe_mul_iff hdpos (Φ q) x g).mp h1
    have h3 := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_multiplierIdealIncluded
      hqinc x g h2
    rw [sourceDegreeMultiplierIdeal_pos k (by omega) φ]
    exact h3
  exact fullHolomorphicIdealSections_mono (twistedPower L T k).Fiber hle hs'mem

end Reduction

end SGPT.Trace.OTExt
