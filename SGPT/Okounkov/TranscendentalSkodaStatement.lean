import SGPT.Foundations.Analysis.FirstPass.MultiplierIdeals
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Skoda's theorem for analytic singularities: the statement

Blueprint node `tok:ext-skoda` (chapter `claude-okounkov-transcendental`, refined in
`claude-tok-skoda`): Skoda's division theorem in the form used by DRWNXZ, Lemma 3.1 and
Lemma 5.3 (cited there from Demailly, *On the cohomology of pseudoeffective line bundles*,
Theorem 11.17; Demailly, *Analytic methods in algebraic geometry*, Theorem 12.17).

Let `g₁, …, g_r` be holomorphic near a point `x ∈ ℂⁿ`, `J ⊆ 𝒪_x` the ideal they generate and
`φ = log ∑ᵢ |gᵢ|²`. For every integer `m ≥ n` and every `k ≥ 0`,
`𝓘((k + m)φ)_x = J^k · 𝓘(mφ)_x`.

This file contains **statements only** (`def … : Prop`); it is the interface consumed by the
DENSITY package (`tok:density`, `tok:partial-analytic`). The proof is the SKODA package
(`TranscendentalSkoda*.lean`).

## Conventions

* `ComplexModel n = EuclideanSpace ℂ (Fin n)` with Lebesgue (Haar) measure `volume`.
* `𝓘(cφ)_x` is TN's local multiplier predicate `MultiplierIntegrableAt (generatorLog g) c f x`:
  `f` is holomorphic on a neighbourhood `U` of `x` and `∫_U |f|² e^{-cφ} < ∞` (the weight is
  `e^{-cφ}`, with no factor `2`, so `𝓘(cφ)` consists of the `f` with `|f|²/|g|^{2c}` locally
  integrable); `generatorLog g = log ∑ᵢ |gᵢ|²` as an `EReal`-valued function.
* `J^k · 𝓘(cφ)_x` is `MemPowMulMultiplierAt g k c x`: the germ of `f` at `x` is
  `∑_β g^β h_β`, the sum over all `β : Fin k → Fin r` of `(∏ᵢ g_{β i}) h_β`, with every
  `h_β ∈ 𝓘(cφ)_x`. Since the monomials `g^β` generate `J^k` and `𝓘(cφ)_x` is an ideal, this is
  membership in the product ideal.

## Adaptation

DRWNXZ use `m = min(n - 1, r - 1)` (Demailly's sharp exponent, which needs the reduction of
`J` to `n` generators with the same integral closure, Demailly AM Lemma 12.16). The consumers
only need one fixed `m` independent of `k`; the statement here is for every `m ≥ n`, which the
route of `claude-tok-skoda` proves from Skoda's `L²` estimate for the everywhere surjective
regularized tuple `(g₁, …, g_r, √δ)` (no reduction lemma, no complete Kähler metric on the
complement of `g⁻¹(0)`). The positivity `0 < n` excludes the degenerate dimension `0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- `f ∈ J^k · 𝓘(cφ)_x` for `J = (g₁, …, g_r)` and `φ = log ∑ᵢ |gᵢ|²`: near `x`,
`f = ∑_{β : Fin k → Fin r} (∏ᵢ g_{β i}) h_β` with every `h_β ∈ 𝓘(cφ)_x`. -/
def MemPowMulMultiplierAt {n r : ℕ} (g : Fin r → ComplexModel n → ℂ) (k : ℕ) (c : ℝ)
    (x : ComplexModel n) (f : ComplexModel n → ℂ) : Prop :=
  ∃ h : (Fin k → Fin r) → ComplexModel n → ℂ,
    (∀ β, MultiplierIntegrableAt (generatorLog g) c (h β) x volume) ∧
      f =ᶠ[𝓝 x] fun z => ∑ β, (∏ i, g (β i) z) * h β z

/-- **Skoda's theorem for analytic singularities** (`tok:ext-skoda`): for holomorphic
`g₁, …, g_r` near `x ∈ ℂⁿ` (`n > 0`), `φ = log ∑ᵢ |gᵢ|²`, `J = (g₁, …, g_r)` and integers
`m ≥ n`, `k ≥ 0`: `𝓘((k + m)φ)_x = J^k · 𝓘(mφ)_x`. -/
def SkodaStatement : Prop :=
  ∀ (n r : ℕ), 0 < n → ∀ (g : Fin r → ComplexModel n → ℂ) (x : ComplexModel n),
    HolomorphicGeneratorsAt g x → ∀ (m k : ℕ), n ≤ m → ∀ f : ComplexModel n → ℂ,
      (MultiplierIntegrableAt (generatorLog g) ((k + m : ℕ) : ℝ) f x volume ↔
        MemPowMulMultiplierAt g k (m : ℝ) x f)

/-- **One division step** (`skoda:division-step`): for integers `ℓ ≥ n`,
`𝓘((ℓ + 1)φ)_x ⊆ J · 𝓘(ℓφ)_x`. `SkodaStatement` follows by induction on `k`. -/
def SkodaDivisionStatement : Prop :=
  ∀ (n r : ℕ), 0 < n → ∀ (g : Fin r → ComplexModel n → ℂ) (x : ComplexModel n),
    HolomorphicGeneratorsAt g x → ∀ ℓ : ℕ, n ≤ ℓ → ∀ f : ComplexModel n → ℂ,
      MultiplierIntegrableAt (generatorLog g) ((ℓ + 1 : ℕ) : ℝ) f x volume →
        ∃ h : Fin r → ComplexModel n → ℂ,
          (∀ i, MultiplierIntegrableAt (generatorLog g) (ℓ : ℝ) (h i) x volume) ∧
            f =ᶠ[𝓝 x] fun z => ∑ i, g i z * h i z

end SGPT.Okounkov.TranscendentalSkoda
