import SGPT.Okounkov.TranscendentalSkodaKernel

/-!
# Skoda's theorem: the two `L²` statements of the route

Blueprint `claude-tok-skoda`.

* `TwistedHormanderStatement` (`skoda:twisted-hormander`): Hörmander's `L²` estimate for
  `∂̄` on `ℂ^R`-valued functions with values in the kernel bundle `S = ker G` of a surjective
  holomorphic tuple `G`, with the curvature of `S` (the second fundamental form term
  `secondFundamental`) subtracted from the Levi form of the weight. The shape (bounded convex
  `D`, compact `K`, smaller convex `D'`, cutoff shifts `lam₁ ≤ lam₂` of the weight vanishing on
  `U ⊇ K`) is that of TN's scalar `Hormander.HormanderL2Estimate`.
* `SurjectiveSkodaStatement` (`skoda:surjective-division`): Skoda's `L²` division for tuples
  without common zeros on a bounded convex domain.

Both are statements (`def … : Prop`); `TranscendentalSkodaSurjective.lean` proves
`TwistedHormanderStatement → SurjectiveSkodaStatement` and
`TranscendentalSkodaRegularization.lean` proves `SurjectiveSkodaStatement → SkodaDivisionStatement`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open scoped Topology ComplexConjugate ContDiff ENNReal

/-- **`L²` estimate in the kernel bundle** (`skoda:twisted-hormander`; Demailly, *Analytic
methods*, Theorem 12.3 for `k = 0` and trivial bundles, in Hörmander's cutoff form on bounded
convex domains). For `D` bounded convex, `K ⊆ D` compact and `t > 0` there are `D'`, `U` and
weight shifts `lam₁ ≤ lam₂` (vanishing on `U ⊇ K`) such that: for every tuple `G` holomorphic
without common zeros on `D` and every smooth `Φ` with `(1 + t) B_z(α) ≤ ∑ᵢ L_Φ(z)(αᵢ•)` on the
kernel bundle, every `∂̄`-closed `S`-valued `v ∈ L²(D', e^{-Φ-lam₂})` with the twisted bound
`|⟨α, v(z)⟩|² ≤ g(z) (∑ᵢ L_Φ(z)(αᵢ•) - (1 + t) B_z(α))` has an `S`-valued solution of `∂̄ u = v`
with `∫ |u|² e^{-Φ-lam₁} ≤ (1 + t) ∫ g e^{-Φ-lam₁}`. -/
def TwistedHormanderStatement : Prop :=
  ∀ (n : ℕ) (D : Set (ComplexModel n)), IsOpen D → Convex ℝ D → Bornology.IsBounded D →
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D → ∀ t : ℝ, 0 < t →
  ∃ (D' U : Set (ComplexModel n)) (lam₁ lam₂ : ComplexModel n → ℝ),
    IsOpen D' ∧ Convex ℝ D' ∧ closure D' ⊆ D ∧ IsOpen U ∧ K ⊆ U ∧ U ⊆ D' ∧
    ContinuousOn lam₁ D' ∧ ContinuousOn lam₂ D' ∧
    (∀ x ∈ D', 0 ≤ lam₁ x ∧ lam₁ x ≤ lam₂ x) ∧ (∀ x ∈ U, lam₁ x = 0 ∧ lam₂ x = 0) ∧
    ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (G i) D) →
    (∀ z ∈ D, 0 < generatorNormSq G z) →
    ∀ Φ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ Φ D →
    (∀ z ∈ D, ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      (1 + t) * secondFundamental G z α ≤ vectorLevi Φ z α) →
    ∀ v : Fin R → Fin n → ComplexModel n → ℂ,
      (∀ i j, MemLp (v i j) 2 (weightedVolume D' fun x ↦ Φ x + lam₂ x)) →
      (∀ z ∈ D', InKernel G z fun i j ↦ v i j z) → (∀ i, WeakDbarClosed D' (v i)) →
    ∀ g : ComplexModel n → ℝ, (∀ x ∈ D', 0 ≤ g x) →
      (∀ z ∈ D', ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
        ‖∑ i, ∑ j, conj (α i j) * v i j z‖ ^ 2 ≤
          g z * (vectorLevi Φ z α - (1 + t) * secondFundamental G z α)) →
      Integrable (fun x ↦ g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') →
    ∃ u : Fin R → ComplexModel n → ℂ,
      (∀ i, MemLp (u i) 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x)) ∧
      (∀ᵐ x ∂(volume.restrict D'), ∑ i, G i x * u i x = 0) ∧
      (∀ i, WeakDbarEq D' (u i) (v i)) ∧
      ∫ x in D', (∑ i, ‖u i x‖ ^ 2) * Real.exp (-(Φ x + lam₁ x)) ≤
        (1 + t) * ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x))

/-- **Skoda's `L²` division for surjective tuples** (`skoda:surjective-division`; Demailly,
*Analytic methods*, Theorem 12.8 for `k = 0`, `E = ℂ^R`, `Q = ℂ`). For `D ⊆ ℂⁿ` bounded convex,
`K ⊆ D` compact and `p > n` there is an open `U` with `K ⊆ U ⊆ D` such that for every tuple
`G` holomorphic without common zeros on `D` and every `f` holomorphic on `D` with
`I = ∫_D |f|² |G|^{-2(p+1)} < ∞` there are `H` holomorphic on `U` with `f = ∑ Gᵢ Hᵢ` on `U` and
`∫_U |H|² |G|^{-2p} ≤ (2 + 2n/(p - n)) I`. -/
def SurjectiveSkodaStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ D : Set (ComplexModel n), IsOpen D → Convex ℝ D →
  Bornology.IsBounded D → ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
  ∀ p : ℝ, (n : ℝ) < p →
  ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
    ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (G i) D) →
    (∀ z ∈ D, 0 < generatorNormSq G z) →
    ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f D →
    (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)))) ≠ ⊤ →
    ∃ H : Fin R → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, G i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) * generatorNormSq G z ^ (-p)) ≤
        ENNReal.ofReal (2 + 2 * n / (p - n)) *
          ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)))

end SGPT.Okounkov.TranscendentalSkoda
