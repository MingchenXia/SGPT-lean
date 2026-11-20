import SGPT.Foundations.Analysis.Pending.DiagonalSupport

set_option autoImplicit false

/-!
# The diagonal part of a closed positive current is bounded below by its mass on the diagonal

Let `X` be a compact connected complex manifold of dimension `n = q + 1` with a Kähler form `ω`,
`ω̃ = p₁^*ω + p₂^*ω` the product Kähler form on `X × X`, and `Θ` a closed positive current of
bidimension `(n, n)` on `X × X`.  By the support theorem (`DiagonalSupport`,
`bou:diagonal-support`) `𝟙_Δ Θ = λ [Δ]` with `λ ≥ 0` and `Θ - λ [Δ] ≥ 0`.  Comparing masses,

`σ_Θ(Δ) = mass(𝟙_Δ Θ) = λ · mass [Δ] = λ · 2ⁿ ∫_X ωⁿ`,

so a lower bound `δ ≤ σ_Θ(Δ)` gives `λ ≥ δ / (2ⁿ ∫_X ωⁿ)`
(`exists_isPositive_sub_smul_diagonalCurrent_of_le`).  For a weak limit `Θ` of closed positive
currents `Tᵢ` with bounded masses that put mass `≥ δ` on closed sets `F k` shrinking to `Δ`, the
bound `σ_Θ(Δ) ≥ δ` is `DiagonalSupport.le_traceMeasure_iInter_of_tendsto`
(`exists_isPositive_sub_smul_diagonalCurrent_of_tendsto`).

This is the step `λ > 0` of `bou:uniform-diagonal-domination` (Boucksom, *On the volume of a line
bundle*, proof of Lemma 4.10; Demailly--Păun, proof of Theorem 2.12), in the form consumed by
`DiagonalFibreIntegration.isPositive_fibrePushforward_sub` (`δ := c`).  Statements agreed with
TN-CLASSICAL on I-0831.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.DiagonalLowerBound

open FirstPass FirstPass.PositiveClasses PositiveProductCurrents ClosedProductCurrents
  CurrentTraceMeasure CurrentRestriction ProductComplexManifold DiagonalFibreIntegration
  IntegrationCurrent
open scoped ProductComplexManifold

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The diagonal part is bounded below by the mass on the diagonal**: for a closed positive
current `Θ` of bidimension `(n, n)` on `X × X` with `δ ≤ σ_Θ(Δ)` (trace measure for the product
Kähler form), there is `c ≥ max(0, δ / (2ⁿ ∫_X ωⁿ))` with `Θ - c [Δ]` positive. -/
theorem exists_isPositive_sub_smul_diagonalCurrent_of_le [ConnectedSpace X]
    (w : KahlerBackground (q + 1) X)
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)} (hΘ : IsPositive Θ)
    (hΘc : IsClosedCurrent Θ) {δ : ℝ}
    (hδ : δ ≤ (traceMeasure (prodKahlerBackground w w) Θ hΘ).real (Set.diagonal X)) :
    ∃ c : ℝ, 0 ≤ c ∧ δ / (2 ^ (q + 1) * (kahlerVolume w).real univ) ≤ c ∧
      IsPositive (Θ - c • diagonalCurrent w) := by
  obtain ⟨c, hc0, hres, hpos⟩ :=
    DiagonalSupport.exists_restrictCurrent_diagonal_eq_smul w (prodKahlerBackground w w) hΘ hΘc
  refine ⟨c, hc0, ?_, hpos⟩
  -- compare the masses of `𝟙_Δ Θ = c [Δ]`
  have hmass := congrArg (mass (prodKahlerBackground w w)) hres
  rw [mass_restrictCurrent, mass_smul, mass_diagonalCurrent] at hmass
  set V : ℝ := 2 ^ (q + 1) * (kahlerVolume w).real univ with hV
  have hV0 : 0 ≤ V := by positivity
  rcases hV0.eq_or_lt with hV0' | hVpos
  · rw [← hV0', div_zero]
    exact hc0
  · rw [div_le_iff₀ hVpos]
    exact hδ.trans hmass.le

/-- **The diagonal part of a weak limit**: if closed positive currents `Tᵢ → Θ` weakly with
bounded masses and, for every `k`, eventually `σ_{Tᵢ}(F k) ≥ δ` for an antitone family of closed
sets `F k` with `⋂ₖ F k = Δ`, then `Θ ≥ c [Δ]` with `c ≥ max(0, δ / (2ⁿ ∫_X ωⁿ))`. -/
theorem exists_isPositive_sub_smul_diagonalCurrent_of_tendsto [ConnectedSpace X]
    (w : KahlerBackground (q + 1) X)
    {ι : Type*} {l : Filter ι} [l.NeBot] {T : ι → ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)}
    (hT : ∀ i, IsPositive (T i)) (hTc : ∀ i, IsClosedCurrent (T i))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)} (hΘ : IsPositive Θ) {m : ℝ}
    (hm : ∀ᶠ i in l, mass (prodKahlerBackground w w) (T i) ≤ m)
    (hlim : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (Θ φ)))
    {F : ℕ → Set (X × X)} (hF : ∀ k, IsClosed (F k)) (hanti : Antitone F)
    (hFΔ : ⋂ k, F k = Set.diagonal X) {δ : ℝ}
    (hδ : ∀ k, ∀ᶠ i in l, δ ≤ (traceMeasure (prodKahlerBackground w w) (T i) (hT i)).real (F k)) :
    ∃ c : ℝ, 0 ≤ c ∧ δ / (2 ^ (q + 1) * (kahlerVolume w).real univ) ≤ c ∧
      IsPositive (Θ - c • diagonalCurrent w) := by
  have hΘc : IsClosedCurrent Θ := isClosedCurrent_of_tendsto hTc hlim
  have hΔ := DiagonalSupport.le_traceMeasure_iInter_of_tendsto (prodKahlerBackground w w) hT hΘ hm
    hlim hF hanti hδ
  rw [hFΔ] at hΔ
  exact exists_isPositive_sub_smul_diagonalCurrent_of_le w hΘ hΘc hΔ

end SGPT.Foundations.Analysis.Pending.DiagonalLowerBound
