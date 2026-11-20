import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFullQea

set_option autoImplicit false

/-! # Actual order and infimum of fixed-geometry Demailly diagonals -/

open Set Filter Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryDiagonalOrder
open FirstPass DemaillyApproximationSequence QuantitativeRegularizationFixedCover
  DemaillyCommonGeometryMonotonicity

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- Both the actual raw input and the actual dyadic index may vary:
with common doubling geometry the genuine diagonal is antitone. -/
theorem antitone_diagonal_seq
    (F : FixedChartCover d Z) (ρ : F.t → ComplexModel d → ℝ) {D : ℝ}
    {u : ℕ → Z → EReal} (hanti : ∀ x, Antitone fun j => u j x)
    (hdouble : ∀ i, ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
      F.branch ρ (u i) (2 * m) j y ≤
        F.branch ρ (u i) m j y + ((D / (m : ℝ) : ℝ) : EReal))
    {k : ℕ → ℕ} (hk : Monotone k) (x : Z) :
    Antitone fun j => DemaillyApproximationSequence.seq F ρ (u j) (2 * (D + 1 / 4)) (k j) x := by
  intro a b hab
  exact (antitone_seq F (hdouble b) x (hk hab)).trans
    (seq_mono F ρ (fun y => hanti y hab) _ (k a) x)

/-- The diagonal infimum is literally the infimum of the inputs, with
all poles retained; this uses actual fixed-row convergence, not native
zero distance or an assumed diagonal limit. -/
theorem iInf_diagonal_seq
    (F : FixedChartCover d Z) {α : SmoothRealForm d Z 2}
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential α (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j)) {D : ℝ}
    {u : ℕ → Z → EReal} (hu : ∀ i, ThetaPlurisubharmonic α (u i))
    (hanti : ∀ x, Antitone fun j => u j x)
    (hdouble : ∀ i, ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
      F.branch ρ (u i) (2 * m) j y ≤
        F.branch ρ (u i) m j y + ((D / (m : ℝ) : ℝ) : EReal))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (x : Z) :
    (⨅ j, DemaillyApproximationSequence.seq F ρ (u j) (2 * (D + 1 / 4)) (k j) x) =
      ⨅ j, u j x := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    have hlim := (tendsto_seq F (hu i) hρ (2 * (D + 1 / 4)) x).comp hk
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop i] with j hij
    exact (iInf_le (fun j => DemaillyApproximationSequence.seq F ρ (u j)
      (2 * (D + 1 / 4)) (k j) x) j).trans
      (seq_mono F ρ (fun y => hanti y hij) _ (k j) x)
  · refine le_iInf fun j => ?_
    have hrow : u j x ≤ DemaillyApproximationSequence.seq F ρ (u j)
        (2 * (D + 1 / 4)) (k j) x := by
      rw [← iInf_seq F (hu j) hρ (hdouble j) x]
      exact iInf_le _ (k j)
    exact (iInf_le (fun j => u j x) j).trans hrow

end
end SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryDiagonalOrder
