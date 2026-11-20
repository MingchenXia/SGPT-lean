import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound
import SGPT.Foundations.Analysis.FirstPass.OrderedL1Squeeze

set_option autoImplicit false

/-!
# Ordered endpoint recovery for Perron finite geodesics

For ordered theta-PSH endpoints, a finite Perron geodesic is squeezed between
the affine downward translate `u₀ - t` and the chord from `u₀` to `u₁`.
The canonical extended-real chart distance then gives genuine local `L1`
recovery of the left endpoint.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- If two theta-PSH endpoints are ordered, their Perron finite geodesic
recovers the left endpoint in chart-local `L1` as time tends to zero from the
interior. -/
theorem finiteGeodesic_tendsto_left_of_le
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hu₀u₁ : u₀ ≤ u₁) :
    ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic θ u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ := by
  have hIoo : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  have hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, finiteGeodesic θ u₀ u₁ t x ≤
        eRealChord (u₀ x) (u₁ x) t := by
    filter_upwards [hIoo] with t ht
    exact finiteGeodesic_le_eRealChord hu₀ hu₁ ht
  have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, u₀ x + ((-((1 : ℝ) * t) : ℝ) : EReal) ≤
        finiteGeodesic θ u₀ u₁ t x := by
    filter_upwards with t
    intro x
    simpa only [one_mul, neg_mul] using
      affineLower_le_finiteGeodesic_of_le hu₀ hu₀u₁
        (C := (1 : ℝ)) zero_le_one t x
  have htop : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x, finiteGeodesic θ u₀ u₁ t x ≠ ⊤ := by
    filter_upwards [hIoo] with t ht
    intro x hw
    have hle := finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
    rw [hw] at hle
    exact (eRealChord_ne_top
      (hu₀.quasiPshPotential.1.ne_top x)
      (hu₁.quasiPshPotential.1.ne_top x)
      ht.1.le ht.2.le) (top_unique hle)
  exact hu₀.manifoldL1LocallyTendsto_of_eventually_ordered_chord_squeeze
    (1 : ℝ) hu₁ htop hlower hupper

end

end SGPT.Foundations.Analysis.FirstPass

#print axioms SGPT.Foundations.Analysis.FirstPass.finiteGeodesic_tendsto_left_of_le
