import SGPT.Foundations.Analysis.Pending.FiniteRightEndpointSecant
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

/-!
# The actual left derivative at the assigned terminal endpoint

Xia SGPT PDF0158, Proposition 4.2.2. The derivative is produced from
the bounded monotone actual secants, not supplied as an input.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.FiniteRightEndpointDerivative

open FirstPass FiniteUpperGapGeodesicSupremum FiniteRightEndpointSecant

noncomputable section

/-- The real supremum of the actual terminal secants. -/
def terminalSlope {X : Type*} (curve : ℝ → X → EReal) (u₁ : X → EReal) (x : X) : ℝ :=
  sSup ((fun t => (rightEndpointSecant curve u₁ t x).toReal) '' Ioo (0 : ℝ) 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

private theorem rightSecantReal_le_gap [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x).toReal ≤
      (differenceSup u₁ u₀).toReal := by
  have hfinite := differenceSup_ne_top_ne_bot hu₀ hu₁ hmore
  have hb := (rightEndpointSecant_bounds hu₀ hu₁ hmore hx ht).2
  rw [rightEndpointSecant_coe hu₀ hu₁ hmore hx ht,
    ← EReal.coe_toReal hfinite.1 hfinite.2] at hb
  rw [rightEndpointSecant_coe hu₀ hu₁ hmore hx ht, EReal.toReal_coe]
  exact EReal.coe_le_coe_iff.mp hb

private theorem rightSecantReal_bddAbove [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥) :
    BddAbove ((fun t =>
      (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x).toReal) '' Ioo (0 : ℝ) 1) := by
  refine ⟨(differenceSup u₁ u₀).toReal, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  exact rightSecantReal_le_gap hu₀ hu₁ hmore hx ht

/-- Each actual secant is at most its real supremum, which is at most the true finite gap. -/
theorem terminalSlope_bounds [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x).toReal ≤
      terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x ∧
      terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x ≤ (differenceSup u₁ u₀).toReal := by
  have hbdd := rightSecantReal_bddAbove hu₀ hu₁ hmore hx
  constructor
  · exact le_csSup hbdd (mem_image_of_mem _ ht)
  · apply csSup_le ((show (Ioo (0 : ℝ) 1).Nonempty from
      ⟨1 / 2, by constructor <;> norm_num⟩).image _)
    rintro z ⟨t, ht, rfl⟩
    exact rightSecantReal_le_gap hu₀ hu₁ hmore hx ht

/-- The actual finite real secants converge from the left to their actual supremum. -/
theorem tendsto_rightEndpointSecant_terminalSlope [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥) :
    Tendsto (fun t => (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x).toReal)
      (𝓝[<] (1 : ℝ)) (𝓝 (terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x)) := by
  exact MonotoneOn.tendsto_nhdsWithin_Ioo_left
    (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1 / 2, by constructor <;> norm_num⟩)
    (monotoneOn_toReal_rightEndpointSecant hu₀ hu₁ hmore hx)
    (rightSecantReal_bddAbove hu₀ hu₁ hmore hx)

/-- The assigned closed trace has a genuine one-sided derivative at its right endpoint. -/
theorem hasDerivWithinAt_closedFiniteGeodesic_one [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥) :
    HasDerivWithinAt
      (fun t => (closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x).toReal)
      (terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x) (Iio (1 : ℝ)) 1 := by
  let F : ℝ → ℝ := fun t =>
    (closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x).toReal
  have heq : (fun t => (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x).toReal)
      =ᶠ[𝓝[<] (1 : ℝ)] slope F 1 := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    rw [rightEndpointSecant_coe hu₀ hu₁ hmore hx ht, EReal.toReal_coe]
    have hF₁ : F 1 = (u₁ x).toReal := by simp [F]
    have hFt : F t = (finiteGeodesic θ u₀ u₁ t x).toReal := by
      change (closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x).toReal = _
      rw [closedSubgeodesicSlice_eq_curve ht]
    rw [slope_def_field, hF₁, hFt]
    apply (div_eq_div_iff (sub_ne_zero.mpr ht.2.ne') (sub_ne_zero.mpr ht.2.ne)).2
    ring
  exact (hasDerivWithinAt_iff_tendsto_slope' (by simp : (1 : ℝ) ∉ Iio (1 : ℝ))).2
    ((tendsto_congr' heq).mp (tendsto_rightEndpointSecant_terminalSlope hu₀ hu₁ hmore hx))

/-- The actual derivative within the left half-line equals the actual terminal slope. -/
theorem derivWithin_closedFiniteGeodesic_one [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥) :
    derivWithin
      (fun t => (closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x).toReal)
      (Iio (1 : ℝ)) 1 = terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x := by
  exact (hasDerivWithinAt_closedFiniteGeodesic_one hu₀ hu₁ hmore hx).derivWithin
    (uniqueDiffWithinAt_Iio (1 : ℝ))

/-- The true spatial supremum of actual terminal derivatives is the original finite gap. -/
theorem iSup_terminalSlope [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) :
    (⨆ x : {x // u₁ x ≠ ⊥},
      (terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x.val : EReal)) = differenceSup u₁ u₀ := by
  have ht : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hfinite := differenceSup_ne_top_ne_bot hu₀ hu₁ hmore
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [← EReal.coe_toReal hfinite.1 hfinite.2]
    exact EReal.coe_le_coe_iff.mpr (terminalSlope_bounds hu₀ hu₁ hmore x.property ht).2
  · rw [← iSup_rightEndpointSecant hu₀ hu₁ hmore ht]
    apply iSup_le
    intro x
    have hb := (terminalSlope_bounds hu₀ hu₁ hmore x.property ht).1
    rw [rightEndpointSecant_coe hu₀ hu₁ hmore x.property ht, EReal.toReal_coe] at hb
    have hcoe : rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ (1 / 2) x.val ≤
        (terminalSlope (finiteGeodesic θ u₀ u₁) u₁ x.val : EReal) := by
      rw [rightEndpointSecant_coe hu₀ hu₁ hmore x.property ht]
      exact EReal.coe_le_coe_iff.mpr hb
    exact hcoe.trans
      (le_iSup (fun y : {y // u₁ y ≠ ⊥} =>
        (terminalSlope (finiteGeodesic θ u₀ u₁) u₁ y.val : EReal)) x)

end

end SGPT.Foundations.Analysis.Pending.FiniteRightEndpointDerivative
