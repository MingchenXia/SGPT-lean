import SGPT.Foundations.Analysis.FirstPass.SubgeodesicInteriorL1

/-!
# Restriction of subgeodesics to closed subintervals

This file closes the endpoint bookkeeping in Xia, SGPT Proposition 4.1.4.
The strip pullback works uniformly for `0 ≤ a < b ≤ 1`.  At an interior
endpoint we use the proved chart-local `L¹` continuity of the slices; at `0`
or `1` we reuse the endpoint limit already stored by `IsSubgeodesicFrom`.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Extend the slice notation of a subgeodesic to the closed interval by
using its prescribed endpoint potentials at `0` and `1`. -/
def closedSubgeodesicSlice (curve : ℝ → M → EReal)
    (u₀ u₁ : M → EReal) (t : ℝ) : M → EReal :=
  if t = 0 then u₀ else if t = 1 then u₁ else curve t

omit [TopologicalSpace M] in
@[simp] theorem closedSubgeodesicSlice_zero
    (curve : ℝ → M → EReal) (u₀ u₁ : M → EReal) :
    closedSubgeodesicSlice curve u₀ u₁ 0 = u₀ := by
  simp [closedSubgeodesicSlice]

omit [TopologicalSpace M] in
@[simp] theorem closedSubgeodesicSlice_one
    (curve : ℝ → M → EReal) (u₀ u₁ : M → EReal) :
    closedSubgeodesicSlice curve u₀ u₁ 1 = u₁ := by
  simp [closedSubgeodesicSlice]

omit [TopologicalSpace M] in
theorem closedSubgeodesicSlice_eq_curve
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    closedSubgeodesicSlice curve u₀ u₁ t = curve t := by
  simp [closedSubgeodesicSlice, ne_of_gt ht.1, ne_of_lt ht.2]

namespace IsSubgeodesicFrom

variable {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

/-- Restrict a subgeodesic to any nondegenerate closed subinterval of
`[0,1]` and affinely reparametrize it to the normalized strip. -/
theorem closedAffineReparametrized
    (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    IsSubgeodesicFrom theta (affineReparametrizedCurve curve a b)
      (closedSubgeodesicSlice curve u₀ u₁ a)
      (closedSubgeodesicSlice curve u₀ u₁ b) := by
  have ha_lt_one : a < 1 := hab.trans_le hb
  have hb_pos : 0 < b := ha.trans_lt hab
  have hpsh_a : IsThetaPshPotential theta
      (closedSubgeodesicSlice curve u₀ u₁ a) := by
    by_cases ha0 : a = 0
    · subst a
      simpa using h.left_endpoint
    · have haI : a ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ha (Ne.symm ha0), ha_lt_one⟩
      rw [closedSubgeodesicSlice_eq_curve haI]
      exact h.interior.thetaPshPotential haI
  have hpsh_b : IsThetaPshPotential theta
      (closedSubgeodesicSlice curve u₀ u₁ b) := by
    by_cases hb1 : b = 1
    · subst b
      simpa using h.right_endpoint
    · have hbI : b ∈ Ioo (0 : ℝ) 1 :=
        ⟨hb_pos, lt_of_le_of_ne hb hb1⟩
      rw [closedSubgeodesicSlice_eq_curve hbI]
      exact h.interior.thetaPshPotential hbI
  have hleft : ManifoldL1LocallyTendsto (n := n) curve (𝓝[>] a)
      (closedSubgeodesicSlice curve u₀ u₁ a) := by
    by_cases ha0 : a = 0
    · subst a
      simpa using h.tendsto_left
    · have haI : a ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ha (Ne.symm ha0), ha_lt_one⟩
      rw [closedSubgeodesicSlice_eq_curve haI]
      exact (h.manifoldL1LocallyContinuousAt haI).mono_left nhdsWithin_le_nhds
  have hright : ManifoldL1LocallyTendsto (n := n) curve (𝓝[<] b)
      (closedSubgeodesicSlice curve u₀ u₁ b) := by
    by_cases hb1 : b = 1
    · subst b
      simpa using h.tendsto_right
    · have hbI : b ∈ Ioo (0 : ℝ) 1 :=
        ⟨hb_pos, lt_of_le_of_ne hb hb1⟩
      rw [closedSubgeodesicSlice_eq_curve hbI]
      exact (h.manifoldL1LocallyContinuousAt hbI).mono_left nhdsWithin_le_nhds
  refine ⟨hpsh_a, hpsh_b, h.interior.affineReparametrized ha hb hab, ?_, ?_⟩
  · change ManifoldL1LocallyTendsto (n := n)
      (fun t => curve (affineTimeReparam a b t)) (𝓝[>] (0 : ℝ))
        (closedSubgeodesicSlice curve u₀ u₁ a)
    exact hleft.comp (tendsto_affineTimeReparam_nhdsGT_zero hab)
  · change ManifoldL1LocallyTendsto (n := n)
      (fun t => curve (affineTimeReparam a b t)) (𝓝[<] (1 : ℝ))
        (closedSubgeodesicSlice curve u₀ u₁ b)
    exact hright.comp (tendsto_affineTimeReparam_nhdsLT_one hab)

end IsSubgeodesicFrom

end

end SGPT.Foundations.Analysis.FirstPass
