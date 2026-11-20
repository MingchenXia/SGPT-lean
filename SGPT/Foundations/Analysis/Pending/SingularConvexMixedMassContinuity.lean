import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination

set_option autoImplicit false

/-! # Actual convex endpoint mixed mass continuity on the closed coefficient interval -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularConvexMixedMassContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy ThetaPshConvexCombination
  EndpointMixedMassConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual finite selector formula internally produces continuity for
every endpoint mixed mass, including zero original masses and both coefficient endpoints. -/
theorem continuous_toReal_endpointMixedMass_convexComb (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (j : Fin (n + 1)) :
    Continuous (fun a : Icc (0 : ℝ) 1 =>
      (endpointMixedMass θ p (convexComb a.val u p) hp
        (isThetaPshPotential_convexComb_closed hu hp a.property.1 a.property.2) j).toReal) := by
  classical
  have heq (a : Icc (0 : ℝ) 1) :=
    endpointMixedMass_convexComb_eq_sum omega hu hp a.property.1 a.property.2 j
  simp_rw [heq]
  apply continuous_finsetSum
  intro σ _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro i _
  by_cases hi : i.val < j.val
  · simp only [if_pos hi]
    cases σ i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact continuous_sub.comp (continuous_const.prodMk continuous_subtype_val)
    · simpa only [↓reduceIte] using
        (continuous_subtype_val : Continuous (fun a : Icc (0 : ℝ) 1 => a.val))
  · simp only [if_neg hi]
    exact continuous_const

/-- Coefficient-one continuity identifies the limit with the actual original
endpoint mixed mass, using the defining extended-real zero coefficient at poles. -/
theorem tendsto_toReal_endpointMixedMass_convexComb_one (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (j : Fin (n + 1)) :
    Tendsto (fun a : Icc (0 : ℝ) 1 =>
      (endpointMixedMass θ p (convexComb a.val u p) hp
        (isThetaPshPotential_convexComb_closed hu hp a.property.1 a.property.2) j).toReal)
      (𝓝 (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))
      (𝓝 (endpointMixedMass θ p u hp hu j).toReal) := by
  have heq : convexComb 1 u p = u := by
    funext x
    simp only [convexComb, EReal.coe_one, one_mul, sub_self, EReal.coe_zero,
      zero_mul, add_zero]
  simpa only [heq] using
    (continuous_toReal_endpointMixedMass_convexComb omega hu hp j).tendsto
      (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)

end

end SGPT.Foundations.Analysis.Pending.SingularConvexMixedMassContinuity
