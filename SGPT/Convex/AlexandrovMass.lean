import SGPT.Convex.SubgradientMeasure
import SGPT.AlmostSemigroup.Intersection

namespace SGPT.Convex

open Set MeasureTheory

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
  [MeasurableSpace M] [BorelSpace M]
  (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
  {ν : Measure M} [ν.IsAddHaarMeasure]

theorem alexandrovMeasure_univ_eq_body_of_mem_fullMassClass
    {P : Set M} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ FullMassClass B P) :
    alexandrovMeasure B ν f univ =
      ((Module.finrank ℝ E).factorial : ENNReal) * ν P := by
  rw [alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass B hP hne hconv hf,
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_conjugateGradient B f) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

section Coordinates

variable {n : ℕ} (C : E →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ) [C.IsContPerfPair]

/-- Exact source `prop:convex:L541` with the actual coordinate Lebesgue measure.
The already-proved convex-body rigidity is used on the original compact body. -/
theorem mem_fullMassClass_iff_alexandrovMeasure_univ_eq
    {P : Set (Fin n → ℝ)} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ GrowthClass C P) :
    f ∈ FullMassClass C P ↔
      alexandrovMeasure C volume f univ =
        ((Module.finrank ℝ E).factorial : ENNReal) * volume P := by
  have hlsc := lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_mem_growthClass C hP hne hf)
  have hsub := ((singularityLE_support_iff_full_domain_rawSubgradientImage_subset
    C hP hne hconv hf.1).mp hf.2).2
  have hclSub : closure (rawSubgradientImage C f) ⊆ P := closure_minimal hsub hP.isClosed
  constructor
  · exact alexandrovMeasure_univ_eq_body_of_mem_fullMassClass C hP hne hconv
  · intro hmass
    refine ⟨hf, ?_⟩
    by_cases hempty : interior P = ∅
    · exact Or.inl hempty
    · apply Or.inr
      have hmass' : ((Module.finrank ℝ E).factorial : ENNReal) *
          volume (closure (rawSubgradientImage C f)) =
          ((Module.finrank ℝ E).factorial : ENNReal) * volume P := by
        rw [← alexandrovMeasure_univ_eq_closure_rawSubgradientImage C hf.1 hlsc]
        exact hmass
      have hcoef : ((Module.finrank ℝ E).factorial : ENNReal) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (Module.finrank ℝ E)
      have hmeasure := (ENNReal.mul_right_inj hcoef
        (ENNReal.natCast_ne_top (Module.finrank ℝ E).factorial)).mp hmass'
      have hreal : volume.real (P ∩ closure (rawSubgradientImage C f)) = volume.real P := by
        rw [inter_eq_right.mpr hclSub, measureReal_def, measureReal_def, hmeasure]
      have hPsub := SGPT.AlmostSemigroup.Intersection.subset_of_volume_inter_eq
        hP isClosed_closure hconv (Set.nonempty_iff_ne_empty.mpr hempty) hreal
      exact subset_antisymm hclSub hPsub

end Coordinates
end SGPT.Convex
