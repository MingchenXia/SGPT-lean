import SGPT.PSH.LocallyFiniteSubordinate

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M ι : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual nonempty carrier geometry and original local finiteness INTERNALLY
make every duplicate-carrier fiber finite. -/
theorem geometricPrimeCarrier_fiber_finite (K : ι → GeometricPrimeCarrier n M)
    (hLF : LocallyFinite (fun t => (K t).val)) (P : GeometricPrimeCarrier n M) :
    {t | K t = P}.Finite := by
  obtain ⟨x, hx⟩ := P.nonempty
  refine (hLF.point_finite x).subset ?_
  intro t ht
  change K t = P at ht
  change x ∈ (K t).val
  rw [ht]
  exact hx

private def contributionSum (K : ι → GeometricPrimeCarrier n M) (w : ι → ℚ)
    (hLF : LocallyFinite (fun t => (K t).val)) (P : GeometricPrimeCarrier n M) : ℚ :=
  ∑ t ∈ (geometricPrimeCarrier_fiber_finite K hLF P).toFinset, w t

private theorem contributionSum_nonneg (K : ι → GeometricPrimeCarrier n M)
    (w : ι → ℚ) (hw : ∀ t, 0 < w t)
    (hLF : LocallyFinite (fun t => (K t).val)) (P : GeometricPrimeCarrier n M) :
    0 ≤ contributionSum K w hLF P :=
  Finset.sum_nonneg (fun t _ => (hw t).le)

private theorem contributionSum_pos_iff (K : ι → GeometricPrimeCarrier n M)
    (w : ι → ℚ) (hw : ∀ t, 0 < w t)
    (hLF : LocallyFinite (fun t => (K t).val)) (P : GeometricPrimeCarrier n M) :
    0 < contributionSum K w hLF P ↔ ∃ t, K t = P := by
  classical
  rw [contributionSum, Finset.sum_pos_iff_of_nonneg (fun t _ => (hw t).le)]
  simp only [Set.Finite.mem_toFinset, mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, _⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, ht, hw t⟩

/-- Original locally finite actual prime contributions produce the genuine
rational divisor by summing EVERY duplicate-carrier contribution internally. -/
def geometricQDivisorOfLocallyFiniteFamily (K : ι → GeometricPrimeCarrier n M)
    (w : ι → ℚ) (hw : ∀ t, 0 < w t)
    (hLF : LocallyFinite (fun t => (K t).val)) : EffectiveGeometricQDivisor n M where
  coefficient := contributionSum K w hLF
  coefficient_nonneg := contributionSum_nonneg K w hw hLF
  locallyFinite := by
    classical
    intro x
    obtain ⟨N, hN, hfinite⟩ := hLF x
    refine ⟨N, hN, (hfinite.image K).subset ?_⟩
    intro P hP
    obtain ⟨z, hzP, hzN⟩ := hP
    by_cases hzero : contributionSum K w hLF P = 0
    · simp only [hzero, ite_true, mem_empty_iff_false] at hzP
    · have hpos : 0 < contributionSum K w hLF P :=
        lt_of_le_of_ne (contributionSum_nonneg K w hw hLF P) (Ne.symm hzero)
      obtain ⟨t, ht⟩ := (contributionSum_pos_iff K w hw hLF P).mp hpos
      exact ⟨t,
        ⟨z, by simpa only [ht, if_neg hzero] using hzP, hzN⟩, ht⟩

/-- The coefficient is the literal finite sum over ALL original contributions
on this same actual carrier, with no finite-fiber premise. -/
theorem geometricQDivisorOfLocallyFiniteFamily_coefficient
    (K : ι → GeometricPrimeCarrier n M) (w : ι → ℚ) (hw : ∀ t, 0 < w t)
    (hLF : LocallyFinite (fun t => (K t).val)) (P : GeometricPrimeCarrier n M) :
    (geometricQDivisorOfLocallyFiniteFamily K w hw hLF).coefficient P =
      ∑ t ∈ (geometricPrimeCarrier_fiber_finite K hLF P).toFinset, w t := rfl

/-- The produced nonzero carriers are EXACTLY the same original range. -/
theorem geometricQDivisorOfLocallyFiniteFamily_positive
    (K : ι → GeometricPrimeCarrier n M) (w : ι → ℚ) (hw : ∀ t, 0 < w t)
    (hLF : LocallyFinite (fun t => (K t).val)) (P : GeometricPrimeCarrier n M) :
    0 < (geometricQDivisorOfLocallyFiniteFamily K w hw hLF).coefficient P ↔
      ∃ t, K t = P := contributionSum_pos_iff K w hw hLF P

/-- Grouping duplicate actual carriers retains the entire literal support. -/
theorem geometricQDivisorOfLocallyFiniteFamily_support
    (K : ι → GeometricPrimeCarrier n M) (w : ι → ℚ) (hw : ∀ t, 0 < w t)
    (hLF : LocallyFinite (fun t => (K t).val)) :
    (geometricQDivisorOfLocallyFiniteFamily K w hw hLF).support = ⋃ t, (K t).val := by
  ext x
  rw [EffectiveGeometricQDivisor.mem_support]
  constructor
  · rintro ⟨P, hP, hxP⟩
    obtain ⟨t, ht⟩ := (geometricQDivisorOfLocallyFiniteFamily_positive K w hw hLF P).mp hP
    exact mem_iUnion.mpr ⟨t, by simpa only [ht] using hxP⟩
  · intro hx
    obtain ⟨t, hxt⟩ := mem_iUnion.mp hx
    exact ⟨K t, (geometricQDivisorOfLocallyFiniteFamily_positive K w hw hLF (K t)).mpr
      ⟨t, rfl⟩, hxt⟩

end SGPT.PSH
