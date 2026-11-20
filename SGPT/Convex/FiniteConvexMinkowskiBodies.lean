import SGPT.Convex.GeometricMinkowskiPolarization
import SGPT.Convex.GrowthSum
import SGPT.Convex.MixedAlexandrovFunctional

/-! Minimal source-body producer for the direct actual-current polarization route.
The earlier ConvexMinkowskiTotal draft is superseded for this integration;
do not import both, since their body declarations intentionally coincide. -/

noncomputable section
namespace SGPT.Convex

open Set Filter MeasureTheory
open scoped Topology BigOperators Pointwise ENNReal

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual original closed subgradient image of a finite convex function. -/
def finiteConvexGradientBody (f : RealConvexFunction E) : Set E :=
  closure (rawSubgradientImage (innerₗ E) (fun x => (f.val x : EReal)))

private theorem finiteConvex_coe_closed (f : RealConvexFunction E) :
    IsClosedConvex (fun x => (f.val x : EReal)) := by
  apply isClosedConvex_of_isProper_full_domain (isProper_coe_of_convexOn f.property)
  ext x
  simp [effectiveDomain]

private theorem bounded_conjugate_domain_of_compact_gradientBody
    (f : RealConvexFunction E) (hf : IsCompact (finiteConvexGradientBody f)) :
    Bornology.IsBounded
      (effectiveDomain (conjugate (innerₗ E) (fun x => (f.val x : EReal)))) := by
  apply hf.isBounded.subset
  change effectiveDomain (conjugate (innerₗ E) (fun x => (f.val x : EReal))) ⊆
    closure (rawSubgradientImage (innerₗ E) (fun x => (f.val x : EReal)))
  rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate
    (innerₗ E) (isProper_coe_of_convexOn f.property)
    (lowerSemicontinuous_of_isClosedConvex (finiteConvex_coe_closed f))]
  exact subset_closure

theorem finiteConvexGradientBody_add (f g : RealConvexFunction E)
    (hf : IsCompact (finiteConvexGradientBody f)) :
    finiteConvexGradientBody (realConvexAdd f g) =
      finiteConvexGradientBody f + finiteConvexGradientBody g := by
  simpa only [finiteConvexGradientBody, realConvexAdd] using
    closure_rawSubgradientImage_add_coe (innerₗ E) f.property g.property
      (bounded_conjugate_domain_of_compact_gradientBody f hf)

private theorem rawSubgradientImage_zero :
    rawSubgradientImage (innerₗ E) (fun _ : E => (0 : EReal)) = ({0} : Set E) := by
  ext m
  constructor
  · intro hm
    obtain ⟨x, hx⟩ := mem_iUnion.mp hm
    have hh := hx (x + m)
    have hnorm : ‖m‖ ^ 2 ≤ 0 := by
      apply EReal.coe_nonpos.mp
      simpa only [zero_add,
        add_sub_cancel_left, innerₗ_apply_apply, EReal.coe_le_coe_iff,
        real_inner_self_eq_norm_sq] using hh
    have hz : ‖m‖ = 0 := by nlinarith [norm_nonneg m]
    exact mem_singleton_iff.mpr (norm_eq_zero.mp hz)
  · intro hm
    obtain rfl := mem_singleton_iff.mp hm
    exact mem_iUnion.mpr ⟨0, by simp [rawSubdifferential, innerₗ_apply_apply]⟩

/-- All subset sums, including the EMPTY sum, have their actual Minkowski bodies. -/
theorem finiteConvexGradientBody_subsetSum (u : Fin n → RealConvexFunction E)
    (hu : ∀ i, IsCompact (finiteConvexGradientBody (u i))) (S : Finset (Fin n)) :
    finiteConvexGradientBody (finiteConvexSubsetSum u S) =
      sourceMinkowskiSubsetSum (fun i => finiteConvexGradientBody (u i)) S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [finiteConvexGradientBody, finiteConvexSubsetSum, Finset.sum_empty,
      sourceMinkowskiSubsetSum, EReal.coe_zero, rawSubgradientImage_zero,
      isClosed_singleton.closure_eq, Finset.sum_empty]
    exact Set.singleton_zero
  | @insert a S ha ih =>
    have hfun : finiteConvexSubsetSum u (insert a S) =
        realConvexAdd (u a) (finiteConvexSubsetSum u S) := by
      apply Subtype.ext
      funext x
      simp [finiteConvexSubsetSum, realConvexAdd, Finset.sum_insert ha]
    rw [hfun, finiteConvexGradientBody_add (u a) _ (hu a), ih]
    simp only [sourceMinkowskiSubsetSum, Finset.sum_insert ha]

theorem isCompact_sourceMinkowskiSubsetSum
    (P : Fin n → Set E) (hP : ∀ i, IsCompact (P i)) (S : Finset (Fin n)) :
    IsCompact (sourceMinkowskiSubsetSum P S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sourceMinkowskiSubsetSum]
  | @insert a S ha ih =>
    simpa only [sourceMinkowskiSubsetSum, Finset.sum_insert ha] using (hP a).add ih

end SGPT.Convex
