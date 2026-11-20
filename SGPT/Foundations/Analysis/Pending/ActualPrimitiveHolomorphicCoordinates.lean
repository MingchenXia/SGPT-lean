import SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicGraphProjection

set_option autoImplicit false

/-! # Actual primitive holomorphic germs in invertible graph coordinates

Actual complex linear and germ ring equivalences transport the natural
algebraic primitive condition.  No uniform residual factor property is
assumed to follow from an origin-only factorization.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicCoordinates

open ActualPrimitiveHolomorphicGraphProjection DivisorRegularLocus

/-- Actual germ ring equivalences preserve the natural primitive family property. -/
theorem isPrimitiveAt_comp_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {N : ℕ}
    (L : E ≃L[ℂ] F) (f : Fin N → F → ℂ) (x : E)
    (hp : IsPrimitiveAt f (L x)) : IsPrimitiveAt (fun i y => f i (L y)) x := by
  obtain ⟨hf, hprim⟩ := hp
  have hg : ∀ i, ∀ᶠ y in 𝓝 (0 : E),
      DifferentiableAt ℂ (fun y => f i (L (y + x))) y := by
    intro i
    simpa [Function.comp_def] using eventually_differentiableAt_comp_clm
      (L : E →L[ℂ] F) (hf i)
  refine ⟨hg, ?_⟩
  let e := HolGerm.comapEquiv L
  have he : ∀ i, e (HolGerm.mk (fun y => f i (y + L x)) (hf i)) =
      HolGerm.mk (fun y => f i (L (y + x))) (hg i) := by
    intro i
    rw [HolGerm.comapEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun y => by simp
  intro q hq
  have hunit : IsUnit (e.symm q) := by
    apply hprim
    intro i
    obtain ⟨d, hd⟩ := hq i
    refine ⟨e.symm d, ?_⟩
    apply e.injective
    simpa only [map_mul, RingEquiv.apply_symm_apply, he i] using hd
  simpa using hunit.map e.toRingHom

/-- The genuine splitting supplies invertible coordinates internally;
primitive families have null transverse common zeros on the actual graph. -/
theorem volume_splitting_graph_common_zero_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m N : ℕ}
    (f : Fin N → V → ℂ) {u : V} (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {W : Set (EuclideanSpace ℂ (Fin m))} (hW : IsOpen W)
    {k : EuclideanSpace ℂ (Fin m) → ℂ} (hk : DifferentiableOn ℂ k W)
    (hp : ∀ w ∈ W, IsPrimitiveAt f (k w • u + S.ι w)) :
    volume {w : EuclideanSpace ℂ (Fin m) |
      w ∈ W ∧ ∀ i, f i (k w • u + S.ι w) = 0} = 0 := by
  have hinner : (innerSL ℂ u) u ≠ 0 := by
    simp [innerSL_apply_apply, inner_self_eq_norm_sq_to_K, hu]
  let B := S.equiv (innerSL ℂ u) hinner
  let A : (EuclideanSpace ℂ (Fin m) × ℂ) ≃L[ℂ] V :=
    (ContinuousLinearEquiv.prodComm ℂ (EuclideanSpace ℂ (Fin m)) ℂ).trans B.symm
  have hA : ∀ z : EuclideanSpace ℂ (Fin m) × ℂ, A z = z.2 • u + S.ι z.1 := by
    intro z
    apply B.injective
    simp [A, B, Splitting.equiv_apply, S.inner_smul_add hu, S.π_smul_add, Prod.swap]
  have hprim : ∀ w ∈ W, IsPrimitiveAt (fun i z => f i (A z)) (w, k w) := by
    intro w hw
    apply isPrimitiveAt_comp_equiv
    simpa only [hA] using hp w hw
  simpa only [hA] using volume_graph_common_zero_eq_zero (fun i z => f i (A z)) hW hk hprim

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicCoordinates
