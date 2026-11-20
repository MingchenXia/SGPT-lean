import SGPT.Projective.NumEqCurves

/-! Genuine real-linearity of the ORIGINAL degreeAlong on actual compact
whole curves, every ambient dimension, no connected/nonempty premise.
Blueprint: actual-curve-degree-linearity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Projective.NumEq
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {X C : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C] [CompactSpace C]
  (κ : KahlerBackground 1 C) {g : C → X}
  (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)

theorem degreeAlong_add_actual (alpha beta : ClosedRealOneOneForm n X) :
    degreeAlong κ hg (alpha + beta) = degreeAlong κ hg alpha + degreeAlong κ hg beta := by
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  have hpb : ClosedRealOneOneForm.pullback hg (alpha + beta) =
      ClosedRealOneOneForm.pullback hg alpha + ClosedRealOneOneForm.pullback hg beta := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl
  change slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg (alpha + beta)) =
    slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg alpha) +
      slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg beta)
  rw [hpb]
  have h := slotIntegral_update_add κ (fun _ => κ.form) 0
    (ClosedRealOneOneForm.pullback hg alpha) (ClosedRealOneOneForm.pullback hg beta)
  rw [← fun_eq_update_dim_one, ← fun_eq_update_dim_one, ← fun_eq_update_dim_one] at h
  exact h

theorem degreeAlong_smul_actual (r : ℝ) (alpha : ClosedRealOneOneForm n X) :
    degreeAlong κ hg (r • alpha) = r • degreeAlong κ hg alpha := by
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  have hpb : ClosedRealOneOneForm.pullback hg (r • alpha) = r • ClosedRealOneOneForm.pullback hg alpha := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl
  change slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg (r • alpha)) =
    r • slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg alpha)
  rw [hpb]
  have h := slotIntegral_update_smul κ (fun _ => κ.form) 0 r (ClosedRealOneOneForm.pullback hg alpha)
  rw [← fun_eq_update_dim_one, ← fun_eq_update_dim_one] at h
  exact h

theorem degreeAlong_finite_sum_actual {N : ℕ} (r : Fin N → ℝ) (theta : Fin N → ClosedRealOneOneForm n X) :
    degreeAlong κ hg (∑ i, r i • theta i) = ∑ i, r i * degreeAlong κ hg (theta i) := by
  let F : ClosedRealOneOneForm n X →ₗ[ℝ] ℝ :=
    { toFun := degreeAlong κ hg
      map_add' := degreeAlong_add_actual κ hg
      map_smul' := degreeAlong_smul_actual κ hg }
  change F (∑ i, r i • theta i) = ∑ i, r i * F (theta i)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
