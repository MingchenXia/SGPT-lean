import SGPT.Unibranch.ComplexSpaceProperDiscDescent
import SGPT.Unibranch.ComplexDiscRecenter

/-! Actual original proper PSH descent passes the ENTIRE genuine original
disk criterion; no target test/membership certificate is an input.
Blueprint: complex-space-proper-disc-criterion.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry Metric
open scoped Topology
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- ALL actual disk centers and the full genuine original raw circle criterion. -/
theorem discPullback_discPshOn_of_proper {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    {ψ : Y.obj.left → EReal} (hψ : ∀ y,Y.IsLocallyAmbientPSHAt ψ y)
    {φ : X.obj.left → EReal} (hφ : UpperSemicontinuous φ)
    (hcoh : ∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) (f : unitDisc ⟶ X) :
    DiscPshOn (discPullback f φ) (ball (0 : ℂ) 1) :=
  SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn
    (plurisubharmonicOn_discPullback_of_zero_germs φ
      (fun g => discPullback_pshAt_zero_of_proper π hπ hψ hφ hcoh g) f)

/-- The exact original non-bottom-qualified source FN subharmonic disk test. -/
theorem discPullback_subharmonic_of_proper {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    {ψ : Y.obj.left → EReal} (hψ : ∀ y,Y.IsLocallyAmbientPSHAt ψ y)
    {φ : X.obj.left → EReal} (hφ : UpperSemicontinuous φ)
    (hcoh : ∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) (f : unitDisc ⟶ X)
    (hn : ∃ z ∈ ball (0 : ℂ) 1,discPullback f φ z ≠ ⊥) :
    SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1) :=
  SGPT.PSH.subharmonicOn_of_disc (discPullback_discPshOn_of_proper π hπ hψ hφ hcoh f) hn

/-- ONLY the ORIGINAL upstairs PSH function and original geometric hypotheses
manufacture unique USC descent with EVERY genuine whole-disk FN test. -/
theorem IsPSH.exists_unique_usc_descent_with_diskCriterion {X Y : SourceReducedComplexSpace}
    {ψ : Y.obj.left → EReal} (hψ : Y.IsPSH ψ)
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    ∃! φ : X.obj.left → EReal,UpperSemicontinuous φ ∧
      (∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) ∧
      ∀ f : unitDisc ⟶ X,(∃ z ∈ ball (0 : ℂ) 1,discPullback f φ z ≠ ⊥) →
        SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1) := by
  obtain ⟨φ,⟨hφ,hcoh⟩,hunique⟩ := exists_unique_usc_descent_of_connected_proper_fibers
    π hπ.1 (hπ.isConnected_fiber_of_isUnibranch hX) hψ.2
  refine ⟨φ,⟨hφ,hcoh,fun f hn => discPullback_subharmonic_of_proper π hπ hψ.2 hφ hcoh f hn⟩,?_⟩
  intro χ hχ
  exact hunique χ ⟨hχ.1,hχ.2.1⟩

end SGPT.Unibranch.SourceReducedComplexSpace
