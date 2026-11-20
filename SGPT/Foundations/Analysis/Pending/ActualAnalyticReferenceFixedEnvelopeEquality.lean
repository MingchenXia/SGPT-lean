import SGPT.Foundations.Analysis.Pending.ActualAnalyticReferenceLocalExactOrder
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-! # Exact analytic fixed-background P/I equality in all dimensions and masses -/

open Set Filter
open scoped Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticReferenceFixedEnvelopeEquality

open FirstPass FirstPass.IEnvelope FirstPass.QuasiEquisingularApproximation

noncomputable section

/-- Original full ideal order to an analytic reference has one global
additive constant, including dimension zero and zero non-pluripolar mass. -/
theorem moreSingularOn_of_iOrder_analytic_reference
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {θ ζ : ClosedRealOneOneForm n X} {ψ φ : X → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) (hφ : IsThetaPshPotential ζ.val φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) φ)
    (hI : IOrderOnManifold (n := n) ψ φ) :
    MoreSingularOn ψ φ univ := by
  apply IdealWeightComparison.moreSingularOn_univ_of_forall_moreSingularAt
  intro x
  cases n with
  | zero =>
    have hψx : ψ x = ((ψ x).toReal : EReal) :=
      (EReal.coe_toReal (hψ.1.quasiPlurisubharmonic.ne_top x)
        (FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hψ x)).symm
    have hφx : φ x = ((φ x).toReal : EReal) :=
      (EReal.coe_toReal (hφ.1.quasiPlurisubharmonic.ne_top x)
        (FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hφ x)).symm
    refine ⟨(ψ x).toReal - (φ x).toReal,
      eventually_of_mem ((FiniteGeodesicsFullMassAnyDim.isOpen_singleton_of_dim_zero x).mem_nhds
        (mem_singleton x)) ?_⟩
    intro y hy
    subst y
    rw [hψx, hφx, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simp only [EReal.toReal_coe]
    linarith
  | succ m =>
    exact ActualAnalyticReferenceLocalExactOrder.moreSingularAt_of_iOrder_analytic_reference
      hψ hφ hA hI x

/-- The literal ordinary and I-envelopes of the same original analytic
reference agree in its arbitrary fixed closed background, without mass input. -/
theorem singularityEnvelope_eq_iSingularityEnvelope_of_analytic_reference
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (β : ClosedRealOneOneForm n X) {v : X → EReal}
    (hv : IsThetaPshPotential β.val v)
    (hA : HasManifoldAnalyticSingularityType (n := n) v) :
    singularityEnvelope β.val v = iSingularityEnvelope β.val v := by
  classical
  by_cases hX : Nonempty X
  · let : Nonempty X := hX
    have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials β
    apply le_antisymm
      (singularityEnvelope_le_iSingularityEnvelope β.val β.property.1 β.property.2 hlocal v hv)
    apply (iSingularityEnvelope_le_iff (upperSemicontinuous_singularityEnvelope β.val v)).mpr
    intro u hu hu0 hi
    exact le_singularityEnvelope hu hu0
      (moreSingularOn_of_iOrder_analytic_reference hu hv hA hi.1)
  · exact funext fun x => False.elim (hX ⟨x⟩)

end
end SGPT.Foundations.Analysis.Pending.ActualAnalyticReferenceFixedEnvelopeEquality
