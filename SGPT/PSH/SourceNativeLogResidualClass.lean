import SGPT.PSH.GeometricLogMetricClass
import SGPT.PSH.DisconnectedLogResidualPositivity

/-! Genuine nef/Kahler conclusions for the ORIGINAL geometric rational
divisor class, all n and no connectedness or nonempty certificate premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open ManifoldTubePositivity
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

omit [CompactSpace M] in
private theorem ofRepresentative_sub (a b : ClosedRealOneOneForm n M) :
    RealBottChern.ofRepresentative (a-b)=RealBottChern.ofRepresentative a-RealBottChern.ofRepresentative b := by
  change RealBottChern.ofRepresentative (a+(-b))=_
  rw [RealBottChern.ofRepresentative_add,RealBottChern.ofRepresentative_neg,sub_eq_add_neg]

omit [CompactSpace M] in
private theorem ofRepresentative_add_ddc (theta : ClosedRealOneOneForm n M)
    {h : M → ℝ} (hh : ChartSmooth (n := n) h) :
    RealBottChern.ofRepresentative (theta+ddcClosedForm h hh)=RealBottChern.ofRepresentative theta := by
  refine ((RealBottChern.ofRepresentative_eq_iff _ _).mpr ?_).symm
  exact ⟨h,hh,fun e z hz => by rw [ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff]⟩

/-- ORIGINAL D and complete source logarithms yield nefness of its FIXED
standard prime-current class difference, in EVERY natural dimension.
No metric, bounded residual or class/nef output is a premise. -/
theorem native_original_log_divisor_class_nef (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (D : EffectiveGeometricQDivisor n M) (u : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D u) :
    ClassNefWithRespectTo omega (RealBottChern.ofRepresentative theta-compact_geometric_divisor_class D) := by
  obtain ⟨E,_hsupport,hclass,_hlocal,⟨L⟩⟩ := compact_exists_actual_log_metric_class_dictionary D u hlog
  rw [hclass,←ofRepresentative_sub]
  exact actual_residual_nef omega hu L

/-- ORIGINAL Kahler-current lower bound produces an ACTUAL smooth closed
strictly positive representative of the SAME original divisor class
difference, with no metric/residual/class certificate as source hypothesis. -/
theorem native_original_log_divisor_class_kahler
    (theta : ClosedRealOneOneForm n M) (D : EffectiveGeometricQDivisor n M) (u : M → EReal)
    (hu : IsKahlerCurrentPotential theta u)
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D u) :
    ∃ kappa : ClosedRealOneOneForm n M,kappa.val.IsKahler ∧
      RealBottChern.ofRepresentative kappa=RealBottChern.ofRepresentative theta-compact_geometric_divisor_class D := by
  obtain ⟨E,_hsupport,hclass,_hlocal,⟨L⟩⟩ := compact_exists_actual_log_metric_class_dictionary D u hlog
  obtain ⟨h,hh,hpos⟩ := actual_residual_kahler hu L
  refine ⟨(theta-E.curvature)+ddcClosedForm h hh,hpos,?_⟩
  rw [ofRepresentative_add_ddc,ofRepresentative_sub,hclass]

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
