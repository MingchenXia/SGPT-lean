import SGPT.Checks.Comparison.BJPrintedDefinition
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! A canonical actual numerical module topology and its unconditional
one-way comparison with true curve-degree convergence. No FD premise. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.NativePicard
open AlgebraicGeometry CategoryTheory Topology Filter
open SGPT.Foundations.Envelope
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- Canonical finest real module topology of the SAME actual numerical
quotient. No usual-NS/curve-weak/ample-order topology equality is asserted. -/
abbrev numericalModuleTopology : TopologicalSpace (NativeRealNumericalClasses.Space p) :=
  moduleTopology ℝ (NativeRealNumericalClasses.Space p)

theorem continuous_curveDegree_from_moduleTopology
    (C : NativeClosedCurveDegrees.ClosedIntegralCurve X) :
    @Continuous _ _ (numericalModuleTopology p) inferInstance
      (NativeRealNumericalClasses.curveDegree p C) := by
  let := numericalModuleTopology p
  exact IsModuleTopology.continuous_of_linearMap (NativeRealNumericalClasses.curveDegree p C)

/-- Actual identity comparison on the SAME original numerical classes,
without an assumed topology bridge or global numerical finite dimension. -/
theorem continuous_module_to_curveWeak :
    @Continuous _ _ (numericalModuleTopology p) (numericalCurveWeakTopology p) id := by
  let := numericalModuleTopology p
  apply continuous_induced_rng.mpr
  change Continuous (numericalDegreeEmbedding p)
  exact IsModuleTopology.continuous_of_linearMap (numericalDegreeEmbedding p)

theorem tendsto_curveWeak_of_module {T : Type u}
    {c : T → NativeRealNumericalClasses.Space p} {l : Filter T}
    {θ : NativeRealNumericalClasses.Space p}
    (h : Tendsto c l (@nhds _ (numericalModuleTopology p) θ)) :
    Tendsto c l (@nhds _ (numericalCurveWeakTopology p) θ) :=
  (@Continuous.tendsto _ _ (numericalModuleTopology p) (numericalCurveWeakTopology p)
    id (continuous_module_to_curveWeak p) θ).comp h

end SGPT.NAPotential.BJ.NativePicard

namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- Literal source-shaped actual rational-GF net predicate, using the
EXPLICIT canonical finest real module topology for original class convergence. -/
def IsModuleTopologyPSH (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) : Prop :=
  IsPSHForNumericalTopology.{u} p (numericalModuleTopology p) L φ

/-- SAME actual net and SAME full original pointwise limit; only the
unconditional numerical-topology comparison is applied. -/
theorem IsModuleTopologyPSH.isCurveWeakPSH {L : RationalPicardSpace X}
    {φ : BerkovichPoint p → EReal} (h : IsModuleTopologyPSH.{u} p L φ) :
    IsCurveWeakPSH.{u} p L φ := by
  obtain ⟨hne,D,hclass,hlim⟩ := h
  exact ⟨hne,D,tendsto_curveWeak_of_module p hclass,hlim⟩

end SGPT.NAPotential.BJ.Printed
