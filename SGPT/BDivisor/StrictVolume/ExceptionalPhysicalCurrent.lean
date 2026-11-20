import SGPT.BDivisor.StrictVolume.OffCentreSupport
import SGPT.Toric.ExceptionalSelfIntersection
import SGPT.Toric.PointBlowdownMass
import SGPT.PSH.BookDeepLelongPoincare
import SGPT.Toric.PolytopeToricOperations

/-! The SAME original physical O(E) metric internally manufactures an actual
positive divisor current with the actual exceptional-fibre support.
No prime-current/Chern comparison or pushforward-zero certificate is input.
Checks and provider-boundary receipts are preserved separately. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SGPT.BDivisor.TraceOffCentreNext

open Set Bundle Filter
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Projective SGPT.PSH SGPT.PSH.LineBundleMetric
open SGPT.Bergman.NativeHermitianMetric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.GlobalCurrents
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
open SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
open SGPT.Currents.AnalyticSupport

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem originalExceptional_zero_mem :
    (0 : Fin 2 → ℤ) ∈ toricLatticePoints (originalExceptionalDivisor hs) := by
  have hLat : latticeVector (0 : Fin 2 → ℤ) = (0 : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    simp
  change latticeVector (0 : Fin 2 → ℤ) ∈ toricDivisorPolytope (originalExceptionalDivisor hs)
  rw [hLat]
  intro rho
  simp only [map_zero]
  change -((if rho.val = blowupRay7 then 1 else 0 : ℤ) : ℝ) ≤ 0
  split_ifs <;> norm_num

/-- The actual character-zero section of the SAME physical O(E) bundle. -/
def originalExceptionalPhysicalSection : ToricNativeHolomorphicSections (originalExceptionalMetric hs) :=
  toricNativeSectionOfToric (originalExceptionalMetric hs)
    (originalMonomialSection (originalExceptionalDivisor hs) ⟨0, originalExceptional_zero_mem hs⟩)

/-- Exact coefficients in ALL FOUR original charts: t,1,1,s. -/
theorem originalExceptionalPhysicalSection_literal (k : Fin 4) (z : Fin 2 → ℂ) :
    ((toricNativeLineTrivialization (originalExceptionalMetric hs) (blowupVertex k))
      ⟨blowupOriginalChartPoint hs k z,
        originalExceptionalPhysicalSection hs (blowupOriginalChartPoint hs k z)⟩).2 =
      (![z 0, 1, 1, z 1] : Fin 4 → ℂ) k := by
  change ((toricNativeLineTrivialization (originalExceptionalMetric hs) (blowupVertex k))
    ⟨blowupOriginalChartPoint hs k z, toricOriginalSectionNativeValue (originalExceptionalMetric hs)
      (originalMonomialSection (originalExceptionalDivisor hs) ⟨0, originalExceptional_zero_mem hs⟩)
        (blowupOriginalChartPoint hs k z)⟩).2 = _
  rw [toricOriginalSectionNativeValue_coefficient _ _ _ (blowupOriginalChartPoint_mem hs k z),
    originalMonomialSection_coefficient, blowupOriginalChartPoint_coordinate,
    blowupMonomial_ordered, originalExceptional_cartierDatum]
  fin_cases k <;>
    norm_num [Fin.prod_univ_two, originalExceptionalDatum, blowupBasis,
      vertexConeRay_lattice2Basis_zero, vertexConeRay_lattice2Basis_one,
      intPairing, Fin.sum_univ_two]

private theorem physical_section_zero_iff_coefficient (k : Fin 4) (z : Fin 2 → ℂ) :
    originalExceptionalPhysicalSection hs (blowupOriginalChartPoint hs k z) = 0 ↔
      ((toricNativeLineTrivialization (originalExceptionalMetric hs) (blowupVertex k))
        ⟨blowupOriginalChartPoint hs k z,
          originalExceptionalPhysicalSection hs (blowupOriginalChartPoint hs k z)⟩).2 = 0 := by
  exact ((toricNativeLineTrivialization (originalExceptionalMetric hs) (blowupVertex k)).continuousLinearEquivAt
    ℂ (blowupOriginalChartPoint hs k z) (blowupOriginalChartPoint_mem hs k z)).map_eq_zero_iff.symm

theorem originalExceptionalPhysicalSection_zero_iff (p : PolytopeToricVariety blowupGenerator hs) :
    originalExceptionalPhysicalSection hs p = 0 ↔
      p ∈ toricPrimeDivisor (blowupExceptionalRay hs) := by
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  rw [physical_section_zero_iff_coefficient, originalExceptionalPhysicalSection_literal,
    exceptionalRay_chart]
  fin_cases k <;> simp

theorem originalExceptionalPhysicalSection_ne_zero :
    ∃ p, originalExceptionalPhysicalSection hs p ≠ 0 := by
  refine ⟨blowupOriginalChartPoint hs 1 (0 : Fin 2 → ℂ), ?_⟩
  intro hzero
  have hCoeff := (physical_section_zero_iff_coefficient hs 1 (0 : Fin 2 → ℂ)).mp hzero
  rw [originalExceptionalPhysicalSection_literal] at hCoeff
  norm_num at hCoeff

theorem originalExceptionalPhysicalSection_holomorphic :
    IsHolomorphicSectionOn (n := 2)
      (ToricNativeLineFiber (originalExceptionalMetric hs))
      (originalExceptionalPhysicalSection hs) univ :=
  ((originalExceptionalPhysicalSection hs).contMDiff.mdifferentiable (by simp)).mdifferentiableOn

/-- Actual whole-book metric from the SAME original physical fibre norms. -/
def originalExceptionalPhysicalBookMetric :=
  sourceNativeHermitianMetric (toricNativeHermitianLineBundle (originalExceptionalMetric hs))
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle (originalExceptionalMetric hs))

/-- Lelong--Poincare manufactures the actual divisor from that actual global section. -/
def originalExceptionalPhysicalDivisor :
    MeteredEffectiveQDivisor 2 (PolytopeToricVariety blowupGenerator hs) :=
  BookDeepLelongPoincare.zeroDivisor (ToricNativeLineFiber (originalExceptionalMetric hs))
    (originalExceptionalPhysicalBookMetric hs)
    (originalExceptionalPhysicalSection_holomorphic hs)
    (originalExceptionalPhysicalSection_ne_zero hs)

private theorem physical_divisor_support_iff (p : PolytopeToricVariety blowupGenerator hs) :
    p ∈ (originalExceptionalPhysicalDivisor hs).support ↔
      originalExceptionalPhysicalSection hs p = 0 := by
  change ENNReal.log (ENNReal.ofReal
    (((originalExceptionalPhysicalBookMetric hs).form p).normSq
      (originalExceptionalPhysicalSection hs p))) = ⊥ ↔ _
  unfold originalExceptionalPhysicalBookMetric
  rw [sourceNativeHermitianMetric_normSq]
  simp only [ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero, sq_nonpos_iff, norm_eq_zero]

/-- Genuine whole exceptional support, derived from all original local equations. -/
theorem originalExceptionalPhysicalDivisor_support :
    (originalExceptionalPhysicalDivisor hs).support =
      toricPrimeDivisor (blowupExceptionalRay hs) := by
  ext p
  exact (physical_divisor_support_iff hs p).trans (originalExceptionalPhysicalSection_zero_iff hs p)

theorem originalExceptionalPhysicalDivisor_support_fibre :
    (originalExceptionalPhysicalDivisor hs).support =
      (originalBlowdown hs) ⁻¹' ({blowdownOrigin} : Set (ComplexProjectiveSpace 2)) := by
  rw [originalExceptionalPhysicalDivisor_support]
  exact (originalBlowdown_fibre_origin hs).symm

/-- Positivity AND local nondegeneracy are manufactured from the actual section. -/
theorem originalExceptionalPhysicalDivisor_weight_psh :
    IsThetaPshPotential (originalExceptionalPhysicalDivisor hs).curvature.val
      (originalExceptionalPhysicalDivisor hs).weight := by
  refine ⟨MeteredDivisorPositivity.thetaPlurisubharmonic_weight _, ?_⟩
  intro x U hU hxU
  obtain ⟨y, hyU, hy⟩ := BookDeepLelongPoincare.exists_ne_zero_of_isOpen
    (originalExceptionalPhysicalSection_holomorphic hs)
    (originalExceptionalPhysicalSection_ne_zero hs) hU ⟨x, hxU⟩
  refine ⟨y, hyU, ?_⟩
  intro hbot
  exact hy ((physical_divisor_support_iff hs y).mp hbot)

/-- The SAME physical O(E) Chern class, internally identified with the
curvature of its actual effective metered section divisor. -/
theorem originalExceptionalPhysicalDivisor_class :
    RealBottChern.ofRepresentative (originalExceptionalPhysicalDivisor hs).curvature =
      RealBottChern.ofRepresentative (originalExceptionalMetric hs).form := by
  exact RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (toricNativeFirstChernForm_geometricallyEq (originalExceptionalMetric hs))

section Pushforward

variable {X Y Z : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X] [IsComplexManifold 2 X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel 2) Y] [IsComplexManifold 2 Y] [CompactSpace Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel 2) Z] [IsComplexManifold 2 Z] [CompactSpace Z]

omit [IsComplexManifold 2 X] in
/-- First actual geometric producer: ANY genuine commuting refinement of a
re-centred original point blowdown and a model isomorphic at its actual centre
has ZERO push-pull of the SAME physical original exceptional Chern class.
No exceptional-support/class-comparison/pushforward-zero output is input. -/
theorem pushforward_pullback_originalExceptionalClass_eq_zero
    (a : ComplexProjectiveSpace 2 → X) {rho : Y → X}
    {q : Z → PolytopeToricVariety blowupGenerator hs} {beta : Z → Y}
    (hq : IsAnalyticModification (n := 2) q)
    (hbeta : IsAnalyticModification (n := 2) beta)
    (hcomm : (a ∘ originalBlowdown hs) ∘ q = rho ∘ beta)
    {U : Set X} (hiso : FirstPass.BlowupSequences.IsIsomorphismOver 2 rho U)
    (hp : a blowdownOrigin ∈ U) :
    classPushforward hbeta.1 (canonicalBasis 2) (by decide)
      (classPullback hq.1 (RealBottChern.ofRepresentative (originalExceptionalMetric hs).form)) = 0 := by
  rw [← originalExceptionalPhysicalDivisor_class hs]
  apply pushforward_pullback_metered_fibre_class_eq_zero hq hbeta hcomm hiso hp
    (originalExceptionalPhysicalDivisor hs) (originalExceptionalPhysicalDivisor_weight_psh hs)
  intro z hz
  rw [originalExceptionalPhysicalDivisor_support_fibre] at hz
  change a (originalBlowdown hs z) = a blowdownOrigin
  exact congrArg a hz

end Pushforward

end SGPT.BDivisor.TraceOffCentreNext
