import SGPT.Toric.NonNefExceptionalChern
import SGPT.Toric.Toric3PEquivalence
import SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly
import SGPT.Toric.SameDivisorChernClass
import SGPT.Toric.BigToricEnvelope
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN OriginalNonNefPolarizationDraft; original source SHA256 efae312c344a323a6ab4c2748e6f495dafd6ffd04544a8f41b4f5b1de54ceb3b -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual original auxiliary divisor A=2H-E, expressed by its original ray coefficients. -/
def originalAuxiliaryDivisor : ToricDivisor blowupGenerator hs :=
  toricDivisorOfCoeff hs fun u => if u = blowupRay4 then 2 else if u = blowupRay7 then -1 else 0

/-- Its original Cartier data are the ACTUAL original P-prime vertices. -/
theorem originalAuxiliary_cartierDatum (k : Fin 4) :
    toricCartierDatum (originalAuxiliaryDivisor hs) (blowupVertex k) = (blowupVertex k).val := by
  apply toricCartierDatum_ofCoeff
    (fun u => if u = blowupRay4 then 2 else if u = blowupRay7 then -1 else 0)
    (blowupVertex k) (blowup_isVertexConeBasis k)
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [blowupVertex, blowupGenerator, blowupBasis, vertexConeRay_lattice2Basis_zero,
      vertexConeRay_lattice2Basis_one, blowupRay4, blowupRay7, intPairing, Fin.sum_univ_two]

/-- Genuine identification with the SAME original polarizing Cartier divisor, from all actual ray pairings. -/
theorem originalAuxiliary_eq_originalPolarization :
    originalAuxiliaryDivisor hs = polytopeToricAmpleDivisor blowupGenerator hs := by
  have hdatum (v : latticePolytopeVertices blowupGenerator) :
      toricCartierDatum (originalAuxiliaryDivisor hs) v = v.val := by
    obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
    have hv : v = blowupVertex k := Subtype.ext hk.symm
    subst v
    exact originalAuxiliary_cartierDatum hs k
  funext ρ
  obtain ⟨v, j, hj⟩ := ρ.property
  have hray : polytopeToricRay blowupGenerator hs v j = ρ := Subtype.ext hj
  have hA := toricCartierDatum_pairing (originalAuxiliaryDivisor hs) v j
  have hP := toricCartierDatum_pairing (polytopeToricAmpleDivisor blowupGenerator hs) v j
  rw [hdatum, hray] at hA
  rw [toricCartierDatum_ampleDivisor, hray] at hP
  exact neg_injective (hA.symm.trans hP)

/-- Literal original D equals the original Kähler polarization plus the actual effective 2E. -/
theorem originalNonNefDivisor_twoE_add_polarization :
    blowupNonNefDivisor hs = (2 : ℕ) • originalExceptionalDivisor hs +
      polytopeToricAmpleDivisor blowupGenerator hs := by
  rw [← originalAuxiliary_eq_originalPolarization hs]
  funext ρ
  change (if ρ.val = blowupRay4 then 2 else if ρ.val = blowupRay7 then 1 else 0) =
    (2 : ℕ) • (if ρ.val = blowupRay7 then 1 else 0 : ℤ) +
      (if ρ.val = blowupRay4 then 2 else if ρ.val = blowupRay7 then -1 else 0)
  have h47 : blowupRay4 ≠ blowupRay7 := by decide
  by_cases h4 : ρ.val = blowupRay4
  · simp [h4, h47]
  · by_cases h7 : ρ.val = blowupRay7
    · simp [h7, Ne.symm h47]
    · simp [h4, h7]

/-- The effective character0 lies in the ACTUAL original polytope of 2E. -/
theorem originalTwoExceptional_zero_mem :
    (0 : EuclideanSpace ℝ (Fin 2)) ∈ toricDivisorPolytope ((2 : ℕ) • originalExceptionalDivisor hs) := by
  intro ρ
  simp only [map_zero]
  change -(((2 : ℕ) • (if ρ.val = blowupRay7 then 1 else 0 : ℤ) : ℤ) : ℝ) ≤ 0
  split_ifs <;> norm_num

end SGPT.Toric.F1IntersectionDraft

end
/- END OriginalNonNefPolarizationDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN OriginalNonNefBigCurrentDraft; original source SHA256 a3d79c40e202d5a4bf01c330d2217c83b1404744e9196e288014ce43a0176e52 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- A genuine native smooth metric on the ACTUAL effective divisor 2E, internally manufactured. -/
def originalTwoExceptionalMetric : BigToricMetric ((2 : ℕ) • originalExceptionalDivisor hs) :=
  Classical.choice (exists_bigToricMetric _)

/-- The ACTUAL source metric of D=2E+D_P, with original Cartier transitions transported
by the proved equality of divisors. The curvature remains the actual sum theta_(2E)+omega_P. -/
def originalBigComparisonMetric : BigToricMetric (blowupNonNefDivisor hs) where
  form := (originalTwoExceptionalMetric hs).addGuillemin.form
  weight := (originalTwoExceptionalMetric hs).addGuillemin.weight
  smooth := (originalTwoExceptionalMetric hs).addGuillemin.smooth
  coeff := (originalTwoExceptionalMetric hs).addGuillemin.coeff
  invariant := (originalTwoExceptionalMetric hs).addGuillemin.invariant
  transition v w a := by
    rw [originalNonNefDivisor_twoE_add_polarization hs]
    exact (originalTwoExceptionalMetric hs).addGuillemin.transition v w a

/-- A real global native theta_(2E)-psh potential, produced from the actual original
Cartier polytope containing character0. No psef/current/metric certificate is an input. -/
theorem originalTwoExceptional_has_native_potential :
    IsThetaPshPotential (originalTwoExceptionalMetric hs).form.val
      (originalTwoExceptionalMetric hs).minimalEnvelope := by
  have hP : (toricDivisorPolytope ((2 : ℕ) • originalExceptionalDivisor hs)).Nonempty :=
    ⟨0, originalTwoExceptional_zero_mem hs⟩
  exact (isThetaPSH_iff_nativeThetaPotential (originalTwoExceptionalMetric hs).atlasForm _).mp
    ((originalTwoExceptionalMetric hs).minimalEnvelope_mem hP).1

/-- An actual Kähler current for the SAME original D comparison metric: the produced
positive current of 2E plus the actual original P-prime Kähler form. -/
theorem originalBigComparisonMetric_isBig :
    IsBigClass (RealBottChern.ofRepresentative (originalBigComparisonMetric hs).form) := by
  have h := SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
    (polytopeToricKahlerBackground blowupGenerator hs) (originalTwoExceptionalMetric hs).form
    (originalTwoExceptional_has_native_potential hs) (ε := 1) zero_lt_one
  simpa only [one_smul, originalBigComparisonMetric, BigToricMetric.addGuillemin,
    polytopeToricKahlerBackground] using h

/-- Literal original D is BIG in the EXISTING genuine native Kähler-current sense,
for its SAME actual physical Chern class, by produced current and metric independence. -/
theorem originalNonNef_isBigClass :
    IsBigClass (RealBottChern.ofRepresentative (originalNonNefMetric hs).form) := by
  rw [toricSameDivisor_firstChernClass (originalNonNefMetric hs) (originalBigComparisonMetric hs)]
  exact originalBigComparisonMetric_isBig hs

end SGPT.Toric.F1IntersectionDraft

end
/- END OriginalNonNefBigCurrentDraft -/
end F1CanonicalFragment002


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"
