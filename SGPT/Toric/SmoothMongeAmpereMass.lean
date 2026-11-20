import SGPT.Toric.BigToricMongeAmpere
import SGPT.Hodge.SourceSmoothMixedCohomology
import Lean.Elab.Command

section FsBlowdownCanonicalFragmentToricOriginalSmoothMassDraft
/- BEGIN ToricOriginalSmoothMassDraft; original frozen source SHA256 beca26487951fa0cd19404f8ab096de5bf3fd056ba331d356e3393e919fe09fe -/
/-! Actual original toric zero-potential mass readbacks. All mass objects
are the original source/global non-pluripolar measures and literal integrals. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Projective.FsNormalizationNext

open Set Filter MeasureTheory
open SGPT.Toric SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open scoped BigOperators Topology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
  {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
  {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- Actual semipositive curvature internally makes zero an original toric PSH input. -/
theorem toricSmoothMetric_zero_mem (hsemi : h.form.val.IsSemipositive) :
    (0 : PolytopeToricVariety γ hs → EReal) ∈ h.PSHTor := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  apply (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mpr
  rw [BigToricMetric.atlasForm, sourceNativeAtlasForm_roundTrip]
  exact (LocalPotentials.isThetaPshPotential_zero_iff h.form).mpr hsemi

/-- The actual ALL-competitor original minimal envelope is zero, not a supplied output. -/
theorem toricSmoothMetric_minimalEnvelope_zero (hsemi : h.form.val.IsSemipositive) :
    h.minimalEnvelope = 0 := by
  funext p
  apply le_antisymm (sourceMinimalEnvelope_le_zero h.atlasForm p)
  change (0 : EReal) ≤ ⨆ v : {v : PolytopeToricVariety γ hs → EReal //
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm v ∧ v ≤ 0}, v.1 p
  exact le_iSup (fun v : {v : PolytopeToricVariety γ hs → EReal //
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm v ∧ v ≤ 0} => v.1 p)
    ⟨0, (toricSmoothMetric_zero_mem h hsemi).1, le_rfl⟩

/-- Actual source MA is the SAME genuine smooth integral, for every original background. -/
theorem toricSmoothMetric_zero_MA_eq_nativeIntegral (hsemi : h.form.val.IsSemipositive)
    (κ : KahlerBackground n (PolytopeToricVariety γ hs)) :
    (h.MA (toricSmoothMetric_zero_mem h hsemi)).real univ =
      slotIntegral κ (fun _ : Fin n => h.form) := by
  have h0 : ∀ _ : Fin n, ThetaPlurisubharmonic h.form.val (fun _ => (0 : EReal)) :=
    fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff h.form).mpr hsemi).1
  unfold BigToricMetric.MA sourcePotentialNonPluripolarMeasure diagonalPotentialMeasure
  simp only [BigToricMetric.atlasForm, sourceNativeAtlasForm_roundTrip, slotIntegral]
  convert globalMixedMeasure_real_univ_eq_integral κ (fun _ : Fin n => h.form) h0 using 1
  rfl

/-- The actual zero-potential mass is n! times the SAME original divisor-polytope volume. -/
theorem toricSmoothMetric_zero_MA_univ (hsemi : h.form.val.IsSemipositive)
    (hP : (toricDivisorPolytope D).Nonempty) :
    h.MA (toricSmoothMetric_zero_mem h hsemi) univ =
      (n.factorial : ENNReal) * volume (toricDivisorPolytope D) := by
  have hbody : h.newtonBody (0 : PolytopeToricVariety γ hs → EReal) = toricDivisorPolytope D := by
    simpa only [toricSmoothMetric_minimalEnvelope_zero h hsemi] using
      h.newtonBody_minimalEnvelope hP
  rw [h.MA_univ hP (toricSmoothMetric_zero_mem h hsemi), hbody]

end SGPT.Projective.FsNormalizationNext

end
/- END ToricOriginalSmoothMassDraft -/
end FsBlowdownCanonicalFragmentToricOriginalSmoothMassDraft


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden original private module in actual proper FS/blowdown provider: {m}"
