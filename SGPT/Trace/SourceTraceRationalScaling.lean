import SGPT.Trace.TraceMass
import SGPT.Okounkov.SourceTraceOperations
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeRationalScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Trace
open Set Filter
open scoped Topology Manifold ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
open SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy DiagonalMass

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Rational analytic scaling and actual native scalar equivalence supply
all fields of the literally scaled full reader, including admissibility. -/
theorem isSourceTraceRepresentativeAlong_pos_rat_smul
    {omega : KahlerBackground n M} (omegaY : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : Y → EReal}
    (hT : IsSourceTraceRepresentativeAlong omega omegaY hι u τ)
    {r : ℚ} (hr : 0 < r) :
    IsSourceTraceRepresentativeAlong omega omegaY hι
      (fun x => ((r : ℝ) : EReal) * u x) (fun y => ((r : ℝ) : EReal) * τ y) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨hg, θ, ε, U, hu, β, hadm, hτ, hU, hlim⟩ := hT
  have hgr : sourceGenericLelongNumber (n := n) ι
      (fun x => ((r : ℝ) : EReal) * u x) = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul ι u hrR, hg, mul_zero]
  let βr : KahlerBackground k Y := KahlerBackground.smul hrR β
  have hτr : IsThetaPshPotential βr.form.val (fun y => ((r : ℝ) : EReal) * τ y) :=
    RestrictedApproximantComparison.isThetaPshPotential_smul hτ hrR
  have hUr (j : ℕ) : IsThetaPshPotential βr.form.val
      (fun y => ((r : ℝ) : EReal) * U j (ι y)) :=
    RestrictedApproximantComparison.isThetaPshPotential_smul (hU j) hrR
  have hpull (a : ClosedRealOneOneForm n M) :
      ClosedRealOneOneForm.pullback hι ((r : ℝ) • a) =
        (r : ℝ) • ClosedRealOneOneForm.pullback hι a := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl
  have hform (j : ℕ) : βr.form - ClosedRealOneOneForm.pullback hι
      ((r : ℝ) • θ + ((r : ℝ) * ε j) • omega.form) =
      (r : ℝ) • (β.form - ClosedRealOneOneForm.pullback hι
        (θ + ε j • omega.form)) := by
    have heq : (r : ℝ) • θ + ((r : ℝ) * ε j) • omega.form =
        (r : ℝ) • (θ + ε j • omega.form) := by module
    rw [heq, hpull]
    dsimp only [βr, KahlerBackground.smul_form]
    module
  have hadmr : IsAdmissibleTraceBackground hι omega ((r : ℝ) • θ)
      (fun j => (r : ℝ) * ε j) βr.form := by
    refine ⟨βr.isKahler, fun j => ?_⟩
    change (βr.form - ClosedRealOneOneForm.pullback hι
      ((r : ℝ) • θ + ((r : ℝ) * ε j) • omega.form)).val.IsSemipositive
    rw [hform]
    exact KahlerDomination.isSemipositive_smul (hadm.2 j) hrR.le
  have hlimr := (SingularCanonicalSingularityScalarEquivalence.tendsto_native_positive_smul_iff
    omegaY β.form (isBigClass_kahler β) hrR atTop
    (fun j => (⟨fun y => U j (ι y), hU j⟩ : ThetaPshL1 β.form.val))
    (⟨τ, hτ⟩ : ThetaPshL1 β.form.val)).mpr hlim
  exact ⟨hgr, (r : ℝ) • θ, (fun j => (r : ℝ) * ε j),
    (fun j x => ((r : ℝ) : EReal) * U j x),
    QuasiEquisingularRationalScaling.isQuasiEquisingularApproximation_pos_rat_smul hu hr,
    βr, hadmr, hτr, hUr, hlimr⟩

end SGPT.Trace
