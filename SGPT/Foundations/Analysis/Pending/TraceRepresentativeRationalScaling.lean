import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityScalarEquivalence
import SGPT.Foundations.Analysis.Pending.LelongNumberScaling

set_option autoImplicit false


/-! # Genuine full trace readers under positive rational scaling -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeRationalScaling

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Rational analytic scaling and actual native scalar equivalence supply
all fields of the literally scaled full reader, including admissibility. -/
theorem isTraceRepresentativeAlong_pos_rat_smul
    {omega : KahlerBackground n M} (omegaY : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : Y → EReal}
    (hT : IsTraceRepresentativeAlong omega omegaY hι u τ)
    {r : ℚ} (hr : 0 < r) :
    IsTraceRepresentativeAlong omega omegaY hι
      (fun x => ((r : ℝ) : EReal) * u x) (fun y => ((r : ℝ) : EReal) * τ y) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨hg, θ, ε, U, hu, β, hadm, hτ, hU, hlim⟩ := hT
  have hgr : (⨅ y : Y, lelongNumber (n := n)
      (fun x => ((r : ℝ) : EReal) * u x) (ι y)) = 0 := by
    apply le_antisymm _ bot_le
    calc
      (⨅ y : Y, lelongNumber (n := n) (fun x => ((r : ℝ) : EReal) * u x) (ι y)) ≤
          ⨅ y : Y, ENNReal.ofReal (r : ℝ) * lelongNumber (n := n) u (ι y) :=
        iInf_mono fun y => LelongNumberScaling.lelongNumber_smul_le hrR
      _ = ENNReal.ofReal (r : ℝ) * ⨅ y : Y, lelongNumber (n := n) u (ι y) :=
        (ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hrR).ne'
          ENNReal.ofReal_ne_top).symm
      _ = 0 := by rw [hg, mul_zero]
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

variable [CompactSpace M]

/-- Any actual reader of the rationally scaled target has the produced
scaled reader's global class, for all original auxiliary choices. -/
theorem sourcePEquivalent_pos_rat_smul_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaY₀ omegaY₁ : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ τr : Y → EReal}
    (hT : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τ)
    {r : ℚ} (hr : 0 < r)
    (hTr : IsTraceRepresentativeAlong omega₁ omegaY₁ hι
      (fun x => ((r : ℝ) : EReal) * u x) τr) :
    SourcePEquivalent (n := k) τr (fun y => ((r : ℝ) : EReal) * τ y) := by
  exact TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaY₁ omegaY₀ hι hTr (isTraceRepresentativeAlong_pos_rat_smul omegaY₀ hι hT hr)

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeRationalScaling
