import SGPT.Trace.SourceTraceRationalScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Trace
open Set Filter
open scoped Topology Manifold ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SourceTraceRepresentativeDefinition DiagonalMass

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

omit [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- Literal pullback respects the original real scalar, with no cohomology
or target-form certificate. -/
theorem sourceTrace_pullback_smul {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (c : ℝ) (θ : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hι (c • θ) = c • ClosedRealOneOneForm.pullback hι θ := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- Every actual positive trace reader scales to an actual positive trace
reader for the rationally scaled current, including ambient dimension zero. -/
theorem hasPositiveSourceTraceAlong_pos_rat_smul
    (omega : KahlerBackground n M) (omegaY : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {r : ℚ} (hr : 0 < r) (hdefined : HasPositiveSourceTraceAlong omega omegaY hι θ u) :
    HasPositiveSourceTraceAlong omega omegaY hι ((r : ℝ) • θ)
      (fun x => ((r : ℝ) : EReal) * u x) := by
  obtain ⟨τ, hT, hτ, hpos⟩ := hdefined
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hτr := RestrictedApproximantComparison.isThetaPshPotential_smul hτ hrR
  have hposr : HasPositivePotentialMass ((r : ℝ) • ClosedRealOneOneForm.pullback hι θ)
      (fun y => ((r : ℝ) : EReal) * τ y) hτr := by
    unfold HasPositivePotentialMass at hpos ⊢
    rw [RestrictedApproximantComparison.diagonalPotentialMass_smul hτ hrR hτr]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hrR k), hpos⟩
  refine ⟨fun y => ((r : ℝ) : EReal) * τ y,
    isSourceTraceRepresentativeAlong_pos_rat_smul omegaY hι hT hr, ?_⟩
  rw [sourceTrace_pullback_smul]
  exact ⟨hτr, hposr⟩

/-- Positive rational scaling preserves and reflects the ORIGINAL defined
normalized-trace domain. The inverse direction constructs the literal
inverse-scaled full reader; no conclusion is supplied by a caller. -/
theorem hasPositiveSourceTraceAlong_pos_rat_smul_iff
    (omega : KahlerBackground n M) (omegaY : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) {r : ℚ} (hr : 0 < r) :
    HasPositiveSourceTraceAlong omega omegaY hι ((r : ℝ) • θ)
        (fun x => ((r : ℝ) : EReal) * u x) ↔
      HasPositiveSourceTraceAlong omega omegaY hι θ u := by
  constructor
  · intro hscaled
    have hinv := hasPositiveSourceTraceAlong_pos_rat_smul omega omegaY hι (inv_pos.mpr hr) hscaled
    have hc : ((r⁻¹ : ℚ) : ℝ) * (r : ℝ) = 1 := by
      exact_mod_cast inv_mul_cancel₀ hr.ne'
    have hform : ((r⁻¹ : ℚ) : ℝ) • ((r : ℝ) • θ) = θ := by
      rw [smul_smul, hc, one_smul]
    have hpot : (fun x => (((r⁻¹ : ℚ) : ℝ) : EReal) * (((r : ℝ) : EReal) * u x)) = u := by
      funext x
      rw [← mul_assoc, ← EReal.coe_mul, hc, EReal.coe_one, one_mul]
    simpa only [hform, hpot] using hinv
  · exact hasPositiveSourceTraceAlong_pos_rat_smul omega omegaY hι hr

variable [CompactSpace M]

/-- The independently defined original source trace mass has its genuine
positive rational homogeneity, including undefined traces, all poles and
ambient/target dimension zero. The full source trace readers and target
PSH/mass scaling are constructed internally from the original domain. -/
theorem sourceTraceMass_pos_rat_smul (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaY : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) {r : ℚ} (hr : 0 < r) :
    sourceTraceMass omega omegaY hι ((r : ℝ) • θ)
        (fun x => ((r : ℝ) : EReal) * u x) =
      ENNReal.ofReal ((r : ℝ) ^ k) * sourceTraceMass omega omegaY hι θ u := by
  by_cases hdefined : HasPositiveSourceTraceAlong omega omegaY hι θ u
  · obtain ⟨τ, hT, hτ, hpos⟩ := hdefined
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hτr0 := RestrictedApproximantComparison.isThetaPshPotential_smul hτ hrR
    have hτr : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι ((r : ℝ) • θ)).val
        (fun y => ((r : ℝ) : EReal) * τ y) := by
      rw [sourceTrace_pullback_smul]
      exact hτr0
    have hscale : diagonalPotentialMass (ClosedRealOneOneForm.pullback hι ((r : ℝ) • θ))
        (fun y => ((r : ℝ) : EReal) * τ y) hτr =
      ENNReal.ofReal ((r : ℝ) ^ k) * diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ := by
      simpa only [sourceTrace_pullback_smul] using
        RestrictedApproximantComparison.diagonalPotentialMass_smul hτ hrR hτr0
    have hposr : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι ((r : ℝ) • θ))
        (fun y => ((r : ℝ) : EReal) * τ y) hτr := by
      unfold HasPositivePotentialMass at hpos ⊢
      rw [hscale]
      exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hrR k), hpos⟩
    rw [sourceTraceMass_eq_of_trace hk omegaY omegaY hι θ u hT hτ hpos,
      sourceTraceMass_eq_of_trace hk omegaY omegaY hι ((r : ℝ) • θ) _
        (isSourceTraceRepresentativeAlong_pos_rat_smul omegaY hι hT hr) hτr hposr]
    exact hscale
  · have hnscaled : ¬ HasPositiveSourceTraceAlong omega omegaY hι ((r : ℝ) • θ)
        (fun x => ((r : ℝ) : EReal) * u x) :=
      fun hscaled => hdefined ((hasPositiveSourceTraceAlong_pos_rat_smul_iff omega omegaY hι θ u hr).mp hscaled)
    simp only [sourceTraceMass, dif_neg hdefined, dif_neg hnscaled, mul_zero]

end SGPT.Trace
