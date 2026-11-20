import SGPT.Trace.SourceTraceMassRationalHomogeneity

set_option autoImplicit false
noncomputable section
namespace SGPT.Trace
open Set Filter
open scoped Topology Manifold ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- The actual integral perturbation N*theta+omega with potential N*u
has N^dim(Y) times the actual rational perturbation's source trace mass.
This includes undefined traces and dimension0; literal full rational trace
readers, pulled forms and genuine non-pluripolar mass homogeneity prove it. -/
theorem sourceTraceMass_integral_perturbation (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaY : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (N : ℕ) (hN : 0 < N) :
    sourceTraceMass omega omegaY hι ((N : ℝ) • θ + omega.form)
        (fun x => ((N : ℝ) : EReal) * u x) =
      ENNReal.ofReal ((N : ℝ) ^ k) *
        sourceTraceMass omega omegaY hι (θ + (N : ℝ)⁻¹ • omega.form) u := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hform : (N : ℝ) • (θ + (N : ℝ)⁻¹ • omega.form) = (N : ℝ) • θ + omega.form := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hNR,one_smul]
  have hmass := sourceTraceMass_pos_rat_smul hk omega omegaY hι
    (θ + (N : ℝ)⁻¹ • omega.form) u (r := (N : ℚ)) (by exact_mod_cast hN)
  simpa only [Rat.cast_natCast,hform] using hmass

end SGPT.Trace
