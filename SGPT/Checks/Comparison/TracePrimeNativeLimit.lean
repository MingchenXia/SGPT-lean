import SGPT.PSH.CompactPrimeNumerical

/-! SAME original prime readers on the ACTUAL native singularity topology.
Blueprint: `trace-res-prime-limit.tex`. No finite-tower/target Kähler premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open ThetaPshL1Topology SingularCanonicalSingularityDistance DemaillyApproximantDivisorialLelong
open SquaredLogLelongSourceNormalization
open scoped Topology ENNReal

/-- The ACTUAL native dS limit gives convergence of the SAME original
source prime reader on every genuine original prime presentation. -/
theorem tendsto_presentationReader_of_native
    {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    (p : PrimePresentation n M) :
    Tendsto (fun i => presentationReader (w i).val p) F (𝓝 (presentationReader u.val p)) := by
  cases n with
  | zero => have hp := p.dimension_pos; omega
  | succ m =>
    have hread (a : M → EReal) : presentationReader a p =
        (2 : ℝ≥0∞)⁻¹ * divisorialLelongNumber m (a ∘ p.projection) p.divisor := by
      simp only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq]
      rw [divisorialLelongNumber, iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
      exact (ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)).symm
    have hnative := AnalyticModificationNativeLelongLimit.tendsto_divisorialLelongNumber_comp_of_native
      omega θ hbig p.modification F w u hlim p.divisor
    have hcont : Continuous (fun a : ℝ≥0∞ => (2 : ℝ≥0∞)⁻¹ * a) :=
      ENNReal.continuous_const_mul (by norm_num)
    simpa only [Function.comp_def, hread] using
      (hcont.tendsto (divisorialLelongNumber m (u.val ∘ p.projection) p.divisor)).comp hnative

end SGPT.NAPotential.TraceComparison
