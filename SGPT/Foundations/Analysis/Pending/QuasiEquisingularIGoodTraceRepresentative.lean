import SGPT.Foundations.Analysis.Pending.AnalyticAntitoneIGoodLimit
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback

set_option autoImplicit false

/-! # A genuine approximation internally produces an I-good trace representative -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularIGoodTraceRepresentative

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  FirstPass.IEnvelope TraceRepresentativeConstruction

noncomputable section

variable {k : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The actual full approximation and holomorphic target geometry internally
produce one trace reader, its admissible background, positive model, and I-goodness. -/
theorem exists_iGood_traceRepresentative_of_quasiEquisingularApproximation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ τ : V → EReal, IsTraceRepresentativeAlong omega omegaV hι u τ ∧
      ∃ β : KahlerBackground k V,
        IsAdmissibleTraceBackground hι omega θ ε β.form ∧
        ∃ hτ : IsModelPotential β.form τ,
          IGoodWith β.form τ hτ.plurisubharmonic := by
  obtain ⟨C, -, hadm, hterms, δ, hδ, hbound⟩ :=
    AnalyticRestrictedApproximantUniformMass.exists_admissible_background_uniform_positive_restricted_mass
      omegaV happ hι hgeneric
  let β : KahlerBackground k V := ⟨C • omegaV.form, hadm.1⟩
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k)
      (fun y => uSeq j (ι y)) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
      hι (happ.term_hasAnalyticSingularityType j)
  have hanti : Antitone (fun j y => uSeq j (ι y)) := fun i j hij y =>
    happ.term_antitone (ι y) hij
  obtain ⟨hτ, hI, hlim⟩ :=
    AnalyticAntitoneIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      omegaV β hterms hA hanti hδ hbound
  let τ : V → EReal := ⨅ j, singularityEnvelope β.form.val (fun y => uSeq j (ι y))
  refine ⟨τ, ?_, β, hadm, hτ, hI⟩
  exact ⟨hgeneric, θ, ε, uSeq, happ, β, hadm, hτ.plurisubharmonic, hterms, hlim⟩

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularIGoodTraceRepresentative
