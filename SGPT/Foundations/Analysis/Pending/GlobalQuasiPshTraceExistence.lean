import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

set_option autoImplicit false

/-! # Actual trace existence for genuine global quasi-PSH potentials -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshTraceExistence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  TraceRepresentativeConstruction

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [TopologicalSpace V]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Actual Demailly approximation data internally supply a trace of
every genuine closed-background potential with zero generic infimum. -/
theorem exists_of_isThetaPshPotential
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ τ : V → EReal, IsTraceRepresentativeAlong omega omegaV hι u τ ∧
      ∃ β : KahlerBackground k V, IsModelPotential β.form τ := by
  obtain ⟨ε, uSeq, happ⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega θ hu
  exact exists_of_quasiEquisingularApproximation omegaV happ hι hgeneric

/-- Compact genuine global quasi-PSH geometry internally supplies
both an ambient closed background and all actual trace data. -/
theorem exists_of_globalQuasiPshPotential
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ τ : V → EReal, IsTraceRepresentativeAlong omega omegaV hι u τ ∧
      ∃ β : KahlerBackground k V, IsModelPotential β.form τ := by
  obtain ⟨C, hC, hCu⟩ :=
    GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul omega hu
  exact exists_of_isThetaPshPotential omega omegaV hCu hι hgeneric

end

end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshTraceExistence
