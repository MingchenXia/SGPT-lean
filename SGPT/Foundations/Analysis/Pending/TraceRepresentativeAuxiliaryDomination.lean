import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAuxiliaryDomination
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Actual trace readers under auxiliary Kähler domination -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeAuxiliaryDomination

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Auxiliary domination reconstructs actual target admissibility and
candidate PSH data before transporting the original defining native limit. -/
theorem isTraceRepresentativeAlong_of_auxiliary_domination
    {omega κ : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ)
    (hsemi : (κ.form - omega.form).val.IsSemipositive) :
    IsTraceRepresentativeAlong κ omegaV hι u τ := by
  obtain ⟨hg, θ, ε, uSeq, happ, β₀, _, hτ₀, hv₀, hlim₀⟩ := htrace
  have happκ :=
    QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
      happ hsemi
  obtain ⟨C, hC, hadmC, _⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι κ omegaV θ happκ.error_antitone
  obtain ⟨D, hD, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul
    omegaV (C • omegaV.form - β₀.form)
  have hCD : 0 < C + D := by linarith
  let γ : KahlerBackground k V := KahlerBackground.smul hCD omegaV
  have hγof {p : V → EReal} (hp : IsThetaPshPotential β₀.form.val p) :
      IsThetaPshPotential γ.form.val p := by
    have hform : β₀.form + (C • omegaV.form - β₀.form + D • omegaV.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp hdom
  have hvγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => uSeq j (ι y)) :=
    hγof (hv₀ j)
  have hτγ : IsThetaPshPotential γ.form.val τ := hγof hτ₀
  have hadmγ : IsAdmissibleTraceBackground hι κ θ ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    change (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • κ.form)).val.IsSemipositive
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • κ.form) =
        (C • omegaV.form - ClosedRealOneOneForm.pullback hι (θ + ε j • κ.form)) +
          D • omegaV.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    rw [hform]
    have hscaled := KahlerDomination.isSemipositive_smul omegaV.isSemipositive hD.le
    intro e z hz v
    exact add_nonneg (hadmC.2 j e z hz v) (hscaled e z hz v)
  have hlimγ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β₀ γ atTop hv₀ hτ₀ hvγ hτγ).mp hlim₀
  exact ⟨hg, θ, ε, uSeq, happκ, γ, hadmγ, hτγ, hvγ, hlimγ⟩

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeAuxiliaryDomination
