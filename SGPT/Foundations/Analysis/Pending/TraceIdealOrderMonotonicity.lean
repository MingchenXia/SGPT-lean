import SGPT.Foundations.Analysis.Pending.QuasiEquisingularComparison
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed

set_option autoImplicit false

/-! # Ambient multiplier-ideal order produces genuine global trace order -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceIdealOrderMonotonicity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground FirstPass.IEnvelope
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Complete compatible QEAs, actual common geometry, and native order
closure are all produced before comparing the original literal trace readers. -/
theorem sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : V → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u τu)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaV₁ hι v τv)
    (hI : IOrderOnManifold (n := n) u v) : SourcePOrder (n := k) τu τv := by
  have hTuOriginal := hTu
  have hTvOriginal := hTv
  obtain ⟨_, θu, _, _, hU, βu, _, hτu, _, _⟩ := hTu
  obtain ⟨_, θv, _, _, hV, βv, _, hτv, _, _⟩ := hTv
  let B : Bool → ClosedRealOneOneForm n M := fun b => if b then θv else θu
  obtain ⟨S, hS, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omega₀ (fun b : Bool => -(B b))
  let κ : KahlerBackground n M := KahlerBackground.smul hS omega₀
  have hκof (b : Bool) {p : M → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential κ.form.val p := by
    have hform : B b + (-B b + S • omega₀.form) = κ.form := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hdom b)
  have huκ : IsThetaPshPotential κ.form.val u := hκof false hU.target
  have hvκ : IsThetaPshPotential κ.form.val v := hκof true hV.target
  obtain ⟨ε, U, W, hUq, hWq, hmore⟩ :=
    QuasiEquisingularComparison.exists_quasiEquisingularApproximations_moreSingular
      omega₀ κ.form huκ hvκ hI
  obtain ⟨C, hC, hadmC, _⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omega₀ omegaV₀ κ.form hUq.error_antitone
  let T : Bool → ClosedRealOneOneForm k V := fun b => if b then βv.form else βu.form
  obtain ⟨D, hD, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaV₀ (fun b : Bool => C • omegaV₀.form - T b)
  have hCD : 0 < C + D := by linarith
  let γ : KahlerBackground k V := KahlerBackground.smul hCD omegaV₀
  have hγform : (C + D) • omegaV₀.form = γ.form := rfl
  have hγof (b : Bool) {p : V → EReal} (hp : IsThetaPshPotential (T b).val p) :
      IsThetaPshPotential γ.form.val p := by
    have hform : T b + (C • omegaV₀.form - T b + D • omegaV₀.form) = γ.form := by
      rw [← hγform]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hsemi b)
  have hτuγ : IsThetaPshPotential γ.form.val τu := hγof false hτu
  have hτvγ : IsThetaPshPotential γ.form.val τv := hγof true hτv
  have hadmγ : IsAdmissibleTraceBackground hι omega₀ κ.form ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (κ.form + ε j • omega₀.form) =
        (C • omegaV₀.form - ClosedRealOneOneForm.pullback hι (κ.form + ε j • omega₀.form)) +
          D • omegaV₀.form := by
      rw [← hγform]
      module
    change (γ.form - ClosedRealOneOneForm.pullback hι (κ.form + ε j • omega₀.form)).val.IsSemipositive
    rw [hform]
    have hscale := KahlerDomination.isSemipositive_smul omegaV₀.isSemipositive hD.le
    intro e z hz w
    exact add_nonneg (hadmC.dominates j e z hz w) (hscale e z hz w)
  obtain ⟨hUr, hUlim, _⟩ :=
    TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
      omegaV₀ omegaV₀ hι hTuOriginal hUq γ hadmγ hτuγ
  obtain ⟨hWr, hWlim, _⟩ :=
    TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
      omegaV₁ omegaV₀ hι hTvOriginal hWq γ hadmγ hτvγ
  let A : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => U j (ι y), hUr j⟩
  let Z : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => W j (ι y), hWr j⟩
  have horder : ∀ᶠ j in atTop, SourcePOrder (n := k) (A j).val (Z j).val := by
    apply Filter.Eventually.of_forall
    intro j
    obtain ⟨c, hc⟩ := hmore j
    exact sourcePOrder_of_moreSingularOn omegaV₀ γ.form γ.form (hUr j) (hWr j)
      ⟨c, fun y _ => hc (ι y) (mem_univ _)⟩
  exact SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
    omegaV₀ γ.form (isBigClass_kahler γ) atTop A Z ⟨τu, hτuγ⟩ ⟨τv, hτvγ⟩
      hUlim hWlim horder

/-- Ambient equality of all actual positive-level multiplier ideals gives
global equivalence of any two original trace readers. -/
theorem sourcePEquivalent_of_iEquivalent_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : V → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u τu)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaV₁ hι v τv)
    (hI : IEquivalentOnManifold (n := n) u v) : SourcePEquivalent (n := k) τu τv :=
  ⟨sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong omegaV₀ omegaV₁ hι hTu hTv hI.1,
    sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong omegaV₁ omegaV₀ hι hTv hTu hI.2⟩

end

end SGPT.Foundations.Analysis.Pending.TraceIdealOrderMonotonicity
