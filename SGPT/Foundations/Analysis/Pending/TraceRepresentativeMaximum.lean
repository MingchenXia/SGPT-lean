import SGPT.Foundations.Analysis.Pending.QuasiEquisingularTwoPotentialMaximum
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.SingularNativeMaximumContinuity

set_option autoImplicit false

/-! # Actual full trace representatives preserve maxima -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeMaximum

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]


/-- Actual auxiliary domination, full maximum approximation, and native
maximum continuity produce every field of the maximum reader predicate. -/
theorem isTraceRepresentativeAlong_max
    {omega₀ omega₁ : KahlerBackground n M} (omegaY₀ omegaY₁ omegaY : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τᵤ τᵥ : Y → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τᵤ)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaY₁ hι v τᵥ) :
    ∃ omega : KahlerBackground n M,
      IsTraceRepresentativeAlong omega omegaY hι
        (fun x => max (u x) (v x)) (fun y => max (τᵤ y) (τᵥ y)) := by
  have hTuKeep := hTu
  have hTvKeep := hTv
  obtain ⟨hgu, θ₀, ε, U, hu, βᵤ, _, hτᵤ, _, _⟩ := hTu
  obtain ⟨_, θ₁, δ, V, hv, βᵥ, _, hτᵥ, _, _⟩ := hTv
  obtain ⟨omega, hω₀, hω₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background omega₀ omega₁
  have huω := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hu hω₀
  have hvω := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hv hω₁
  let A : Bool → ClosedRealOneOneForm n M := fun b => if b then θ₁ else θ₀
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omega (fun b : Bool => -(A b))
  let κ : KahlerBackground n M := KahlerBackground.smul hC omega
  have hκgap (b : Bool) : (κ.form - A b).val.IsSemipositive := by
    have hform : κ.form - A b = -A b + C • omega.form := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [hform] using hsemi b
  have huκ : IsQuasiEquisingularApproximation omega κ.form u ε U :=
    QuasiEquisingularBackgroundDomination.isQuasiEquisingularApproximation_of_background_domination
      huω (hκgap false)
  have hvκ : IsQuasiEquisingularApproximation omega κ.form v δ V :=
    QuasiEquisingularBackgroundDomination.isQuasiEquisingularApproximation_of_background_domination
      hvω (hκgap true)
  have hw := QuasiEquisingularTwoPotentialMaximum.isQuasiEquisingularApproximation_max_two_potentials
    huκ hvκ
  have hgw : (⨅ y : Y, lelongNumber (n := n) (fun x => max (u x) (v x)) (ι y)) = 0 := by
    apply le_antisymm _ bot_le
    have hle : (⨅ y : Y, lelongNumber (n := n) (fun x => max (u x) (v x)) (ι y)) ≤
        ⨅ y : Y, lelongNumber (n := n) u (ι y) := by
      exact iInf_mono fun y => KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall fun x => le_max_left (u x) (v x))
    exact hle.trans_eq hgu
  let r : ℝ := max (ε 0) (δ 0)
  let B : Bool × Bool → ClosedRealOneOneForm k Y := fun b =>
    if b.1 then ClosedRealOneOneForm.pullback hι (κ.form + r • omega.form)
    else if b.2 then βᵥ.form else βᵤ.form
  obtain ⟨D, hD, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaY (fun b : Bool × Bool => -(B b))
  let γ : KahlerBackground k Y := KahlerBackground.smul hD omegaY
  have hγgap (b : Bool × Bool) : (γ.form - B b).val.IsSemipositive := by
    have hform : γ.form - B b = -B b + D • omegaY.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using hdom b
  have hγof (b : Bool × Bool) {p : Y → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential γ.form.val p := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hγgap b)
  have hτᵤγ : IsThetaPshPotential γ.form.val τᵤ := hγof (false, false) hτᵤ
  have hτᵥγ : IsThetaPshPotential γ.form.val τᵥ := hγof (false, true) hτᵥ
  have hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hι omega.isSemipositive
  have hstagegap (t : ℝ) (ht : t ≤ r) :
      (γ.form - ClosedRealOneOneForm.pullback hι (κ.form + t • omega.form)).val.IsSemipositive := by
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (κ.form + t • omega.form) =
        (γ.form - B (true, false)) +
          (r - t) • ClosedRealOneOneForm.pullback hι omega.form := by
      change γ.form - ClosedRealOneOneForm.pullback hι (κ.form + t • omega.form) =
        (γ.form - ClosedRealOneOneForm.pullback hι (κ.form + r • omega.form)) +
          (r - t) • ClosedRealOneOneForm.pullback hι omega.form
      simp only [NefCoreKahlerCurrent.pullback_add_smul]
      module
    rw [hform]
    intro e z hz w
    exact add_nonneg (hγgap (true, false) e z hz w)
      (KahlerDomination.isSemipositive_smul hpull (sub_nonneg.mpr ht) e z hz w)
  have hadmU : IsAdmissibleTraceBackground hι omega κ.form ε γ.form :=
    ⟨γ.isKahler, fun j => hstagegap (ε j)
      ((hu.error_antitone (Nat.zero_le j)).trans (le_max_left _ _))⟩
  have hadmV : IsAdmissibleTraceBackground hι omega κ.form δ γ.form :=
    ⟨γ.isKahler, fun j => hstagegap (δ j)
      ((hv.error_antitone (Nat.zero_le j)).trans (le_max_right _ _))⟩
  have hadmW : IsAdmissibleTraceBackground hι omega κ.form
      (fun j => max (ε j) (δ j)) γ.form :=
    ⟨γ.isKahler, fun j => hstagegap (max (ε j) (δ j))
      (max_le_max (hu.error_antitone (Nat.zero_le j)) (hv.error_antitone (Nat.zero_le j)))⟩
  obtain ⟨hU, hlimU, _⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    omegaY₀ omegaY hι hTuKeep huκ γ hadmU hτᵤγ
  obtain ⟨hV, hlimV, _⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    omegaY₁ omegaY hι hTvKeep hvκ γ hadmV hτᵥγ
  have hτW : IsThetaPshPotential γ.form.val (fun y => max (τᵤ y) (τᵥ y)) :=
    IsThetaPshPotential.max hτᵤγ hτᵥγ
  have hW (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => max (U j (ι y)) (V j (ι y))) :=
    IsThetaPshPotential.max (hU j) (hV j)
  have hlimW := SingularNativeMaximumContinuity.tendsto_native_max
    omegaY γ.form (isBigClass_kahler γ) atTop
    (fun j => (⟨fun y => U j (ι y), hU j⟩ : ThetaPshL1 γ.form.val))
    (fun j => (⟨fun y => V j (ι y), hV j⟩ : ThetaPshL1 γ.form.val))
    (⟨τᵤ, hτᵤγ⟩ : ThetaPshL1 γ.form.val) (⟨τᵥ, hτᵥγ⟩ : ThetaPshL1 γ.form.val)
    hlimU hlimV
  exact ⟨omega, hgw, κ.form, (fun j => max (ε j) (δ j)),
    (fun j x => max (U j x) (V j x)), hw, γ, hadmW, hτW, hW, hlimW⟩


/-- The same literal maximum target has globally equivalent readers with
every original ambient and target auxiliary choice. -/
theorem sourcePEquivalent_max_of_isTraceRepresentativeAlong
    {omega₀ omega₁ omega₂ : KahlerBackground n M}
    (omegaY₀ omegaY₁ omegaY₂ : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τᵤ τᵥ τw : Y → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τᵤ)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaY₁ hι v τᵥ)
    (hTw : IsTraceRepresentativeAlong omega₂ omegaY₂ hι
      (fun x => max (u x) (v x)) τw) :
    SourcePEquivalent (n := k) τw (fun y => max (τᵤ y) (τᵥ y)) := by
  obtain ⟨omega, hmax⟩ := isTraceRepresentativeAlong_max
    omegaY₀ omegaY₁ omegaY₀ hι hTu hTv
  exact TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaY₂ omegaY₀ hι hTw hmax

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeMaximum
