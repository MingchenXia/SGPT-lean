import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAddition
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.SingularNativeAdditionContinuity

set_option autoImplicit false

/-! # Actual trace addition with a natural reader of the ambient sum -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeAddition

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  MixedSummandCapacityDomination GlobalMultilinearExpansion

noncomputable section

private theorem genuineAdd {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h


variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Natural original readers and the actual sum domain produce a full additive reader. -/
theorem isTraceRepresentativeAlong_add
    {omega₀ omega₁ : KahlerBackground n M} (omegaY₀ omegaY₁ omegaY : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τᵤ τᵥ : Y → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τᵤ)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaY₁ hι v τᵥ)
    (hgsum : (⨅ y : Y, lelongNumber (n := n) (fun x => u x + v x) (ι y)) = 0) :
    ∃ omega : KahlerBackground n M,
      IsTraceRepresentativeAlong omega omegaY hι
        (fun x => u x + v x) (fun y => τᵤ y + τᵥ y) := by
  have hTuKeep := hTu
  have hTvKeep := hTv
  obtain ⟨_, θ, ε, U, hu, βᵤ, _, hτᵤ, _, _⟩ := hTu
  obtain ⟨_, σ, δ, V, hv, βᵥ, _, hτᵥ, _, _⟩ := hTv
  obtain ⟨omega, hω₀, hω₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background omega₀ omega₁
  have huω := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hu hω₀
  have hvω := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hv hω₁
  have hsum := QuasiEquisingularAddition.isQuasiEquisingularApproximation_add huω hvω
  let B : Bool × Bool → ClosedRealOneOneForm k Y := fun b =>
    if b.1 then if b.2 then ClosedRealOneOneForm.pullback hι (σ + δ 0 • omega.form)
      else ClosedRealOneOneForm.pullback hι (θ + ε 0 • omega.form)
    else if b.2 then βᵥ.form else βᵤ.form
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaY (fun b : Bool × Bool => -(B b))
  let γ : KahlerBackground k Y := KahlerBackground.smul hC omegaY
  have hγgap (b : Bool × Bool) : (γ.form - B b).val.IsSemipositive := by
    have hform : γ.form - B b = -B b + C • omegaY.form := by
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
  have hadmU : IsAdmissibleTraceBackground hι omega θ ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
        (γ.form - B (true, false)) +
          (ε 0 - ε j) • ClosedRealOneOneForm.pullback hι omega.form := by
      change γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
        (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε 0 • omega.form)) +
          (ε 0 - ε j) • ClosedRealOneOneForm.pullback hι omega.form
      simp only [NefCoreKahlerCurrent.pullback_add_smul]
      module
    change (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)).val.IsSemipositive
    rw [hform]
    intro e z hz w
    exact add_nonneg (hγgap (true, false) e z hz w)
      (KahlerDomination.isSemipositive_smul hpull
        (sub_nonneg.mpr (hu.error_antitone (Nat.zero_le j))) e z hz w)
  have hadmV : IsAdmissibleTraceBackground hι omega σ δ γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (σ + δ j • omega.form) =
        (γ.form - B (true, true)) +
          (δ 0 - δ j) • ClosedRealOneOneForm.pullback hι omega.form := by
      change γ.form - ClosedRealOneOneForm.pullback hι (σ + δ j • omega.form) =
        (γ.form - ClosedRealOneOneForm.pullback hι (σ + δ 0 • omega.form)) +
          (δ 0 - δ j) • ClosedRealOneOneForm.pullback hι omega.form
      simp only [NefCoreKahlerCurrent.pullback_add_smul]
      module
    change (γ.form - ClosedRealOneOneForm.pullback hι (σ + δ j • omega.form)).val.IsSemipositive
    rw [hform]
    intro e z hz w
    exact add_nonneg (hγgap (true, true) e z hz w)
      (KahlerDomination.isSemipositive_smul hpull
        (sub_nonneg.mpr (hv.error_antitone (Nat.zero_le j))) e z hz w)
  obtain ⟨hU, hlimU, _⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    omegaY₀ omegaY hι hTuKeep huω γ hadmU hτᵤγ
  obtain ⟨hV, hlimV, _⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    omegaY₁ omegaY hι hTvKeep hvω γ hadmV hτᵥγ
  let βsum : KahlerBackground k Y := ⟨γ.form + γ.form, by
    have hzero : (γ.form + (0 : ℝ) • γ.form).val.IsSemipositive := by
      simpa only [zero_smul, add_zero] using γ.isSemipositive
    simpa only [zero_add, one_smul] using KahlerDomination.isKahler_add_smul_succ γ hzero⟩
  have hτsum : IsThetaPshPotential βsum.form.val (fun y => τᵤ y + τᵥ y) :=
    genuineAdd hτᵤγ hτᵥγ
  have hW (j : ℕ) : IsThetaPshPotential βsum.form.val (fun y => U j (ι y) + V j (ι y)) :=
    genuineAdd (hU j) (hV j)
  have hlimW := SingularNativeAdditionContinuity.tendsto_native_add
    omegaY γ.form γ.form (isBigClass_kahler γ) (isBigClass_kahler γ) atTop
    (fun j => (⟨fun y => U j (ι y), hU j⟩ : ThetaPshL1 γ.form.val))
    (fun j => (⟨fun y => V j (ι y), hV j⟩ : ThetaPshL1 γ.form.val))
    (⟨τᵤ, hτᵤγ⟩ : ThetaPshL1 γ.form.val) (⟨τᵥ, hτᵥγ⟩ : ThetaPshL1 γ.form.val)
    hlimU hlimV
  have hadmSum : IsAdmissibleTraceBackground hι omega (θ + σ)
      (fun j => ε j + δ j) βsum.form := by
    refine ⟨βsum.isKahler, fun j => ?_⟩
    have hform : θ + σ + (ε j + δ j) • omega.form =
        (θ + ε j • omega.form) + (σ + δ j • omega.form) := by module
    have hpadd : ClosedRealOneOneForm.pullback hι
        ((θ + ε j • omega.form) + (σ + δ j • omega.form)) =
        ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) +
          ClosedRealOneOneForm.pullback hι (σ + δ j • omega.form) := by
      apply ClosedRealOneOneForm.ext
      intro e z
      ext w
      rfl
    have hdiff : βsum.form - ClosedRealOneOneForm.pullback hι
        (θ + σ + (ε j + δ j) • omega.form) =
        (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)) +
          (γ.form - ClosedRealOneOneForm.pullback hι (σ + δ j • omega.form)) := by
      rw [hform, hpadd]
      change (γ.form + γ.form) -
          (ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) +
            ClosedRealOneOneForm.pullback hι (σ + δ j • omega.form)) = _
      module
    change (βsum.form - ClosedRealOneOneForm.pullback hι
      (θ + σ + (ε j + δ j) • omega.form)).val.IsSemipositive
    rw [hdiff]
    intro e z hz w
    exact add_nonneg (hadmU.2 j e z hz w) (hadmV.2 j e z hz w)
  exact ⟨omega, hgsum, θ + σ, (fun j => ε j + δ j),
    (fun j x => U j x + V j x), hsum, βsum, hadmSum, hτsum, hW, hlimW⟩

/-- The ambient-sum reader supplies only its natural domain condition;
all additive candidate-reader and class conclusions are internally produced. -/
theorem sourcePEquivalent_add_of_isTraceRepresentativeAlong
    {omega₀ omega₁ omega₂ : KahlerBackground n M}
    (omegaY₀ omegaY₁ omegaY₂ : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τᵤ τᵥ τs : Y → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τᵤ)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaY₁ hι v τᵥ)
    (hTs : IsTraceRepresentativeAlong omega₂ omegaY₂ hι (fun x => u x + v x) τs) :
    SourcePEquivalent (n := k) τs (fun y => τᵤ y + τᵥ y) := by
  obtain ⟨omega, hadd⟩ := isTraceRepresentativeAlong_add
    omegaY₀ omegaY₁ omegaY₀ hι hTu hTv hTs.1
  exact TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaY₂ omegaY₀ hι hTs hadd

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeAddition
