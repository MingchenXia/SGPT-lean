import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.PSH.NativeThetaModificationDescent
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Foundations.Analysis.Pending.BoucksomResolutionStep

/-!
# Extension across analytic sets and pullback of quasi-psh functions along modifications

Source: blueprint nodes `tok:ext-psh-extension` and `tok:zariski-bijection` (chapter
`claude-okounkov-transcendental`), i.e. Demailly, *Complex analytic and differential geometry*,
Theorem I.5.24 (Grauert--Remmert) and DRWNXZ Lemma 2.1 (the book's `prop:PSHpullbij`).

* `thetaPsh_extend_across_analytic` (`tok:ext-psh-extension`): if `A` is a nowhere dense
  analytic subset of a complex manifold `M` and `w` is `θ`-psh on `M \ A` and locally bounded
  above near `A`, then its upper regularization across `A` is `θ`-psh on `M`, agrees with `w` off
  `A`, and is the unique `θ`-psh function with this property. This packages TN's proof of the
  removable singularity theorem (`PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed`, no
  codimension restriction) and its uniqueness statement
  (`AnalyticModificationPotentialDescent.eq_of_eq_off_analytic_set`).
* `thetaPsh_pullback_bijOn`, `singularityLE_comp_iff`, `pushforward_isKahlerCurrentPotential`
  (`tok:zariski-bijection`): for an analytic modification `π : Z → X` (proper bimeromorphic
  holomorphic) from a compact complex manifold, `φ ↦ φ ∘ π` is a bijection
  `PSH(X, θ) → PSH(Z, π^*θ)`, compatible with `⪯` in both directions, and its inverse (the
  pushforward `π_*`) maps Kähler currents to Kähler currents (for `X` Kähler). The descent is
  TN's `exists_descent_of_isAnalyticModification` (itself proved with the extension theorem
  across the analytic set over which `π` is not biholomorphic).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open SGPT.PSH

section Extension

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`θ`-psh functions bounded above extend across analytic sets** (blueprint
`tok:ext-psh-extension`; Demailly CADG I.5.24, Grauert--Remmert). Let `A` be a closed nowhere
dense analytic subset of a complex manifold `M` (an analytic subset with empty interior), `θ` a
closed real `(1,1)`-form, and `w` a function that is `θ`-psh on `M \ A` and locally bounded above
near `A`. Then the upper regularization `w*` of `w` across `A` is `θ`-psh on `M`, `w* = w` off `A`,
and `w*` is the only `θ`-psh function on `M` agreeing with `w` off `A`. -/
theorem thetaPsh_extend_across_analytic (θ : ClosedRealOneOneForm n M)
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hAi : interior A = ∅) {w : M → EReal}
    (hw : ThetaPshOff θ.val A w) (hbd : LocallyBoundedAboveOff A w) :
    ThetaPlurisubharmonic θ.val (extensionAcross A w) ∧
      (∀ x ∉ A, extensionAcross A w x = w x) ∧
      ∀ v : M → EReal, ThetaPlurisubharmonic θ.val v → (∀ x ∉ A, v x = w x) →
        v = extensionAcross A w := by
  have hext : ThetaPlurisubharmonic θ.val (extensionAcross A w) := by
    rcases isEmpty_or_nonempty M with hM | hM
    · intro e z _
      exact (IsEmpty.false (e.val.symm z)).elim
    · have hAne : A ≠ univ := fun h => by
        rw [h, interior_univ] at hAi
        exact univ_nonempty.ne_empty hAi
      exact thetaPlurisubharmonic_extensionAcross_of_localClosure hA.isClosed hw
        (PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed θ A w hA hAne hw hbd)
  have hoff : ∀ x ∉ A, extensionAcross A w x = w x := fun x hx =>
    extensionAcross_eq_of_notMem hA.isClosed hw hx
  refine ⟨hext, hoff, fun v hv hvw => ?_⟩
  funext x
  exact AnalyticModificationPotentialDescent.eq_of_eq_off_analytic_set hA hAi hv hext
    (fun y hy => (hvw y hy).trans (hoff y hy).symm) x

/-- A positive multiple of a Kähler form is Kähler. -/
theorem isKahler_smul {a : ClosedRealOneOneForm n M} (ha : a.val.IsKahler) {c : ℝ}
    (hc : 0 < c) : (c • a).val.IsKahler :=
  ExceptionalMetricProof.isKahler_of_isStrictlyPositive fun e z hz v hv => by
    have h := (ha.1 e z hz).2 v hv
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    exact mul_pos hc h

/-- The Kähler background `c ω` for `c > 0`. -/
def kahlerSmul (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) : KahlerBackground n M :=
  ⟨c • omega.form, isKahler_smul omega.isKahler hc⟩

@[simp] theorem kahlerSmul_form (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) :
    (kahlerSmul omega hc).form = c • omega.form := rfl

end Extension

section Pullback

variable {n : ℕ} {X Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {π : Z → X} (hπ : IsAnalyticModification (n := n) π)

include hπ in
/-- Descent of a `π^*θ`-psh potential along an analytic modification from a compact manifold
(DRWNXZ Lemma 2.1, surjectivity part). -/
theorem exists_descent [CompactSpace Z] (θ : ClosedRealOneOneForm n X) {w : Z → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val w) :
    ∃ φ : X → EReal, IsThetaPshPotential θ.val φ ∧ ∀ z, φ (π z) = w z := by
  let : CompactSpace X := VariableComplexAtlas.compactSpace_of_compact_nativeModification_source hπ
  exact AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hπ θ hw

/-- **Pullback is a bijection on quasi-psh potentials** (blueprint `tok:zariski-bijection`, DRWNXZ
Lemma 2.1, the book's `prop:PSHpullbij`): for an analytic modification `π : Z → X` from a compact
complex manifold, `φ ↦ φ ∘ π` maps `PSH(X, θ)` bijectively onto `PSH(Z, π^*θ)`. -/
theorem thetaPsh_pullback_bijOn [CompactSpace Z] (θ : ClosedRealOneOneForm n X) :
    BijOn (fun φ : X → EReal => fun z => φ (π z)) {φ | IsThetaPshPotential θ.val φ}
      {w | IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val w} := by
  have hs := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  refine ⟨fun φ hφ =>
      AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ θ hφ,
    fun φ _ ψ _ h => ?_, fun w hw => ?_⟩
  · funext x
    obtain ⟨z, rfl⟩ := hs x
    exact congrFun h z
  · obtain ⟨φ, hφ, hφw⟩ := exists_descent hπ θ hw
    exact ⟨φ, hφ, funext hφw⟩

include hπ in
/-- The pullback is compatible with the singularity order in both directions:
`π^*φ ⪯ π^*ψ ↔ φ ⪯ ψ`. -/
theorem singularityLE_comp_iff {φ ψ : X → EReal} :
    SingularityLE (fun z => φ (π z)) (fun z => ψ (π z)) ↔ SingularityLE φ ψ := by
  have hs := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  constructor
  · intro h
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp h
    refine (singularityLE_iff_exists_real _ _).mpr ⟨C, fun x => ?_⟩
    obtain ⟨z, rfl⟩ := hs x
    exact hC z
  · intro h
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp h
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C, fun z => hC (π z)⟩

/-- **The pushforward of a Kähler current is a Kähler current** (blueprint `tok:zariski-bijection`,
last clause): if `X` is compact Kähler, `φ ∈ PSH(X, θ)` and `π^*θ + dd^c(φ ∘ π)` is a Kähler current
on `Z`, then `θ + dd^c φ` is a Kähler current on `X`. (If `π^*θ + dd^c v ≥ ε ω_Z` and
`π^*ω ≤ C ω_Z`, then `v ∈ PSH(Z, π^*(θ - (ε/C) ω))`, so `π_* v ∈ PSH(X, θ - (ε/C) ω)`.) -/
theorem pushforward_isKahlerCurrentPotential [CompactSpace Z] (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hK : IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.1 θ) (fun z => φ (π z))) :
    IsKahlerCurrentPotential θ φ := by
  have hs := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  obtain ⟨κ, hκ⟩ := hK
  -- `π^*ω ≤ A κ`
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ
    (-(ClosedRealOneOneForm.pullback hπ.1 omega.form))
  have hδ : 0 < A⁻¹ := inv_pos.mpr hA
  -- `κ - A⁻¹ π^*ω` is semipositive
  have hsemi' :
      (κ.form - A⁻¹ • ClosedRealOneOneForm.pullback hπ.1 omega.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hsemi hδ.le
    have heq : A⁻¹ • (-(ClosedRealOneOneForm.pullback hπ.1 omega.form) + A • κ.form) =
        κ.form - A⁻¹ • ClosedRealOneOneForm.pullback hπ.1 omega.form := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [heq] at h
  -- `φ ∘ π` is `π^*(θ - A⁻¹ ω)`-psh
  have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hκ hsemi'
  have hform : ClosedRealOneOneForm.pullback hπ.1 θ - κ.form +
      (κ.form - A⁻¹ • ClosedRealOneOneForm.pullback hπ.1 omega.form) =
      ClosedRealOneOneForm.pullback hπ.1 (θ - (kahlerSmul omega hδ).form) := by
    rw [BoucksomResolutionStep.pullback_sub, kahlerSmul_form,
      show A⁻¹ • omega.form = (0 : ClosedRealOneOneForm n X) + A⁻¹ • omega.form by rw [zero_add],
      NefCoreKahlerCurrent.pullback_add_smul,
      show ClosedRealOneOneForm.pullback hπ.1 (0 : ClosedRealOneOneForm n X) = 0 by
        apply ClosedRealOneOneForm.ext; intro e z; ext v; rfl]
    abel
  rw [hform] at h1
  obtain ⟨v, hv, hvφ⟩ := exists_descent hπ _ h1
  have hveq : v = φ := by
    funext x
    obtain ⟨z, rfl⟩ := hs x
    exact hvφ z
  exact ⟨kahlerSmul omega hδ, hveq ▸ hv⟩

end Pullback

end SGPT.Okounkov.TranscendentalLifting
