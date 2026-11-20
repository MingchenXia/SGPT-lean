import SGPT.PSH.BookCurrentPositivity
import SGPT.Okounkov.ThetaPotentialCurrentSingularity
import SGPT.PSH.SingularityOrder
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.PSH.VariableLelong
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

/-!
# The space of closed positive `(1,1)`-currents

Source: `chapter_pshfunctions.tex`, section `sec:currents`: `def:psefclass`, `def:spaceofcurrents`,
`def:pshfunctions:L1594`, `rmk:qpshtocurrents`, `ex:Lelongcurrent` (the convention
`ν(T, x) = ν(φ, x)`), `def:polarlocus`.  Proofs: Xia, *Foundations of pluripotential theory*,
`q07` (global potentials of closed positive currents, `dd^c`-lemma).

`X` is a compact complex manifold of positive dimension `m + 1` (TN's native holomorphic atlas;
the book's standing assumptions "connected" and "Kähler" are not needed for the definitions).
A closed `(1,1)`-current is TN's `ClosedOneOneCurrent` (closed real currents of degree two and
type `(1,1)`); its cohomology class `{T}` is TN's Bott–Chern class map `bottChernClass` into
`RealBottChern (m+1) X`, the space `H^{1,1}(X, ℝ)` of the project (closed real `(1,1)`-forms
modulo `dd^c` of smooth functions; on compact Kähler manifolds this is `H^{1,1}(X, ℝ)` by the
`∂∂̄`-lemma).  Positivity is the source weak positivity `IsPositiveCurrent` (`def:pos_curr`).

## Main results

* `ClosedPositiveCurrent m X` (`𝒵₊(X)`), `currentClass` (`{T}`), `ClosedPositiveCurrentIn α`
  (`𝒵₊(X, α)`).
* `IsPseudoeffective`, `IsKahlerCurrent`, `IsBig`, `ClassLE` (`def:psefclass` and the order of
  classes after it); `isPseudoeffective_iff_classPseudoeffectiveViaPotentials`,
  `isBig_iff_isBigClass` identify them with TN's potential-presented notions.
* `IsPresentation`, `exists_presentation` (every `T ∈ 𝒵₊(X)` is `θ + dd^c φ`, `φ ∈ PSH(X, θ)`),
  `singularityEquiv_of_isPresentation` (two potentials of `T` have the same singularity type).
* `MoreSingular`, `SameSingularityType` (`def:pshfunctions:L1594`) and their independence of the
  presentations.
* `QPSH`, `currentQPSHEquiv` (`rmk:qpshtocurrents`: `𝒵₊(X)/∼ ≃ QPSH(X)/∼`, sending the class of
  `θ + dd^c φ` to the class of `φ`).
* `currentLelong` (`ν(T, x) = ν(φ, x)`, `ex:Lelongcurrent`), `polarLocus` (`def:polarlocus`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions ENNReal

namespace SGPT.PSH.BookCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
open SGPT.PSH.VariableComplexAtlas
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-! ### `𝒵₊(X)` -/

variable (m X) in
/-- **`𝒵₊(X)`** (`def:spaceofcurrents` (1)): the closed positive `(1,1)`-currents on `X`. -/
def ClosedPositiveCurrent : Type _ :=
  {T : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m) //
    IsPositiveCurrent 1 (degreeTwo_val_eq m) T.val}

namespace ClosedPositiveCurrent

/-- The underlying current. -/
def current (T : ClosedPositiveCurrent m X) :
    GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)) := T.val.val

theorem ext {S T : ClosedPositiveCurrent m X} (h : S.current = T.current) : S = T :=
  Subtype.ext (Subtype.ext h)

theorem isClosed (T : ClosedPositiveCurrent m X) :
    T.current.IsClosed (canonicalBasis (m + 1)) := T.val.property.1

theorem isTypeOneOne (T : ClosedPositiveCurrent m X) :
    T.current.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) := T.val.property.2

theorem isPositive (T : ClosedPositiveCurrent m X) :
    IsPositiveCurrent 1 (degreeTwo_val_eq m) T.current := T.property

end ClosedPositiveCurrent

/-- The current `θ + dd^c u` of a `θ`-psh function, as an element of `𝒵₊(X)`. -/
def thetaPositiveCurrent (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) : ClosedPositiveCurrent m X :=
  ⟨thetaClosedCurrent θ u hu,
    isPositiveCurrent_of_isFullPositive _ (thetaPotentialCurrent_full_positive θ.val u hu)⟩

@[simp] theorem thetaPositiveCurrent_current (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    (thetaPositiveCurrent θ u hu).current = thetaPotentialCurrent θ.val u hu := rfl

/-! ### Presentations `T = θ + dd^c φ` -/

/-- `T = θ + dd^c u` with `u ∈ PSH(X, θ)`. -/
def IsPresentation (T : ClosedPositiveCurrent m X) (θ : ClosedRealOneOneForm (m + 1) X)
    (u : X → EReal) : Prop :=
  ∃ hu : IsThetaPshPotential θ.val u, T.current = thetaPotentialCurrent θ.val u hu

theorem isPresentation_thetaPositiveCurrent (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) : IsPresentation (thetaPositiveCurrent θ u hu) θ u :=
  ⟨hu, rfl⟩

theorem IsPresentation.isThetaPsh {T : ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal} (h : IsPresentation T θ u) :
    IsThetaPshPotential θ.val u := h.1

/-- **Two presentations of the same current have potentials of the same singularity type**
(the potentials differ by a smooth function). -/
theorem singularityEquiv_of_isPresentation [CompactSpace X] {T : ClosedPositiveCurrent m X}
    {θ θ' : ClosedRealOneOneForm (m + 1) X} {u u' : X → EReal}
    (h : IsPresentation T θ u) (h' : IsPresentation T θ' u') : SingularityEquiv u u' := by
  obtain ⟨hu, hT⟩ := h
  obtain ⟨hu', hT'⟩ := h'
  exact SGPT.Okounkov.sameSingularity_of_thetaPotentialCurrent_eq hu hu' (hT.symm.trans hT')

/-- Near every point two potentials of the same current differ by a continuous real function,
pointwise (including the poles). -/
theorem exists_local_difference_of_isPresentation {T : ClosedPositiveCurrent m X}
    {θ θ' : ClosedRealOneOneForm (m + 1) X} {u u' : X → EReal}
    (h : IsPresentation T θ u) (h' : IsPresentation T θ' u') (p : X) :
    ∃ (O : Set X) (g : X → ℝ), IsOpen O ∧ p ∈ O ∧ ContinuousOn g O ∧
      EqOn u (fun y => u' y + (g y : EReal)) O := by
  obtain ⟨hu, hT⟩ := h
  obtain ⟨hu', hT'⟩ := h'
  exact SGPT.Okounkov.exists_local_smooth_difference_of_thetaPotentialCurrent_eq hu hu'
    (hT.symm.trans hT') p

variable [CompactSpace X]

/-- **Every closed positive `(1,1)`-current has a presentation** `T = θ + dd^c φ` with
`φ ∈ PSH(X, θ)` (the `dd^c`-lemma). -/
theorem exists_presentation (T : ClosedPositiveCurrent m X) :
    ∃ (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal), IsPresentation T θ u := by
  obtain ⟨θ, u, hu, h⟩ := exists_theta_representation_of_isPositiveCurrent T.current
    T.isClosed T.isTypeOneOne T.isPositive
  exact ⟨θ, u, hu, h⟩

/-- A chosen presentation form. -/
def presentationForm (T : ClosedPositiveCurrent m X) : ClosedRealOneOneForm (m + 1) X :=
  Classical.choose (exists_presentation T)

/-- A chosen presentation potential. -/
def presentationPotential (T : ClosedPositiveCurrent m X) : X → EReal :=
  Classical.choose (Classical.choose_spec (exists_presentation T))

theorem isPresentation_presentation (T : ClosedPositiveCurrent m X) :
    IsPresentation T (presentationForm T) (presentationPotential T) :=
  Classical.choose_spec (Classical.choose_spec (exists_presentation T))

/-! ### Classes of currents (`def:spaceofcurrents`, `def:psefclass`) -/

/-- The cohomology class `{T} ∈ H^{1,1}(X, ℝ)` of a closed positive current. -/
def currentClass (T : ClosedPositiveCurrent m X) : RealBottChern (m + 1) X :=
  bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T.val

theorem IsPresentation.currentClass_eq {T : ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal} (h : IsPresentation T θ u) :
    currentClass T = RealBottChern.ofRepresentative θ := by
  obtain ⟨hu, hT⟩ := h
  have : T.val = thetaClosedCurrent θ u hu := Subtype.ext hT
  rw [currentClass, this, bottChernClass_thetaClosedCurrent]

@[simp] theorem currentClass_thetaPositiveCurrent (θ : ClosedRealOneOneForm (m + 1) X)
    (u : X → EReal) (hu : IsThetaPshPotential θ.val u) :
    currentClass (thetaPositiveCurrent θ u hu) = RealBottChern.ofRepresentative θ :=
  (isPresentation_thetaPositiveCurrent θ u hu).currentClass_eq

variable (m X) in
/-- **`𝒵₊(X, α)`** (`def:spaceofcurrents` (2)): the currents `T ∈ 𝒵₊(X)` with `{T} = α`. -/
def ClosedPositiveCurrentIn (α : RealBottChern (m + 1) X) : Type _ :=
  {T : ClosedPositiveCurrent m X // currentClass T = α}

/-- **Pseudo-effective classes** (`def:psefclass`): `α` contains a closed positive
`(1,1)`-current. -/
def IsPseudoeffective (α : RealBottChern (m + 1) X) : Prop :=
  ∃ T : ClosedPositiveCurrent m X, currentClass T = α

/-- **Kähler currents** (`def:psefclass`): closed positive currents dominating a Kähler form,
`T ≥ ω`, i.e. `T - ω` is positive. -/
def IsKahlerCurrent (T : ClosedPositiveCurrent m X) : Prop :=
  ∃ κ : KahlerBackground (m + 1) X, IsPositiveCurrent 1 (degreeTwo_val_eq m)
    (T.current - (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) κ.form).val)

/-- **Big classes** (`def:psefclass`): `α` contains a Kähler current. -/
def IsBig (α : RealBottChern (m + 1) X) : Prop :=
  ∃ T : ClosedPositiveCurrent m X, currentClass T = α ∧ IsKahlerCurrent T

/-- The order of classes after `def:psefclass`: `α ≤ β` if `β - α` is pseudo-effective. -/
def ClassLE (α β : RealBottChern (m + 1) X) : Prop :=
  IsPseudoeffective (β - α)

theorem isPseudoeffective_iff_nonempty (α : RealBottChern (m + 1) X) :
    IsPseudoeffective α ↔ Nonempty (ClosedPositiveCurrentIn m X α) :=
  ⟨fun ⟨T, hT⟩ => ⟨⟨T, hT⟩⟩, fun ⟨T⟩ => ⟨T.1, T.2⟩⟩

/-- The source definition agrees with TN's potential-presented pseudo-effectivity. -/
theorem isPseudoeffective_iff_classPseudoeffectiveViaPotentials (α : RealBottChern (m + 1) X) :
    IsPseudoeffective α ↔ ClassPseudoeffectiveViaPotentials α := by
  constructor
  · rintro ⟨T, rfl⟩
    obtain ⟨θ, u, h⟩ := exists_presentation T
    rw [h.currentClass_eq, classPseudoeffectiveViaPotentials_ofRepresentative]
    exact ⟨u, h.isThetaPsh⟩
  · refine Quotient.inductionOn α ?_
    intro θ hθ
    obtain ⟨u, hu⟩ := hθ
    exact ⟨thetaPositiveCurrent θ u hu, currentClass_thetaPositiveCurrent θ u hu⟩

omit [CompactSpace X] in
private theorem smoothFormDistribution_add' (σ τ : ClosedRealOneOneForm (m + 1) X)
    (e : ComplexChart (m + 1) X) :
    smoothFormDistribution (canonicalBasis (m + 1)) (σ + τ).val e =
      smoothFormDistribution (canonicalBasis (m + 1)) σ.val e +
        smoothFormDistribution (canonicalBasis (m + 1)) τ.val e := by
  ext v φ
  have hσ : Integrable (fun z => φ z • σ.val.coeff e z) (canonicalBasis (m + 1)).addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable (canonicalBasis (m + 1)) σ.val e)
  have hτ : Integrable (fun z => φ z • τ.val.coeff e z) (canonicalBasis (m + 1)).addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable (canonicalBasis (m + 1)) τ.val e)
  rw [AlternatingMap.add_apply, add_apply, smoothFormDistribution_apply,
    smoothFormDistribution_apply, smoothFormDistribution_apply]
  simp only [ClosedRealOneOneForm.coeff_add, smul_add]
  rw [integral_add hσ hτ]
  rfl

omit [CompactSpace X] in
/-- `[σ + τ] = [σ] + [τ]` for the smooth currents of closed forms. -/
theorem smoothGlobalCurrent_add (σ τ : ClosedRealOneOneForm (m + 1) X) :
    GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
        (k := degreeTwo (Nat.succ_pos m)) (σ + τ).val =
      GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
          (k := degreeTwo (Nat.succ_pos m)) σ.val +
        GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
          (k := degreeTwo (Nat.succ_pos m)) τ.val := by
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  rw [GlobalCurrent.coefficients_add, coefficients_smoothGlobalCurrent,
    coefficients_smoothGlobalCurrent, coefficients_smoothGlobalCurrent,
    smoothFormDistribution_add']

/-- The source bigness agrees with TN's bigness (existence of a potential-presented Kähler
current `θ + dd^c u`, `u ∈ PSH(X, θ - ω)`). -/
theorem isBig_iff_isBigClass (α : RealBottChern (m + 1) X) : IsBig α ↔ IsBigClass α := by
  constructor
  · rintro ⟨T, rfl, κ, hpos⟩
    let C := smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) κ.form
    let S : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
      T.val + (-1 : ℝ) • C
    have hS : S.val = T.current - C.val := by
      change T.current + (-1 : ℝ) • C.val = _
      module
    let S' : ClosedPositiveCurrent m X := ⟨S, by rw [hS]; exact hpos⟩
    obtain ⟨σ, u, h⟩ := exists_presentation S'
    have hclass : currentClass S' = currentClass T - RealBottChern.ofRepresentative κ.form := by
      change bottChernClassLinearMap (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (T.val + (-1 : ℝ) • C) = _
      rw [map_add, map_smul, neg_one_smul, ← sub_eq_add_neg]
      change currentClass T - bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) C = _
      rw [bottChernClass_smoothClosedCurrent]
    refine ⟨⟨σ + κ.form, ?_, u, κ, ?_⟩⟩
    · rw [RealBottChern.ofRepresentative_add, ← h.currentClass_eq, hclass, sub_add_cancel]
    · rw [add_sub_cancel_right]
      exact h.isThetaPsh
  · rintro ⟨K⟩
    set σ : ClosedRealOneOneForm (m + 1) X := K.representative - K.lowerBound.form with hσ
    have hu : IsThetaPshPotential K.representative.val K.potential := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive K.strictlyPsh
        K.lowerBound.isSemipositive
      rwa [sub_add_cancel] at h
    refine ⟨thetaPositiveCurrent K.representative K.potential hu, ?_, K.lowerBound, ?_⟩
    · rw [currentClass_thetaPositiveCurrent, K.represents]
    · have hrep : K.representative = σ + K.lowerBound.form := by rw [hσ, sub_add_cancel]
      have hcur : (thetaPositiveCurrent K.representative K.potential hu).current -
          (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) K.lowerBound.form).val =
          thetaPotentialCurrent σ.val K.potential K.strictlyPsh := by
        rw [thetaPositiveCurrent_current]
        unfold thetaPotentialCurrent
        change GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
            (k := degreeTwo (Nat.succ_pos m)) K.representative.val + _ -
          GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
            (k := degreeTwo (Nat.succ_pos m)) K.lowerBound.form.val = _
        have hsm : GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
              (k := degreeTwo (Nat.succ_pos m)) K.representative.val =
            GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
                (k := degreeTwo (Nat.succ_pos m)) σ.val +
              GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
                (k := degreeTwo (Nat.succ_pos m)) K.lowerBound.form.val := by
          rw [← smoothGlobalCurrent_add, ← hrep]
        rw [hsm]
        abel
      rw [hcur]
      exact isPositiveCurrent_of_isFullPositive _
        (thetaPotentialCurrent_full_positive σ.val K.potential K.strictlyPsh)

/-! ### The singularity preorder on `𝒵₊(X)` (`def:pshfunctions:L1594`) -/

/-- **`T ⪯ T'`** (`T` is more singular than `T'`): whenever `T = θ + dd^c φ` and
`T' = θ' + dd^c φ'`, `φ ⪯ φ'` (`def:parorder`). -/
def MoreSingular (T T' : ClosedPositiveCurrent m X) : Prop :=
  ∀ (θ θ' : ClosedRealOneOneForm (m + 1) X) (u u' : X → EReal),
    IsPresentation T θ u → IsPresentation T' θ' u' → SingularityLE u u'

/-- **`T ∼ T'`**: same singularity type. -/
def SameSingularityType (T T' : ClosedPositiveCurrent m X) : Prop :=
  MoreSingular T T' ∧ MoreSingular T' T

/-- Well-definedness: the condition holds for all presentations iff it holds for one. -/
theorem moreSingular_iff_of_isPresentation {T T' : ClosedPositiveCurrent m X}
    {θ θ' : ClosedRealOneOneForm (m + 1) X} {u u' : X → EReal}
    (h : IsPresentation T θ u) (h' : IsPresentation T' θ' u') :
    MoreSingular T T' ↔ SingularityLE u u' := by
  refine ⟨fun hT => hT θ θ' u u' h h', fun hle ψ ψ' v v' hv hv' => ?_⟩
  have h1 := (singularityEquiv_of_isPresentation hv h).1
  have h2 := (singularityEquiv_of_isPresentation h' hv').1
  exact singularityLE_trans h1 (singularityLE_trans hle h2)

theorem moreSingular_iff_exists {T T' : ClosedPositiveCurrent m X} :
    MoreSingular T T' ↔ ∃ (θ θ' : ClosedRealOneOneForm (m + 1) X) (u u' : X → EReal),
      IsPresentation T θ u ∧ IsPresentation T' θ' u' ∧ SingularityLE u u' := by
  constructor
  · intro hT
    obtain ⟨θ, u, h⟩ := exists_presentation T
    obtain ⟨θ', u', h'⟩ := exists_presentation T'
    exact ⟨θ, θ', u, u', h, h', hT θ θ' u u' h h'⟩
  · rintro ⟨θ, θ', u, u', h, h', hle⟩
    exact (moreSingular_iff_of_isPresentation h h').mpr hle

theorem sameSingularityType_iff_of_isPresentation {T T' : ClosedPositiveCurrent m X}
    {θ θ' : ClosedRealOneOneForm (m + 1) X} {u u' : X → EReal}
    (h : IsPresentation T θ u) (h' : IsPresentation T' θ' u') :
    SameSingularityType T T' ↔ SingularityEquiv u u' := by
  rw [SameSingularityType, moreSingular_iff_of_isPresentation h h',
    moreSingular_iff_of_isPresentation h' h, singularityEquiv_iff]

theorem moreSingular_refl (T : ClosedPositiveCurrent m X) : MoreSingular T T := by
  obtain ⟨θ, u, h⟩ := exists_presentation T
  exact (moreSingular_iff_of_isPresentation h h).mpr (singularityLE_refl u)

theorem moreSingular_trans {T T' T'' : ClosedPositiveCurrent m X}
    (h₁ : MoreSingular T T') (h₂ : MoreSingular T' T'') : MoreSingular T T'' := by
  obtain ⟨θ, u, h⟩ := exists_presentation T
  obtain ⟨θ', u', h'⟩ := exists_presentation T'
  obtain ⟨θ'', u'', h''⟩ := exists_presentation T''
  exact (moreSingular_iff_of_isPresentation h h'').mpr
    (singularityLE_trans (h₁ θ θ' u u' h h') (h₂ θ' θ'' u' u'' h' h''))

variable (m X) in
/-- The singularity-type equivalence on `𝒵₊(X)`. -/
def currentSetoid : Setoid (ClosedPositiveCurrent m X) where
  r := SameSingularityType
  iseqv := ⟨fun T => ⟨moreSingular_refl T, moreSingular_refl T⟩, fun h => ⟨h.2, h.1⟩,
    fun h₁ h₂ => ⟨moreSingular_trans h₁.1 h₂.1, moreSingular_trans h₂.2 h₁.2⟩⟩

/-! ### `𝒵₊(X)/∼ ≃ QPSH(X)/∼` (`rmk:qpshtocurrents`) -/

omit [CompactSpace X] in
theorem isQPSH_iff_exists_native (u : X → EReal) :
    (ofFixedModel (m + 1) X).IsQPSH u ↔
      ∃ θ : ClosedRealOneOneForm (m + 1) X, IsThetaPshPotential θ.val u := by
  constructor
  · rintro ⟨θ, hθ⟩
    exact ⟨atlasClosedFormToNative θ, (isThetaPSH_iff_nativeThetaPotential θ u).mp hθ⟩
  · rintro ⟨θ, hθ⟩
    refine ⟨nativeClosedFormToAtlas θ, (isThetaPSH_iff_nativeThetaPotential _ u).mpr ?_⟩
    have hinv : atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
      rcases θ with ⟨θ, hθ⟩
      cases θ
      rfl
    rwa [hinv]

variable (m X) in
/-- `QPSH(X)` (`def:qpsh`, the verified source definition on the native atlas). -/
def QPSH : Type _ := {u : X → EReal // (ofFixedModel (m + 1) X).IsQPSH u}

variable (m X) in
/-- The singularity-type equivalence on `QPSH(X)`. -/
def qpshSetoid : Setoid (QPSH m X) where
  r u v := SingularityEquiv u.1 v.1
  iseqv := ⟨fun u => singularityEquiv_refl u.1, singularityEquiv_symm, singularityEquiv_trans⟩

omit [CompactSpace X] in
theorem QPSH.exists_form (u : QPSH m X) :
    ∃ θ : ClosedRealOneOneForm (m + 1) X, IsThetaPshPotential θ.val u.1 :=
  (isQPSH_iff_exists_native u.1).mp u.2

/-- The potential of a current, as an element of `QPSH(X)`. -/
def potentialQPSH (T : ClosedPositiveCurrent m X) : QPSH m X :=
  ⟨presentationPotential T, (isQPSH_iff_exists_native _).mpr
    ⟨presentationForm T, (isPresentation_presentation T).isThetaPsh⟩⟩

/-- A current with prescribed potential `u ∈ QPSH(X)`. -/
def qpshCurrent (u : QPSH m X) : ClosedPositiveCurrent m X :=
  thetaPositiveCurrent (Classical.choose u.exists_form) u.1 (Classical.choose_spec u.exists_form)

omit [CompactSpace X] in
theorem isPresentation_qpshCurrent (u : QPSH m X) :
    IsPresentation (qpshCurrent u) (Classical.choose u.exists_form) u.1 :=
  isPresentation_thetaPositiveCurrent _ _ _

/-- **`𝒵₊(X)/∼ ≃ QPSH(X)/∼`** (`rmk:qpshtocurrents`), the class of `θ + dd^c φ` going to the
class of `φ`. -/
def currentQPSHEquiv :
    Quotient (currentSetoid m X) ≃ Quotient (qpshSetoid m X) where
  toFun := Quotient.map potentialQPSH fun T T' hTT' =>
    (sameSingularityType_iff_of_isPresentation (isPresentation_presentation T)
      (isPresentation_presentation T')).mp hTT'
  invFun := Quotient.map qpshCurrent fun u v huv =>
    (sameSingularityType_iff_of_isPresentation (isPresentation_qpshCurrent u)
      (isPresentation_qpshCurrent v)).mpr huv
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h T =>
      apply Quotient.sound
      exact (sameSingularityType_iff_of_isPresentation
        (isPresentation_qpshCurrent (potentialQPSH T)) (isPresentation_presentation T)).mpr
        (singularityEquiv_refl _)
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h u =>
      apply Quotient.sound
      exact singularityEquiv_of_isPresentation
        (isPresentation_presentation (qpshCurrent u)) (isPresentation_qpshCurrent u)

/-- The correspondence sends the class of `θ_φ = θ + dd^c φ` to the class of `φ`. -/
theorem currentQPSHEquiv_mk (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    currentQPSHEquiv (Quotient.mk (currentSetoid m X) (thetaPositiveCurrent θ u hu)) =
      Quotient.mk (qpshSetoid m X) ⟨u, (isQPSH_iff_exists_native u).mpr ⟨θ, hu⟩⟩ := by
  apply Quotient.sound
  exact singularityEquiv_of_isPresentation
    (isPresentation_presentation (thetaPositiveCurrent θ u hu))
    (isPresentation_thetaPositiveCurrent θ u hu)

/-! ### Lelong numbers and polar loci of currents -/

/-- **`ν(T, x) = ν(φ, x)`** (`ex:Lelongcurrent`, `eq:convnuTx`) for `T = θ + dd^c φ`, with the
verified source Lelong number `sourceLelong` (`def:pshfunctions:L1002`). -/
def currentLelong (T : ClosedPositiveCurrent m X) (x : X) : ℝ≥0∞ :=
  (ofFixedModel (m + 1) X).sourceLelong (presentationPotential T) x

/-- The convention is independent of the presentation `T = θ + dd^c φ`. -/
theorem currentLelong_eq_of_isPresentation {T : ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal} (h : IsPresentation T θ u) (x : X) :
    currentLelong T x = (ofFixedModel (m + 1) X).sourceLelong u x := by
  obtain ⟨hu, hT⟩ := h
  obtain ⟨hv, hT'⟩ := isPresentation_presentation T
  rw [currentLelong, sourceLelong_ofFixedModel_eq, sourceLelong_ofFixedModel_eq]
  exact congrFun (SGPT.Okounkov.squaredLogLelongNumber_eq_of_thetaPotentialCurrent_eq hv hu
    (hT'.symm.trans hT)) x

/-- **The polar locus** of `T = θ + dd^c φ` (`def:polarlocus`): `{φ = -∞}`. -/
def polarLocus (T : ClosedPositiveCurrent m X) : Set X :=
  {x | presentationPotential T x = ⊥}

/-- The polar locus is independent of the presentation (the source's "it is clear"). -/
theorem polarLocus_eq_of_isPresentation {T : ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal} (h : IsPresentation T θ u) :
    polarLocus T = {x | u x = ⊥} := by
  ext x
  obtain ⟨O, g, _hO, hxO, _hg, heq⟩ :=
    exists_local_difference_of_isPresentation (isPresentation_presentation T) h x
  change presentationPotential T x = ⊥ ↔ u x = ⊥
  rw [heq hxO]
  exact EReal.add_eq_bot_iff.trans (by simp)

end SGPT.PSH.BookCurrent
