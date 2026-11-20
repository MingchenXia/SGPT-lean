import SGPT.Siu.SiuDecompositionBook
import SGPT.Siu.SiuDecompositionGeneric
import SGPT.PSH.BookCurrentLoci
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

/-!
# Lelong numbers of pseudo-effective classes along prime divisors

Source: `def:mult_class` (chapter *Plurisubharmonic functions*), Boucksom's minimal multiplicity:
for a pseudo-effective class `α ∈ H^{1,1}(X, ℝ)` and a prime divisor `D`,

1. if `α` is big, `ν(α, D) = ν(T, D)` for any closed positive current `T ∈ α` with minimal
   singularities;
2. in general, `ν(α, D) = lim_{ε → 0+} ν(α + ε{ω}, D)`.

* `minimalGenericLelong α D`: `ν(T_min, D)`; `minimalGenericLelong_eq` shows that it equals
  `ν(T, D)` for **every** current `T` with minimal singularities in `α` (well-definedness of 1).
* `classGenericLelong ω α D`: the book's two-clause definition.
* `minimalGenericLelong_kahler_antitone`: `ε ↦ ν(α + ε{ω}, D)` is antitone on `(0, ∞)`, and
  `tendsto_classGenericLelong`: for a pseudo-effective class which is not big, the limit in 2
  exists and equals `classGenericLelong ω α D = sup_{ε > 0} ν(α + ε{ω}, D)` (well-definedness
  of 2).
* `classGenericLelong_le_of_isBig`: for big `α`, `ν(α + ε{ω}, D) ≤ ν(α, D)` for all `ε > 0`
  (one half of the compatibility of 2 with 1 claimed after the definition).
* `iSup_minimalGenericLelong_kahler_eq`: the limit in 2 does not depend on the Kähler form `ω`
  (the claim after the definition, for the second clause).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass CanonicalCurrentFrame
open SGPT.PSH.BookCurrent

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m + 1) X
local notation "bookLelong" => SGPT.PSH.BookCurrent.currentLelong

/-! ### Minimal singularities -/

/-- `ν(T_min, D)` for the currents `T_min` with minimal singularities in `α` (clause 1 of
`def:mult_class`). -/
def minimalGenericLelong (α : RealBottChern (m + 1) X) (D : Prime) : ℝ≥0∞ :=
  ⨅ (T : ClosedPositiveCurrent m X) (_ : IsMinimalSingularities α T), bookGenericLelong T D

/-- **Clause 1 is well defined**: `ν(T, D)` is the same for every current `T` with minimal
singularities in `α`. -/
theorem minimalGenericLelong_eq {α : RealBottChern (m + 1) X} {T : ClosedPositiveCurrent m X}
    (hT : IsMinimalSingularities α T) (D : Prime) :
    minimalGenericLelong α D = bookGenericLelong T D := by
  apply le_antisymm (iInf₂_le T hT)
  refine le_iInf₂ fun T' hT' => le_of_eq ?_
  unfold bookGenericLelong
  congr 1
  funext x
  congr 1
  funext _
  exact currentLelong_eq_of_sameSingularityType (hT.sameSingularityType hT') x

/-- A more singular current has larger Lelong numbers. -/
theorem currentLelong_le_of_moreSingular {T T' : ClosedPositiveCurrent m X}
    (h : MoreSingular T T') (x : X) : bookLelong T' x ≤ bookLelong T x := by
  obtain ⟨θ, u, hu⟩ := exists_presentation T
  obtain ⟨θ', u', hu'⟩ := exists_presentation T'
  rw [currentLelong_eq_of_isPresentation hu, currentLelong_eq_of_isPresentation hu']
  exact sourceLelong_le_of_singularityLE ((moreSingular_iff_of_isPresentation hu hu').mp h) x

/-- Adding a smooth closed semipositive form `σ` to a closed positive current gives a closed
positive current in `{T} + {σ}` with the same Lelong numbers. -/
theorem exists_add_semipositive (T : ClosedPositiveCurrent m X) {σ : ClosedRealOneOneForm (m + 1) X}
    (hσ : σ.val.IsSemipositive) :
    ∃ T' : ClosedPositiveCurrent m X,
      currentClass T' = currentClass T + RealBottChern.ofRepresentative σ ∧
        ∀ x, bookLelong T' x = bookLelong T x := by
  obtain ⟨θ, u, hu⟩ := exists_presentation T
  have hu' := LocalPotentials.isThetaPshPotential_add_of_semipositive hu.isThetaPsh hσ
  refine ⟨thetaPositiveCurrent (θ + σ) u hu', ?_, fun x => ?_⟩
  · rw [currentClass_thetaPositiveCurrent, RealBottChern.ofRepresentative_add,
      hu.currentClass_eq]
  · rw [currentLelong_eq_of_isPresentation (isPresentation_thetaPositiveCurrent _ _ hu'),
      currentLelong_eq_of_isPresentation hu]

theorem bookGenericLelong_mono {T T' : ClosedPositiveCurrent m X}
    (h : ∀ x, bookLelong T x ≤ bookLelong T' x) (D : Prime) :
    bookGenericLelong T D ≤ bookGenericLelong T' D :=
  iInf₂_mono fun x _ => h x

variable [ConnectedSpace X]

/-- Minimal singularities: if `α + {σ}` with `σ` semipositive, then
`ν((α + {σ})_min, D) ≤ ν(α_min, D)`. -/
theorem minimalGenericLelong_add_semipositive_le {α : RealBottChern (m + 1) X}
    (hα : IsPseudoeffective α) {σ : ClosedRealOneOneForm (m + 1) X} (hσ : σ.val.IsSemipositive)
    (D : Prime) :
    minimalGenericLelong (α + RealBottChern.ofRepresentative σ) D ≤ minimalGenericLelong α D := by
  obtain ⟨T, hT⟩ := exists_minimalSingularities hα
  obtain ⟨T'', hT''cl, hT''ν⟩ := exists_add_semipositive T hσ
  have hpsef : IsPseudoeffective (α + RealBottChern.ofRepresentative σ) :=
    ⟨T'', by rw [hT''cl, hT.1]⟩
  obtain ⟨T', hT'⟩ := exists_minimalSingularities hpsef
  rw [minimalGenericLelong_eq hT, minimalGenericLelong_eq hT']
  have hmore : MoreSingular T'' T' := hT'.2 T'' (by rw [hT''cl, hT.1])
  exact bookGenericLelong_mono (fun x => (currentLelong_le_of_moreSingular hmore x).trans
    (hT''ν x).le) D

omit [ConnectedSpace X] in
theorem isPseudoeffective_add_kahler {α : RealBottChern (m + 1) X} (hα : IsPseudoeffective α)
    (ω : KahlerBackground (m + 1) X) {ε : ℝ} (hε : 0 ≤ ε) :
    IsPseudoeffective (α + ε • RealBottChern.ofRepresentative ω.form) := by
  obtain ⟨T, hT⟩ := hα
  obtain ⟨T', hT'cl, -⟩ := exists_add_semipositive T
    (RestrictedMassEnvelopeMonotone.kahler_smul_isSemipositive ω hε)
  exact ⟨T', by rw [hT'cl, hT, RealBottChern.ofRepresentative_smul]⟩

/-- `ε ↦ ν(α + ε{ω}, D)` is antitone on `(0, ∞)`. -/
theorem minimalGenericLelong_kahler_antitone {α : RealBottChern (m + 1) X}
    (hα : IsPseudoeffective α) (ω : KahlerBackground (m + 1) X) (D : Prime) {ε ε' : ℝ}
    (hε : 0 ≤ ε) (hεε' : ε ≤ ε') :
    minimalGenericLelong (α + ε' • RealBottChern.ofRepresentative ω.form) D ≤
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D := by
  have h := minimalGenericLelong_add_semipositive_le (isPseudoeffective_add_kahler hα ω hε)
    (RestrictedMassEnvelopeMonotone.kahler_smul_isSemipositive ω (sub_nonneg.mpr hεε')) D
  have heq : α + ε • RealBottChern.ofRepresentative ω.form +
      RealBottChern.ofRepresentative ((ε' - ε) • ω.form) =
        α + ε' • RealBottChern.ofRepresentative ω.form := by
    rw [RealBottChern.ofRepresentative_smul, add_assoc, ← add_smul, add_sub_cancel]
  rwa [heq] at h

/-! ### The Lelong number of a class -/

open Classical in
/-- **The Lelong number `ν(α, D)` of a pseudo-effective class along a prime divisor**
(`def:mult_class`): `ν(T_min, D)` if `α` is big, and `lim_{ε → 0+} ν(α + ε{ω}, D)` in general
(the limit exists and is the supremum, `tendsto_classGenericLelong`). -/
def classGenericLelong (ω : KahlerBackground (m + 1) X) (α : RealBottChern (m + 1) X)
    (D : Prime) : ℝ≥0∞ :=
  if IsBig α then minimalGenericLelong α D
  else ⨆ (ε : ℝ) (_ : 0 < ε), minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D

/-- The supremum over `ε > 0` of an antitone function on `(0, ∞)` is its limit at `0+`. -/
theorem tendsto_iSup_of_antitoneOn {f : ℝ → ℝ≥0∞}
    (hf : ∀ ε ε', 0 < ε → ε ≤ ε' → f ε' ≤ f ε) :
    Tendsto f (𝓝[>] 0) (𝓝 (⨆ (ε : ℝ) (_ : 0 < ε), f ε)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨ε₀, hε₀, hb'⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ b < f ε₀ := by
      by_contra hcon
      push Not at hcon
      exact absurd (iSup₂_le hcon) (not_le.mpr hb)
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact hb'.trans_le (hf ε ε₀ hε.1 hε.2.le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (le_iSup₂ (f := fun ε (_ : 0 < ε) => f ε) ε hε).trans_lt hb

/-- **Clause 2 is well defined**: for a pseudo-effective class `α` which is not big,
`ν(α + ε{ω}, D) → ν(α, D)` as `ε → 0+`. -/
theorem tendsto_classGenericLelong {α : RealBottChern (m + 1) X} (hα : IsPseudoeffective α)
    (hnb : ¬ IsBig α) (ω : KahlerBackground (m + 1) X) (D : Prime) :
    Tendsto (fun ε : ℝ => minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D)
      (𝓝[>] 0) (𝓝 (classGenericLelong ω α D)) := by
  rw [classGenericLelong, if_neg hnb]
  exact tendsto_iSup_of_antitoneOn fun ε ε' hε hεε' =>
    minimalGenericLelong_kahler_antitone hα ω D hε.le hεε'

/-- For big `α`, `ν(α + ε{ω}, D) ≤ ν(α, D)` for every `ε ≥ 0`. -/
theorem classGenericLelong_le_of_isBig {α : RealBottChern (m + 1) X} (hα : IsBig α)
    (ω : KahlerBackground (m + 1) X) (D : Prime) {ε : ℝ} (hε : 0 ≤ ε) :
    minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D ≤
      classGenericLelong ω α D := by
  rw [classGenericLelong, if_pos hα]
  have hpsef : IsPseudoeffective α := by
    obtain ⟨T, hT, -⟩ := hα
    exact ⟨T, hT⟩
  have h := minimalGenericLelong_add_semipositive_le hpsef
    (RestrictedMassEnvelopeMonotone.kahler_smul_isSemipositive ω hε) D
  rwa [RealBottChern.ofRepresentative_smul] at h

/-- **The limit in clause 2 does not depend on the Kähler form.** -/
theorem iSup_minimalGenericLelong_kahler_eq {α : RealBottChern (m + 1) X}
    (hα : IsPseudoeffective α) (ω ω' : KahlerBackground (m + 1) X) (D : Prime) :
    (⨆ (ε : ℝ) (_ : 0 < ε),
        minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D) =
      ⨆ (ε : ℝ) (_ : 0 < ε),
        minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω'.form) D := by
  -- one inequality, for an arbitrary pair of Kähler forms
  have key : ∀ ω₁ ω₂ : KahlerBackground (m + 1) X,
      (⨆ (ε : ℝ) (_ : 0 < ε),
          minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω₂.form) D) ≤
        ⨆ (ε : ℝ) (_ : 0 < ε),
          minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω₁.form) D := by
    intro ω₁ ω₂
    -- `ω₁ ≤ A ω₂`
    obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω₂ (-ω₁.form)
    refine iSup₂_le fun ε hε => ?_
    have hεA : 0 < ε / A := div_pos hε hA
    have hsemi' : ((ε / A) • (-ω₁.form + A • ω₂.form)).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul hsemi hεA.le
    have h := minimalGenericLelong_add_semipositive_le
      (isPseudoeffective_add_kahler hα ω₁ hεA.le) hsemi' D
    have heq : α + (ε / A) • RealBottChern.ofRepresentative ω₁.form +
        RealBottChern.ofRepresentative ((ε / A) • (-ω₁.form + A • ω₂.form)) =
          α + ε • RealBottChern.ofRepresentative ω₂.form := by
      rw [RealBottChern.ofRepresentative_smul, RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_smul, smul_add, smul_smul, div_mul_cancel₀ ε hA.ne']
      have hneg : RealBottChern.ofRepresentative (-ω₁.form) =
          -RealBottChern.ofRepresentative ω₁.form := by
        rw [← neg_one_smul ℝ ω₁.form, RealBottChern.ofRepresentative_smul, neg_one_smul]
      rw [hneg, smul_neg]
      abel
    rw [heq] at h
    exact h.trans (le_iSup₂ (f := fun ε (_ : 0 < ε) =>
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω₁.form) D) (ε / A) hεA)
  exact le_antisymm (key ω' ω) (key ω ω')

/-- For a pseudo-effective class which is not big, `ν(α, D)` does not depend on `ω`. -/
theorem classGenericLelong_indep {α : RealBottChern (m + 1) X} (hα : IsPseudoeffective α)
    (ω ω' : KahlerBackground (m + 1) X) (D : Prime) :
    classGenericLelong ω α D = classGenericLelong ω' α D := by
  unfold classGenericLelong
  split_ifs
  · rfl
  · exact iSup_minimalGenericLelong_kahler_eq hα ω ω' D

/-! ### Compatibility of the two clauses for big classes -/

omit [ConnectedSpace X] in
/-- The class of a nonnegative combination of two currents of `𝒵₊(X)`. -/
theorem currentClass_toBookCurrent_combination (A B : ClosedPositiveCurrent m X) (a b : ℝ)
    (h : IsClosedPositiveCurrent (a • A.current + b • B.current)) :
    currentClass (toBookCurrent _ h) = a • currentClass A + b • currentClass B := by
  have hval : (toBookCurrent _ h).val = a • A.val + b • B.val := Subtype.ext rfl
  change bottChernClass _ _ (toBookCurrent _ h).val = _
  rw [hval]
  change bottChernClassLinearMap _ _ (a • A.val + b • B.val) = _
  rw [map_add, map_smul, map_smul]
  rfl

omit [ConnectedSpace X] in
/-- A big class stays pseudo-effective after subtracting a small multiple of `{ω}`. -/
theorem exists_pos_isPseudoeffective_sub_of_isBig {α : RealBottChern (m + 1) X} (hα : IsBig α)
    (ω : KahlerBackground (m + 1) X) :
    ∃ δ : ℝ, 0 < δ ∧ IsPseudoeffective (α - δ • RealBottChern.ofRepresentative ω.form) := by
  obtain ⟨S, hS, κ, hpos⟩ := hα
  set κc := smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) κ.form with hκc
  have hpos' : IsPositiveCurrent 1 (degreeTwo_val_eq m) (S.val + (-1 : ℝ) • κc).val := by
    have heq : (S.val + (-1 : ℝ) • κc).val = S.current - κc.val := by
      change S.current + (-1 : ℝ) • κc.val = S.current - κc.val
      module
    rw [heq]
    exact hpos
  let S0 : ClosedPositiveCurrent m X := ⟨S.val + (-1 : ℝ) • κc, hpos'⟩
  have hS0cl : currentClass S0 = α - RealBottChern.ofRepresentative κ.form := by
    change bottChernClassLinearMap _ _ (S.val + (-1 : ℝ) • κc) = _
    rw [map_add, map_smul]
    change bottChernClass _ _ S.val + (-1 : ℝ) • bottChernClass _ _ κc = _
    rw [hκc, bottChernClass_smoothClosedCurrent, neg_one_smul, ← sub_eq_add_neg, ← hS]
    rfl
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-ω.form)
  have hA' : 0 < 1 / A := one_div_pos.mpr hA
  have hσ := KahlerDomination.isSemipositive_smul hsemi hA'.le
  obtain ⟨S1, hS1cl, -⟩ := exists_add_semipositive S0 hσ
  refine ⟨1 / A, hA', S1, ?_⟩
  rw [hS1cl, hS0cl, RealBottChern.ofRepresentative_smul, RealBottChern.ofRepresentative_add,
    RealBottChern.ofRepresentative_smul]
  have hneg : RealBottChern.ofRepresentative (-ω.form) =
      -RealBottChern.ofRepresentative ω.form := by
    rw [← neg_one_smul ℝ ω.form, RealBottChern.ofRepresentative_smul, neg_one_smul]
  rw [hneg, smul_add, smul_neg, smul_smul, one_div_mul_cancel hA.ne', one_smul]
  abel

/-- **Compatibility of the two clauses for big classes** (the claim after `def:mult_class`):
`ν(α, D) ≤ sup_{ε > 0} ν(α + ε{ω}, D)` for big `α`.  Following FPT
`prop:big-class-minimal-multiplicity`: `(1 - t) T_ε + t S ∈ α` for a current `S ∈ α - δ{ω}` and
`t = ε / (ε + δ)`, evaluated at an almost generic point of `D`. -/
theorem minimalGenericLelong_le_iSup_of_isBig {α : RealBottChern (m + 1) X} (hα : IsBig α)
    (ω : KahlerBackground (m + 1) X) (D : Prime) :
    minimalGenericLelong α D ≤ ⨆ (ε : ℝ) (_ : 0 < ε),
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D := by
  have hpsef : IsPseudoeffective α := by
    obtain ⟨T, hT, -⟩ := hα
    exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := exists_minimalSingularities hpsef
  obtain ⟨δ, hδ, S1, hS1⟩ := exists_pos_isPseudoeffective_sub_of_isBig hα ω
  have hS1r := isClosedPositiveCurrent_bookCurrent S1
  set K := bookGenericLelong S1 D with hKdef
  have hKfin : K ≠ ⊤ := by rw [hKdef, bookGenericLelong_eq]; exact currentGenericLelong_ne_top _ D
  rw [minimalGenericLelong_eq hT]
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  set ρ : ℝ := (η : ℝ) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  set t : ℝ := min (1 / 2) (ρ / (K.toReal + ρ + 1)) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htK : t * (K.toReal + ρ) ≤ ρ := by
    have h1 : t ≤ ρ / (K.toReal + ρ + 1) := min_le_right _ _
    have hpos : 0 < K.toReal + ρ + 1 := by positivity
    calc t * (K.toReal + ρ) ≤ ρ / (K.toReal + ρ + 1) * (K.toReal + ρ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ρ / (K.toReal + ρ + 1) * (K.toReal + ρ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ := div_mul_cancel₀ ρ hpos.ne'
  set ε : ℝ := δ * t / (1 - t) with hεdef
  have h1t : 0 < 1 - t := by linarith
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hcoef : (1 - t) * ε = t * δ := by
    rw [hεdef]; field_simp
  obtain ⟨Tε, hTε⟩ := exists_minimalSingularities (isPseudoeffective_add_kahler hpsef ω hε.le)
  have hTεr := isClosedPositiveCurrent_bookCurrent Tε
  have hAr : IsClosedPositiveCurrent ((1 - t) • Tε.current + t • S1.current) :=
    (hTεr.smul h1t.le).add (hS1r.smul ht0.le)
  set C := toBookCurrent _ hAr with hCdef
  have hCcl : currentClass C = α := by
    rw [hCdef, currentClass_toBookCurrent_combination, hTε.1, hS1]
    have key : (1 - t) • (α + ε • RealBottChern.ofRepresentative ω.form) +
        t • (α - δ • RealBottChern.ofRepresentative ω.form) =
          α + ((1 - t) * ε - t * δ) • RealBottChern.ofRepresentative ω.form := by
      module
    rw [key, hcoef, sub_self, zero_smul, add_zero]
  have hmore : MoreSingular C T := hT.2 C hCcl
  obtain ⟨x, hxD, hx1, hx2⟩ := exists_mem_lt_currentGenericLelong_add hTεr hS1r D hρ
  have hCx : bookLelong C x = ENNReal.ofReal (1 - t) * currentLelong Tε.current hTεr x +
      ENNReal.ofReal t * currentLelong S1.current hS1r x := by
    rw [bookCurrentLelong_eq_currentLelong]
    have h1 := currentLelong_add (hTεr.smul h1t.le) (hS1r.smul ht0.le) hAr x
    rw [currentLelong_smul hTεr h1t.le, currentLelong_smul hS1r ht0.le] at h1
    exact h1
  have hfε : currentGenericLelong Tε.current hTεr D ≤ ⨆ (ε : ℝ) (_ : 0 < ε),
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D := by
    rw [← bookGenericLelong_eq, ← minimalGenericLelong_eq hTε]
    exact le_iSup₂ (f := fun ε (_ : 0 < ε) =>
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D) ε hε
  have hS1D : currentGenericLelong S1.current hS1r D = K := by rw [hKdef, bookGenericLelong_eq]
  set s := ⨆ (ε : ℝ) (_ : 0 < ε),
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D with hsdef
  calc bookGenericLelong T D ≤ bookLelong T x := iInf₂_le x hxD
    _ ≤ bookLelong C x := currentLelong_le_of_moreSingular hmore x
    _ = ENNReal.ofReal (1 - t) * currentLelong Tε.current hTεr x +
          ENNReal.ofReal t * currentLelong S1.current hS1r x := hCx
    _ ≤ ENNReal.ofReal (1 - t) * (s + ENNReal.ofReal ρ) +
          ENNReal.ofReal t * (K + ENNReal.ofReal ρ) := by
        gcongr
        · exact hx1.le.trans (add_le_add hfε le_rfl)
        · rw [← hS1D]; exact hx2.le
    _ ≤ (s + ENNReal.ofReal ρ) + ENNReal.ofReal ρ := by
        gcongr
        · calc ENNReal.ofReal (1 - t) * (s + ENNReal.ofReal ρ) ≤ 1 * (s + ENNReal.ofReal ρ) := by
                gcongr
                exact ENNReal.ofReal_le_one.mpr (by linarith)
            _ = s + ENNReal.ofReal ρ := one_mul _
        · rw [← ENNReal.ofReal_toReal hKfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hρ.le,
            ← ENNReal.ofReal_mul ht0.le]
          exact ENNReal.ofReal_le_ofReal htK
    _ = s + (η : ℝ≥0∞) := by
        rw [add_assoc, ← ENNReal.ofReal_add hρ.le hρ.le, hρdef, add_halves,
          ENNReal.ofReal_coe_nnreal]

/-- **Compatibility of the two clauses for big classes**: for big `α`,
`ν(α + ε{ω}, D) → ν(α, D)` as `ε → 0+`. -/
theorem tendsto_classGenericLelong_of_isBig {α : RealBottChern (m + 1) X} (hα : IsBig α)
    (ω : KahlerBackground (m + 1) X) (D : Prime) :
    Tendsto (fun ε : ℝ => minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D)
      (𝓝[>] 0) (𝓝 (classGenericLelong ω α D)) := by
  have hpsef : IsPseudoeffective α := by
    obtain ⟨T, hT, -⟩ := hα
    exact ⟨T, hT⟩
  have hlim := tendsto_iSup_of_antitoneOn (f := fun ε : ℝ =>
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D)
    fun _ _ hε hεε' => minimalGenericLelong_kahler_antitone hpsef ω D hε.le hεε'
  have heq : (⨆ (ε : ℝ) (_ : 0 < ε),
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D) =
        classGenericLelong ω α D := by
    apply le_antisymm
    · exact iSup₂_le fun ε hε => classGenericLelong_le_of_isBig hα ω D hε.le
    · rw [classGenericLelong, if_pos hα]
      exact minimalGenericLelong_le_iSup_of_isBig hα ω D
  rwa [heq] at hlim

/-- **`ν(α, D)` is the limit `lim_{ε → 0+} ν(α + ε{ω}, D)` for every pseudo-effective class**
(big or not). -/
theorem tendsto_classGenericLelong_of_isPseudoeffective {α : RealBottChern (m + 1) X}
    (hα : IsPseudoeffective α) (ω : KahlerBackground (m + 1) X) (D : Prime) :
    Tendsto (fun ε : ℝ => minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D)
      (𝓝[>] 0) (𝓝 (classGenericLelong ω α D)) := by
  by_cases hb : IsBig α
  · exact tendsto_classGenericLelong_of_isBig hb ω D
  · exact tendsto_classGenericLelong hα hb ω D

/-- **`ν(α, D)` does not depend on the Kähler form**, for every pseudo-effective class. -/
theorem classGenericLelong_eq_iSup {α : RealBottChern (m + 1) X} (hα : IsPseudoeffective α)
    (ω : KahlerBackground (m + 1) X) (D : Prime) :
    classGenericLelong ω α D = ⨆ (ε : ℝ) (_ : 0 < ε),
      minimalGenericLelong (α + ε • RealBottChern.ofRepresentative ω.form) D :=
  tendsto_nhds_unique (tendsto_classGenericLelong_of_isPseudoeffective hα ω D)
    (tendsto_iSup_of_antitoneOn fun _ _ hε hεε' =>
      minimalGenericLelong_kahler_antitone hα ω D hε.le hεε')

/-- **Modified nef classes via Lelong numbers** (the remark after `def:mult_class`): a
pseudo-effective class `α = {θ}` is modified nef iff `ν(α, D) = 0` for every prime divisor `D`. -/
theorem modifiedNefWithRespectTo_iff_classGenericLelong (ω : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X)
    (hα : IsPseudoeffective (RealBottChern.ofRepresentative θ)) :
    ModifiedNefWithRespectTo ω θ ↔
      ∀ D : Prime, classGenericLelong ω (RealBottChern.ofRepresentative θ) D = 0 := by
  rw [modifiedNefWithRespectTo_iff_exists_bookCurrent]
  have hcl : ∀ ε : ℝ, RealBottChern.ofRepresentative (θ + ε • ω.form) =
      RealBottChern.ofRepresentative θ + ε • RealBottChern.ofRepresentative ω.form := by
    intro ε
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  constructor
  · intro h D
    rw [classGenericLelong_eq_iSup hα]
    refine le_antisymm (iSup₂_le fun ε hε => ?_) bot_le
    obtain ⟨S, hS, hSD⟩ := h ε hε
    obtain ⟨T, hT⟩ := exists_minimalSingularities (isPseudoeffective_add_kahler hα ω hε.le)
    rw [minimalGenericLelong_eq hT, ← hSD D]
    exact bookGenericLelong_mono (currentLelong_le_of_moreSingular (hT.2 S (by rw [hS, hcl]))) D
  · intro h ε hε
    obtain ⟨T, hT⟩ := exists_minimalSingularities (isPseudoeffective_add_kahler hα ω hε.le)
    refine ⟨T, by rw [hT.1, hcl], fun D => ?_⟩
    rw [← minimalGenericLelong_eq hT]
    refine le_antisymm ?_ bot_le
    rw [← h D, classGenericLelong_eq_iSup hα]
    exact le_iSup₂ (f := fun ε (_ : 0 < ε) =>
      minimalGenericLelong (RealBottChern.ofRepresentative θ + ε •
        RealBottChern.ofRepresentative ω.form) D) ε hε

end SGPT.Siu
