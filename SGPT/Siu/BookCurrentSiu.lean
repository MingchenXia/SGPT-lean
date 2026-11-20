import SGPT.Siu.SiuLemma
import SGPT.Siu.CurrentLevelSets
import SGPT.Siu.ModifiedNef
import SGPT.PSH.BookCurrentSpace

/-!
# Siu's lemma for the book's space of currents `𝒵₊(X)`

The book's space `𝒵₊(X)` of closed positive `(1,1)`-currents is formalized as
`SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X` (closed real `(1,1)`-currents with the source
weak positivity of `def:pos_curr`), with Lelong numbers `SGPT.PSH.BookCurrent.currentLelong`
(`ex:Lelongcurrent`).  This file identifies that API with the predicate
`SGPT.Siu.IsClosedPositiveCurrent` and the reader `SGPT.Siu.currentLelong` used to prove Siu's
lemma,
and restates Siu's lemma (`lma:Siudec`) and Siu's theorem for currents on `𝒵₊(X)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.BookCurrent
open SquaredLogLelongSourceNormalization

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- Elements of `𝒵₊(X)` are closed positive currents in the sense of `IsClosedPositiveCurrent`. -/
theorem isClosedPositiveCurrent_bookCurrent (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    IsClosedPositiveCurrent T.current :=
  ⟨T.isClosed, T.isTypeOneOne,
    isFullPositive_of_isPositiveCurrent _ T.isClosed T.isTypeOneOne T.isPositive⟩

/-- Every closed positive current in the sense of `IsClosedPositiveCurrent` is an element of
`𝒵₊(X)`. -/
def toBookCurrent (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hT : IsClosedPositiveCurrent T) : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  ⟨⟨T, hT.1, hT.2.1⟩, isPositiveCurrent_of_isFullPositive T hT.2.2⟩

omit [CompactSpace X] in
@[simp] theorem toBookCurrent_current (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hT : IsClosedPositiveCurrent T) : (toBookCurrent T hT).current = T := rfl

/-- The two Lelong-number readers agree. -/
theorem bookCurrentLelong_eq_currentLelong (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    SGPT.PSH.BookCurrent.currentLelong T =
      currentLelong T.current (isClosedPositiveCurrent_bookCurrent T) := by
  funext x
  obtain ⟨hu, hT⟩ := isPresentation_presentation T
  rw [currentLelong_eq_of_isPresentation ⟨hu, hT⟩ x,
    SGPT.PSH.VariableComplexAtlas.sourceLelong_ofFixedModel_eq,
    currentLelong_eq_of_eq_thetaPotentialCurrent _ hT]

/-- The generic Lelong number `ν(T, D)` of an element of `𝒵₊(X)` along a prime divisor. -/
def bookGenericLelong (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) : ℝ≥0∞ :=
  ⨅ x ∈ D.val, SGPT.PSH.BookCurrent.currentLelong T x

theorem bookGenericLelong_eq (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    bookGenericLelong T D =
      currentGenericLelong T.current (isClosedPositiveCurrent_bookCurrent T) D := by
  rw [bookGenericLelong, bookCurrentLelong_eq_currentLelong]
  rfl

/-- The current of integration `[D]` of a prime divisor, as an element of `𝒵₊(X)`. -/
def primeDivisorBookCurrent (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  toBookCurrent (primeDivisorCurrent D) (isClosedPositiveCurrent_primeDivisorCurrent D)

/-- **Siu's lemma** (`lma:Siudec`) on `𝒵₊(X)`: for every prime divisor `D` and every
`T ∈ 𝒵₊(X)`, `T - ν(T, D)[D] ∈ 𝒵₊(X)`. -/
theorem exists_bookCurrent_sub_genericLelong_smul
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    ∃ R : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X,
      R.current =
        T.current - (bookGenericLelong T D).toReal • (primeDivisorBookCurrent D).current := by
  have h := isClosedPositiveCurrent_sub_currentGenericLelong_smul
    (isClosedPositiveCurrent_bookCurrent T) D
  rw [← bookGenericLelong_eq] at h
  exact ⟨toBookCurrent _ h, rfl⟩

/-- **Siu's theorem for currents** on `𝒵₊(X)`: the upper level sets of `x ↦ ν(T, x)` are
analytic. -/
theorem isComplexAnalyticSubset_bookCurrentLelong_superlevel
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) (c : ℝ) :
    IsComplexAnalyticSubset (n := m + 1)
      {x : X | ENNReal.ofReal c ≤ SGPT.PSH.BookCurrent.currentLelong T x} := by
  rw [bookCurrentLelong_eq_currentLelong]
  exact isComplexAnalyticSubset_currentLelong_superlevel _ c

/-- The generic Lelong number of `T ∈ 𝒵₊(X)` is that of any potential of a presentation. -/
theorem bookGenericLelong_eq_primeGenericLelong {T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal} (h : IsPresentation T θ u)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    bookGenericLelong T D = primeGenericLelong u D := by
  obtain ⟨hu, hT⟩ := h
  rw [bookGenericLelong_eq, currentGenericLelong_eq_primeGenericLelong _ hT]

/-- **`def:mnclass` with currents.**  A class `α = {θ}` is modified nef (with respect to `ω`)
iff for every `ε > 0` there is a closed positive current `S ∈ 𝒵₊(X, α + ε{ω})` (i.e.
`S = T + εω` for a closed `(1,1)`-current `T ∈ α` with `T + εω ≥ 0`) with `ν(S, D) = 0` for every
prime divisor `D`. -/
theorem modifiedNefWithRespectTo_iff_exists_bookCurrent
    (ω : PositiveClasses.KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) :
    ModifiedNefWithRespectTo ω θ ↔ ∀ ε : ℝ, 0 < ε →
      ∃ S : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X,
        currentClass S = RealBottChern.ofRepresentative (θ + ε • ω.form) ∧
          ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X, bookGenericLelong S D = 0 := by
  constructor
  · intro h ε hε
    obtain ⟨φ, hφ, hD⟩ := h ε hε
    refine ⟨thetaPositiveCurrent (θ + ε • ω.form) φ hφ, currentClass_thetaPositiveCurrent _ _ _,
      fun D => ?_⟩
    rw [bookGenericLelong_eq_primeGenericLelong (isPresentation_thetaPositiveCurrent _ _ hφ), hD D]
  · intro h ε hε
    obtain ⟨S, hS, hD⟩ := h ε hε
    obtain ⟨θ', u', h'⟩ := exists_presentation S
    have hcl : RealBottChern.ofRepresentative θ' =
        RealBottChern.ofRepresentative (θ + ε • ω.form) := by
      rw [← h'.currentClass_eq, hS]
    obtain ⟨g, hg, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hcl
    refine ⟨fun x => u' x - (g x : EReal),
      PositiveClasses.thetaPshPotential_sub_smooth hg hrel h'.isThetaPsh,
      fun D => ?_⟩
    rw [primeGenericLelong_sub_smooth u' hg D, ← bookGenericLelong_eq_primeGenericLelong h' D, hD D]

end SGPT.Siu
