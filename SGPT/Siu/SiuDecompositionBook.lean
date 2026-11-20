import SGPT.Siu.SiuDecomposition
import SGPT.Siu.BookCurrentSiu

/-!
# Siu's decomposition for the book's space of currents `𝒵₊(X)`

Source: `eq:Siudec` and `def:nd_curr` (chapter *Plurisubharmonic functions*).  This file restates
`SGPT.Siu.siu_decomposition` and the non-divisorial / divisorial currents of `def:nd_curr` for the
book's space `𝒵₊(X)` of closed positive `(1,1)`-currents,
`SGPT.PSH.BookCurrent.ClosedPositiveCurrent`
, with the book's Lelong numbers `SGPT.PSH.BookCurrent.currentLelong` and generic Lelong
numbers `SGPT.Siu.bookGenericLelong`.

* `bookSiuRegularPart T = Reg T ∈ 𝒵₊(X)` and `bookSiuDivisorialPart T ∈ 𝒵₊(X)`;
* `book_siu_decomposition`: `T = Reg T + ∑_D ν(T, D)[D]` with countable support, weak convergence,
  and `ν(Reg T, D) = 0` for every prime divisor `D`;
* `BookIsNonDivisorial`, `BookIsDivisorial` (`def:nd_curr`) and `bookIsNonDivisorial_iff`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- `Reg T ∈ 𝒵₊(X)` (`eq:Siudec`). -/
def bookSiuRegularPart (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  toBookCurrent _ (isClosedPositiveCurrent_siuRegularPart (isClosedPositiveCurrent_bookCurrent T))

/-- The divisorial part `∑_D ν(T, D)[D] ∈ 𝒵₊(X)` (`eq:Siudec`). -/
def bookSiuDivisorialPart (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  toBookCurrent _
    (isClosedPositiveCurrent_siuDivisorialPart (isClosedPositiveCurrent_bookCurrent T))

/-- **Siu's decomposition on `𝒵₊(X)`** (`eq:Siudec`): `T = Reg T + ∑_D ν(T, D)[D]`, the set of
prime divisors with `ν(T, D) > 0` is countable, the series converges weakly, and
`ν(Reg T, D) = 0` for every prime divisor `D`. -/
theorem book_siu_decomposition (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    T.current = (bookSiuRegularPart T).current + (bookSiuDivisorialPart T).current ∧
      {D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X | bookGenericLelong T D ≠ 0}.Countable ∧
      (∀ (e : ComplexChart (m + 1) X)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        HasSum (fun D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X =>
          ((bookGenericLelong T D).toReal • (primeDivisorBookCurrent D).current).inChart e η)
          ((bookSiuDivisorialPart T).current.inChart e η)) ∧
      ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X,
        bookGenericLelong (bookSiuRegularPart T) D = 0 := by
  have hT := isClosedPositiveCurrent_bookCurrent T
  obtain ⟨hdec, -, -, hcount, hsum, hreg, -⟩ := siu_decomposition hT
  refine ⟨hdec, ?_, ?_, ?_⟩
  · simpa only [bookGenericLelong_eq] using hcount
  · intro e η
    simp only [bookGenericLelong_eq]
    exact hsum e η
  · intro D
    rw [bookGenericLelong_eq]
    exact hreg D

/-- **Non-divisorial currents** in `𝒵₊(X)` (`def:nd_curr`): `T = Reg T`. -/
def BookIsNonDivisorial (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) : Prop :=
  T = bookSiuRegularPart T

/-- **Divisorial currents** in `𝒵₊(X)` (`def:nd_curr`): `Reg T = 0`. -/
def BookIsDivisorial (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) : Prop :=
  (bookSiuRegularPart T).current = 0

theorem bookIsNonDivisorial_iff_isNonDivisorial
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    BookIsNonDivisorial T ↔ IsNonDivisorial T.current (isClosedPositiveCurrent_bookCurrent T) := by
  constructor
  · intro h
    exact congrArg SGPT.PSH.BookCurrent.ClosedPositiveCurrent.current h
  · intro h
    exact SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext h

/-- A current in `𝒵₊(X)` is non-divisorial iff `ν(T, D) = 0` for every prime divisor `D`. -/
theorem bookIsNonDivisorial_iff (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    BookIsNonDivisorial T ↔ ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X,
      bookGenericLelong T D = 0 := by
  rw [bookIsNonDivisorial_iff_isNonDivisorial, isNonDivisorial_iff]
  simp only [bookGenericLelong_eq]

theorem bookIsDivisorial_iff (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    BookIsDivisorial T ↔ T = bookSiuDivisorialPart T := by
  constructor
  · intro h
    exact SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
      ((isDivisorial_iff (isClosedPositiveCurrent_bookCurrent T)).mp h)
  · intro h
    exact (isDivisorial_iff (isClosedPositiveCurrent_bookCurrent T)).mpr
      (congrArg SGPT.PSH.BookCurrent.ClosedPositiveCurrent.current h)

end SGPT.Siu
