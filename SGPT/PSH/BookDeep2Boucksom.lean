import SGPT.PSH.BookCurrentNonKahler
import SGPT.PSH.SourceSiu
import SGPT.PSH.VariableComponentConverse
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded

/-!
# Boucksom's theorem on the non-Kähler locus (`thm:pshfunctions:L1641`)

Source `thm:pshfunctions:L1641` (chapter `chapter_pshfunctions.tex`, after Boucksom, *Divisorial
Zariski decompositions*, Thm. 2.1.20 / 3.17): *if `α` is big, there is a Kähler current `T ∈ α`
with analytic singularities whose polar locus is exactly `nK(α)`; in particular `nK(α)` is a
proper Zariski closed subset of `X`.*

Objects are the verified book notions of `SGPT.PSH.BookCurrent`: `𝒵₊(X)`
(`ClosedPositiveCurrent`), the class `{T}` (`currentClass`), Kähler currents
(`IsKahlerCurrent`), currents with analytic singularities (`HasAnalyticSingularities`), the polar
locus (`polarLocus`) and `nK(α)` (`currentNonKahlerLocus`, `def:nKlocus`); bigness is
`BookCurrent.IsBig`.  "Zariski closed" is read as: cut out locally in every chart by finitely
many holomorphic equations (`HasAnalyticChartEquations`), equivalently closed in the analytic
Zariski topology (`analyticZariskiTopology`).

The proof reuses TN's bounded-remainder form of Boucksom's theorem
(`NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus`,
whose `nonKahlerLocus` is defined by positivity of Lelong numbers of all Kähler currents) and
identifies the two definitions of the non-Kähler locus (`sourceNonKahlerLocus_eq_nonKahlerLocus`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace SGPT.PSH.BookDeep2Boucksom

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.BookCurrent

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- For a big class, the book's non-Kähler locus (intersection of the polar loci of the Kähler
currents with analytic singularities) is TN's locus of points where every Kähler current has a
positive Lelong number. -/
theorem sourceNonKahlerLocus_eq_nonKahlerLocus (α : RealBottChern (m + 1) X)
    (hα : IsBigClass α) : sourceNonKahlerLocus α = nonKahlerLocus α := by
  obtain ⟨K, hKan, hKpole⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      (Nat.succ_pos m) α hα
  ext x
  constructor
  · intro hx
    rw [← hKpole]
    exact hx K ((sourceRationalAnalyticType_iff_native K.potential).mpr hKan)
  · intro hx T _
    exact eq_bot_of_lelongNumber_pos (Nat.succ_pos m) T.strictlyPsh.1 (hx T)

/-- **`thm:pshfunctions:L1641`, main clause (Boucksom).** A big class `α` contains a Kähler
current `T ∈ 𝒵₊(X)` with analytic singularities whose polar locus is exactly `nK(α)`. -/
theorem exists_kahlerCurrent_polarLocus_eq_nonKahlerLocus (α : RealBottChern (m + 1) X)
    (hα : IsBig α) :
    ∃ T : ClosedPositiveCurrent m X, currentClass T = α ∧ IsKahlerCurrent T ∧
      HasAnalyticSingularities T ∧ polarLocus T = currentNonKahlerLocus α := by
  have hbig : IsBigClass α := (isBig_iff_isBigClass α).mp hα
  obtain ⟨K, hKan, hKpole⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      (Nat.succ_pos m) α hbig
  have hu := kahlerCurrent_isThetaPsh K
  have hpres := isPresentation_thetaPositiveCurrent K.representative K.potential hu
  refine ⟨thetaPositiveCurrent K.representative K.potential hu, ?_,
    kahlerCurrent_isKahlerCurrent K hu,
    (hasAnalyticSingularities_iff_of_isPresentation hpres).mpr
      ((sourceRationalAnalyticType_iff_native K.potential).mpr hKan), ?_⟩
  · rw [currentClass_thetaPositiveCurrent, K.represents]
  · rw [polarLocus_eq_of_isPresentation hpres, currentNonKahlerLocus_eq_sourceNonKahlerLocus,
      sourceNonKahlerLocus_eq_nonKahlerLocus α hbig, ← hKpole]
    rfl

/-- `nK(α)` is cut out locally by holomorphic equations in every chart. -/
theorem hasAnalyticChartEquations_currentNonKahlerLocus (α : RealBottChern (m + 1) X)
    (hα : IsBig α) :
    (ofFixedModel (m + 1) X).HasAnalyticChartEquations (currentNonKahlerLocus α) := by
  have hbig : IsBigClass α := (isBig_iff_isBigClass α).mp hα
  have hS : IsComplexAnalyticSubset (n := m + 1) (currentNonKahlerLocus α) := by
    rw [currentNonKahlerLocus_eq_sourceNonKahlerLocus,
      sourceNonKahlerLocus_eq_nonKahlerLocus α hbig]
    exact NonKahlerLocusPoleSetBounded.isComplexAnalyticSubset_nonKahlerLocus
      (Nat.succ_pos m) α hbig
  intro e z hz
  exact SGPT.PSH.nativeAnalytic_chartEquations hS e z hz

/-- **`thm:pshfunctions:L1641`, second clause.** For a big class `α` on a nonempty `X`, `nK(α)`
is a proper Zariski closed subset of `X`: it is analytic (cut out locally by holomorphic
equations), hence closed in the analytic Zariski topology, and it is not all of `X`. -/
theorem nonKahlerLocus_proper_zariskiClosed [Nonempty X] (α : RealBottChern (m + 1) X)
    (hα : IsBig α) :
    (ofFixedModel (m + 1) X).HasAnalyticChartEquations (currentNonKahlerLocus α) ∧
      @IsClosed X (ofFixedModel (m + 1) X).analyticZariskiTopology (currentNonKahlerLocus α) ∧
      currentNonKahlerLocus α ≠ univ := by
  have hZ := hasAnalyticChartEquations_currentNonKahlerLocus α hα
  refine ⟨hZ, hZ.isClosed_analyticZariski, ?_⟩
  obtain ⟨T, -, -, -, hpolar⟩ := exists_kahlerCurrent_polarLocus_eq_nonKahlerLocus α hα
  obtain ⟨θ, u, hu, hT⟩ := exists_presentation T
  have hpres : IsPresentation T θ u := ⟨hu, hT⟩
  intro huniv
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, -, hy⟩ := hu.2 x univ isOpen_univ (mem_univ x)
  have hmem : y ∈ polarLocus T := by rw [hpolar, huniv]; exact mem_univ y
  rw [polarLocus_eq_of_isPresentation hpres] at hmem
  exact hy hmem

end SGPT.PSH.BookDeep2Boucksom
