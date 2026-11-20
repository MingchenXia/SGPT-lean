import SGPT.Foundations.Analysis.Pending.DemaillyAnalyticType

set_option autoImplicit false

/-!
# Finite maxima of local analytic-singularity presentations

A finite atlas gluing step combines local Bergman logarithms by a finite
maximum.  This module records the purely local, same-coefficient consequence:
finite maxima retain a rational analytic-singularity type after the finite
generator families are concatenated.  It makes no assertion that the local
weights patch to a global theta-plurisubharmonic sequence.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyAnalyticType

open SGPT.Foundations.Analysis

lemma iSup_fin_succ_eq_max
    {α : Type*} [CompleteLinearOrder α] {k : ℕ} (F : Fin (k + 1) → α) :
    (⨆ i, F i) = max (F 0) (⨆ i : Fin k, F i.succ) := by
  apply le_antisymm
  · refine iSup_le fun i => Fin.cases ?_ ?_ i
    · exact le_max_left _ _
    · intro j
      exact (le_iSup (fun i : Fin k => F i.succ) j).trans (le_max_right _ _)
  · refine max_le ?_ ?_
    · exact le_iSup F 0
    · exact iSup_le fun i => le_iSup F i.succ

lemma iSup_fin_one_eq
    {α : Type*} [CompleteLinearOrder α] (F : Fin 1 → α) : (⨆ i, F i) = F 0 := by
  rw [iSup_fin_succ_eq_max]
  simp

/-- A nonempty finite maximum of local logarithmic presentations with one
fixed rational coefficient has a presentation with that same coefficient. -/
theorem exists_logarithmicTypeAt_fin_iSup_of_same_coefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} {c : ℚ} {k : ℕ} (u : Fin (k + 1) → E → EReal)
    (h : ∀ i, ∃ N : ℕ, ∃ f : Fin N → E → ℂ,
      LogarithmicTypeAt (u i) (c : ℝ) f x) :
    ∃ N : ℕ, ∃ f : Fin N → E → ℂ,
      LogarithmicTypeAt (fun y => ⨆ i, u i y) (c : ℝ) f x := by
  induction k with
  | zero =>
      obtain ⟨N, f, hf⟩ := h 0
      refine ⟨N, f, ?_⟩
      convert hf using 1
      ext y
      exact iSup_fin_one_eq (fun i => u i y)
  | succ k ih =>
      have htail : ∀ i : Fin (k + 1), ∃ N : ℕ, ∃ f : Fin N → E → ℂ,
          LogarithmicTypeAt (u i.succ) (c : ℝ) f x := fun i => h i.succ
      obtain ⟨N, f, hf⟩ := h 0
      obtain ⟨M, g, hg⟩ := ih (fun i => u i.succ) htail
      refine ⟨N + M, Fin.append f g, ?_⟩
      convert LogarithmicTypeAt.max_of_generators hf hg using 1
      ext y
      exact iSup_fin_succ_eq_max (fun i => u i y)

/-- A nonempty finite maximum of local logarithmic presentations with one
rational coefficient has a local analytic singularity type. -/
theorem hasAnalyticSingularityTypeAt_fin_iSup_of_same_coefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} {c : ℚ} {k : ℕ} (u : Fin (k + 1) → E → EReal)
    (h : ∀ i, ∃ N : ℕ, ∃ f : Fin N → E → ℂ,
      LogarithmicTypeAt (u i) (c : ℝ) f x) :
    HasAnalyticSingularityTypeAt (fun y => ⨆ i, u i y) x := by
  obtain ⟨N, f, hf⟩ := exists_logarithmicTypeAt_fin_iSup_of_same_coefficient u h
  exact ⟨c, N, f, hf⟩

end SGPT.Foundations.Analysis.Pending.DemaillyAnalyticType
