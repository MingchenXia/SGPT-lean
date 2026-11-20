import SGPT.PSH.HermitianExtremalEnvelopeValues
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization

/-!
# Actual increasing nonnegative extremal competitors

Choquet selection chooses original members of the genuine competitor
family. Finite maxima and the actual zero member produce an increasing
nonnegative sequence with the same original regularized supremum.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

theorem competitors_max (ω : Background (m + 1) M) {A : Set M}
    {u v : M → EReal} (hu : u ∈ competitors ω A) (hv : v ∈ competitors ω A) :
    (fun x => max (u x) (v x)) ∈ competitors ω A :=
  ⟨hu.1.max hv.1, fun x hx => max_le (hu.2 x hx) (hv.2 x hx)⟩

/-- Every term is an original genuine Hermitian competitor; the limit
identity concerns the actual USC regularization, not an envelope package. -/
theorem exists_increasing_nonnegative_competitors (ω : Background (m + 1) M) (A : Set M) :
    ∃ u : ℕ → M → EReal, (∀ j, u j ∈ competitors ω A) ∧
      (∀ j x, 0 ≤ u j x) ∧ (∀ x, Monotone fun j => u j x) ∧
      uscRegularization (fun x => ⨆ j, u j x) = regularizedExtremal ω A := by
  obtain ⟨s, hs, heq⟩ := exists_seq_uscRegularization_iSup_eq
    (show (competitors ω A).Nonempty from ⟨fun _ => 0, zero_mem_competitors ω A⟩)
  have hrun : ∀ j, runningMax s j ∈ competitors ω A := by
    intro j
    induction j with
    | zero => exact hs 0
    | succ j ih => exact competitors_max ω ih (hs (j + 1))
  let u : ℕ → M → EReal := fun j x => max 0 (runningMax s j x)
  have hu (j : ℕ) : u j ∈ competitors ω A :=
    competitors_max ω (zero_mem_competitors ω A) (hrun j)
  have hssup : sSup (competitors ω A) = extremal ω A :=
    funext fun x => sSup_apply
  have heq' : uscRegularization (fun x => ⨆ j, s j x) = regularizedExtremal ω A := by
    have hi : (⨆ j, s j) = fun x => ⨆ j, s j x := funext fun _ => iSup_apply
    rw [hi, hssup] at heq
    exact heq
  refine ⟨u, hu, fun j x => le_max_left _ _, fun x j k hjk => ?_, ?_⟩
  · exact max_le_max le_rfl (runningMax_monotone s hjk x)
  · apply le_antisymm
    · apply uscRegularization_mono
      intro x
      exact iSup_le fun j => le_iSup (fun v : competitors ω A => v.val x) ⟨u j, hu j⟩
    · rw [← heq']
      apply uscRegularization_mono
      intro x
      exact iSup_mono fun j => (le_runningMax s j x).trans (le_max_right _ _)

/-- Any actual finite bound for the canonical extremal bounds the whole
increasing competitor sequence produced above, by the same constant. -/
theorem exists_bounded_increasing_nonnegative_competitors (ω : Background (m + 1) M)
    (A : Set M) (C : ℝ) (hC : ∀ x, regularizedExtremal ω A x ≤ (C : EReal)) :
    ∃ u : ℕ → M → EReal, (∀ j, u j ∈ competitors ω A) ∧
      (∀ j x, 0 ≤ u j x ∧ u j x ≤ (C : EReal)) ∧
      (∀ x, Monotone fun j => u j x) ∧
      uscRegularization (fun x => ⨆ j, u j x) = regularizedExtremal ω A := by
  obtain ⟨u, hu, hpos, hmono, heq⟩ := exists_increasing_nonnegative_competitors ω A
  exact ⟨u, hu, fun j x => ⟨hpos j x,
    (competitor_le_regularizedExtremal ω (hu j) x).trans (hC x)⟩, hmono, heq⟩

end SGPT.PSH.HermitianExtremal
