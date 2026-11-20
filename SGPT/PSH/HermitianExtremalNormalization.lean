import SGPT.PSH.HermitianExtremalCurrentAlgebra
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-!
# Actual compact normalization for a nonclosed Hermitian background

A genuine quasi-PSH potential attains a finite real maximum on a nonempty
compact manifold. Subtracting this same maximum preserves the full current
and gives an actual zero point, rather than a normalization certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalNormalization

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremalCurrentAlgebra
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [Nonempty M]

/-- The actual extended-real supremum of a genuine compact Hermitian PSH
potential is a finite real number and is attained at an original point. -/
theorem exists_real_sup (ω : Background (m + 1) M) {u : M → EReal}
    (hu : IsHermitianPSH ω u) :
    ∃ b : ℝ, (⨆ x, u x) = (b : EReal) ∧ (∀ x, u x ≤ (b : EReal)) ∧
      ∃ p, u p = (b : EReal) := by
  obtain ⟨p, _, hpmax⟩ :=
    (hu.quasiPshPotential.1.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
      univ_nonempty isCompact_univ
  obtain ⟨y, _, hy⟩ := hu.quasiPshPotential.2 p univ isOpen_univ (mem_univ p)
  have hpbot : u p ≠ ⊥ := fun h => hy (le_bot_iff.mp ((hpmax (mem_univ y)).trans_eq h))
  let b : ℝ := (u p).toReal
  have hpb : u p = (b : EReal) := (EReal.coe_toReal (hu.ne_top p) hpbot).symm
  have hbound : ∀ x, u x ≤ (b : EReal) := fun x => (hpmax (mem_univ x)).trans_eq hpb
  refine ⟨b, le_antisymm (iSup_le hbound) ?_, hbound, p, hpb⟩
  rw [← hpb]
  exact le_iSup u p

/-- Subtracting the same actual maximum manufactures a nonpositive
Hermitian PSH potential with a genuine zero point. -/
theorem exists_normalized_sub_sup (ω : Background (m + 1) M) {u : M → EReal}
    (hu : IsHermitianPSH ω u) :
    ∃ b : ℝ, (⨆ x, u x) = (b : EReal) ∧
      IsHermitianPSH ω (fun x => u x + ((-b : ℝ) : EReal)) ∧
      (∀ x, u x + ((-b : ℝ) : EReal) ≤ 0) ∧
      ∃ p, u p + ((-b : ℝ) : EReal) = 0 := by
  obtain ⟨b, hsup, hbound, p, hp⟩ := exists_real_sup ω hu
  refine ⟨b, hsup, isFormPSH_add_const hu (-b), fun x => ?_, p, ?_⟩
  · calc
      u x + ((-b : ℝ) : EReal) ≤ (b : EReal) + ((-b : ℝ) : EReal) :=
        add_le_add (hbound x) le_rfl
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  · rw [hp, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]

end SGPT.PSH.HermitianExtremalNormalization
