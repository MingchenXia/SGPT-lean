import SGPT.PSH.HermitianExtremalPoleAlternative
import SGPT.PSH.HermitianEnvelopeStability
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

/-!
# The actual bounded regularized Hermitian extremal

The canonical original competitor supremum is regularized as a function.
Nonempty interior prevents a pole, the proved pole alternative bounds the
whole family, and actual nonclosed-background upper-envelope stability
manufactures its Hermitian PSH regularization. On every open subset of the
prescribed set the regularized extremal is exactly zero.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual upper-semicontinuous regularization of the literal original
extremal function; no class membership is stored in its definition. -/
def regularizedExtremal (ω : Background (m + 1) M) (A : Set M) : M → EReal :=
  uscRegularization (extremal ω A)

theorem regularizedExtremal_nonneg (ω : Background (m + 1) M) (A : Set M) (x : M) :
    0 ≤ regularizedExtremal ω A x :=
  (extremal_nonneg ω A x).trans (le_uscRegularization _ x)

theorem regularizedExtremal_upperSemicontinuous (ω : Background (m + 1) M) (A : Set M) :
    UpperSemicontinuous (regularizedExtremal ω A) :=
  upperSemicontinuous_uscRegularization _

/-- Every actual competitor lies below this same original regularization. -/
theorem competitor_le_regularizedExtremal (ω : Background (m + 1) M) {A : Set M}
    {u : M → EReal} (hu : u ∈ competitors ω A) : u ≤ regularizedExtremal ω A := by
  intro x
  exact (le_iSup (fun v : competitors ω A => v.val x) ⟨u, hu⟩).trans
    (le_uscRegularization (extremal ω A) x)

/-- A genuine uniform bound for the original family bounds its actual
regularization by the same finite constant. -/
theorem regularizedExtremal_le_of_uniform_bound (ω : Background (m + 1) M) (A : Set M)
    (C : ℝ) (hbound : ∀ u ∈ competitors ω A, ∀ x, u x ≤ (C : EReal)) :
    ∀ x, regularizedExtremal ω A x ≤ (C : EReal) := by
  intro x
  apply uscRegularization_le_of_eventually_le (upperSemicontinuousAt_const)
  exact Eventually.of_forall fun y => iSup_le fun u => hbound u.val u.property y

/-- Increasing the prescribed set decreases the actual regularized extremal. -/
theorem regularizedExtremal_antitone (ω : Background (m + 1) M)
    {A B : Set M} (hAB : A ⊆ B) : regularizedExtremal ω B ≤ regularizedExtremal ω A :=
  uscRegularization_mono (extremal_antitone ω hAB)

/-- The value is exactly zero on every actual open subset of the prescribed
set, without assuming a PSH conclusion for the regularization. -/
theorem regularizedExtremal_eq_zero_on_open (ω : Background (m + 1) M)
    {A U : Set M} (hU : IsOpen U) (hUA : U ⊆ A) :
    EqOn (regularizedExtremal ω A) (fun _ => 0) U := by
  intro x hx
  apply le_antisymm ?_ (regularizedExtremal_nonneg ω A x)
  apply uscRegularization_le_of_eventually_le upperSemicontinuousAt_const
  exact eventually_of_mem (hU.mem_nhds hx) fun y hy => extremal_le_zero_on ω (hUA hy)

variable [CompactSpace M] [ConnectedSpace M]

/-- The actual bounded branch of the extremal-pole alternative in a fixed
Hermitian class. The class and bounds of the regularization are produced. -/
theorem bounded_regularizedExtremal_of_not_pole (ω : Background (m + 1) M) (A : Set M)
    (hnot : ¬ ∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥) :
    ∃ C : ℝ, IsHermitianPSH ω (regularizedExtremal ω A) ∧
      (∀ x, 0 ≤ regularizedExtremal ω A x) ∧
      ∀ x, regularizedExtremal ω A x ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_of_not_pole ω A hnot
  have : Nonempty (competitors ω A) := ⟨⟨fun _ => 0, zero_mem_competitors ω A⟩⟩
  have hclass := isHermitianPSH_uscRegularization_iSup_of_uniform_bound ω
    (fun u : competitors ω A => u.val) (fun u => u.property.1) C
    (fun u x => hC u.val u.property x)
  exact ⟨C, hclass, regularizedExtremal_nonneg ω A,
    regularizedExtremal_le_of_uniform_bound ω A C hC⟩

/-- In particular the original extremal of any set with nonempty interior
has a genuinely manufactured bounded Hermitian PSH regularization. -/
theorem bounded_regularizedExtremal_of_nonempty_interior (ω : Background (m + 1) M)
    (A : Set M) (hA : (interior A).Nonempty) :
    ∃ C : ℝ, IsHermitianPSH ω (regularizedExtremal ω A) ∧
      (∀ x, 0 ≤ regularizedExtremal ω A x) ∧
      ∀ x, regularizedExtremal ω A x ≤ (C : EReal) :=
  bounded_regularizedExtremal_of_not_pole ω A (not_pole_of_nonempty_interior ω A hA)

omit [CompactSpace M] in
/-- A finite bound for this actual regularization rules out a pole in the
same class, because pole-preserving translates are unbounded competitors. -/
theorem not_pole_of_bounded_regularizedExtremal (ω : Background (m + 1) M) (A : Set M)
    (C : ℝ) (hC : ∀ x, regularizedExtremal ω A x ≤ (C : EReal)) :
    ¬ ∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥ := by
  rintro ⟨q, hq, hpoles⟩
  obtain ⟨u, hu, hbig⟩ := unbounded_competitors_of_pole ω A hq hpoles (C + 1)
  have hubound : (⨆ x, u x) ≤ (C : EReal) :=
    iSup_le fun x => (competitor_le_regularizedExtremal ω hu x).trans (hC x)
  have hfalse : C + 1 ≤ C := EReal.coe_le_coe_iff.mp (hbig.trans hubound)
  linarith

/-- Exactly the bounded branch is equivalent to the absence of a genuine
same-background pole potential. Both directions are proved on actual functions. -/
theorem not_pole_iff_bounded_regularizedExtremal (ω : Background (m + 1) M) (A : Set M) :
    (¬ ∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥) ↔
      ∃ C : ℝ, IsHermitianPSH ω (regularizedExtremal ω A) ∧
        (∀ x, 0 ≤ regularizedExtremal ω A x) ∧
        ∀ x, regularizedExtremal ω A x ≤ (C : EReal) := by
  constructor
  · exact bounded_regularizedExtremal_of_not_pole ω A
  · rintro ⟨C, _, _, hC⟩
    exact not_pole_of_bounded_regularizedExtremal ω A C hC

end SGPT.PSH.HermitianExtremal
