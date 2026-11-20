import SGPT.PSH.HermitianExtremalPoleAlternative
import SGPT.PSH.HermitianQuasiPSHScaling

/-!
# Countable unions of genuine global quasi-PSH pole sets

Every input is an original locally quasi-plurisubharmonic potential, with
its actual local nondegeneracy. The proved positive-scaling theorem puts
each in the same supplied nonclosed Hermitian class. The normalized pole
series then produces a single genuine potential for the countable union.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- A pole set of any genuine global quasi-PSH potential has a potential
in every fixed Hermitian class after strictly positive scaling. -/
theorem exists_hermitian_pole_of_quasiPsh_pole (ω : Background (m + 1) M)
    (A : Set M) {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (hpole : ∀ x ∈ A, u x = ⊥) :
    ∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥ := by
  obtain ⟨t, ht, htu⟩ := exists_pos_mul_isHermitianPSH ω hu
  refine ⟨fun x => (t : EReal) * u x, htu, fun x hx => ?_⟩
  change (t : EReal) * u x = ⊥
  rw [hpole x hx]
  exact EReal.mul_bot_of_pos (EReal.coe_pos.mpr ht)

/-- Countably many genuine global quasi-PSH pole sets have one original
nonpositive pole potential in the supplied nonclosed Hermitian class. -/
theorem exists_pole_iUnion_of_quasiPsh_poles (ω : Background (m + 1) M)
    (A : ℕ → Set M)
    (hA : ∀ j, ∃ u : M → EReal, IsGlobalQuasiPshPotential (n := m + 1) u ∧
      ∀ x ∈ A j, u x = ⊥) :
    ∃ q : M → EReal, IsHermitianPSH ω q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ ⋃ j, A j, q x = ⊥ := by
  apply exists_pole_iUnion ω A
  intro j
  obtain ⟨u, hu, hpole⟩ := hA j
  exact exists_hermitian_pole_of_quasiPsh_pole ω (A j) hu hpole

end SGPT.PSH.HermitianExtremal
