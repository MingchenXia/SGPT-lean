import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Finite.Sigma

universe u v w
namespace SGPT.Foundations.Schemes
noncomputable section

/-- An infinite-field parameter avoids all associated primes of finitely
many actual Noetherian rings; each coefficient map genuinely attains one. -/
theorem finite_linear_maps_exists_nonZeroDivisors
    (K : Type u) [Field K] [Infinite K] {I : Type v} [Finite I]
    (R : I → Type w) [∀ i, CommRing (R i)] [∀ i, IsNoetherianRing (R i)]
    [∀ i, Module K (R i)] [∀ i, IsScalarTower K (R i) (R i)]
    (V : Type w) [AddCommGroup V] [Module K V]
    (f : ∀ i, V →ₗ[K] R i) (hf : ∀ i, ∃ x, f i x = 1) :
    ∃ x : V, ∀ i, f i x ∈ nonZeroDivisors (R i) := by
  let B := Σ i, {P : Ideal (R i) // P ∈ associatedPrimes (R i) (R i)}
  let : ∀ i, Finite {P : Ideal (R i) // P ∈ associatedPrimes (R i) (R i)} :=
    fun i ↦ (associatedPrimes.finite (R i) (R i)).to_subtype
  let : Finite B := by dsimp [B]; infer_instance
  let p (b : B) : Submodule K V :=
    (b.2.val.restrictScalars K).comap (f b.1)
  have hp (b : B) : p b ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hf b.1
    intro h
    have hmem : x ∈ p b := h.symm ▸ Submodule.mem_top
    have : (1 : R b.1) ∈ b.2.val := by simpa [p, hx] using hmem
    exact b.2.property.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨x, fun i ↦ ?_⟩
  by_contra h
  have hU : f i x ∈ ⋃ P ∈ associatedPrimes (R i) (R i), (P : Set (R i)) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact h
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hU
  exact hx ⟨i, ⟨P, hP⟩⟩ hxP



end
end SGPT.Foundations.Schemes
