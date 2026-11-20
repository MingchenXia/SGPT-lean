import SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization
import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior

set_option autoImplicit false

/-!
# General increasing directed-net continuity for independent mixed products

Xia, Corollary 2.4.1. Joint countable Choquet selection and directed upper
bounds preserve every regularized supremum. A neighborhood contradiction
upgrades the genuine mixed sequence theorem to the entire directed net.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open IncreasingMixedContinuity IncreasingMixedRegularizedContinuity

noncomputable section

/-- A countable family of increasing directed families admits a single monotone
sequence preserving all regularized suprema, in any chosen tail. -/
theorem exists_monotone_sequence_uscRegularization_iSup_eq
    {X K I : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [Countable K] [Preorder I] [IsDirectedOrder I] (i0 : I)
    {u : I → K → X → EReal} (hmono : ∀ a, Monotone fun i => u i a) :
    ∃ j : ℕ → I, Monotone j ∧ (∀ k, i0 ≤ j k) ∧ ∀ a,
      uscRegularization (⨆ k, u (j k) a) = uscRegularization (⨆ i, u i a) := by
  classical
  have hsel : ∀ a : K, ∃ s : ℕ → X → EReal,
      (∀ k, s k ∈ range (fun i => u i a)) ∧
      uscRegularization (⨆ k, s k) = uscRegularization (⨆ i, u i a) := by
    intro a
    obtain ⟨s, hs, heq⟩ := exists_seq_uscRegularization_iSup_eq
      (F := range (fun i => u i a)) ⟨u i0 a, mem_range_self i0⟩
    have hr : sSup (range (fun i => u i a)) = ⨆ i, u i a := sSup_range
    rw [hr] at heq
    exact ⟨s, hs, heq⟩
  choose s hs hsup using hsel
  have hindices : ∀ a k, ∃ i, u i a = s a k := fun a k => hs a k
  choose b hb using hindices
  let G : Set I := insert i0 (⋃ a : K, range (b a))
  have hGc : G.Countable := (countable_iUnion fun a => countable_range (b a)).insert i0
  obtain ⟨c, hc⟩ := hGc.exists_eq_range ⟨i0, mem_insert _ _⟩
  choose ub hub1 hub2 using exists_ge_ge (α := I)
  let j : ℕ → I := fun k => Nat.rec (ub i0 (c 0))
    (fun k prev => ub prev (c (k + 1))) k
  have hj : Monotone j := monotone_nat_of_le_succ fun k => hub1 (j k) (c (k + 1))
  have hji0 : ∀ k, i0 ≤ j k := fun k => (hub1 i0 (c 0)).trans (hj (Nat.zero_le k))
  have hjc : ∀ k, c k ≤ j k := by
    intro k
    cases k with
    | zero => exact hub2 i0 (c 0)
    | succ k => exact hub2 (j k) (c (k + 1))
  refine ⟨j, hj, hji0, fun a => le_antisymm ?_ ?_⟩
  · exact uscRegularization_mono (iSup_le fun k => le_iSup (fun i => u i a) (j k))
  · rw [← hsup a]
    apply uscRegularization_mono
    apply iSup_le
    intro k
    have hmem : b a k ∈ G := mem_insert_of_mem _ (mem_iUnion.mpr ⟨a, mem_range_self k⟩)
    rw [hc] at hmem
    obtain ⟨l, hl⟩ := hmem
    rw [← hb a k]
    exact (hmono a (hl ▸ hjc l)).trans (le_iSup (fun k => u (j k) a) l)

/-- A directed net converges if every monotone sequence dominating a fixed
sequence converges. This does not require countable cofinality. -/
theorem tendsto_atTop_of_monotone_dominating_sequences
    {I Y : Type*} [Preorder I] [IsDirectedOrder I] [TopologicalSpace Y]
    (s : ℕ → I) {f : I → Y} {y : Y}
    (hseq : ∀ j : ℕ → I, Monotone j → (∀ k, s k ≤ j k) →
      Tendsto (fun k => f (j k)) atTop (𝓝 y)) :
    Tendsto f atTop (𝓝 y) := by
  classical
  let : Nonempty I := ⟨s 0⟩
  apply tendsto_def.mpr
  intro V hV
  change ∀ᶠ i in atTop, f i ∈ V
  by_contra hn
  have hbad : ∀ i : I, ∃ b, i ≤ b ∧ f b ∉ V :=
    frequently_atTop.mp (not_eventually.mp hn)
  choose next hnext houtside using hbad
  choose ub hub1 hub2 using exists_ge_ge (α := I)
  let j : ℕ → I := fun k => Nat.rec (next (s 0))
    (fun k prev => next (ub prev (s (k + 1)))) k
  have hj : Monotone j := monotone_nat_of_le_succ fun k =>
    (hub1 (j k) (s (k + 1))).trans (hnext _)
  have hs : ∀ k, s k ≤ j k := by
    intro k
    cases k with
    | zero => exact hnext (s 0)
    | succ k => exact (hub2 (j k) (s (k + 1))).trans (hnext _)
  have hnot : ∀ k, f (j k) ∉ V := by
    intro k
    cases k with
    | zero => exact houtside (s 0)
    | succ k => exact houtside (ub (j k) (s (k + 1)))
  obtain ⟨k, hk⟩ := ((hseq j hj hs).eventually_mem hV).exists
  exact hnot k hk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual independent mixed measures converge along every increasing directed
PSH net whose individual regularized suprema are genuine. -/
theorem weakTendsto_mixed_of_directed_monotone_regularized
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : I → Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (theta a).val (u j a))
    (hmono : ∀ a, Monotone fun j => u j a)
    (hv : ∀ a, IsThetaPshPotential (theta a).val
      (uscRegularization (⨆ j, u j a))) :
    Tendsto (fun j => finiteMixedMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteMixedMeasure omega theta
        (fun a => uscRegularization (⨆ j, u j a)) hv)) := by
  classical
  obtain ⟨s, _, _, hsup⟩ := exists_monotone_sequence_uscRegularization_iSup_eq
    (Classical.arbitrary I) hmono
  apply tendsto_atTop_of_monotone_dominating_sequences s
  intro j hj hjs
  have heq : ∀ a, uscRegularization (⨆ k, u (j k) a) =
      uscRegularization (⨆ i, u i a) := by
    intro a
    apply le_antisymm
    · exact uscRegularization_mono (iSup_le fun k => le_iSup (fun i => u i a) (j k))
    · rw [← hsup a]
      exact uscRegularization_mono (iSup_mono fun k => hmono a (hjs k))
  have hvj : ∀ a, IsThetaPshPotential (theta a).val
      (uscRegularization (⨆ k, u (j k) a)) := by
    intro a
    rw [heq a]
    exact hv a
  have hlim := weakTendsto_mixed_of_monotone_regularized omega (fun k => hu (j k))
    (fun a k l hkl => hmono a (hj hkl)) hvj
  simpa only [heq] using hlim

/-- Every actual continuous test integral converges along the full increasing
directed mixed net. -/
theorem tendsto_integral_mixed_of_directed_monotone_regularized
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : I → Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (theta a).val (u j a))
    (hmono : ∀ a, Monotone fun j => u j a)
    (hv : ∀ a, IsThetaPshPotential (theta a).val
      (uscRegularization (⨆ j, u j a))) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂globalMixedMeasure theta (u j)
      (fun a => (hu j a).1)) atTop
      (𝓝 (∫ x, chi x ∂globalMixedMeasure theta
        (fun a => uscRegularization (⨆ j, u j a)) (fun a => (hv a).1))) := by
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (weakTendsto_mixed_of_directed_monotone_regularized omega hu hmono hv))
      (BoundedContinuousFunction.mkOfCompact chi)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A true finite global family bound produces a genuine regularized supremum. -/
theorem isThetaPshPotential_regularized_of_uniformlyBounded
    {I : Type*} [Nonempty I] {theta : ClosedRealOneOneForm n M}
    {u : I → M → EReal} (hu : ∀ i, IsThetaPshPotential theta.val (u i))
    {C : ℝ} (hC : ∀ i x, u i x ≤ (C : EReal)) :
    IsThetaPshPotential theta.val (uscRegularization (⨆ i, u i)) := by
  have h := SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup hu hC
  have heq : (fun x => ⨆ i, u i x) = ⨆ i, u i := by
    funext x
    simp only [iSup_apply]
  rw [heq] at h
  exact h

/-- Source-facing mixed weak convergence: genuine limits are produced from
actual uniform family bounds rather than supplied as assumptions. -/
theorem weakTendsto_mixed_of_directed_monotone_uniformlyBounded
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : I → Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (theta a).val (u j a))
    (hmono : ∀ a, Monotone fun j => u j a)
    {C : Fin n → ℝ} (hC : ∀ a j x, u j a x ≤ (C a : EReal)) :
    Tendsto (fun j => finiteMixedMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteMixedMeasure omega theta
        (fun a => uscRegularization (⨆ j, u j a))
        (fun a => isThetaPshPotential_regularized_of_uniformlyBounded
          (fun j => hu j a) (hC a)))) :=
  weakTendsto_mixed_of_directed_monotone_regularized omega hu hmono
    (fun a => isThetaPshPotential_regularized_of_uniformlyBounded (fun j => hu j a) (hC a))

/-- The actual total mixed masses converge for general uniformly bounded
increasing directed PSH nets, as in Xia's Corollary 2.4.1. -/
theorem tendsto_mixed_mass_of_directed_monotone_uniformlyBounded
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : I → Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (theta a).val (u j a))
    (hmono : ∀ a, Monotone fun j => u j a)
    {C : Fin n → ℝ} (hC : ∀ a j x, u j a x ≤ (C a : EReal)) :
    Tendsto (fun j => (globalMixedMeasure theta (u j) (fun a => (hu j a).1)).real univ)
      atTop (𝓝 ((globalMixedMeasure theta (fun a => uscRegularization (⨆ j, u j a))
        (fun a => (isThetaPshPotential_regularized_of_uniformlyBounded
          (fun j => hu j a) (hC a)).1)).real univ)) := by
  have h := tendsto_integral_mixed_of_directed_monotone_regularized omega hu hmono
    (fun a => isThetaPshPotential_regularized_of_uniformlyBounded
      (fun j => hu j a) (hC a)) (1 : C(M, ℝ))
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] using h

end
end SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets
