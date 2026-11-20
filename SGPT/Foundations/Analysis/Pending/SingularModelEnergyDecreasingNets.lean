import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedContinuity
import Mathlib.Topology.Semicontinuity.Lindelof

set_option autoImplicit false

/-!
# General directed-net continuity of singular-model energy

Xia SGPT PDF0120--0121, Proposition 3.1.16. A countable semicontinuous
subfamily with the same actual pointwise infimum gives a monotone sequence
of indices by directed upper bounds. The actual extended sequence energy
identity then produces the energy identity and convergence for the full net.
This adapts the source's L1 extraction using hereditary Lindelof topology.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyDecreasingNets

open FirstPass FirstPass.PositiveClasses RelativeDarvasDistance RelativePreceqClasses

noncomputable section

/-- A decreasing semicontinuous family on a second-countable space admits a
monotone sequence of indices with exactly the same pointwise infimum, in any tail. -/
theorem exists_monotone_sequence_iInf_eq {X ι : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [Preorder ι] [IsDirectedOrder ι]
    {v : ι → X → EReal} (i0 : ι)
    (husc : ∀ i, UpperSemicontinuous (v i)) (hanti : Antitone v) :
    ∃ j : ℕ → ι, Monotone j ∧ (∀ k, i0 ≤ j k) ∧
      (⨅ k, v (j k)) = ⨅ i, v i := by
  classical
  have hglb : IsGLB (range v) (⨅ i, v i) :=
    ⟨by rintro f ⟨i, rfl⟩; exact iInf_le _ i,
      fun f hf => le_iInf fun i => hf (mem_range_self i)⟩
  obtain ⟨G, hGF, hGc, hGglb⟩ :=
    exists_countable_upperSemicontinuous_isGLB
      (by rintro f ⟨i, rfl⟩; exact husc i) hglb
  have hG'F : insert (v i0) G ⊆ range v := by
    rintro f (rfl | hf)
    · exact mem_range_self i0
    · exact hGF hf
  have hG'glb : IsGLB (insert (v i0) G) (⨅ i, v i) :=
    ⟨fun f hf => hglb.1 (hG'F hf),
      fun f hf => hGglb.2 fun g hg => hf (mem_insert_of_mem _ hg)⟩
  obtain ⟨s, hs⟩ := (hGc.insert (v i0)).exists_eq_range ⟨v i0, mem_insert _ _⟩
  have hsF (k : ℕ) : s k ∈ range v := hG'F (by rw [hs]; exact mem_range_self k)
  choose a ha using hsF
  choose ub hub1 hub2 using exists_ge_ge (α := ι)
  let j : ℕ → ι := fun k =>
    Nat.rec (ub i0 (a 0)) (fun k prev => ub prev (a (k + 1))) k
  have hj : Monotone j := monotone_nat_of_le_succ fun k => hub1 (j k) (a (k + 1))
  have hji0 (k : ℕ) : i0 ≤ j k :=
    (hub1 i0 (a 0)).trans (hj (Nat.zero_le k))
  have hja (k : ℕ) : a k ≤ j k := by
    cases k with
    | zero => exact hub2 i0 (a 0)
    | succ k => exact hub2 (j k) (a (k + 1))
  refine ⟨j, hj, hji0, le_antisymm ?_ (le_iInf fun k => iInf_le _ (j k))⟩
  apply hG'glb.2
  intro f hf
  rw [hs] at hf
  obtain ⟨k, rfl⟩ := hf
  exact (iInf_le (fun k => v (j k)) k).trans ((hanti (hja k)).trans_eq (ha k))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual extended energy commutes with the infimum of any decreasing
directed net of genuine potentials with a tail more singular than the model. -/
theorem energy_iInf_of_directed_antitone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u : M → EReal} (hφ : IsModelPotential θ φ) {ui : ι → M → EReal}
    (hui : ∀ i, IsThetaPshPotential θ.val (ui i)) (i0 : ι)
    (hui0φ : MoreSingularOn (ui i0) φ univ)
    (hanti : ∀ x, Antitone fun i => ui i x)
    (hlim : ∀ x, Tendsto (fun i => ui i x) atTop (𝓝 (u x))) :
    (⨅ i, energy θ φ hφ (ui i)) = energy θ φ hφ u := by
  let : Nonempty ι := ⟨i0⟩
  have hinf (x : M) : (⨅ i, ui i x) = u x :=
    tendsto_nhds_unique (tendsto_atTop_iInf (hanti x)) (hlim x)
  obtain ⟨j, hj, hji0, hji⟩ := exists_monotone_sequence_iInf_eq i0
    (fun i => (hui i).1.quasiPlurisubharmonic.upperSemicontinuous)
    (fun i k hik x => hanti x hik)
  have hjlim (x : M) : Tendsto (fun k => ui (j k) x) atTop (𝓝 (u x)) := by
    have ht := tendsto_atTop_iInf (fun a b hab => hanti x (hj hab))
    have heq := congrFun hji x
    simp only [iInf_apply] at heq
    rw [heq, hinf x] at ht
    exact ht
  have hseq := SingularModelEnergyExtendedContinuity.energy_iInf_of_antitone omega θ hφ
    (fun k => hui (j k))
    ((MoreSingularOn.of_le fun x _ => hanti x (hji0 0)).trans hui0φ)
    (fun x a b hab => hanti x (hj hab)) hjlim
  refine le_antisymm ?_ (le_iInf fun i => energy_mono_of_le fun x => ?_)
  · exact (le_iInf fun k => iInf_le (fun i => energy θ φ hφ (ui i)) (j k)).trans_eq hseq
  · rw [← hinf x]
    exact iInf_le _ i

/-- Actual extended energies converge along general decreasing directed PSH nets.
No countable cofinality or finite-energy assumption is needed. -/
theorem energy_tendsto_of_directed_antitone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u : M → EReal} (hφ : IsModelPotential θ φ) {ui : ι → M → EReal}
    (hui : ∀ i, IsThetaPshPotential θ.val (ui i)) (i0 : ι)
    (hui0φ : MoreSingularOn (ui i0) φ univ)
    (hanti : ∀ x, Antitone fun i => ui i x)
    (hlim : ∀ x, Tendsto (fun i => ui i x) atTop (𝓝 (u x))) :
    Tendsto (fun i => energy θ φ hφ (ui i)) atTop (𝓝 (energy θ φ hφ u)) := by
  let : Nonempty ι := ⟨i0⟩
  have hmono : Antitone fun i => energy θ φ hφ (ui i) :=
    fun i j hij => energy_mono_of_le fun x => hanti x hij
  have hL := tendsto_atTop_iInf hmono
  rwa [energy_iInf_of_directed_antitone omega θ hφ hui i0 hui0φ hanti hlim] at hL

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyDecreasingNets
