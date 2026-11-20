import SGPT.Foundations.Analysis.Pending.NaturalCountableWeakHartogsEvents
import SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshOrder
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof

/-!
# Genuine original decreasing suprema of actual countable weak-filter events

Only the newly constructed sequence of USC event suprema is given an
atTop convergence statement. The original weak convergence filter keeps
its actual events, including when it is a cofinal ultrafilter.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalGenuineWeakEventSuprema

open FirstPass NaturalCountableWeakHartogsEvents NaturalWeakThetaPshOrder

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- The literal original USC supremum of a nonempty countable original subfamily is genuine. -/
theorem isThetaPshPotential_usc_iSup_subtype_of_le
    {ι : Type*} [Countable ι] {u : ι → M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) {C : ℝ}
    (hC : ∀ i x, u i x ≤ (C : EReal)) {S : Set ι} (hS : S.Nonempty) :
    IsThetaPshPotential θ (uscRegularization (⨆ i : S, u i.val)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  have hScount : S.Countable := Set.to_countable S
  let f : ℕ → ι := enumerateCountable hScount i₀
  have hfm (j : ℕ) : f j ∈ S := enumerateCountable_mem hScount hi₀ j
  have hsup : (⨆ j : ℕ, u (f j)) = (⨆ i : S, u i.val) := by
    apply le_antisymm
    · intro x
      simp only [iSup_apply]
      exact iSup_le (fun j => le_iSup_of_le ⟨f j, hfm j⟩ le_rfl)
    · intro x
      simp only [iSup_apply]
      refine iSup_le fun i => ?_
      obtain ⟨j, hj⟩ := subset_range_enumerate hScount i₀ i.property
      have hread : f j = i.val := hj
      rw [← hread]
      exact le_iSup (fun j => u (f j) x) j
  have hg := NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
    (fun j => hu (f j)) (fun j x => hC (f j) x)
  rw [hsup] at hg
  exact hg

/-- Genuine nested original filter-event suprema have exactly the original pointwise limit. -/
theorem exists_genuine_antitone_events_exact_inf_and_tendsto
    {ι : Type*} [Countable ι] {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal)) :
    ∃ S : ℕ → Set ι,
      (∀ k, S k ∈ l) ∧ (∀ k, (S k).Nonempty) ∧ Antitone S ∧
      (∀ k, IsThetaPshPotential θ (uscRegularization (⨆ i : S k, u i.val))) ∧
      Antitone (fun k => uscRegularization (⨆ i : S k, u i.val)) ∧
      (⨅ k : ℕ, uscRegularization (⨆ i : S k, u i.val)) = v ∧
      (∀ x, Tendsto (fun k => uscRegularization (⨆ i : S k, u i.val) x) atTop (𝓝 (v x))) := by
  obtain ⟨S, hS, hSne, hantiS, hantiW, hupper⟩ :=
    exists_antitone_events_and_usc_inf_le_of_chart_weak_tests hu hv hlim hC
  have hg (k : ℕ) : IsThetaPshPotential θ (uscRegularization (⨆ i : S k, u i.val)) :=
    isThetaPshPotential_usc_iSup_subtype_of_le hu hC (hSne k)
  have hlower (k : ℕ) : v ≤ uscRegularization (⨆ i : S k, u i.val) := by
    apply le_of_chart_weak_limit_eventually_le hu hv (hg k) hlim
    filter_upwards [hS k] with i hi
    intro x
    have hsup : u i x ≤ (⨆ j : S k, u j.val) x := by
      simp only [iSup_apply]
      exact le_iSup (fun j : S k => u j.val x) ⟨i, hi⟩
    exact hsup.trans (le_uscRegularization _ x)
  have heq : (⨅ k : ℕ, uscRegularization (⨆ i : S k, u i.val)) = v :=
    le_antisymm hupper (le_iInf hlower)
  refine ⟨S, hS, hSne, hantiS, hg, hantiW, heq, fun x => ?_⟩
  have h := tendsto_atTop_iInf (fun k m hkm => hantiW hkm x)
  have hinf : (⨅ k : ℕ, uscRegularization (⨆ i : S k, u i.val) x) = v x := by
    simpa only [iInf_apply] using congrFun heq x
  simpa only [hinf] using h

end SGPT.Foundations.Analysis.Pending.NaturalGenuineWeakEventSuprema
