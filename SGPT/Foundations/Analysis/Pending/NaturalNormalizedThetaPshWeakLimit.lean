import SGPT.Foundations.Analysis.Pending.NaturalGenuineWeakEventSuprema
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Original normalization retained by genuine native weak theta-PSH limits

Compact nested zero-level sets belong to the actual new event-supremum
sequence. No original weak-filter event is identified with an atTop tail.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshWeakLimit

open FirstPass NaturalGenuineWeakEventSuprema

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2}

/-- The original singular supremum-normalized potential has an actual zero point. -/
theorem exists_eq_zero_of_sup_eq_zero {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (hsup : (⨆ x, u x) = 0) :
    ∃ x₀, u x₀ = 0 := by
  obtain ⟨x₀, _, hmax⟩ :=
    (hu.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
      univ_nonempty isCompact_univ
  refine ⟨x₀, le_antisymm (hsup ▸ le_iSup u x₀) ?_⟩
  rw [← hsup]
  exact iSup_le (fun x => hmax (mem_univ x))

/-- Original supremum-zero normalization survives the actual genuine weak chart limit. -/
theorem sup_eq_zero_of_chart_weak_tests
    {ι : Type*} [Countable ι] {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hsup : ∀ i, (⨆ x, u i x) = 0)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume))) :
    (⨆ x, v x) = 0 := by
  have hle (i : ι) (x : M) : u i x ≤ 0 := hsup i ▸ le_iSup (u i) x
  obtain ⟨S, _hS, hSne, _hantiS, hg, hantiW, heq, _htend⟩ :=
    exists_genuine_antitone_events_exact_inf_and_tendsto hu hv hlim
      (C := 0) (fun i x => by simpa using hle i x)
  let W (k : ℕ) : M → EReal := uscRegularization (⨆ i : S k, u i.val)
  have hWle (k : ℕ) : W k ≤ fun _ => (0 : EReal) := by
    have hsupLe : (⨆ i : S k, u i.val) ≤ fun _ : M => (0 : EReal) := by
      intro x
      simp only [iSup_apply]
      exact iSup_le (fun i => hle i.val x)
    simpa only [uscRegularization_const] using uscRegularization_mono hsupLe
  have hvle (x : M) : v x ≤ 0 := by
    have h := congrFun heq x
    simp only [iInf_apply] at h
    rw [← h]
    exact (iInf_le (fun k => W k x) 0).trans (hWle 0 x)
  let Z (k : ℕ) : Set M := (W k) ⁻¹' Ici 0
  have hZclosed (k : ℕ) : IsClosed (Z k) :=
    (hg k).1.quasiPlurisubharmonic.upperSemicontinuous.isClosed_preimage 0
  have hZne (k : ℕ) : (Z k).Nonempty := by
    obtain ⟨i, hi⟩ := hSne k
    obtain ⟨x, hx⟩ := exists_eq_zero_of_sup_eq_zero (hu i) (hsup i)
    refine ⟨x, ?_⟩
    change 0 ≤ W k x
    rw [← hx]
    have hsupRead : u i x ≤ (⨆ j : S k, u j.val) x := by
      simp only [iSup_apply]
      exact le_iSup (fun j : S k => u j.val x) ⟨i, hi⟩
    exact hsupRead.trans (le_uscRegularization _ x)
  have hZsucc (k : ℕ) : Z (k + 1) ⊆ Z k := by
    intro x hx
    exact hx.trans (hantiW (Nat.le_succ k) x)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    Z hZsucc hZne (hZclosed 0).isCompact hZclosed
  have hxv : 0 ≤ v x := by
    have h := congrFun heq x
    simp only [iInf_apply] at h
    rw [← h]
    exact le_iInf (fun k => mem_iInter.mp hx k)
  have hxzero : v x = 0 := le_antisymm (hvle x) hxv
  apply le_antisymm (iSup_le hvle)
  rw [← hxzero]
  exact le_iSup v x

end SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshWeakLimit
