import SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshHartogs
import SGPT.Foundations.Analysis.FirstPass.Envelopes
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Order.Filter.Finite

/-!
# Actual countable finite intersections of weak Hartogs filter events

The resulting sets are genuine members of the original filter. Their
literal original USC suprema recover the original limit from above;
no event is asserted to contain an atTop tail.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalCountableWeakHartogsEvents

open FirstPass NaturalWeakThetaPshHartogs

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- Genuine finite intersections of countably chosen Hartogs events recover the USC infimum above. -/
theorem exists_antitone_events_and_usc_inf_le_of_chart_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal)) :
    ∃ S : ℕ → Set ι,
      (∀ k, S k ∈ l) ∧ (∀ k, (S k).Nonempty) ∧ Antitone S ∧
      Antitone (fun k => uscRegularization (⨆ i : S k, u i.val)) ∧
      (⨅ k : ℕ, uscRegularization (⨆ i : S k, u i.val)) ≤ v := by
  classical
  let P (q : ℚ) : Set M := {x | v x < ((q : ℝ) : EReal)}
  have hloc : ∀ (q : ℚ) (x : P q), ∃ V : Set M,
      V ∈ 𝓝 (x : M) ∧ ∀ᶠ i in l, ∀ y ∈ V, u i y ≤ ((q : ℝ) : EReal) :=
    fun q x => eventually_locally_le_of_chart_weak_tests hu hv hlim hC x.val x.property
  choose V hV hbound using hloc
  let Dq (q : ℚ) (x : P q) : Set ι := {i | ∀ y ∈ V q x, u i y ≤ ((q : ℝ) : EReal)}
  have hDq (q : ℚ) (x : P q) : Dq q x ∈ l := hbound q x
  have hcover : ∀ q : ℚ, ∃ r : Set (P q), r.Countable ∧
      P q ⊆ ⋃ x ∈ r, interior (V q x) := by
    intro q
    apply (HereditarilyLindelofSpace.isLindelof (P q)).elim_countable_subcover
      (fun x => interior (V q x)) (fun _ => isOpen_interior)
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hV q ⟨x, hx⟩)⟩
  choose r hrCount hrCover using hcover
  let F : Set (Set ι) := insert univ (⋃ q : ℚ, Dq q '' r q)
  have hFCount : F.Countable :=
    (countable_iUnion (fun q => (hrCount q).image (Dq q))).insert univ
  have hFmem : ∀ D ∈ F, D ∈ l := by
    intro D hD
    rcases mem_insert_iff.mp hD with h | h
    · rw [h]
      exact univ_mem
    · obtain ⟨q, hq⟩ := mem_iUnion.mp h
      obtain ⟨x, _, rfl⟩ := hq
      exact hDq q x
  let D : ℕ → Set ι := enumerateCountable hFCount univ
  have hD (j : ℕ) : D j ∈ l :=
    hFmem _ (enumerateCountable_mem hFCount (mem_insert _ _) j)
  let S (k : ℕ) : Set ι := ⋂ j ∈ Finset.range k, D j
  have hS (k : ℕ) : S k ∈ l :=
    (biInter_finset_mem (Finset.range k)).mpr (fun j _ => hD j)
  have hanti : Antitone S := by
    intro k m hkm i hi
    simp only [S, mem_iInter] at hi ⊢
    intro j hj
    exact hi j (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hkm))
  have hSD (j : ℕ) : S (j + 1) ⊆ D j := by
    intro i hi
    exact mem_iInter.mp (mem_iInter.mp hi j) (Finset.mem_range.mpr (Nat.lt_succ_self j))
  have hWanti : Antitone (fun k => uscRegularization (⨆ i : S k, u i.val)) := by
    intro k m hkm
    apply uscRegularization_mono
    intro x
    simp only [iSup_apply]
    exact iSup_le (fun i => le_iSup_of_le ⟨i.val, hanti hkm i.property⟩ le_rfl)
  refine ⟨S, hS, fun k => Filter.nonempty_of_mem (hS k), hanti, hWanti, ?_⟩
  intro x
  rw [iInf_apply]
  apply le_of_forall_gt
  intro a ha
  obtain ⟨q, hvq, hqa⟩ := EReal.exists_rat_btwn_of_lt ha
  have hxP : x ∈ P q := hvq
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hrCover q hxP)
  obtain ⟨hyr, hxy⟩ := mem_iUnion.mp hy
  have hFD : Dq q y ∈ F := mem_insert_of_mem _ (mem_iUnion.mpr ⟨q, ⟨y, hyr, rfl⟩⟩)
  obtain ⟨j, hj⟩ := subset_range_enumerate hFCount univ hFD
  have hnbhd : V q y ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxy
  have hWbound : uscRegularization (⨆ i : S (j + 1), u i.val) x ≤ ((q : ℝ) : EReal) := by
    refine (uscRegularization_le_localSup _ hnbhd).trans ?_
    refine iSup_le fun z => iSup_le fun hz => ?_
    simp only [iSup_apply]
    refine iSup_le fun i => ?_
    have hidx : i.val ∈ Dq q y := by
      rw [← hj]
      exact hSD j i.property
    exact hidx z hz
  exact (iInf_le_of_le (j + 1) hWbound).trans_lt hqa

end SGPT.Foundations.Analysis.Pending.NaturalCountableWeakHartogsEvents
