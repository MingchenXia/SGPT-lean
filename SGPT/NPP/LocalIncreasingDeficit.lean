import SGPT.Foundations.Analysis.Pending.IncreasingPshGapCapacityZero
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasingCollar

/-!
# The actual unbounded local increasing deficit has zero relative capacity

This is an intermediate producer for revised `prop:mono_psh_cap` (2).
Inputs are actual original PSH functions, monotonicity and Lebesgue-a.e.
convergence. No target capacity convergence, negligible-set certificate,
boundedness, connectedness or positive-dimension assumption is supplied.
The output concerns the persistent deficit, not finite-stage gap convergence.

Checked with the full local monotone-capacity package; the retained source,
recursive guard and logs are in validation/source-local-increasing-capacity-20261105.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.NPP.LocalIncreasingCapacityDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- The genuine unbounded increasing deficit is internally reduced to the
actual locally bounded Bedford--Taylor increasing-gap theorem. -/
theorem relCapacity_deficit_eq_zero_of_monotone_ae
    {D O : Opens (ComplexModel n)} (hOD : O ≤ D)
    {u : ℕ → ComplexModel n → EReal} {v : ComplexModel n → EReal}
    (hu : ∀ j, PlurisubharmonicOn (u j) D)
    (hv : PlurisubharmonicOn v D)
    (hmono : ∀ z ∈ D, Monotone fun j => u j z)
    (hae : ∀ᵐ z, z ∈ D → Tendsto (fun j => u j z) atTop (𝓝 (v z))) :
    relCapacity O {z | z ∈ O ∧ (⨆ j, u j z) < v z} = 0 := by
  let E : ℕ → Set (ComplexModel n) := fun k =>
    {z | z ∈ O ∧ ∃ a : ℝ, 0 < a ∧
      ∀ j, truncationReal (u j) k z + a ≤ truncationReal v k z}
  have hE : ∀ k, relCapacity O (E k) = 0 := by
    intro k
    have hm : ∀ z ∈ D, Monotone fun j => truncationReal (u j) k z := by
      intro z hz i j hij
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncationReal (hu i) k hz, coe_truncationReal (hu j) k hz]
      exact max_le_max (hmono z hz hij) le_rfl
    have ht : ∀ᵐ z, z ∈ D →
        Tendsto (fun j => truncationReal (u j) k z) atTop
          (𝓝 (truncationReal v k z)) := by
      filter_upwards [hae] with z hz hzD
      have hmax : Tendsto (fun j => truncation (u j) k z) atTop
          (𝓝 (truncation v k z)) := (hz hzD).max tendsto_const_nhds
      apply EReal.tendsto_coe.mp
      rw [coe_truncationReal hv k hzD]
      exact hmax.congr fun j => (coe_truncationReal (hu j) k hzD).symm
    have hInc := isIncApprox_of_monotone_ae
      (truncationReal_isLocallyBoundedPshOn hv k)
      (fun j => truncationReal_isLocallyBoundedPshOn (hu j) k) hm ht
    exact SGPT.Foundations.Analysis.Pending.IncreasingPshGapCapacityZero.relCapacity_gap_eq_zero_of_le
      hOD (truncationReal_isLocallyBoundedPshOn hv k) hInc
  have hsub : {z | z ∈ O ∧ (⨆ j, u j z) < v z} ⊆ ⋃ k, E k := by
    rintro z ⟨hzO, hgap⟩
    have hzD : z ∈ D := hOD hzO
    have hvt : v z ≠ ⊤ := (hv z hzD).ne_top
    have hvb : v z ≠ ⊥ := ne_bot_of_gt hgap
    have hveq : ((v z).toReal : EReal) = v z := EReal.coe_toReal hvt hvb
    obtain ⟨k, hk⟩ := exists_nat_gt (-(v z).toReal)
    have hkV : ((-(k : ℝ) : ℝ) : EReal) < v z := by
      rw [← hveq, EReal.coe_lt_coe_iff]
      linarith
    let q : EReal := max (⨆ j, u j z) ((-(k : ℝ) : ℝ) : EReal)
    have hqv : q < v z := max_lt hgap hkV
    have hqt : q ≠ ⊤ := ne_top_of_le_ne_top hvt hqv.le
    have hqb : q ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe _).trans_le (le_max_right _ _))
    have hqeq : (q.toReal : EReal) = q := EReal.coe_toReal hqt hqb
    have hqvr : q.toReal < (v z).toReal := by
      have h := hqv
      rw [← hqeq, ← hveq, EReal.coe_lt_coe_iff] at h
      exact h
    have hub : ∀ j, truncationReal (u j) k z ≤ q.toReal := by
      intro j
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncationReal (hu j) k hzD, hqeq]
      exact max_le_max (le_iSup (fun i => u i z) j) le_rfl
    have hvk : truncationReal v k z = (v z).toReal := by
      apply EReal.coe_injective
      rw [coe_truncationReal hv k hzD, hveq]
      exact max_eq_left hkV.le
    refine mem_iUnion.mpr ⟨k, hzO, ((v z).toReal - q.toReal) / 2, by linarith, ?_⟩
    intro j
    rw [hvk]
    linarith [hub j]
  refine le_antisymm ((relCapacity_mono hsub).trans ?_) bot_le
  calc relCapacity O (⋃ k, E k) ≤ ∑' k, relCapacity O (E k) := relCapacity_iUnion_le O E
    _ = 0 := by simp only [hE, tsum_zero]

end SGPT.NPP.LocalIncreasingCapacityDraft
