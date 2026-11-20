import SGPT.PSH.HermitianExtremalCurrentAlgebra
import SGPT.PSH.HermitianExtremalCurrentLimits
import SGPT.PSH.HermitianExtremalSeries

/-!
# Genuine normalized weighted pole series for Hermitian backgrounds

Uniform local negative-integral estimates rule out collapse of the actual
weighted series. Finite convex current algebra and decreasing full-current
positivity then put its limit in the same Hermitian PSH class. No closedness
or global potential for the background is used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalSeriesPole

open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremalL1Bound HermitianExtremalSeries
  HermitianExtremalCurrentAlgebra HermitianExtremalCurrentLimits
open scoped Topology ENNReal

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual normalized weighted series belongs to the same nonclosed
Hermitian PSH class. Its finite locus is manufactured from the common local
L1 estimate, rather than supplied as a limit certificate. -/
theorem isHermitianPSH_normalized_series (ω : Background (m + 1) M)
    (hcorr : HasCommonLocalCorrections (n := m + 1) (IsHermitianPSH ω))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, a j ≤ 1)
    (ψ : ℕ → M → EReal) (hψ : ∀ j, IsHermitianPSH ω (ψ j))
    (hle : ∀ j x, ψ j x ≤ 0) (hnorm : ∀ j, ∃ x, 0 ≤ ψ j x) :
    IsHermitianPSH ω (fun x => ⨅ N, partialSum a ψ N x) := by
  classical
  have hpartial (N : ℕ) : IsHermitianPSH ω (partialSum a ψ N) := by
    have h := isHermitianPSH_fintype_nonnegSum ω (fun j : Fin N => a j)
      (fun j => ha j) (by simpa only [Fin.sum_univ_eq_sum_range] using hbudget N)
      (fun j : Fin N => ψ j) (fun j => hψ j)
    have heq : (fun x => ∑ j : Fin N, (a j : EReal) * ψ j x) = partialSum a ψ N := by
      funext x
      exact (Finset.sum_range (fun j => (a j : EReal) * ψ j x)).symm
    exact heq ▸ h
  have hbudgetENN (N : ℕ) : ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => ha j)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hbudget N)
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  let e := complexChartAt (n := m + 1) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.val.open_target
    (e.val p) (e.val.map_source hp)
  let K := closedBall (e.val p) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ e.val.target := (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨B, hBtop, hB⟩ := exists_lintegral_compact_le hcorr e hK hKt 0
  have hbound (j : ℕ) :
      ∫⁻ z in K, (-chartFunction (ψ j) e z).toENNReal ≤ B := by
    exact hB (ψ j) (hψ j) (hle j) (by simpa only [neg_zero, EReal.coe_zero] using hnorm j)
  have hmeas (j : ℕ) : AEMeasurable (fun z => (-chartFunction (ψ j) e z).toENNReal)
      (volume.restrict K) :=
    ((hψ j).quasiPshPotential.aemeasurable_chart_restrict e hKt).neg.ereal_toENNReal
  have hae := ae_ne_bot_series_of_uniform_lintegral ha
    (fun j z => hle j (e.val.symm z)) hmeas hBtop hbound hbudgetENN
  have hKpos : volume K ≠ 0 := ne_of_gt
    ((measure_ball_pos volume (e.val p) (half_pos hr)).trans_le (measure_mono ball_subset_closedBall))
  obtain ⟨z, _, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hKpos hae
  exact isHermitianPSH_iInf_of_exists_ne_bot ω hcorr hpartial
    (partialSum_antitone ha hle) ⟨e.val.symm z, hz⟩

/-- The same genuine series is nonpositive and carries every input pole
whose coefficient is positive. -/
theorem normalized_series_nonpositive_and_poles (ω : Background (m + 1) M)
    (hcorr : HasCommonLocalCorrections (n := m + 1) (IsHermitianPSH ω))
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, a j ≤ 1)
    (ψ : ℕ → M → EReal) (hψ : ∀ j, IsHermitianPSH ω (ψ j))
    (hle : ∀ j x, ψ j x ≤ 0) (hnorm : ∀ j, ∃ x, 0 ≤ ψ j x) :
    ∃ q : M → EReal, IsHermitianPSH ω q ∧ (∀ x, q x ≤ 0) ∧
      ∀ j x, ψ j x = ⊥ → q x = ⊥ := by
  refine ⟨fun x => ⨅ N, partialSum a ψ N x,
    isHermitianPSH_normalized_series ω hcorr a (fun j => (ha j).le) hbudget ψ hψ hle hnorm,
    fun x => ?_, fun j x hx => series_eq_bot_of_input_pole (ha j) hx⟩
  exact (iInf_le (fun N => partialSum a ψ N x) 0).trans_eq (by simp [partialSum])

end SGPT.PSH.HermitianExtremalSeriesPole
