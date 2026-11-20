import SGPT.NAPotential.WeightedSupProduct
import SGPT.Okounkov.TranscendentalSkodaRegularization
import SGPT.Okounkov.TranscendentalSkodaSurjective
import SGPT.Foundations.Analysis.FirstPass.BTTruncations

/-!
# The actual regularized weights at one truncation level

This isolates the pointwise monotone limit of the two simultaneous
regularizations.  The real function family `v` is the smooth decreasing
approximation constructed by the regularization theorem; no quotient family
or estimate is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Okounkov.TranscendentalSkoda

variable {n r : ℕ}

def regularizedSkodaWeight (g : Fin r → ComplexModel n → ℂ) (p : ℝ)
    (v : ℕ → ComplexModel n → ℝ) (j : ℕ) (z : ComplexModel n) : ℝ≥0∞ :=
  ENNReal.ofReal ((generatorNormSq g z + 1 / ((j : ℝ) + 1)) ^ (-p)) *
    ENNReal.ofReal (Real.exp (-v j z))

theorem regularizedSkodaWeight_monotone {D : Opens (ComplexModel n)}
    {g : Fin r → ComplexModel n → ℂ} {p : ℝ} (hp : 0 < p)
    {u : ComplexModel n → ℝ} {v : ℕ → ComplexModel n → ℝ}
    (hv : IsDecreasingApproximation D u v) {z : ComplexModel n} (hz : z ∈ D) :
    Monotone (fun j => regularizedSkodaWeight g p v j z) := by
  intro i j hij
  unfold regularizedSkodaWeight
  apply mul_le_mul'
  · apply ENNReal.ofReal_le_ofReal
    have hδ : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact Real.rpow_le_rpow_of_nonpos
      (add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) (by positivity))
      (by linarith) (by linarith)
  · apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (neg_le_neg (hv.2.1 z hz hij))

theorem iSup_regularizedSkodaWeight {D : Opens (ComplexModel n)}
    {g : Fin r → ComplexModel n → ℂ} {p : ℝ} (hp : 0 < p)
    {u : ComplexModel n → ℝ} {v : ℕ → ComplexModel n → ℝ}
    (hv : IsDecreasingApproximation D u v) {z : ComplexModel n} (hz : z ∈ D) :
    (⨆ j, regularizedSkodaWeight g p v j z) =
      multiplierWeight p (generatorLog g z) * multiplierWeight 1 (u z : EReal) := by
  let a : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
    ((generatorNormSq g z + 1 / ((j : ℝ) + 1)) ^ (-p))
  let b : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (-v j z))
  have ha : Monotone a := by
    intro i j hij
    apply ENNReal.ofReal_le_ofReal
    have hδ : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact Real.rpow_le_rpow_of_nonpos
      (add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) (by positivity))
      (by linarith) (by linarith)
  have hb : Monotone b := by
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hv.2.1 z hz hij)))
  have hga : (⨆ j, a j) = multiplierWeight p (generatorLog g z) := by
    apply le_antisymm
    · exact iSup_le fun j => ofReal_rpow_le_multiplierWeight g hp (by positivity) z
    · exact multiplierWeight_le_iSup g hp z
  have hgb : (⨆ j, b j) = multiplierWeight 1 (u z : EReal) := by
    rw [multiplierWeight_coe, one_mul]
    have hlim : Tendsto b atTop (𝓝 (ENNReal.ofReal (Real.exp (-u z)))) := by
      apply ENNReal.tendsto_ofReal
      exact (Real.continuous_exp.tendsto _).comp (hv.2.2 z hz).neg
    apply le_antisymm
    · refine iSup_le fun j => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      exact neg_le_neg ((hv.2.1 z hz).le_of_tendsto (hv.2.2 z hz) j)
    · exact le_of_tendsto' hlim fun j => le_iSup b j
  change (⨆ j, a j * b j) = _
  rw [iSup_mul_of_monotone a b ha hb, hga, hgb]

/-- Each regularized weight is measurable on the actual quotient domain. -/
theorem regularizedSkodaWeight_aemeasurable {D : Opens (ComplexModel n)}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hUD : U ⊆ D)
    {g : Fin r → ComplexModel n → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    {p : ℝ} {u : ComplexModel n → ℝ} {v : ℕ → ComplexModel n → ℝ}
    (hv : IsDecreasingApproximation D u v) (j : ℕ) :
    AEMeasurable (regularizedSkodaWeight g p v j) (volume.restrict U) := by
  have hS : ContinuousOn (generatorNormSq g) U :=
    (contDiffOn_generatorNormSq hU hg).continuousOn
  have hw : ContinuousOn (fun z => (generatorNormSq g z + 1 / ((j : ℝ) + 1)) ^ (-p)) U := by
    refine ContinuousOn.rpow_const (hS.add continuousOn_const) fun z _ => Or.inl ?_
    exact (add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) (by positivity)).ne'
  have hvj : ContinuousOn (v j) U := ((hv.1 j).1.continuousOn).mono hUD
  exact ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hU.measurableSet).mul
    ((ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn hvj.neg)).aemeasurable hU.measurableSet)

/-- The first regularized weight has a positive lower bound on a whole ball,
derived from continuity of the actual tuple and smooth approximation. -/
theorem regularizedSkodaWeight_zero_local_lower {D : Opens (ComplexModel n)}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hUD : U ⊆ D)
    {g : Fin r → ComplexModel n → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    {p : ℝ} (hp : 0 < p) {u : ComplexModel n → ℝ} {v : ℕ → ComplexModel n → ℝ}
    (hv : IsDecreasingApproximation D u v) {z : ComplexModel n} (hz : z ∈ U) :
    ∃ ρ > 0, ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ ball z ρ, ENNReal.ofReal c ≤ regularizedSkodaWeight g p v 0 y := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z hz
  have hclosed : closedBall z (R / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hRU
  have hSc : ContinuousOn (generatorNormSq g) (closedBall z (R / 2)) :=
    (contDiffOn_generatorNormSq hU hg).continuousOn.mono hclosed
  have hvc : ContinuousOn (v 0) (closedBall z (R / 2)) :=
    (hv.1 0).1.continuousOn.mono (hclosed.trans hUD)
  obtain ⟨B, hB⟩ := (isCompact_closedBall z (R / 2)).exists_bound_of_continuousOn hSc
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (R / 2)).exists_bound_of_continuousOn hvc
  set M : ℝ := max B 0 + 2
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right B 0]
  refine ⟨R / 2, by linarith, M ^ (-p) * Real.exp (-C), by positivity, ?_⟩
  intro y hy
  have hyK : y ∈ closedBall z (R / 2) := ball_subset_closedBall hy
  have hS : generatorNormSq g y + 1 ≤ M := by
    have hb := hB y hyK
    rw [Real.norm_of_nonneg (generatorNormSq_nonneg g y)] at hb
    dsimp [M]
    linarith [le_max_left B 0]
  have hvc' : v 0 y ≤ C := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hyK)
  unfold regularizedSkodaWeight
  simp only [Nat.cast_zero, zero_add, div_one]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hM.le _)]
  apply mul_le_mul'
  · apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_nonpos (by linarith [generatorNormSq_nonneg g y]) hS (by linarith)
  · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hvc'))

end SGPT.NAPotential.GAGAMult
