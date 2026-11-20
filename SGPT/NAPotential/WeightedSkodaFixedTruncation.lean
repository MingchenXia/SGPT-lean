import SGPT.NAPotential.WeightedSkodaUniformApprox
import SGPT.NAPotential.WeightedSkodaInnerWeights
import SGPT.NAPotential.WeightedSkodaTruncation
import SGPT.NAPotential.WeightedFiniteNormal
import SGPT.NAPotential.WeightedRegularizedLimitIdentity

/-!
# Fixed-truncation weighted division from the original input

This assembles the smooth regularized divisions, their actual monotone
weights, a single normal-family subsequence for all `r + 1` components,
the vanishing auxiliary term, and Fatou for the full sum.  Every quotient
and every estimate is produced from the original singular input.  This is
the inner stage only: the limits as truncation level `N` tends to infinity
are a further step.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Okounkov.TranscendentalSkoda

theorem exists_uniform_fixed_truncation_divisions
    (n : ℕ) (hn : 0 < n) (Ω D : Opens (ComplexModel n))
    (hrel : RelativelyCompactIn D Ω) (hconv : Convex ℝ (D : Set (ComplexModel n)))
    (hbounded : Bornology.IsBounded (D : Set (ComplexModel n)))
    (K : Set (ComplexModel n)) (hK : IsCompact K) (hKD : K ⊆ D)
    (p : ℝ) (hp : (n : ℝ) < p) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
      ∀ (r : ℕ) (g : Fin r → ComplexModel n → ℂ),
        (∀ i, DifferentiableOn ℂ (g i) D) →
      ∀ (f : ComplexModel n → ℂ), DifferentiableOn ℂ f D →
      ∀ ψ : ComplexModel n → EReal, PlurisubharmonicOn ψ Ω →
        singularSkodaInput g f (p + 1) ψ D ≠ ⊤ →
      ∀ N : ℕ, ∃ h : Fin r → ComplexModel n → ℂ,
        (∀ i, DifferentiableOn ℂ (h i) U) ∧
        (∀ z ∈ U, f z = ∑ i, g i z * h i z) ∧
        (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖h i z‖ ^ 2) *
          truncatedSkodaWeight g p ψ N z) ≤
          ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D := by
  obtain ⟨U, hU, hKU, hUD, hreg⟩ :=
    exists_uniform_regularized_weighted_divisions n hn Ω D hrel hconv hbounded K hK hKD p hp
  refine ⟨U, hU, hKU, hUD, ?_⟩
  intro r g hg f hf ψ hψ hI N
  obtain ⟨v, H, hv, hHhol, hHid, hHbound⟩ := hreg r g hg f hf ψ hψ hI N
  have hp0 : 0 < p := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  let A : ℝ≥0∞ := ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI
  have hwm : ∀ z ∈ U, Monotone fun j => regularizedSkodaWeight g p v j z :=
    fun z hz => regularizedSkodaWeight_monotone hp0 hv (hUD hz)
  have hmeas : ∀ j, AEMeasurable (regularizedSkodaWeight g p v j) (volume.restrict U) :=
    fun j => regularizedSkodaWeight_aemeasurable hU hUD (fun i => (hg i).mono hUD) hv j
  have hlow : ∀ z ∈ U, ∃ ρ > 0, ∃ c : ℝ, 0 < c ∧ ∀ y ∈ ball z ρ,
      ENNReal.ofReal c ≤ regularizedSkodaWeight g p v 0 y :=
    fun z hz => regularizedSkodaWeight_zero_local_lower hU hUD
      (fun i => (hg i).mono hUD) hp0 hv hz
  have hb : ∀ j, (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H j i z‖ ^ 2) *
      regularizedSkodaWeight g p v j z) ≤ A := by
    intro j
    calc
      _ = ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H j i z‖ ^ 2) *
          (generatorNormSq g z + 1 / ((j : ℝ) + 1)) ^ (-p) * Real.exp (-v j z)) := by
        refine lintegral_congr fun z => ?_
        unfold regularizedSkodaWeight
        rw [ENNReal.ofReal_mul (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (Real.rpow_nonneg (add_nonneg (generatorNormSq_nonneg g z) (by positivity)) _)),
          ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
        exact (mul_assoc _ _ _).symm
      _ ≤ A := hHbound j
  obtain ⟨σ, L, hσ, hLhol, hLconv, hLbound⟩ :=
    exists_common_holomorphic_limit_of_finite_weighted_bounds hU hwm hmeas hlow hHhol hA hb
  have hid := regularized_division_identity_of_locally_uniform_limit hσ hLconv hHid
  refine ⟨fun i => L i.castSucc, fun i => hLhol i.castSucc, hid, ?_⟩
  calc
    _ ≤ ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖L i z‖ ^ 2) * truncatedSkodaWeight g p ψ N z := by
      refine lintegral_mono fun z => ?_
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply ENNReal.ofReal_le_ofReal
      rw [Fin.sum_univ_castSucc]
      linarith [sq_nonneg ‖L (Fin.last r) z‖]
    _ = ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖L i z‖ ^ 2) *
        ⨆ j, regularizedSkodaWeight g p v j z := by
      refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
      rw [iSup_regularizedSkodaWeight hp0 hv (hUD hz)]
      rfl
    _ ≤ A := hLbound

end SGPT.NAPotential.GAGAMult
