import SGPT.NAPotential.WeightedSkodaFixedTruncation
import SGPT.NAPotential.WeightedDivisionLimitIdentity

/-!
# Singular weighted division from the actual input

The producer is the two-stage assembly: smooth regularized division gives
the fixed-truncation quotients and the second common subsequence removes the
truncation.  It assumes only the holomorphic data, psh weight, domain data,
and original weighted input integral.  No solutions, approximating sequence,
or bound certificate occur as hypotheses.  The resulting statement is local
analytic division; a multiplier-ideal stalk statement requires further work.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Okounkov.TranscendentalSkoda

theorem exists_uniform_singular_weighted_division
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
      ∃ h : Fin r → ComplexModel n → ℂ,
        (∀ i, DifferentiableOn ℂ (h i) U) ∧
        (∀ z ∈ U, f z = ∑ i, g i z * h i z) ∧
        (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖h i z‖ ^ 2) *
          (multiplierWeight p (generatorLog g z) * multiplierWeight 1 (ψ z))) ≤
          ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D := by
  obtain ⟨U, hU, hKU, hUD, hfixed⟩ :=
    exists_uniform_fixed_truncation_divisions n hn Ω D hrel hconv hbounded K hK hKD p hp
  refine ⟨U, hU, hKU, hUD, ?_⟩
  intro r g hg f hf ψ hψ hI
  have hp0 : 0 < p := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hUΩ : U ⊆ Ω := hUD.trans (subset_closure.trans hrel.2)
  have hgU : ∀ i, DifferentiableOn ℂ (g i) U := fun i => (hg i).mono hUD
  have hex : ∀ N, ∃ h : Fin r → ComplexModel n → ℂ,
      (∀ i, DifferentiableOn ℂ (h i) U) ∧
      (∀ z ∈ U, f z = ∑ i, g i z * h i z) ∧
      (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖h i z‖ ^ 2) * truncatedSkodaWeight g p ψ N z) ≤
        ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D :=
    hfixed r g hg f hf ψ hψ hI
  choose H hHhol hHid hHbound using hex
  let A : ℝ≥0∞ := ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI
  have hwm : ∀ z ∈ U, Monotone fun N => truncatedSkodaWeight g p ψ N z :=
    fun z hz => truncatedSkodaWeight_monotone hψ (hUΩ hz)
  have hmeas : ∀ N, AEMeasurable (truncatedSkodaWeight g p ψ N) (volume.restrict U) :=
    fun N => truncatedSkodaWeight_aemeasurable hU hUΩ hgU hp0 hψ N
  have hlow : ∀ z ∈ U, ∃ ρ > 0, ∃ c : ℝ, 0 < c ∧ ∀ y ∈ ball z ρ,
      ENNReal.ofReal c ≤ truncatedSkodaWeight g p ψ 0 y :=
    fun z hz => truncatedSkodaWeight_zero_local_lower hU hUΩ hgU hp0 hψ hz
  obtain ⟨σ, h, hσ, hhol, hconv, hbound⟩ :=
    exists_common_holomorphic_limit_of_finite_weighted_bounds hU hwm hmeas hlow hHhol hA hHbound
  have hid : ∀ z ∈ U, f z = ∑ i, g i z * h i z := by
    apply finite_division_identity_of_tendsto
      (H := fun j => H (σ j)) (fun i z hz => (hconv i).tendsto_at hz)
    exact fun j z hz => hHid (σ j) z hz
  refine ⟨h, hhol, hid, ?_⟩
  calc
    _ = ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖h i z‖ ^ 2) *
        ⨆ N, truncatedSkodaWeight g p ψ N z := by
      refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
      rw [iSup_truncatedSkodaWeight hψ (hUΩ hz)]
    _ ≤ A := hbound

end SGPT.NAPotential.GAGAMult
