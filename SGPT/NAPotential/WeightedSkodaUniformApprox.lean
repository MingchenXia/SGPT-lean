import SGPT.NAPotential.WeightedSkodaDivision
import SGPT.NAPotential.WeightedSkodaInputComparison
import SGPT.Foundations.Analysis.FirstPass.BTTruncations
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Actual regularized divisions from the original weighted input

For a singular psh weight and a tuple that may have common zeros, construct
the smooth truncation approximants and apply the smooth-weight division draft
to the regularized tuple.  The output family and its one uniform estimate
are produced from the actual original input integral.  This is the first stage
of the singular-weight limit, not yet the limiting division theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalSkoda

/-- The original input integral, with actual multiplier weights at both sets
of poles and the library's `0 * ∞ = 0` convention. -/
def singularSkodaInput {n r : ℕ} (g : Fin r → ComplexModel n → ℂ)
    (f : ComplexModel n → ℂ) (q : ℝ) (ψ : ComplexModel n → EReal)
    (D : Set (ComplexModel n)) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight q (generatorLog g z) *
    multiplierWeight 1 (ψ z)

/-- The entire regularized input integral is bounded by the original one. -/
theorem weightedSkodaInput_regTuple_le {n r : ℕ} (D : Set (ComplexModel n))
    (hD : MeasurableSet D) (g : Fin r → ComplexModel n → ℂ)
    (f : ComplexModel n → ℂ) {p δ : ℝ} (hp : 0 < p + 1) (hδ : 0 < δ)
    (v : ComplexModel n → ℝ) (ψ : ComplexModel n → EReal)
    (hv : ∀ z ∈ D, ψ z ≤ (v z : EReal)) :
    weightedSkodaInput (regTuple g δ) f p v D ≤ singularSkodaInput g f (p + 1) ψ D := by
  unfold weightedSkodaInput singularSkodaInput
  refine setLIntegral_mono' hD fun z hz => ?_
  rw [generatorNormSq_regTuple g hδ.le]
  exact regularized_input_density_le g f hp hδ (hv z hz)

/-- On a fixed open `U`, chosen independently of the tuple, function, weight,
and truncation level, every singular-input datum produces its actual smooth
approximants and regularized divisions with a single original-input bound. -/
theorem exists_uniform_regularized_weighted_divisions
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
      ∀ N : ℕ, ∃ (v : ℕ → ComplexModel n → ℝ)
        (H : ℕ → Fin (r + 1) → ComplexModel n → ℂ),
        IsDecreasingApproximation D (truncationReal ψ N) v ∧
        (∀ j i, DifferentiableOn ℂ (H j i) U) ∧
        (∀ j z, z ∈ U → f z = ∑ i : Fin r, g i z * H j i.castSucc z +
          ((Real.sqrt (1 / ((j : ℝ) + 1)) : ℝ) : ℂ) * H j (Fin.last r) z) ∧
        ∀ j, (∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H j i z‖ ^ 2) *
            (generatorNormSq g z + 1 / ((j : ℝ) + 1)) ^ (-p) * Real.exp (-v j z))) ≤
          ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D := by
  obtain ⟨U, hUo, hKU, hUD, hdiv⟩ :=
    exists_smooth_psh_weighted_skoda_division n hn D D.isOpen hconv hbounded K hK hKD p hp
  refine ⟨U, hUo, hKU, hUD, ?_⟩
  intro r g hg f hf ψ hψ hI N
  obtain ⟨v, hv⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
    (truncationReal_isLocallyBoundedPshOn hψ N) hrel
  have hDΩ : (D : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hrel.2
  have hvdom : ∀ j z, z ∈ D → ψ z ≤ (v j z : EReal) := by
    intro j z hz
    have htr : ψ z ≤ (truncationReal ψ N z : EReal) := by
      rw [coe_truncationReal hψ N (hDΩ hz)]
      exact le_max_left _ _
    have hvj : truncationReal ψ N z ≤ v j z :=
      (hv.2.1 z hz).le_of_tendsto (hv.2.2 z hz) j
    exact htr.trans (EReal.coe_le_coe_iff.mpr hvj)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1 : 0 < p + 1 := by linarith
  have hex : ∀ j : ℕ, ∃ H : Fin (r + 1) → ComplexModel n → ℂ,
      (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i : Fin r, g i z * H i.castSucc z +
        ((Real.sqrt (1 / ((j : ℝ) + 1)) : ℝ) : ℂ) * H (Fin.last r) z) ∧
      (∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) *
          (generatorNormSq g z + 1 / ((j : ℝ) + 1)) ^ (-p) * Real.exp (-v j z))) ≤
        ENNReal.ofReal (2 + 2 * n / (p - n)) * singularSkodaInput g f (p + 1) ψ D := by
    intro j
    set δ : ℝ := 1 / ((j : ℝ) + 1) with hδdef
    have hδ : 0 < δ := by positivity
    have hle := weightedSkodaInput_regTuple_le (D : Set (ComplexModel n)) D.isOpen.measurableSet
      g f hp1 hδ (v j) ψ (fun z hz => hvdom j z hz)
    have hreg : weightedSkodaInput (regTuple g δ) f p (v j) D ≠ ⊤ :=
      ne_top_of_le_ne_top hI hle
    have hpos : ∀ z ∈ D, 0 < generatorNormSq (regTuple g δ) z := by
      intro z hz
      rw [generatorNormSq_regTuple g hδ.le]
      exact add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) hδ
    obtain ⟨H, hHhol, hHid, hHb⟩ := hdiv (r + 1) (regTuple g δ)
      (differentiableOn_regTuple hg δ) hpos f hf (v j) (hv.1 j).1 (hv.1 j).2.1 hreg
    refine ⟨H, hHhol, ?_, ?_⟩
    · intro z hz
      simpa only [sum_regTuple_mul, hδdef] using hHid z hz
    · have hHb' := hHb.trans (mul_le_mul_of_nonneg_left hle zero_le)
      calc
        _ = ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) *
            generatorNormSq (regTuple g δ) z ^ (-p) * Real.exp (-v j z)) := by
          refine lintegral_congr fun z => ?_
          rw [generatorNormSq_regTuple g hδ.le, hδdef]
        _ ≤ _ := hHb'
  choose H hHhol hHid hHbound using hex
  exact ⟨v, H, hv, hHhol, hHid, hHbound⟩

end SGPT.NAPotential.GAGAMult
