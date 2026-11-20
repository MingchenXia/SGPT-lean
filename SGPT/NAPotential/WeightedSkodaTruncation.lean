import SGPT.NAPotential.WeightedSkodaLower
import SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiRegularReduction
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics

/-!
# Actual weights for the outer singular Skoda limit

The weights are constructed from the original tuple and truncations of the
original psh function.  Their monotonicity, exact supremum, measurability and
local positive lower bound are derived internally; no sequence of solutions
or uniform `L²` certificate is an input to these lemmas.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalSkoda

variable {n r : ℕ}

/-- The genuine weight at truncation level `N`, including both pole sets. -/
def truncatedSkodaWeight (g : Fin r → ComplexModel n → ℂ) (p : ℝ)
    (ψ : ComplexModel n → EReal) (N : ℕ) (z : ComplexModel n) : ℝ≥0∞ :=
  multiplierWeight p (generatorLog g z) * multiplierWeight 1 (truncationReal ψ N z : EReal)

/-- The actual weights increase as the truncation descends. -/
theorem truncatedSkodaWeight_monotone {Ω : Opens (ComplexModel n)}
    {g : Fin r → ComplexModel n → ℂ} {p : ℝ} {ψ : ComplexModel n → EReal}
    (hψ : PlurisubharmonicOn ψ Ω) {z : ComplexModel n} (hz : z ∈ Ω) :
    Monotone (fun N => truncatedSkodaWeight g p ψ N z) := by
  intro i j hij
  unfold truncatedSkodaWeight
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply multiplierWeight_antitone (c := (1 : ℝ)) (by norm_num)
  exact EReal.coe_le_coe_iff.mpr (truncationReal_antitone hψ hz hij)

/-- The entire increasing family recovers the original singular weight,
including common zeros of `g` and points where `ψ = -∞`. -/
theorem iSup_truncatedSkodaWeight {Ω : Opens (ComplexModel n)}
    {g : Fin r → ComplexModel n → ℂ} {p : ℝ} {ψ : ComplexModel n → EReal}
    (hψ : PlurisubharmonicOn ψ Ω) {z : ComplexModel n} (hz : z ∈ Ω) :
    (⨆ N, truncatedSkodaWeight g p ψ N z) =
      multiplierWeight p (generatorLog g z) * multiplierWeight 1 (ψ z) := by
  have heq : (⨆ N : ℕ, multiplierWeight 1 (truncationReal ψ N z : EReal)) =
      multiplierWeight 1 (ψ z) := by
    apply le_antisymm
    · refine iSup_le fun N => ?_
      apply multiplierWeight_antitone (c := (1 : ℝ)) (by norm_num)
      rw [coe_truncationReal hψ N hz]
      exact le_max_left _ _
    · exact multiplierWeight_le_iSup_truncationReal hψ one_pos hz
  change (⨆ N : ℕ, multiplierWeight p (generatorLog g z) *
    multiplierWeight 1 (truncationReal ψ N z : EReal)) = _
  rw [← ENNReal.mul_iSup, heq]

/-- The first weight has the ballwise positive lower bound demanded by the
weighted normal-family theorem, produced from the actual source data. -/
theorem truncatedSkodaWeight_zero_local_lower {Ω : Opens (ComplexModel n)}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    {g : Fin r → ComplexModel n → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    {p : ℝ} (hp : 0 < p) {ψ : ComplexModel n → EReal}
    (hψ : PlurisubharmonicOn ψ Ω) {z : ComplexModel n} (hz : z ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ ball z ρ, ENNReal.ofReal c ≤ truncatedSkodaWeight g p ψ 0 y := by
  have htr : PlurisubharmonicOn (fun y => (truncationReal ψ 0 y : EReal)) U :=
    (truncationReal_plurisubharmonicOn hψ 0).mono hUΩ
  simpa only [truncatedSkodaWeight] using
    (exists_local_lower_bound_singular_skoda_weight hU hg htr hp hz)

/-- Each actual truncation weight is measurable on the normal-family domain. -/
theorem truncatedSkodaWeight_aemeasurable {Ω : Opens (ComplexModel n)}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    {g : Fin r → ComplexModel n → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    {p : ℝ} (hp : 0 < p) {ψ : ComplexModel n → EReal}
    (hψ : PlurisubharmonicOn ψ Ω) (N : ℕ) :
    AEMeasurable (truncatedSkodaWeight g p ψ N) (volume.restrict U) := by
  have hlog : PlurisubharmonicOn (generatorLog g) U := by
    intro z hz
    have h := plurisubharmonicAt_scaled_generatorLog ⟨U, hU, hz, hg⟩ one_pos
    simpa only [EReal.coe_one, one_mul] using h
  have hqlog : QuasiPlurisubharmonicOn (generatorLog g) U :=
    fun z hz => (hlog z hz).quasiPlurisubharmonicAt
  have hm1 := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
    (μ := volume) hU hqlog hp.ne' (f := fun _ => (1 : ℂ)) continuousOn_const
  have hm1' : AEMeasurable (fun z => multiplierWeight p (generatorLog g z))
      (volume.restrict U) := hm1.congr (Eventually.of_forall fun z => by simp [multiplierDensity])
  have hqψ : QuasiPlurisubharmonicOn (fun z => (truncationReal ψ N z : EReal)) U :=
    fun z hz => (truncationReal_plurisubharmonicOn hψ N z (hUΩ hz)).quasiPlurisubharmonicAt
  have hm2 := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
    (μ := volume) hU hqψ one_ne_zero (f := fun _ => (1 : ℂ)) continuousOn_const
  have hm2' : AEMeasurable (fun z => multiplierWeight 1 (truncationReal ψ N z : EReal))
      (volume.restrict U) := hm2.congr (Eventually.of_forall fun z => by simp [multiplierDensity])
  exact hm1'.mul hm2'

end SGPT.NAPotential.GAGAMult
