import SGPT.NAPotential.WeightedSkodaSingularDivision

/-!
# The local Skoda step of Siu's global generation

Blueprint `claude-gagamult:skoda-step`.  For a plurisubharmonic weight `Ψ` on a ball `B(p, R)` of
`ℂⁿ` (`n ≥ 1`) and a holomorphic `f` on a smaller ball `B(p, r)` with

`∫_{B(p,r)} |f|² |z - p|^{-2(n+2)} e^{-Ψ} < ∞`,

there are holomorphic `h₁, …, hₙ` near `p` with `f = ∑ᵢ (zᵢ - pᵢ) hᵢ` and `∫ |hᵢ|² e^{-Ψ} < ∞`
near `p`.  In stalk terms: `𝓘(Ψ + (n+2) log |z - p|²)_p ⊆ 𝔪_p · 𝓘(Ψ)_p`, the Nakayama step of
Siu's uniform global generation (Demailly, *Analytic methods in algebraic geometry*, proof of
Siu's uniform global generation).

The proof is the weighted Skoda division `exists_uniform_singular_weighted_division` applied to
the coordinate tuple `zᵢ - pᵢ` with exponent `p' = n + 1 > n`; on the unit ball the factor
`|z - p|^{-2(n+1)}` of the output weight is at least `1`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- The coordinate functions `zᵢ - pᵢ` centred at `p`. -/
def centredCoords (p : ComplexModel n) : Fin n → ComplexModel n → ℂ := fun i z => z i - p i

theorem generatorVector_centredCoords (p z : ComplexModel n) :
    generatorVector (centredCoords p) z = z - p := by
  ext i
  simp [generatorVector, centredCoords]

theorem generatorLog_centredCoords (p z : ComplexModel n) :
    generatorLog (centredCoords p) z = logNormSq (z - p) := by
  rw [generatorLog, generatorVector_centredCoords]

theorem differentiable_centredCoords (p : ComplexModel n) (i : Fin n) :
    Differentiable ℂ (centredCoords p i) := by
  have h : Differentiable ℂ (fun z : ComplexModel n => z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable
  exact h.sub_const _

theorem centredCoords_self (p : ComplexModel n) (i : Fin n) : centredCoords p i p = 0 := by
  simp [centredCoords]

/-- `|z - p|^{-2c} ≥ 1` on the unit ball, for `c ≥ 0` (with the value `∞` at `p`). -/
theorem one_le_multiplierWeight_logNormSq {c : ℝ} (hc : 0 ≤ c) {p z : ComplexModel n}
    (hz : ‖z - p‖ ≤ 1) : 1 ≤ multiplierWeight c (logNormSq (z - p)) := by
  have hle : logNormSq (z - p) ≤ 0 := by
    unfold logNormSq
    rw [← ENNReal.log_one]
    apply ENNReal.log_monotone
    rw [ENNReal.ofReal_le_one]
    nlinarith [norm_nonneg (z - p)]
  have h0 : multiplierWeight c 0 = 1 := by
    rw [← EReal.coe_zero, multiplierWeight_coe]; simp
  rw [← h0]
  exact multiplierWeight_antitone hc hle

/-- **The local Skoda step.**  For `Ψ` psh on `B(p, R)`, `0 < r < R` and `f` holomorphic on
`B(p, r)` with `∫_{B(p,r)} |f|² |z - p|^{-2(n+2)} e^{-Ψ} < ∞`, there are an open `U ∋ p`, `U ⊆ B(p, r)`,
and `hᵢ` holomorphic on `U` with `f = ∑ᵢ (zᵢ - pᵢ) hᵢ` on `U` and `∫_U |hᵢ|² e^{-Ψ} < ∞`. -/
theorem exists_centred_division (hn : 0 < n) {p : ComplexModel n} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) {Ψ : ComplexModel n → EReal} (hΨ : PlurisubharmonicOn Ψ (ball p R))
    {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f (ball p r))
    (hI : ∫⁻ z in ball p r, ENNReal.ofReal (‖f z‖ ^ 2) *
        multiplierWeight ((n : ℝ) + 2) (logNormSq (z - p)) * multiplierWeight 1 (Ψ z) ≠ ⊤) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ p ∈ U ∧ U ⊆ ball p r ∧
      ∃ h : Fin n → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (h i) U) ∧
        (∀ z ∈ U, f z = ∑ i, centredCoords p i z * h i z) ∧
        ∀ i, ∫⁻ z in U, ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψ z) ≠ ⊤ := by
  set Ω : Opens (ComplexModel n) := ⟨ball p R, isOpen_ball⟩ with hΩ
  set D : Opens (ComplexModel n) := ⟨ball p r, isOpen_ball⟩ with hD
  have hrel : RelativelyCompactIn D Ω := by
    refine ⟨?_, ?_⟩
    · exact (isCompact_closedBall p r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
    · exact closure_ball_subset_closedBall.trans (closedBall_subset_ball hrR)
  have hconv : Convex ℝ (D : Set (ComplexModel n)) := convex_ball p r
  have hbdd : Bornology.IsBounded (D : Set (ComplexModel n)) := isBounded_ball
  have hK : IsCompact ({p} : Set (ComplexModel n)) := isCompact_singleton
  have hKD : ({p} : Set (ComplexModel n)) ⊆ D := singleton_subset_iff.mpr (mem_ball_self hr)
  have hpn : (n : ℝ) < (n : ℝ) + 1 := by linarith
  obtain ⟨U, hUo, hKU, hUD, hdiv⟩ := exists_uniform_singular_weighted_division n hn Ω D hrel
    hconv hbdd {p} hK hKD ((n : ℝ) + 1) hpn
  have hg : ∀ i, DifferentiableOn ℂ (centredCoords p i) D :=
    fun i => (differentiable_centredCoords p i).differentiableOn
  have hinput : singularSkodaInput (centredCoords p) f ((n : ℝ) + 1 + 1) Ψ D ≠ ⊤ := by
    unfold singularSkodaInput
    have e : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
    simp only [e, generatorLog_centredCoords]
    exact hI
  obtain ⟨h, hhol, hid, hbound⟩ := hdiv n (centredCoords p) hg f hf Ψ hΨ hinput
  have hpU : p ∈ U := hKU (mem_singleton p)
  set U' := U ∩ ball p 1 with hU'
  have hfin : ENNReal.ofReal (2 + 2 * n / ((n : ℝ) + 1 - n)) *
      singularSkodaInput (centredCoords p) f ((n : ℝ) + 1 + 1) Ψ D ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinput
  refine ⟨U', hUo.inter isOpen_ball, ⟨hpU, mem_ball_self one_pos⟩, inter_subset_left.trans hUD,
    h, fun i => (hhol i).mono inter_subset_left, fun z hz => hid z hz.1, fun i => ?_⟩
  refine ne_top_of_le_ne_top hfin (le_trans ?_ hbound)
  calc ∫⁻ z in U', ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψ z)
      ≤ ∫⁻ z in U', ENNReal.ofReal (∑ j, ‖h j z‖ ^ 2) *
          (multiplierWeight ((n : ℝ) + 1) (generatorLog (centredCoords p) z) *
            multiplierWeight 1 (Ψ z)) := by
        refine setLIntegral_mono' (hUo.inter isOpen_ball).measurableSet fun z hz => ?_
        have h1 : ENNReal.ofReal (‖h i z‖ ^ 2) ≤ ENNReal.ofReal (∑ j, ‖h j z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := fun j => ‖h j z‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
        have h2 : 1 ≤ multiplierWeight ((n : ℝ) + 1) (generatorLog (centredCoords p) z) := by
          rw [generatorLog_centredCoords]
          refine one_le_multiplierWeight_logNormSq (by positivity) ?_
          have := hz.2
          rw [mem_ball, dist_eq_norm] at this
          exact this.le
        calc ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψ z)
            = ENNReal.ofReal (‖h i z‖ ^ 2) * (1 * multiplierWeight 1 (Ψ z)) := by rw [one_mul]
          _ ≤ _ := by gcongr
    _ ≤ ∫⁻ z in U, ENNReal.ofReal (∑ j, ‖h j z‖ ^ 2) *
          (multiplierWeight ((n : ℝ) + 1) (generatorLog (centredCoords p) z) *
            multiplierWeight 1 (Ψ z)) := lintegral_mono_set inter_subset_left

end SGPT.NAPotential.GAGAMult
