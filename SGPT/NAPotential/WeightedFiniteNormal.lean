import SGPT.NAPotential.WeightedFiniteFatou
import SGPT.Okounkov.TranscendentalSkodaRegularization
import SGPT.Foundations.Analysis.Pending.WeightedL2ExtensionLimit

/-!
# A common weighted normal-family subsequence with one sum bound

This is a general normal-family lemma, not the final Skoda theorem.  The
quantified family and its bound are general analytic inputs to this lemma;
the actual Skoda assembly must construct both from the original input via
`exists_uniform_regularized_weighted_divisions` and the fixed-truncation
limit.  In particular, this module does not assume the target division or its
final estimate.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalSkoda

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- A finite family with one uniform weighted sum bound has one common
locally uniform subsequence, and the limiting whole sum has the same bound. -/
theorem exists_common_holomorphic_limit_of_finite_weighted_bounds
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    {w : ℕ → ComplexModel n → ℝ≥0∞}
    (hwmono : ∀ z ∈ U, Monotone fun j => w j z)
    (hwmeas : ∀ j, AEMeasurable (w j) (volume.restrict U))
    (hlow : ∀ z ∈ U, ∃ ρ > 0, ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ ball z ρ, ENNReal.ofReal c ≤ w 0 y)
    {F : ℕ → ι → ComplexModel n → ℂ} (hF : ∀ j i, DifferentiableOn ℂ (F j i) U)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ j, (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖F j i z‖ ^ 2) * w j z) ≤ A) :
    ∃ (σ : ℕ → ℕ) (H : ι → ComplexModel n → ℂ), StrictMono σ ∧
      (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ i, TendstoLocallyUniformlyOn (fun j => F (σ j) i) (H i) atTop U) ∧
      (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * ⨆ j, w j z) ≤ A := by
  classical
  have hcomponent : ∀ i j, (∫⁻ z in U, ENNReal.ofReal (‖F j i z‖ ^ 2) * w j z) ≤ A := by
    intro i j
    refine (lintegral_mono fun z => ?_).trans (hbound j)
    apply mul_le_mul_of_nonneg_right _ zero_le
    apply ENNReal.ofReal_le_ofReal
    exact Finset.single_le_sum (f := fun i => ‖F j i z‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  set P : ι → (ℕ → ℕ) → Prop := fun i φ => ∃ h : ComplexModel n → ℂ,
    DifferentiableOn ℂ h U ∧ TendstoLocallyUniformlyOn (fun j => F (φ j) i) h atTop U with hPdef
  have hPsub : ∀ i (φ ψ : ℕ → ℕ), P i φ → StrictMono ψ → P i (φ ∘ ψ) := by
    rintro i φ ψ ⟨h, hh, hc⟩ hψ
    exact ⟨h, hh, tendstoLocallyUniformlyOn_comp_strictMono hc hψ⟩
  have hPex : ∀ i (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (φ ∘ ψ) := by
    intro i φ hφ
    have hwm' : ∀ z ∈ ⋃ _j : ℕ, U, Monotone fun j => w (φ j) z := by
      intro z hz a b hab
      rw [iUnion_const] at hz
      exact hwmono z hz (hφ.monotone hab)
    have hmeas' : ∀ j, AEMeasurable (w (φ j)) (volume.restrict (⋃ _j : ℕ, U)) := by
      intro j
      rw [iUnion_const]
      exact hwmeas (φ j)
    have hlow' : ∀ z ∈ ⋃ _j : ℕ, U, ∃ ρ > 0, ∃ c : ℝ, 0 < c ∧
        ∀ y ∈ ball z ρ, ENNReal.ofReal c ≤ w (φ 0) y := by
      intro z hz
      rw [iUnion_const] at hz
      obtain ⟨ρ, hρ, c, hc, hcball⟩ := hlow z hz
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
      refine ⟨min ρ ε, lt_min hρ hε, c, hc, fun y hy => ?_⟩
      have hyρ : y ∈ ball z ρ := ball_subset_ball (min_le_left ρ ε) hy
      have hyU : y ∈ U := hεU (ball_subset_ball (min_le_right ρ ε) hy)
      exact (hcball y hyρ).trans (hwmono y hyU (Nat.zero_le _))
    obtain ⟨ψ, H, hψ, hH, hconv, -, -⟩ :=
      exists_subseq_differentiableOn_extension_of_weighted_bounds
        (α := Empty) (ι := Empty.elim) (g := Empty.elim) (U := fun _ => U)
        (fun _ => hU) (fun _ _ _ => le_rfl) (w := fun j => w (φ j)) hwm' hmeas' hlow'
        (F := fun j => F (φ j) i) (fun j => hF (φ j) i) (fun _ a => a.elim)
        hA (fun j => hcomponent i (φ j))
    rw [iUnion_const] at hH hconv
    exact ⟨ψ, hψ, H, hH, hconv⟩
  obtain ⟨σ, hσ, hPσ⟩ := exists_strictMono_forall_of_fintype P hPsub hPex
  choose H hH hconv using hPσ
  refine ⟨σ, H, hσ, hH, hconv, ?_⟩
  apply lintegral_finite_sum_iSup_le_of_tendsto hU hwmono hwmeas
    (fun j i => (hF (σ j) i).continuousOn) (fun i => (hH i).continuousOn)
    (fun i z hz => (hconv i).tendsto_at hz)
  intro j
  refine (setLIntegral_mono' hU.measurableSet fun z hz => ?_).trans (hbound (σ j))
  exact mul_le_mul_of_nonneg_left (hwmono z hz (hσ.id_le j)) zero_le

end SGPT.NAPotential.GAGAMult
