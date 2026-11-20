import SGPT.Trace.TwistedL2MEstimate

/-!
# From graph density to the functional bound on `ℂⁿ`

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:graph-density`, `claude-tl2-main:reduction`).
The twisted a priori estimate (`TwistedDatum.apriori`) bounds the data pairing of a finite family
of local pieces by `M (‖T* τ‖² + Q(τ))`, where `Q(τ) = -Re ∫ tr(A_W Ā_W) a e^{-φ}` is the
`∂̄`-defect.  The functional bound (`TwistedFunctionalBoundStatement`) is the same inequality
without `Q`.  The passage is the density of test forms in `Dom T* ∩ ker S` for the graph norm
(Hörmander's Lemma 4.1.3 / FPT `lem:cutoff-mollifier-density`), which on the level of test families
says:

`TwistedDatum.GraphDensity T`: for every family `τ` and every `ε > 0` there is a family `τ'` whose
data pairing is `ε`-close to that of `τ`, whose `T*`-energy is at most `‖T* τ‖² + ε`, and whose
`∂̄`-defect `Q(τ')` is at most `ε`.

`functionalBound_of_graphDensity` proves the functional bound for every twisted datum on `ℂⁿ`
satisfying `GraphDensity`; `twistedFunctionalBoundStatement_of_graphDensity` packages it as
`TwistedFunctionalBoundStatement n (ComplexModel n)`.  `GraphDensity` itself is the remaining
analytic obligation (it uses the completeness of `σ = ω + ddᶜr` and Friedrichs' lemma).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ContDiff ComplexConjugate Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

namespace TwistedDatum

variable (T : TwistedDatum n (ComplexModel n))

/-- A finite family of local test pieces `h_i ⊗ e_i` on `ℂⁿ` (frames `e_i` of `L`). -/
structure FrameFamily where
  ι : Type
  s : Finset ι
  e : ι → AtlasFrame T.L
  h : ι → ComplexModel n → ComplexModel n
  spec : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i)

namespace FrameFamily

variable {T} (F : T.FrameFamily) (ρ : ComplexModel n → ℝ)

/-- The data pairing `⟨τ, ∂̄G⟩` of the family. -/
def data : ℂ := ∑ i ∈ F.s, T.localDataPairing chart0 (F.e i) ρ (F.h i)

/-- The `T*`-energy `‖T* τ‖²_{H₁}` of the family, as an integral over `ℂⁿ`. -/
def energy : ℝ := ∫ z, (T.Φ (T.FA ρ) F.s F.e F.h z).re

/-- The `∂̄`-defect `Q(τ) = -Re ∫ tr(A_W Ā_W) a e^{-φ}` of the family. -/
def defect : ℝ := -(∫ z, T.Φ (T.FT ρ) F.s F.e F.h z).re

end FrameFamily

/-- **Graph density of test families** (the remaining analytic input of the main estimate on
`ℂⁿ`; FPT `lem:cutoff-mollifier-density`): every family can be approximated, in the data pairing
and in the `T*`-energy, by families with arbitrarily small `∂̄`-defect. -/
def GraphDensity : Prop :=
  ∀ ρ : ComplexModel n → ℝ, IsChartDensity T.μ chart0 ρ →
  ∀ F : T.FrameFamily, ∀ ε : ℝ, 0 < ε → ∃ F' : T.FrameFamily,
    ‖F'.data ρ - F.data ρ‖ ≤ ε ∧ F'.energy ρ ≤ F.energy ρ + ε ∧ F'.defect ρ ≤ ε

variable {T}

theorem FrameFamily.energy_nonneg {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ chart0 ρ)
    (F : T.FrameFamily) : 0 ≤ F.energy ρ :=
  integral_nonneg (FA_re_nonneg hρ F.spec)

theorem FrameFamily.apriori {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ chart0 ρ)
    (F : T.FrameFamily)
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ‖F.data ρ‖ ^ 2 ≤ (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
      (F.energy ρ + F.defect ρ) := by
  have h := TwistedDatum.apriori (s := F.s) hρ F.spec hfin
  simpa [FrameFamily.data, FrameFamily.energy, FrameFamily.defect, sub_eq_add_neg] using h

/-- The functional bound for a family, from graph density. -/
theorem FrameFamily.norm_sq_data_le {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ chart0 ρ)
    (hdens : T.GraphDensity) (F : T.FrameFamily)
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ‖F.data ρ‖ ^ 2 ≤ (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
      F.energy ρ := by
  set M := (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hE := F.energy_nonneg hρ
  -- for every `ε ∈ (0, 1]`, `‖data‖ ≤ √(M (E + 2ε)) + ε`
  have key : ∀ ε : ℝ, 0 < ε → ‖F.data ρ‖ ≤ Real.sqrt (M * (F.energy ρ + 2 * ε)) + ε := by
    intro ε hε
    obtain ⟨F', h1, h2, h3⟩ := hdens ρ hρ F ε hε
    have ha := F'.apriori hρ hfin
    have hb : ‖F'.data ρ‖ ^ 2 ≤ M * (F.energy ρ + 2 * ε) :=
      ha.trans (mul_le_mul_of_nonneg_left (by linarith) hM)
    have hc : ‖F'.data ρ‖ ≤ Real.sqrt (M * (F.energy ρ + 2 * ε)) :=
      Real.le_sqrt_of_sq_le hb
    have hd : ‖F.data ρ‖ ≤ ‖F'.data ρ‖ + ε := by
      have := norm_sub_norm_le (F.data ρ) (F'.data ρ)
      rw [norm_sub_rev] at this
      linarith
    linarith
  have hlim : Tendsto (fun ε : ℝ => Real.sqrt (M * (F.energy ρ + 2 * ε)) + ε) (𝓝[>] 0)
      (𝓝 (Real.sqrt (M * F.energy ρ))) := by
    have hc : Continuous fun ε : ℝ => Real.sqrt (M * (F.energy ρ + 2 * ε)) + ε := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ‖F.data ρ‖ ≤ Real.sqrt (M * F.energy ρ) :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  calc ‖F.data ρ‖ ^ 2 ≤ Real.sqrt (M * F.energy ρ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = M * F.energy ρ := Real.sq_sqrt (mul_nonneg hM hE)

/-- **The functional bound on `ℂⁿ` from graph density** (`claude-tl2-main:reduction`), for an
arbitrary finite family of local pieces as in `TwistedFunctionalBoundStatement`. -/
theorem functionalBound_of_graphDensity (hdens : T.GraphDensity)
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤)
    (ι : Type) (s : Finset ι) (c : ι → ComplexChart n (ComplexModel n))
    (e : ι → AtlasFrame T.L) (ρ : ι → ComplexModel n → ℝ) (h : ι → ComplexModel n → ComplexModel n)
    (hρ : ∀ i ∈ s, IsChartDensity T.μ (c i) (ρ i))
    (hh : ∀ i ∈ s, IsLocalTestField T.L T.U (c i) (e i) (h i)) :
    ENNReal.ofReal (‖∑ i ∈ s, T.localDataPairing (c i) (e i) (ρ i) (h i)‖ ^ 2) ≤
      (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ) *
        ∫⁻ x in T.U, ENNReal.ofReal
          (‖∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x‖ ^ 2 * T.H1weight x) ∂T.μ := by
  classical
  obtain ⟨ρ₀, hρ₀⟩ := T.volume_smooth chart0
  have hρ₀' : IsChartDensity T.μ chart0 ρ₀ := hρ₀
  -- restrict to the index subtype `s`, where all charts are `chart0` and densities `ρ₀`
  let F : T.FrameFamily :=
    { ι := s, s := Finset.univ, e := fun i => e i, h := fun i => h i,
      spec := fun i => by
        have := hh i i.2
        rwa [chart_eq (c i)] at this }
  have hc : ∀ i ∈ s, c i = chart0 := fun i _ => chart_eq (c i)
  have hρi : ∀ i ∈ s, ρ i = ρ₀ := fun i hi => chartDensity_unique (hρ i hi) hρ₀'
  have hdata : ∑ i ∈ s, T.localDataPairing (c i) (e i) (ρ i) (h i) = F.data ρ₀ := by
    rw [FrameFamily.data, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i i.2, hρi i i.2]
  have htstar : ∀ x, ∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x =
      ∑ i ∈ F.s, T.localTStar chart0 (F.e i) ρ₀ (F.h i) x := by
    intro x
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i i.2, hρi i i.2]
  have hE : ∫⁻ x in T.U, ENNReal.ofReal
      (‖∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x‖ ^ 2 * T.H1weight x) ∂T.μ =
      ENNReal.ofReal (F.energy ρ₀) := by
    simp_rw [htstar]
    exact lintegral_tstar_eq hρ₀' F.spec
  rw [hdata, hE]
  have hb := F.norm_sq_data_le hρ₀' hdens hfin
  calc ENNReal.ofReal (‖F.data ρ₀‖ ^ 2)
      ≤ ENNReal.ofReal ((∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
          F.energy ρ₀) := ENNReal.ofReal_le_ofReal hb
    _ = _ := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]

end TwistedDatum

variable (n)

/-- `TwistedFunctionalBoundStatement` on `ℂⁿ`, assuming graph density for every datum. -/
theorem twistedFunctionalBoundStatement_of_graphDensity
    (hdens : ∀ T : TwistedDatum n (ComplexModel n), T.GraphDensity) :
    TwistedFunctionalBoundStatement n (ComplexModel n) :=
  fun T hfin ι s c e ρ h hρ hh =>
    TwistedDatum.functionalBound_of_graphDensity (hdens T) hfin ι s c e ρ h hρ hh

end SGPT.Trace.TwistedL2
