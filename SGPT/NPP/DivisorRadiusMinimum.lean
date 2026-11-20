import SGPT.NPP.HolomorphicRadiusMinimum
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual divisor-equation radii in the Kiselman minimum

The complete source-facing mathematics was written first in
`blueprint/src/dnt-big-divisor-radius.tex`. A genuine nonvanishing
holomorphic divisor equation internally produces its local holomorphic
logarithmic endpoint. The actual variable-radius minimum is then PSH on the
actual complement of the divisor, with no assumed global logarithm.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-- A local holomorphic logarithmic endpoint is manufactured from the actual
divisor equation. Both the real endpoint and its positive radius are exact. -/
theorem exists_local_holomorphic_divisorRadiusEndpoint {U : Set (ComplexModel n)}
    (hU : IsOpen U) {s : ComplexModel n → ℂ} (hs : DifferentiableOn ℂ s U)
    {x : ComplexModel n} (hx : x ∈ U) (hsx : s x ≠ 0) {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ h : ComplexModel n → ℂ, DifferentiableOn ℂ h V ∧ ∀ z ∈ V,
        s z ≠ 0 ∧ (h z).re = Real.log δ + a * Real.log ‖s z‖ ∧
          Real.exp (h z).re = δ * ‖s z‖ ^ a := by
  let q : ComplexModel n → ℂ := fun z => s z / s x
  have hq : DifferentiableOn ℂ q U := by
    change DifferentiableOn ℂ (fun z => s z / s x) U
    simpa only [div_eq_mul_inv] using hs.mul_const (s x)⁻¹
  let V : Set (ComplexModel n) := U ∩ q ⁻¹' {w : ℂ | 0 < w.re}
  have hV : IsOpen V := hq.continuousOn.isOpen_inter_preimage hU
    (isOpen_lt continuous_const Complex.continuous_re)
  have hxV : x ∈ V := by
    refine ⟨hx, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, q, div_self hsx, Complex.one_re]
    norm_num
  have hslit : ∀ z ∈ V, q z ∈ Complex.slitPlane := fun z hz => Or.inl hz.2
  have hlog : DifferentiableOn ℂ (fun z => Complex.log (q z)) V :=
    (hq.mono inter_subset_left).clog hslit
  let h : ComplexModel n → ℂ := fun z =>
    ((Real.log δ + a * Real.log ‖s x‖ : ℝ) : ℂ) + (a : ℂ) * Complex.log (q z)
  have hh : DifferentiableOn ℂ h V :=
    (differentiableOn_const ((Real.log δ + a * Real.log ‖s x‖ : ℝ) : ℂ)).add
      (hlog.const_mul (a : ℂ))
  refine ⟨V, hV, hxV, inter_subset_left, h, hh, ?_⟩
  intro z hz
  have hsz : s z ≠ 0 := by
    intro hsz
    have hpos := hz.2
    simp only [mem_preimage, mem_ofPred_eq, q, hsz, zero_div, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  have hqlog : Real.log ‖q z‖ = Real.log ‖s z‖ - Real.log ‖s x‖ := by
    rw [show ‖q z‖ = ‖s z‖ / ‖s x‖ from norm_div _ _]
    exact Real.log_div (norm_ne_zero_iff.mpr hsz) (norm_ne_zero_iff.mpr hsx)
  have hre : (h z).re = Real.log δ + a * Real.log ‖s z‖ := by
    simp only [h, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.log_re, hqlog]
    ring
  refine ⟨hsz, hre, ?_⟩
  rw [hre, Real.exp_add, Real.exp_log hδ,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hsz)]
  congr 1
  rw [mul_comm a]

/-- The actual logarithmic domain excludes the actual zero set, so no
artificial value for `log 0` enters the analytic endpoint. -/
def divisorRadiusDomain (U : Set (ComplexModel n)) (s : ComplexModel n → ℂ) (δ a : ℝ) :
    Set (ComplexModel n × ℂ) :=
  {p | p.1 ∈ U ∧ s p.1 ≠ 0 ∧ p.2.re < Real.log δ + a * Real.log ‖s p.1‖}

/-- The actual positive-radius minimum under the actual divisor radius. -/
def divisorRadiusMinimum (Φ : ComplexModel n × ℂ → EReal)
    (s : ComplexModel n → ℂ) (δ a : ℝ) (z : ComplexModel n) : EReal :=
  ⨅ r : ↥(Ioo (0 : ℝ) (δ * ‖s z‖ ^ a)), Φ (z, ((Real.log (r : ℝ)) : ℂ))

/-- A genuine holomorphic divisor equation supplies the varying endpoint
internally. The same actual infimum is PSH on the whole divisor complement. -/
theorem plurisubharmonicOn_divisorRadiusMinimum {U : Set (ComplexModel n)}
    (hU : IsOpen U) {s : ComplexModel n → ℂ} (hs : DifferentiableOn ℂ s U)
    {δ : ℝ} (hδ : 0 < δ) (a : ℝ) {Φ : ComplexModel n × ℂ → EReal}
    (hΦ : PlurisubharmonicOn Φ (divisorRadiusDomain U s δ a))
    (hinv : ∀ z (τ σ : ℂ), τ.re = σ.re → Φ (z, τ) = Φ (z, σ)) :
    PlurisubharmonicOn (divisorRadiusMinimum Φ s δ a) {z | z ∈ U ∧ s z ≠ 0} := by
  intro x hx
  obtain ⟨V, hV, hxV, hVU, h, hh, hend⟩ :=
    exists_local_holomorphic_divisorRadiusEndpoint hU hs hx.1 hx.2 hδ a
  have hΦV : PlurisubharmonicOn Φ (holomorphicRadiusDomain V h) := by
    apply hΦ.mono
    intro p hp
    refine ⟨hVU hp.1, (hend p.1 hp.1).1, ?_⟩
    rw [← (hend p.1 hp.1).2.1]
    exact hp.2
  have hmin := plurisubharmonicOn_holomorphicRadiusMinimum hV hh hΦV hinv
  have heq : holomorphicRadiusMinimum Φ h =ᶠ[𝓝 x] divisorRadiusMinimum Φ s δ a := by
    filter_upwards [hV.mem_nhds hxV] with z hz
    rw [holomorphicRadiusMinimum, divisorRadiusMinimum, (hend z hz).2.2]
  exact (hmin x hxV).congr heq

end SGPT.NPP.DNTBig
