import SGPT.Trace.TwistedL2Statement
import SGPT.Foundations.Analysis.Pending.BochnerKodairaIdentity
import SGPT.Foundations.Analysis.Pending.HormanderWeightedL2

/-!
# The polarized Morrey--Kohn--Hörmander identity with one compactly supported factor

Blueprint `claude-twisted-l2:flat-mkh`.  TN proves the polarized flat identity
(`SGPT.Foundations.Analysis.Pending.CauchyGreen.integral_deltaDir_mul_conj_deltaDir`)

`∫ δ_u a · conj(δ_v b) e^{-φ} = ∫ ∂̄_v a · conj(∂̄_u b) e^{-φ} + ∫ (∂̄_v ∂_u φ) a conj(b) e^{-φ}`

for globally `C²` weights `φ` and **compactly supported** `a, b`.  The globalization of the
Bochner--Kodaira inequality on a manifold (`claude-twisted-l2:global-bkn`) needs it in a chart
`D` with only **one** factor compactly supported: `E(W, ψ_α W)` is computed in the chart of
`ψ_α`, while `W` is merely smooth there.  `integral_deltaDir_mul_conj_deltaDir_of_tsupport` gives
exactly this: `φ` and `a` smooth on an open `D ⊆ ℂⁿ`, `b` a `C²` function with compact support in
`D` (the integrands vanish off `tsupport b`, and near it `φ`, `a` agree with global smooth
functions, which TN's identity accepts).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending.CauchyGreen
  SGPT.Foundations.Analysis.Pending.Hormander

variable {n : ℕ}

theorem dDir_congr_of_eventuallyEq {v x : ComplexModel n} {f g : ComplexModel n → ℂ}
    (h : f =ᶠ[𝓝 x] g) : dDir v f x = dDir v g x := by
  simp only [dDir, h.fderiv_eq]

theorem dbarDir_congr_of_eventuallyEq {v x : ComplexModel n} {f g : ComplexModel n → ℂ}
    (h : f =ᶠ[𝓝 x] g) : dbarDir v f x = dbarDir v g x := by
  simp only [dbarDir, h.fderiv_eq]

theorem dDir_eq_zero_of_eventuallyEq_zero {v x : ComplexModel n} {f : ComplexModel n → ℂ}
    (h : f =ᶠ[𝓝 x] fun _ => 0) : dDir v f x = 0 := by
  rw [dDir_congr_of_eventuallyEq h, dDir, (hasFDerivAt_const (0 : ℂ) x).fderiv]
  simp

theorem dbarDir_eq_zero_of_eventuallyEq_zero {v x : ComplexModel n} {f : ComplexModel n → ℂ}
    (h : f =ᶠ[𝓝 x] fun _ => 0) : dbarDir v f x = 0 := by
  rw [dbarDir_congr_of_eventuallyEq h, dbarDir, (hasFDerivAt_const (0 : ℂ) x).fderiv]
  simp

/-- **The polarized flat Morrey--Kohn--Hörmander identity, one factor compactly supported**
(`claude-twisted-l2:flat-mkh`).  For `φ` and `a` smooth on an open `D ⊆ ℂⁿ` and `b` of class
`C²` with compact support in `D`:
`∫ δ_u a · conj(δ_v b) e^{-φ} = ∫ ∂̄_v a · conj(∂̄_u b) e^{-φ} + ∫ (∂̄_v ∂_u φ) a conj(b) e^{-φ}`. -/
theorem integral_deltaDir_mul_conj_deltaDir_of_tsupport {u v : ComplexModel n}
    {D : Set (ComplexModel n)} (hD : IsOpen D) {φ : ComplexModel n → ℝ} (hφ : ContDiffOn ℝ ∞ φ D)
    {a b : ComplexModel n → ℂ} (ha : ContDiffOn ℝ ∞ a D) (hb : ContDiff ℝ 2 b)
    (hbc : HasCompactSupport b) (hbD : tsupport b ⊆ D) :
    ∫ x, deltaDir u φ a x * conj (deltaDir v φ b x) * cweight φ x =
      (∫ x, dbarDir v a x * conj (dbarDir u b x) * cweight φ x) +
        ∫ x, dbarDir v (dDir u (fun y ↦ (φ y : ℂ))) x * a x * conj (b x) * cweight φ x := by
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_contDiff_eventuallyEq_nhdsSet hD hφ hbc hbD
  obtain ⟨α, hα, hαeq⟩ := exists_contDiff_eventuallyEq_nhdsSet hD ha hbc hbD
  obtain ⟨θ, hθ, hθc, -, hθ1, -⟩ := exists_contDiff_cutoff hbc hD hbD
  set α' : ComplexModel n → ℂ := fun x => (θ x : ℂ) * α x with hα'def
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hα' : ContDiff ℝ 2 α' :=
    ((Complex.ofRealCLM.contDiff.comp hθ).mul hα).of_le h2
  have hα'c : HasCompactSupport α' := by
    have : HasCompactSupport (fun x => (θ x : ℂ)) :=
      hθc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
    exact this.mul_right
  -- near `tsupport b` the global data agree with the local ones
  have hloc : ∀ x ∈ tsupport b, (fun y => (Φ y : ℂ)) =ᶠ[𝓝 x] (fun y => (φ y : ℂ)) ∧
      α' =ᶠ[𝓝 x] a ∧ Φ x = φ x := by
    intro x hx
    have hx' : 𝓝 x ≤ 𝓝ˢ (tsupport b) := nhds_le_nhdsSet hx
    have e1 : ∀ᶠ y in 𝓝 x, Φ y = φ y := hΦeq.filter_mono hx'
    have e2 : ∀ᶠ y in 𝓝 x, α y = a y := hαeq.filter_mono hx'
    have e3 : ∀ᶠ y in 𝓝 x, θ y = 1 := hθ1.filter_mono hx'
    refine ⟨e1.mono fun y hy => by simp only [hy], (e2.and e3).mono fun y hy => ?_,
      e1.self_of_nhds⟩
    simp only [hα'def, hy.1, hy.2, Complex.ofReal_one, one_mul]
  have hzero : ∀ x ∉ tsupport b, b =ᶠ[𝓝 x] fun _ => 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp hx
  -- the three integrands
  have i1 : ∀ x, deltaDir u Φ α' x * conj (deltaDir v Φ b x) * cweight Φ x =
      deltaDir u φ a x * conj (deltaDir v φ b x) * cweight φ x := by
    intro x
    by_cases hx : x ∈ tsupport b
    · obtain ⟨h1, h2', h3⟩ := hloc x hx
      simp only [deltaDir, cweight, dDir_congr_of_eventuallyEq h1,
        dDir_congr_of_eventuallyEq h2', h2'.self_of_nhds, h3]
    · have hb0 := hzero x hx
      have hv : ∀ ψ : ComplexModel n → ℝ, deltaDir v ψ b x = 0 := fun ψ => by
        simp only [deltaDir, dDir_eq_zero_of_eventuallyEq_zero hb0, hb0.self_of_nhds, mul_zero,
          sub_zero]
      simp only [hv, map_zero, mul_zero, zero_mul]
  have i2 : ∀ x, dbarDir v α' x * conj (dbarDir u b x) * cweight Φ x =
      dbarDir v a x * conj (dbarDir u b x) * cweight φ x := by
    intro x
    by_cases hx : x ∈ tsupport b
    · obtain ⟨-, h2', h3⟩ := hloc x hx
      simp only [cweight, dbarDir_congr_of_eventuallyEq h2', h3]
    · simp only [dbarDir_eq_zero_of_eventuallyEq_zero (hzero x hx), map_zero, mul_zero, zero_mul]
  have i3 : ∀ x, dbarDir v (dDir u (fun y ↦ (Φ y : ℂ))) x * α' x * conj (b x) * cweight Φ x =
      dbarDir v (dDir u (fun y ↦ (φ y : ℂ))) x * a x * conj (b x) * cweight φ x := by
    intro x
    by_cases hx : x ∈ tsupport b
    · obtain ⟨h1, h2', h3⟩ := hloc x hx
      have hdd : dDir u (fun y ↦ (Φ y : ℂ)) =ᶠ[𝓝 x] dDir u (fun y ↦ (φ y : ℂ)) :=
        h1.eventuallyEq_nhds.mono fun y hy => dDir_congr_of_eventuallyEq hy
      simp only [cweight, dbarDir_congr_of_eventuallyEq hdd, h2'.self_of_nhds, h3]
    · simp only [(hzero x hx).self_of_nhds, map_zero, mul_zero, zero_mul]
  have hTN := integral_deltaDir_mul_conj_deltaDir (μ := (volume : Measure (ComplexModel n)))
    (u := u) (v := v) (hΦ.of_le h2) hα' hb hα'c hbc
  simp only [i1, i2, i3] at hTN
  exact hTN

end SGPT.Trace.TwistedL2
