import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# A potential of a global smooth form off a closed set has bounded Levi form

Lane DN7, `thm:DNT23_C11bar` (FPT `thm:big-metric-laplacian-rooftop`, "Passage to a
modification": "In particular `𝒟φ` is uniformly bounded on `U`, although `φ` tends to `-∞`
near `D`").

Let `(Y, ω_Y)` be a compact Kähler manifold, `γ` a smooth closed real `(1,1)`-form on `Y` and
`Z ⊆ Y` closed.  If off `Z` an extended-real function `φ` is, in every chart, a smooth local
potential of `γ` (`ddᶜ φ = γ` there), then off `Z` the function `φ` is `C^∞` in every chart,
continuous, and its Levi form is bounded by `C · π · ω_Y` for one constant `C ≥ 0`
(compactness: `γ ≤ C ω_Y`, `KahlerDomination.exists_isSemipositive_add_smul`).

## Main results

* `SGPT.NPP.DN7.leviForm_eq_pi_mul_coeff_of_isSmoothLocalPotential`;
* `SGPT.NPP.DN7.exists_coeff_le_smul_kahler`;
* `SGPT.NPP.DN7.offClosed_data_of_localPotential`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.NPP.DN7

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The Levi form of a smooth local potential of a form `a` is `π` times `a` on complex lines. -/
theorem leviForm_eq_pi_mul_coeff_of_isSmoothLocalPotential {a : SmoothRealForm n Y 2}
    {e : ComplexChart n Y} {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hpot : IsSmoothLocalPotential a e W ρ) {z : ComplexModel n} (hz : z ∈ W)
    (v : ComplexModel n) :
    leviForm ρ z v = Real.pi * a.coeff e z ![v, Complex.I • v] := by
  have h2 : ContDiffAt ℝ 2 ρ z :=
    ((hpot.2.2.1.contDiffAt (hpot.1.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top))
  rw [← hpot.2.2.2 hz, smoothDDC_complexDiagonal_eq_leviForm h2]
  field_simp

/-- **Domination of a smooth form by a Kähler form** on a compact manifold, on complex lines:
`γ ≤ C ω_Y` for some `C ≥ 0`. -/
theorem exists_coeff_le_smul_kahler [CompactSpace Y] (wY : KahlerBackground n Y)
    (γ : ClosedRealOneOneForm n Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n,
        γ.val.coeff e z ![v, Complex.I • v] ≤ C * wY.form.val.coeff e z ![v, Complex.I • v] := by
  obtain ⟨A, hA, h⟩ := KahlerDomination.exists_isSemipositive_add_smul (-γ).val wY.form.val
    wY.isKahler.1
  refine ⟨A, hA.le, fun e z hz v => ?_⟩
  have h1 := h e z hz v
  rw [ClosedRealOneOneForm.coeff_neg] at h1
  simp only [ContinuousAlternatingMap.neg_apply] at h1
  linarith

/-- **Off a closed set, a potential of a global smooth form is smooth, continuous and has
bounded Levi form.**  If `φ` is, off the closed set `Z` and in every chart, a smooth local
potential of the global closed form `γ`, then `φ` is `C^∞` in every chart off `Z`, continuous
off `Z`, and `i∂∂̄φ ≤ C ω_Y` there (in the normalization of `DN2`: Levi form
`≤ C · π · ω_Y` on complex lines). -/
theorem offClosed_data_of_localPotential [CompactSpace Y] (wY : KahlerBackground n Y)
    (γ : ClosedRealOneOneForm n Y) {Z : Set Y} {φ : Y → EReal}
    (hpot : ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∉ Z → ∃ W : Set (ComplexModel n), z ∈ W ∧
        IsSmoothLocalPotential γ.val e W (fun ζ => (φ (e.val.symm ζ)).toReal)) :
    (∀ e : ComplexChart n Y, ContDiffOn ℝ ∞ (fun z => (φ (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹' Zᶜ)) ∧
    ContinuousOn (fun y => (φ y).toReal) Zᶜ ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ Zᶜ → ∀ v : ComplexModel n,
        leviForm (fun z => (φ (e.val.symm z)).toReal) z v ≤
          C * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v]) := by
  refine ⟨fun e z hz => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨W, hzW, hW⟩ := hpot e z hz.1 hz.2
    exact ((hW.2.2.1.contDiffAt (hW.1.mem_nhds hzW))).contDiffWithinAt
  · set e := complexChartAt (n := n) y
    have hys : y ∈ e.val.source := mem_complexChartAt_source y
    have hyt : e.val y ∈ e.val.target := e.val.map_source hys
    have hsy : e.val.symm (e.val y) = y := e.val.left_inv hys
    obtain ⟨W, hzW, hW⟩ := hpot e (e.val y) hyt (by rw [hsy]; exact hy)
    have hc : ContinuousAt (fun ζ => (φ (e.val.symm ζ)).toReal) (e.val y) :=
      (hW.2.2.1.contDiffAt (hW.1.mem_nhds hzW)).continuousAt
    have hcomp : ContinuousAt (fun x => (φ (e.val.symm (e.val x))).toReal) y :=
      ContinuousAt.comp (f := e.val) (g := fun ζ => (φ (e.val.symm ζ)).toReal) hc
        (e.val.continuousAt hys)
    refine (hcomp.congr ?_).continuousWithinAt
    filter_upwards [e.val.open_source.mem_nhds hys] with x hx
    rw [e.val.left_inv hx]
  · obtain ⟨C, hC, hle⟩ := exists_coeff_le_smul_kahler wY γ
    refine ⟨C, hC, fun e z hz hzZ v => ?_⟩
    obtain ⟨W, hzW, hW⟩ := hpot e z hz hzZ
    rw [leviForm_eq_pi_mul_coeff_of_isSmoothLocalPotential hW hzW v]
    have := hle e z hz v
    nlinarith [Real.pi_pos]

end SGPT.NPP.DN7
