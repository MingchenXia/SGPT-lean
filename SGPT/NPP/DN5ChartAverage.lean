import SGPT.NPP.DN5Frame
import SGPT.NPP.DN5PshLocal
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The smoothing as a fibre average with a fixed kernel, in a chart

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1; Step 7 uses this form for the
generator).  Near every chart point `z₀` (for lane DN6, `DN6/notes.md`):

  `Ψ_g(e⁻¹ z, t) = ∫ g(e⁻¹ G(z, t s)) χ(‖s‖²) ds`   (`z ∈ O`, `0 < t < t₁`),

with a globally smooth `G : ℂⁿ × ℂⁿ → ℂⁿ`, `G(z, 0) = z`, equal near `O × {0}` to
`(z, η) ↦ e(F(e⁻¹ z, P(z) η))`, where `P(z)` is a smooth family of complex frames normalizing the
Kähler form (`SGPT.NPP.DN5.exists_smooth_normalizingFrame`); hence `η ↦ G(z, η)` is holomorphic
near `0` with derivative `P(z)` at `0` (`exists_chartAverage`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Analysis.KahlerNormal
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A complex linear map normalizing a form to `flatForm` is injective. -/
theorem injective_of_normalizing {α : CoordinateRealTwoForm N}
    {P : ComplexModel N →L[ℂ] ComplexModel N} (hP : ∀ u v, α ![P u, P v] = flatForm N ![u, v]) :
    Function.Injective P := by
  intro u u' huu'
  have h0 : P (u - u') = 0 := by rw [map_sub, huu', sub_self]
  have h := hP (u - u') (Complex.I • (u - u'))
  rw [h0, flatForm_apply_I_smul_self] at h
  have hz : α ![(0 : ComplexModel N), P (Complex.I • (u - u'))] = 0 := by
    rw [α.map_coord_zero (0 : Fin 2) rfl]
  rw [hz] at h
  have hn : ‖u - u'‖ ^ 2 = 0 := by
    have hpi := Real.pi_pos
    have : Real.pi⁻¹ * ‖u - u'‖ ^ 2 = 0 := h.symm
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (inv_ne_zero Real.pi_ne_zero)
    · exact h1
  have : u - u' = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero] at hn
    exact hn
  exact sub_eq_zero.mp this

/-- The frame as a complex linear automorphism. -/
def frameEquiv {α : CoordinateRealTwoForm N} (P : ComplexModel N →L[ℂ] ComplexModel N)
    (hP : ∀ u v, α ![P u, P v] = flatForm N ![u, v]) : ComplexModel N ≃L[ℂ] ComplexModel N :=
  (LinearEquiv.ofInjectiveEndo (P : ComplexModel N →ₗ[ℂ] ComplexModel N)
    (injective_of_normalizing hP)).toContinuousLinearEquiv

@[simp] theorem frameEquiv_apply {α : CoordinateRealTwoForm N}
    (P : ComplexModel N →L[ℂ] ComplexModel N) (hP : ∀ u v, α ![P u, P v] = flatForm N ![u, v])
    (u : ComplexModel N) : frameEquiv P hP u = P u := rfl

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- **The smoothing as a fibre average with the fixed kernel `χ(‖s‖²)`** near every chart point,
along a globally smooth map `G` with `G(z, 0) = z`, holomorphic in the fibre near `0` with
derivative a frame normalizing the Kähler form. -/
theorem exists_chartAverage (wY : KahlerBackground N Y) (A : FibreAtlas N Y)
    {e : ComplexChart N Y} {z₀ : ComplexModel N} (hz₀ : z₀ ∈ e.val.target) :
    ∃ (O : Set (ComplexModel N)) (t₁ : ℝ) (P : ComplexModel N → (ComplexModel N →L[ℂ] ComplexModel N))
      (G : ComplexModel N × ComplexModel N → ComplexModel N),
      IsOpen O ∧ z₀ ∈ O ∧ O ⊆ e.val.target ∧ 0 < t₁ ∧
      ContDiffOn ℝ ∞ P O ∧
      (∀ z ∈ O, ∀ u v, wY.form.val.coeff e z ![P z u, P z v] = flatForm N ![u, v]) ∧
      ContDiff ℝ ∞ G ∧ (∀ z, G (z, 0) = z) ∧
      (∀ z ∈ O, ∀ η ∈ ball (0 : ComplexModel N) t₁,
        G (z, η) = e.val (fibreMap A e z (P z η)) ∧ fibreMap A e z (P z η) ∈ e.val.source ∧
        DifferentiableAt ℂ (fun η => G (z, η)) η) ∧
      (∀ z ∈ O, fderiv ℝ (fun η => G (z, η)) 0 = (P z : ComplexModel N →L[ℂ] ComplexModel N).restrictScalars ℝ) ∧
      ∀ (g : Y → ℝ) (z : ComplexModel N), z ∈ O → ∀ t : ℝ, 0 < t → t < t₁ →
        smoothing wY A g (e.val.symm z) t =
          ∫ s, g (e.val.symm (G (z, t • s))) * DN3.kernel N s := by
  classical
  obtain ⟨U, hU, hz₀U, hUt, P, hP, hPn⟩ := exists_smooth_normalizingFrame wY e hz₀
  obtain ⟨ρ4, hρ4, hρ4U⟩ := Metric.isOpen_iff.mp hU z₀ hz₀U
  set ρ := ρ4 / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  set K := closedBall z₀ (2 * ρ)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith)).trans hρ4U
  have hKt : K ⊆ e.val.target := hKU.trans hUt
  obtain ⟨R, hR, hRsub⟩ := exists_tube_goodSet A (isCompact_closedBall z₀ (2 * ρ)) hKt
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ (2 * ρ)).exists_bound_of_continuousOn
    (hP.continuousOn.mono hKU)
  set r := R / (|B| + 1) with hrdef
  have hr : 0 < r := div_pos hR (by positivity)
  have hPr : ∀ z ∈ K, ∀ η : ComplexModel N, ‖η‖ ≤ r → ‖P z η‖ ≤ R := by
    intro z hz η hη
    calc ‖P z η‖ ≤ ‖P z‖ * ‖η‖ := (P z).le_opNorm η
      _ ≤ (|B| + 1) * r := by
          apply mul_le_mul _ hη (norm_nonneg _) (by positivity)
          exact (hB z hz).trans ((le_abs_self B).trans (by linarith))
      _ = R := by rw [hrdef]; field_simp
  have hgood : ∀ z ∈ K, ∀ η : ComplexModel N, ‖η‖ ≤ r → (z, P z η) ∈ goodSet A e := by
    intro z hz η hη
    exact hRsub ⟨hz, by rw [mem_closedBall, dist_zero_right]; exact hPr z hz η hη⟩
  set Φ : ComplexModel N → ComplexModel N → ComplexModel N := fun z ξ => e.val (fibreMap A e z ξ)
  have hΦ := isLocalFibreMap_goodSet A e
  -- the cutoff
  let β₁ : ContDiffBump z₀ := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let β₂ : ContDiffBump (0 : ComplexModel N) := ⟨r / 2, r, by positivity, by linarith⟩
  set β : ComplexModel N × ComplexModel N → ℝ := fun p => β₁ p.1 * β₂ p.2
  have hβ : ContDiff ℝ ∞ β :=
    (β₁.contDiff.comp contDiff_fst).mul (β₂.contDiff.comp contDiff_snd)
  have hβsupp : ∀ p, β p ≠ 0 → p.1 ∈ K ∧ ‖p.2‖ ≤ r := by
    intro p hp
    have h1 : β₁ p.1 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : β₂ p.2 ≠ 0 := right_ne_zero_of_mul hp
    have h1' : p.1 ∈ tsupport β₁ := subset_tsupport _ h1
    have h2' : p.2 ∈ tsupport β₂ := subset_tsupport _ h2
    rw [β₁.tsupport_eq] at h1'
    rw [β₂.tsupport_eq, mem_closedBall, dist_zero_right] at h2'
    exact ⟨h1', h2'⟩
  have hβone : ∀ z ∈ closedBall z₀ ρ, ∀ η : ComplexModel N, ‖η‖ ≤ r / 2 → β (z, η) = 1 := by
    intro z hz η hη
    have h1 : β₁ z = 1 := β₁.one_of_mem_closedBall hz
    have h2 : β₂ η = 1 := β₂.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hη)
    simp only [β, h1, h2, mul_one]
  set G : ComplexModel N × ComplexModel N → ComplexModel N :=
    fun p => p.1 + β p • (Φ p.1 (P p.1 p.2) - p.1)
  -- smoothness of `G`
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport β
    · -- near the support, `Φ(z, P z η)` is smooth
      have hpK : p.1 ∈ K ∧ ‖p.2‖ ≤ r := by
        have hclosed : IsClosed {q : ComplexModel N × ComplexModel N | q.1 ∈ K ∧ ‖q.2‖ ≤ r} :=
          (isClosed_closedBall.preimage continuous_fst).inter
            (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)
        exact closure_minimal (fun q hq => hβsupp q hq) hclosed hp
      have hpU : p.1 ∈ U := hKU hpK.1
      have hPp : ContDiffAt ℝ ∞ P p.1 := hP.contDiffAt (hU.mem_nhds hpU)
      have hPR : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N =>
          (P q.1).restrictScalars ℝ) p :=
        (ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel N) (ComplexModel N) ℝ ℝ).contDiff.contDiffAt.comp
          p (hPp.comp p contDiffAt_fst)
      have hin : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => (q.1, P q.1 q.2)) p :=
        contDiffAt_fst.prodMk (hPR.clm_apply contDiffAt_snd)
      have hΦp : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => Φ q.1 q.2)
          (p.1, P p.1 p.2) :=
        hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds (hgood p.1 hpK.1 p.2 hpK.2))
      have hcomp : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N =>
          Φ q.1 (P q.1 q.2)) p :=
        ContDiffAt.comp (g := fun q : ComplexModel N × ComplexModel N => Φ q.1 q.2)
          (f := fun q : ComplexModel N × ComplexModel N => (q.1, P q.1 q.2)) p hΦp hin
      exact contDiffAt_fst.add ((hβ.contDiffAt).smul (hcomp.sub contDiffAt_fst))
    · have hzero : G =ᶠ[𝓝 p] fun q => q.1 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
        simp only [G, hq, Pi.zero_apply, zero_smul, add_zero]
      exact contDiffAt_fst.congr_of_eventuallyEq hzero
  have hG0 : ∀ z, G (z, 0) = z := by
    intro z
    by_cases hz : β (z, 0) = 0
    · simp only [G, hz, zero_smul, add_zero]
    · have hzK := (hβsupp (z, 0) hz).1
      have h0 : P z 0 = 0 := map_zero _
      have hmem : (z, (0 : ComplexModel N)) ∈ goodSet A e := by
        have := hgood z hzK 0 (by simp; positivity)
        rwa [h0] at this
      have hz0 : Φ z 0 = z := hΦ.map_zero z hmem
      simp only [G, h0]
      rw [hz0, sub_self, smul_zero, add_zero]
  set O := ball z₀ ρ
  have hOK : O ⊆ closedBall z₀ ρ := ball_subset_closedBall
  have hOK' : O ⊆ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hlocal : ∀ z ∈ O, ∀ η : ComplexModel N, ‖η‖ ≤ r / 2 →
      G (z, η) = Φ z (P z η) := by
    intro z hz η hη
    simp only [G, hβone z (hOK hz) η hη, one_smul, add_sub_cancel]
  refine ⟨O, r / 2, P, G, isOpen_ball, mem_ball_self hρ, hOK'.trans hKt, by positivity,
    hP.mono (hOK'.trans hKU), fun z hz => hPn z (hKU (hOK' hz)), hG, hG0, ?_, ?_, ?_⟩
  · intro z hz η hη
    have hη' : ‖η‖ ≤ r / 2 := by rw [mem_ball, dist_zero_right] at hη; exact hη.le
    have hgη := hgood z (hOK' hz) η (hη'.trans (by linarith))
    refine ⟨hlocal z hz η hη', (goodSet_target A hgη).2, ?_⟩
    -- holomorphy in the fibre
    have hev : (fun η' => G (z, η')) =ᶠ[𝓝 η] fun η' => Φ z (P z η') := by
      filter_upwards [isOpen_ball.mem_nhds hη] with η' hη'
      exact hlocal z hz η' (by rw [mem_ball, dist_zero_right] at hη'; exact hη'.le)
    have hholo : DifferentiableAt ℂ (Φ z) (P z η) := hΦ.holo (z, P z η) hgη
    exact (hholo.comp η (P z).differentiableAt).congr_of_eventuallyEq hev
  · intro z hz
    have hgz : (z, (0 : ComplexModel N)) ∈ goodSet A e := by
      have := hgood z (hOK' hz) 0 (by simp; positivity)
      rwa [map_zero] at this
    have hev : (fun η' => G (z, η')) =ᶠ[𝓝 0] fun η' => Φ z (P z η') := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show 0 < r / 2 by positivity))]
        with η' hη'
      exact hlocal z hz η' (by rw [mem_ball, dist_zero_right] at hη'; exact hη'.le)
    have hd : DifferentiableAt ℝ (Φ z) 0 :=
      ((hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds hgz)).differentiableAt (by simp)).comp
        (0 : ComplexModel N) ((differentiableAt_const z).prodMk differentiableAt_id)
    have hd' : HasFDerivAt (Φ z) (ContinuousLinearMap.id ℝ _) (P z 0) := by
      rw [map_zero]
      have := hd.hasFDerivAt
      rwa [hΦ.fderiv_zero z hgz] at this
    have hPd : HasFDerivAt (fun η' => P z η')
        ((P z : ComplexModel N →L[ℂ] ComplexModel N).restrictScalars ℝ) 0 :=
      ((P z).restrictScalars ℝ).hasFDerivAt
    have hcomp : HasFDerivAt (fun η' => Φ z (P z η'))
        ((ContinuousLinearMap.id ℝ _).comp ((P z : ComplexModel N →L[ℂ] ComplexModel N).restrictScalars ℝ)) 0 :=
      hd'.comp 0 hPd
    rw [hev.fderiv_eq, hcomp.fderiv, ContinuousLinearMap.id_comp]
  · intro g z hz t ht htr
    have hzt : z ∈ e.val.target := hKt (hOK' hz)
    rw [smoothing_eq_chartSmoothing_symm A hzt,
      chartSmoothing_eq_frame A (L := frameEquiv (P z) (hPn z (hKU (hOK' hz)))) (fun u v => by
        simpa using hPn z (hKU (hOK' hz)) u v) g t]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [frameEquiv_apply]
    by_cases hs : DN3.kernel N s = 0
    · rw [hs, mul_zero, mul_zero]
    · have hs1 : ‖s‖ < 1 := by
        by_contra h
        exact hs (DN3.kernel_eq_zero N (not_lt.mp h))
      have hts : ‖t • s‖ ≤ r / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        nlinarith [norm_nonneg s]
      have hgts := hgood z (hOK' hz) (t • s) (hts.trans (by linarith))
      have hlin : P z (t • s) = t • P z s := (P z).map_smul_of_tower t s
      have hsrc : fibreMap A e z (t • P z s) ∈ e.val.source := by
        rw [← hlin]; exact (goodSet_target A hgts).2
      rw [hlocal z hz (t • s) hts, hlin]
      change g (fibreMap A e z (t • P z s)) * _ =
        g (e.val.symm (e.val (fibreMap A e z (t • P z s)))) * _
      rw [e.val.left_inv hsrc]

end SGPT.NPP.DN5
