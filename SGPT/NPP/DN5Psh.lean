import SGPT.NPP.DN5PshLocal
import SGPT.NPP.DN5Assembly

/-!
# The `psh` field from the chart-level estimate; the joint smoothing statement

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 12–368; "All bounds are uniform over the
centers, because the constructions are made in the charts of a fixed finite atlas").

* `pshField_of_localJointEstimate` — for a uniform radius `r₁`, the smoothing
  `SGPT.NPP.DN5.smoothing wY A` has the `psh` field of `SGPT.NPP.DN2.IsJointSmoothing` at the
  radius `r₁ / 2`, given the chart-level estimate `SGPT.NPP.DN5.LocalJointEstimate`:
  small radii by the local estimate on a finite cover (`SGPT.NPP.DN5.psh_local`), radii bounded
  away from zero by compactness (`SGPT.NPP.DN5.psh_large`).
* `jointSmoothingStatement_of_local` — **`SGPT.NPP.DN2.JointSmoothingStatement` from
  `LocalJointEstimate` and `GeneratorEstimate`.**
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending IntegrationCurrent
open SGPT.NPP.DN2

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- **The `psh` field** for the smoothing of lane DN5 at half a uniform radius, from the
chart-level estimate. -/
theorem pshField_of_localJointEstimate (hloc : LocalJointEstimate N) {wY : KahlerBackground N Y}
    {A : FibreAtlas N Y} {r₁ : ℝ} (hr : IsUniformRadius wY A r₁) :
    PshField wY (r₁ / 2) (smoothing wY A) := by
  classical
  set r₀ := r₁ / 2 with hr₀def
  have hr₁ : 0 < r₁ := hr.1
  have hr₀ : 0 < r₀ := by positivity
  have hr₀₁ : r₀ < r₁ := by linarith
  intro θ u hu
  set g : Y → ℝ := fun y => (u y).toReal
  have hg : Integrable g (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh (kahlerVolume wY)
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  choose V hVo hxV rs K₀ A₀ C₀ C₁₀ hrs hrs₀ hK₀ hA₀ hC₀ hC₁₀ h1C₁₀ hcl using
    fun x => psh_local hloc hr θ hu hr₀ hr₀₁ x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  have hcover : ∀ y : Y, ∃ x ∈ s, y ∈ V x := by
    intro y
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
    obtain ⟨hxs, hy⟩ := mem_iUnion.mp hx
    exact ⟨x, hxs, hy⟩
  by_cases hsne : s.Nonempty
  swap
  · -- `Y` is empty
    have hY : ∀ y : Y, False := fun y => by
      obtain ⟨x, hxs, -⟩ := hcover y
      exact hsne ⟨x, hxs⟩
    refine ⟨0, 0, 0, 1, le_rfl, le_rfl, le_rfl, one_pos, fun x => (hY x).elim,
      fun x => (hY x).elim, fun e z hz => (hY (e.val.symm z)).elim, fun x => (hY x).elim⟩
  set rS := s.inf' hsne rs
  set C₁ := s.sup' hsne C₁₀
  set Ks := s.sup' hsne K₀
  set Ac := s.sup' hsne A₀
  set Cs := s.sup' hsne C₀
  have hrS : 0 < rS := (Finset.lt_inf'_iff hsne).mpr fun x _ => hrs x
  obtain ⟨x₀, hx₀⟩ := hsne
  have hC₁1 : 1 ≤ C₁ := (h1C₁₀ x₀).trans (Finset.le_sup' C₁₀ hx₀)
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le zero_lt_one hC₁1
  have hAc : 0 ≤ Ac := (hA₀ x₀).trans (Finset.le_sup' A₀ hx₀)
  set rL := min (rS / C₁) r₀
  have hrL : 0 < rL := lt_min (div_pos hrS hC₁pos) hr₀
  have hrLr₀ : rL ≤ r₀ := min_le_right _ _
  have hrLS : C₁ * rL ≤ rS := by
    have : rL ≤ rS / C₁ := min_le_left _ _
    rw [le_div_iff₀ hC₁pos] at this
    linarith
  have hrLS' : rL ≤ rS := le_trans (by nlinarith) hrLS
  obtain ⟨KL, CL, hKL, hCL, hlarge⟩ := psh_large hr θ hu hrL hrLr₀ hr₀₁
  set K := max Ks KL
  set C := max Cs CL
  have hKs : ∀ x ∈ s, K₀ x ≤ K := fun x hx => (Finset.le_sup' K₀ hx).trans (le_max_left _ _)
  have hAs : ∀ x ∈ s, A₀ x ≤ Ac := fun x hx => Finset.le_sup' A₀ hx
  have hCs : ∀ x ∈ s, C₀ x ≤ C := fun x hx => (Finset.le_sup' C₀ hx).trans (le_max_left _ _)
  have hC₁s : ∀ x ∈ s, C₁₀ x ≤ C₁ := fun x hx => Finset.le_sup' C₁₀ hx
  have hrSs : ∀ x ∈ s, rS ≤ rs x := fun x hx => Finset.inf'_le rs hx
  have hK0 : 0 ≤ K := (hK₀ x₀).trans (hKs x₀ hx₀)
  have hC0 : 0 ≤ C := (hC₀ x₀).trans (hCs x₀ hx₀)
  obtain ⟨La, Lb, Lc, Ld⟩ := hlarge K C Ac (le_max_right _ _) (le_max_right _ _) hAc
  set H := correctedSmoothing (smoothing wY A) u K
  have hloc_at : ∀ y : Y, ∃ x ∈ s, _ := fun y => by
    obtain ⟨x, hxs, hy⟩ := hcover y
    exact ⟨x, hxs, hcl x K Ac C C₁ (hKs x hxs) (hAs x hxs) (hCs x hxs) (hC₁s x hxs) y hy⟩
  -- clause (b), globally
  have hb : ∀ (y : Y) (s' : ℝ), s' < Real.log r₀ →
      0 ≤ deriv (fun s => H y (Real.exp s)) s' ∧
        0 < deriv (deriv (fun s => H y (Real.exp s))) s' := by
    intro y s' hs'
    obtain ⟨x, hxs, hy⟩ := hcover y
    obtain ⟨-, lb, -, -⟩ := hcl x K Ac C C₁ (hKs x hxs) (hAs x hxs) (hCs x hxs) (hC₁s x hxs) y hy
    by_cases hsmall : Real.exp s' < rL
    · refine lb s' ?_
      calc s' = Real.log (Real.exp s') := (Real.log_exp s').symm
        _ < Real.log rL := Real.log_lt_log (Real.exp_pos s') hsmall
        _ ≤ Real.log (rs x) := Real.log_le_log hrL (hrLS'.trans (hrSs x hxs))
    · rw [not_lt] at hsmall
      have hlt : Real.exp s' < r₀ := by
        calc Real.exp s' < Real.exp (Real.log r₀) := Real.exp_lt_exp.mpr hs'
          _ = r₀ := Real.exp_log hr₀
      exact Lb y s' hsmall hlt.le
  have hslope : ∀ (y : Y) (t : ℝ), 0 < t → t < r₀ → 0 ≤ logSlope H y t := by
    intro y t ht htr
    rw [logSlope_eq_deriv_exp ht (differentiableAt_correctedSmoothing hr hg K y ht
      (htr.trans hr₀₁))]
    exact (hb y (Real.log t) (Real.log_lt_log ht htr)).1
  refine ⟨K, Ac, C, C₁, hK0, hAc, hC0, hC₁pos, ?_, hb, ?_, ?_⟩
  · -- clause (a)
    intro y t ht htr
    obtain ⟨x, hxs, hy⟩ := hcover y
    obtain ⟨la, -, -, -⟩ := hcl x K Ac C C₁ (hKs x hxs) (hAs x hxs) (hCs x hxs) (hC₁s x hxs) y hy
    by_cases hsmall : t < rL
    · exact la t ht (hsmall.trans_le (hrLS'.trans (hrSs x hxs)))
    · rw [not_lt] at hsmall
      exact La y t hsmall htr.le
  · -- clause (c)
    intro e z hz w hw0 hwr
    set y := e.val.symm z
    obtain ⟨x, hxs, hy⟩ := hcover y
    obtain ⟨-, -, lc, -⟩ := hcl x K Ac C C₁ (hKs x hxs) (hAs x hxs) (hCs x hxs) (hC₁s x hxs) y hy
    by_cases hsmall : ‖w‖ < rL
    · exact lc e z hz rfl w hw0 (hsmall.trans_le (hrLS'.trans (hrSs x hxs)))
    · rw [not_lt] at hsmall
      exact Lc e z hz w hsmall hwr.le (hslope y ‖w‖ hw0 hwr)
  · -- clause (d)
    intro y a ha L hL r hr0 hC₁r hHlin e z hz hzy w hw
    obtain ⟨x, hxs, hy⟩ := hcover y
    obtain ⟨-, -, -, ld⟩ := hcl x K Ac C C₁ (hKs x hxs) (hAs x hxs) (hCs x hxs) (hC₁s x hxs) y hy
    have hrC : r ≤ C₁ * r := by nlinarith
    have hrr₀ : r < r₀ := lt_of_le_of_lt hrC hC₁r
    by_cases hsmall : r < rL
    · have hC₁rs : C₁ * r < rs x := by
        calc C₁ * r < C₁ * rL := mul_lt_mul_of_pos_left hsmall hC₁pos
          _ ≤ rS := hrLS
          _ ≤ rs x := hrSs x hxs
      exact ld a ha L hL r hr0 hC₁rs hHlin e z hz hzy w hw
    · rw [not_lt] at hsmall
      have hl := hslope y r hr0 hrr₀
      rw [← hzy] at hl ⊢
      exact Ld e z hz L r hL hsmall hrr₀.le hl w hw

universe v

/-- **The `psh` statement from the chart-level estimate.** -/
theorem smoothingPshStatement_of (hloc : ∀ N, LocalJointEstimate N) :
    SmoothingPshStatement.{v} := by
  intro N Y _ _ _ _ _ _ wY A r₁ hr
  exact ⟨r₁ / 2, by linarith [hr.1], by linarith [hr.1],
    pshField_of_localJointEstimate (hloc N) hr⟩

/-- **FPT `lem:chern-joint-smoothing` in the form of `SGPT.NPP.DN2.JointSmoothingStatement`**, from
the chart-level joint estimate (lane DN4, `LocalJointEstimate`) and the generator (lane DN6,
`GeneratorEstimate`).  Everything else — the global fibre map, the smoothing, the fields
`contDiffOn`, `mono`, `neg`, `add_const`, and the passage from the chart-level estimate to the
`psh` field (uniformity over centres and radii) — is proved. -/
theorem jointSmoothingStatement_of_local (hloc : ∀ N, LocalJointEstimate N)
    (hgen : GeneratorEstimate.{v}) : JointSmoothingStatement.{v} :=
  jointSmoothingStatement_of hgen (smoothingPshStatement_of hloc)

end SGPT.NPP.DN5
