import SGPT.PSH.HermitianGlobalMeasure
import SGPT.PSH.HermitianExtremalPoleAlternative
import SGPT.Foundations.Analysis.Pending.IntegrationCurrent

/-!
# Strict positivity of the actual smooth Hermitian background mass

The canonical all-zero mixed measure is read on its actual correction
patches. The smooth exterior identity identifies its original local current
with the genuine positive top power of the Hermitian form. A manufactured
nonnegative compact test proves positive local open mass, and exact patch
readback proves positive mass on every original nonempty open set.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorForms LocalBedfordTaylorSmooth LocalBedfordTaylorSmoothDensity
  LocalBedfordTaylorSmoothProductDensity
  LocalBedfordTaylorLocality LocalCurrentPullbackDdc ConstantFormProducts TopDegreeDensity
  HermitianProducts HermitianExtremal IntegrationCurrent ProductTestForms CoordinateWedgeAssoc
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- Literal bounded zero potentials, with no incoming class certificate. -/
def zeroPotentials : Fin (m + 1) → M → EReal := fun _ _ => 0

theorem zeroPotentials_isHermitianPSH (omega : Background (m + 1) M)
    (i : Fin (m + 1)) : IsHermitianPSH omega (zeroPotentials i) :=
  isHermitianPSH_zero omega

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem zeroPotentials_bounded (i : Fin (m + 1)) :
    ∃ a b : ℝ, ∀ x : M, (a : EReal) ≤ zeroPotentials i x ∧
      zeroPotentials i x ≤ (b : EReal) :=
  ⟨0, 0, fun _ => by simp [zeroPotentials]⟩

namespace BackgroundPatch

private theorem wedgeForm_unit {n r p : ℕ} {U : Opens (ComplexModel n)}
    (hdeg : r + p = n) {α : ComplexModel n → RealForm n (2 * p)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm rfl (oneCurrentOf (U := U) hdeg) hα =
      wedgeForm hdeg (oneCurrent U) hα := by
  cases hdeg
  rfl

theorem correctedReal_zero (P : BackgroundPatch omega) (z : ComplexModel (m + 1)) :
    P.correctedReal (fun _ : M => 0) z = P.correction z := by
  simp [correctedReal, chartFunction]

/-- The literal zero-potential expansion is the actual smooth top form
`omega^(m+1)`, even when the background is not closed. -/
theorem current_zero_eq_smooth (P : BackgroundPatch omega) :
    P.current zeroPotentials = wedgeForm (r := 0) (k := m + 1) (Nat.zero_add (m + 1))
      (oneCurrent P.geometry.domain)
      (((formPow omega.form (m + 1)).smooth P.geometry.chart).mono P.geometry.domain_le_target) := by
  have hq (i : Fin (m + 1)) : IsLocallyBoundedPshOn P.geometry.domain P.correction := by
    have he : P.correctedReal (zeroPotentials i) = P.correction :=
      funext fun z => P.correctedReal_zero z
    rw [← he]
    exact P.correctedReal_isLocallyBoundedPshOn
      (zeroPotentials_isHermitianPSH omega i) (zeroPotentials_bounded i)
  have hv : (fun i => P.correctedReal (zeroPotentials i)) =
      fun _ : Fin (m + 1) => P.correction := by
    funext i z
    exact P.correctedReal_zero z
  unfold current
  rw [hv, backgroundExpansion_smooth (m + 1) 0 _ (fun _ => P.smooth)
    (fun i => (hq i).1) P.residual_smooth
    (fun z hz => oneOne_mem_formSpan (P.residual_isOneOne z hz))]
  · rw [wedgeForm_unit]
    apply wedgeForm_congr
    intro z hz
    change wedgeProd (m + 1) (fun _ => smoothDDC P.correction z +
      (omega.form.coeff P.geometry.chart z - smoothDDC P.correction z)) = _
    have heq : (fun _ : Fin (m + 1) => smoothDDC P.correction z +
        (omega.form.coeff P.geometry.chart z - smoothDDC P.correction z)) =
        fun _ : Fin (m + 1) => omega.form.coeff P.geometry.chart z := by
      funext i
      abel
    rw [heq, formPow_coeff, formPower_eq_wedgeProd]
  · exact isPositive_oneCurrentOf _
  · exact isClosedAny_oneCurrentOf _

/-- The literal smooth top density of the original Hermitian form. -/
def backgroundTopDensity (P : BackgroundPatch omega) (z : ComplexModel (m + 1)) : ℝ :=
  topDensity ((formPow omega.form (m + 1)).coeff P.geometry.chart z)

theorem backgroundTopDensity_pos (P : BackgroundPatch omega) (z : ComplexModel (m + 1))
    (hz : z ∈ P.geometry.domain) : 0 < P.backgroundTopDensity z :=
  topDensity_formPow_pos omega.isHermitian (P.geometry.domain_le_target hz)

theorem backgroundTopDensity_smooth (P : BackgroundPatch omega) :
    ContDiffOn ℝ ∞ P.backgroundTopDensity P.geometry.domain := by
  exact (ContinuousAlternatingMap.apply ℝ (ComplexModel (m + 1)) ℝ (topBasis (m + 1))).contDiff.comp_contDiffOn
    (((formPow omega.form (m + 1)).smooth P.geometry.chart).mono P.geometry.domain_le_target)

/-- Exact native scalar-test reading of the original zero-potential current. -/
theorem current_zero_apply (P : BackgroundPatch omega) (φ : 𝓓(P.geometry.domain, ℝ)) :
    P.current zeroPotentials (kahlerPower (m + 1) 0) φ =
      ∫ z, φ z * P.backgroundTopDensity z := by
  rw [P.current_zero_eq_smooth,
    wedgeForm_oneCurrent_apply (r := 0) (k := m + 1) (Nat.zero_add (m + 1))]
  · apply integral_congr_ae
    filter_upwards [] with z
    change φ z * topDensity (wedgeTo (by omega : 0 + 2 * (m + 1) = 2 * (m + 1))
      (coordinateWedgeUnit : RealForm (m + 1) 0)
      ((formPow omega.form (m + 1)).coeff P.geometry.chart z)) = _
    rw [wedgeTo_unit_left (by omega) rfl]
    rfl
  · intro z hz
    rw [formPow_coeff, formPower_eq_wedgeProd]
    exact wedgeProd_mem_formSpan (m + 1) _
      (fun _ => oneOne_mem_formSpan (omega.isTypeOneOne P.geometry.chart z
        (P.geometry.domain_le_target hz)))

/-- Every nonempty actual coordinate open set has positive trace for the
canonical all-zero product, with the compact test manufactured internally. -/
theorem zero_trace_open_pos (P : BackgroundPatch omega)
    (W : Opens (ComplexModel (m + 1))) (hWP : W ≤ P.geometry.domain)
    (hne : (W : Set (ComplexModel (m + 1))).Nonempty) :
    0 < (P.current_isPositive zeroPotentials (zeroPotentials_isHermitianPSH omega)
      zeroPotentials_bounded).traceMeasure W := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨χ, hχone, hχrange⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := W) (K := {x}) isCompact_singleton (singleton_subset_iff.mpr hx)
  have hχx : χ x = 1 :=
    ((eventually_nhdsSet_iff_forall.mp hχone) x (mem_singleton x)).self_of_nhds
  let φ : 𝓓(P.geometry.domain, ℝ) := extTest hWP χ
  let g : 𝓓(P.geometry.domain, ℝ) := smoothMulTest P.geometry.domain.isOpen
    P.backgroundTopDensity_smooth φ φ.tsupport_subset
  have hg0 : 0 ≤ (g : ComplexModel (m + 1) → ℝ) := by
    intro z
    by_cases hz : z ∈ P.geometry.domain
    · exact mul_nonneg (by simpa only [φ, extTest_apply] using (hχrange z).1)
        (P.backgroundTopDensity_pos z hz).le
    · change 0 ≤ φ z * P.backgroundTopDensity z
      rw [testFunction_eq_zero_of_notMem φ hz, zero_mul]
  have hgx : g x ≠ 0 := by
    change φ x * P.backgroundTopDensity x ≠ 0
    have hφx : φ x = 1 := by simpa only [φ, extTest_apply] using hχx
    rw [hφx, one_mul]
    exact (P.backgroundTopDensity_pos x (hWP hx)).ne'
  have hI : 0 < ∫ z, φ z * P.backgroundTopDensity z :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero g.hasCompactSupport hg0 hgx
  let hT := P.current_isPositive zeroPotentials (zeroPotentials_isHermitianPSH omega)
    zeroPotentials_bounded
  by_contra hnot
  have hnull : hT.traceMeasure W = 0 := le_antisymm (not_lt.mp hnot) bot_le
  have hzero : (φ : ComplexModel (m + 1) → ℝ) =ᵐ[hT.traceMeasure] fun _ => 0 := by
    apply ae_iff.mpr
    apply measure_mono_null (t := (W : Set (ComplexModel (m + 1)))) ?_ hnull
    intro z hz
    apply χ.tsupport_subset
    apply subset_tsupport χ
    change χ z ≠ 0
    change ¬ φ z = 0 at hz
    simpa only [φ, extTest_apply] using hz
  have heq := integral_eq_zero_of_ae hzero
  rw [hT.integral_traceMeasure φ, P.current_zero_apply φ] at heq
  exact hI.ne' heq

end BackgroundPatch

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The canonical smooth background measure has positive mass on every
original nonempty open set. No global volume or mass premise is supplied. -/
theorem zero_globalMixedMeasure_open_pos (omega : Background (m + 1) M)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < globalMixedMeasure omega zeroPotentials (zeroPotentials_isHermitianPSH omega)
      zeroPotentials_bounded U := by
  obtain ⟨x, hxU⟩ := hne
  obtain ⟨P, hxP⟩ := exists_backgroundPatch_containing omega x
  let W : Opens (ComplexModel (m + 1)) :=
    ⟨(P.geometry.domain : Set (ComplexModel (m + 1))) ∩ P.geometry.chart.val.symm ⁻¹' U,
      (P.geometry.chart.val.continuousOn_symm.mono P.geometry.domain_le_target).isOpen_inter_preimage
        P.geometry.domain.isOpen hU⟩
  have hWP : W ≤ P.geometry.domain := inter_subset_left
  have hxW : P.geometry.chart.val x ∈ W := by
    refine ⟨hxP.2, ?_⟩
    change P.geometry.chart.val.symm (P.geometry.chart.val x) ∈ U
    rwa [P.geometry.chart.val.left_inv hxP.1]
  have hpos := P.zero_trace_open_pos W hWP ⟨_, hxW⟩
  have hread := congrArg (fun ν : Measure M => ν U)
    (globalMixedMeasure_restrict_patch zeroPotentials
      (zeroPotentials_isHermitianPSH omega) zeroPotentials_bounded P)
  rw [CoordinatePatch.pushTraceMeasure, CoordinatePatch.pushMeasure_apply,
    Measure.restrict_apply hU.measurableSet] at hread
  apply lt_of_lt_of_le (hread.symm ▸ hpos)
  exact measure_mono inter_subset_left

/-- The actual canonical zero-potential product has full original
topological support, rather than merely positive total mass. -/
theorem zero_globalMixedMeasure_isOpenPosMeasure (omega : Background (m + 1) M) :
    Measure.IsOpenPosMeasure (globalMixedMeasure omega zeroPotentials
      (zeroPotentials_isHermitianPSH omega) zeroPotentials_bounded) :=
  ⟨fun _ hU hne => (zero_globalMixedMeasure_open_pos omega hU hne).ne'⟩

/-- Nonemptiness is the only extra premise for positive total background mass. -/
theorem zero_globalMixedMeasure_univ_pos [Nonempty M] (omega : Background (m + 1) M) :
    0 < globalMixedMeasure omega zeroPotentials (zeroPotentials_isHermitianPSH omega)
      zeroPotentials_bounded univ :=
  zero_globalMixedMeasure_open_pos omega isOpen_univ univ_nonempty

/-- Finiteness of the genuine canonical measure gives a strictly positive
real initial pure trace on every nonempty open set. -/
theorem zero_globalMixedMeasure_open_toReal_pos (omega : Background (m + 1) M)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (globalMixedMeasure omega zeroPotentials (zeroPotentials_isHermitianPSH omega)
      zeroPotentials_bounded U).toReal := by
  let _ := globalMixedMeasure_isFiniteMeasure zeroPotentials
    (zeroPotentials_isHermitianPSH omega) zeroPotentials_bounded
  exact ENNReal.toReal_pos (zero_globalMixedMeasure_open_pos omega hU hne).ne' (measure_ne_top _ _)

theorem zero_globalMixedMeasure_univ_toReal_pos [Nonempty M]
    (omega : Background (m + 1) M) :
    0 < (globalMixedMeasure omega zeroPotentials (zeroPotentials_isHermitianPSH omega)
      zeroPotentials_bounded univ).toReal :=
  zero_globalMixedMeasure_open_toReal_pos omega isOpen_univ univ_nonempty

end SGPT.PSH.HermitianGlobalProducts
