import SGPT.Envelopes.LapClassKahlerClass

/-!
# Localization of the actual metric Laplacian

The complete mathematical argument precedes this file in
`blueprint/src/dnt-big-local-laplacian.tex`. This is the distributional
localization step in the big-class Di Nezza--Trapani regularity route. It uses
the actual Kähler metric Laplacian and volume, and a genuine finite smooth
partition of unity. The function need only be continuous on the open set in
question; its arbitrary values outside that set introduce no integrability
assumption. No regularity assertion about the big-class envelope is assumed
or concluded without the local analytic estimates.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent
open SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y]

/-- A local distributional test integrand is globally continuous. Outside the
test function's support its actual Laplacian vanishes on a neighborhood. -/
theorem continuous_mul_laplacian_of_tsupport_subset (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : ContinuousOn f U)
    {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) (hχU : tsupport χ ⊆ U) :
    Continuous (fun y => f y * laplacian w.form.val χ y) := by
  have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hχ
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ U
  · exact ((hf y hy).continuousAt (hU.mem_nhds hy)).mul hL.continuousAt
  · have hys : y ∉ tsupport χ := fun h => hy (hχU h)
    have hzero : (fun z => f z * laplacian w.form.val χ z) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hys] with z hz
      rw [laplacian_eq_zero_of_notMem_tsupport _ hz, mul_zero]
    exact (continuousAt_congr hzero).mpr continuousAt_const

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- Local metric-Laplacian test pairings are honest integrals, including for a
function whose values outside the open set are arbitrary. -/
theorem integrable_mul_laplacian_of_tsupport_subset (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : ContinuousOn f U)
    {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) (hχU : tsupport χ ⊆ U) :
    Integrable (fun y => f y * laplacian w.form.val χ y) (kahlerVolume w) :=
  integral_continuous (continuous_mul_laplacian_of_tsupport_subset w hU hf hχ hχU) _

/-- A finite smooth partition of unity converts neighborhood distributional
Laplacian estimates into one bound for every compact subset of the open set.
The resulting constant is nonnegative and independent of the test function. -/
theorem exists_compact_laplacian_bound_of_local_bounds (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : ContinuousOn f U)
    (hloc : ∀ x ∈ U, ∃ V : Set Y, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ A : ℝ, ∀ ψ : Y → ℝ, ChartSmooth (n := N) ψ → (∀ y, 0 ≤ ψ y) →
        tsupport ψ ⊆ V →
        |∫ y, f y * laplacian w.form.val ψ y ∂(kahlerVolume w)| ≤
          A * ∫ y, ψ y ∂(kahlerVolume w))
    {K : Set Y} (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
      (∀ y, 0 ≤ χ y) → tsupport χ ⊆ K →
      |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
        A * ∫ y, χ y ∂(kahlerVolume w) := by
  classical
  choose V hVo hxV hVU A hA using fun x : K => hloc x (hKU x.property)
  let S : Option K → TopologicalSpace.Opens Y := fun i =>
    match i with
    | none => ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
    | some x => ⟨V x, hVo x⟩
  have hcover : ∀ y : Y, ∃ i, y ∈ S i := by
    intro y
    by_cases hy : y ∈ K
    · exact ⟨some ⟨y, hy⟩, hxV ⟨y, hy⟩⟩
    · exact ⟨none, hy⟩
  obtain ⟨m, ρ, idx, hρs, hρ0, hρS, _, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := N) S hcover
  let B : Fin m → ℝ := fun a =>
    match idx a with
    | none => 0
    | some x => |A x|
  have hB : ∀ a, 0 ≤ B a := by
    intro a
    cases hi : idx a <;> simp only [B, hi, le_refl, abs_nonneg]
  have hρ1 : ∀ a y, ρ a y ≤ 1 := by
    intro a y
    rw [← hsum y]
    exact Finset.single_le_sum (fun i _ => hρ0 i y) (Finset.mem_univ a)
  refine ⟨∑ a, B a, Finset.sum_nonneg (fun a _ => hB a), ?_⟩
  intro χ hχ hχ0 hχK
  let ψ : Fin m → Y → ℝ := fun a y => ρ a y * χ y
  have hψs : ∀ a, ChartSmooth (n := N) (ψ a) := fun a e =>
    (hρs a e).mul (hχ e)
  have hψ0 : ∀ a y, 0 ≤ ψ a y := fun a y => mul_nonneg (hρ0 a y) (hχ0 y)
  have hψK : ∀ a, tsupport (ψ a) ⊆ K := fun _ =>
    tsupport_mul_subset_right.trans hχK
  have hψint : ∀ a, Integrable (fun y => f y * laplacian w.form.val (ψ a) y)
      (kahlerVolume w) := fun a =>
    integrable_mul_laplacian_of_tsupport_subset w hU hf (hψs a) ((hψK a).trans hKU)
  have hψle : ∀ a, ∫ y, ψ a y ∂(kahlerVolume w) ≤ ∫ y, χ y ∂(kahlerVolume w) := by
    intro a
    refine integral_mono
      (integral_continuous (YauUniformEstimate.continuous_of_chartSmooth (hψs a)) _)
      (integral_continuous (YauUniformEstimate.continuous_of_chartSmooth hχ) _) fun y => ?_
    show ρ a y * χ y ≤ χ y
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hρ1 a y) (hχ0 y)
  have hbound : ∀ a,
      |∫ y, f y * laplacian w.form.val (ψ a) y ∂(kahlerVolume w)| ≤
        B a * ∫ y, χ y ∂(kahlerVolume w) := by
    intro a
    cases hi : idx a with
    | none =>
      have hs : tsupport (ρ a) ⊆ Kᶜ := by
        simpa only [hi, S, TopologicalSpace.Opens.coe_mk] using hρS a
      have hz : ψ a = fun _ => 0 := by
        funext y
        by_cases hy : χ y = 0
        · simp only [ψ, hy, mul_zero]
        · have hyK : y ∈ K := hχK (subset_tsupport χ hy)
          have hyρ : y ∉ tsupport (ρ a) := fun h => (hs h) hyK
          simp only [ψ, image_eq_zero_of_notMem_tsupport hyρ, zero_mul]
      have hL0 : ∀ y, laplacian w.form.val (ψ a) y = 0 := fun y =>
        laplacian_eq_zero_of_notMem_tsupport _ (by rw [hz]; simp)
      simp only [hL0, mul_zero, integral_zero, abs_zero, B, hi, zero_mul, le_refl]
    | some x =>
      have hs : tsupport (ρ a) ⊆ V x := by
        simpa only [hi, S, TopologicalSpace.Opens.coe_mk] using hρS a
      calc
        |∫ y, f y * laplacian w.form.val (ψ a) y ∂(kahlerVolume w)|
            ≤ A x * ∫ y, ψ a y ∂(kahlerVolume w) :=
          hA x (ψ a) (hψs a) (hψ0 a) (tsupport_mul_subset_left.trans hs)
        _ ≤ |A x| * ∫ y, ψ a y ∂(kahlerVolume w) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (integral_nonneg (hψ0 a))
        _ ≤ |A x| * ∫ y, χ y ∂(kahlerVolume w) :=
          mul_le_mul_of_nonneg_left (hψle a) (abs_nonneg _)
        _ = B a * ∫ y, χ y ∂(kahlerVolume w) := by simp only [B, hi]
  have hχsum : χ = fun y => ∑ a, ψ a y := by
    funext y
    dsimp only [ψ]
    rw [← Finset.sum_mul, hsum, one_mul]
  have hLsum : ∀ y, laplacian w.form.val χ y =
      ∑ a, laplacian w.form.val (ψ a) y := by
    intro y
    conv_lhs => rw [hχsum]
    exact laplacian_sum _ _ (fun a _ => chartSmooth_two' (hψs a)) y
  have hsplit : ∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) =
      ∑ a, ∫ y, f y * laplacian w.form.val (ψ a) y ∂(kahlerVolume w) := by
    calc
      _ = ∫ y, ∑ a, f y * laplacian w.form.val (ψ a) y ∂(kahlerVolume w) :=
        integral_congr_ae (Eventually.of_forall fun y => by rw [hLsum, Finset.mul_sum])
      _ = _ := integral_finsetSum _ (fun a _ => hψint a)
  rw [hsplit]
  calc
    |∑ a, ∫ y, f y * laplacian w.form.val (ψ a) y ∂(kahlerVolume w)|
        ≤ ∑ a, |∫ y, f y * laplacian w.form.val (ψ a) y ∂(kahlerVolume w)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, B a * ∫ y, χ y ∂(kahlerVolume w) :=
      Finset.sum_le_sum (fun a _ => hbound a)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The neighborhood test estimates imply the book's actual local bounded
metric-Laplacian condition, on the same open set and for the same function. -/
theorem hasBoundedMetricLaplacianOn_of_local_bounds (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : ContinuousOn f U)
    (hloc : ∀ x ∈ U, ∃ V : Set Y, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ A : ℝ, ∀ ψ : Y → ℝ, ChartSmooth (n := N) ψ → (∀ y, 0 ≤ ψ y) →
        tsupport ψ ⊆ V →
        |∫ y, f y * laplacian w.form.val ψ y ∂(kahlerVolume w)| ≤
          A * ∫ y, ψ y ∂(kahlerVolume w)) :
    HasBoundedMetricLaplacianOn w U f := by
  refine ⟨hf, fun K hKU hK => ?_⟩
  obtain ⟨A, _, hA⟩ := exists_compact_laplacian_bound_of_local_bounds w hU hf hloc hKU hK
  exact ⟨A, hA⟩

end SGPT.NPP.DNTBig
