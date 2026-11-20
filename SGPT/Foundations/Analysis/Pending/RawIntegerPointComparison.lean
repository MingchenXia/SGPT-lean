import SGPT.Foundations.Analysis.Pending.BergmanSupWeight
import SGPT.Foundations.Analysis.Pending.BergmanPointLelongLowerBound
import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.FirstPass.IEnvelope

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Foundations.Analysis.Pending.RawIntegerPointComparison

open Set Filter MeasureTheory
open scoped Topology ENNReal
open FirstPass FirstPass.NonKahlerLocus FirstPass.IEnvelope
open BergmanSupWeight BergmanWeightConvergence

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- Actual finite weighted integrals normalize each generator into the literal
kernel. Added ones handle zero masses and the empty family without division. -/
theorem exists_bergmanMajorant_of_weighted_generators
    {D : Set (ComplexModel n)} {P v : ComplexModel n → EReal}
    {p : ℕ} (hp : 0 < p) {N : ℕ} (g : Fin N → ComplexModel n → ℂ)
    (hg : ∀ i, DifferentiableOn ℂ (g i) D)
    (hL2 : ∀ i, WeightedL2On v (p : ℝ) (g i) D volume)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : ∀ y ∈ D, EReal.exp ((p : EReal) * P y) ≤
      C * ∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) :
    ∃ A : ℝ, ∀ y ∈ D, P y ≤ bergmanWeight D v p y + (A : EReal) := by
  classical
  let I : Fin N → ℝ≥0∞ := fun i =>
    ∫⁻ z in D, ENNReal.ofReal (‖g i z‖ ^ 2) * multiplierWeight (p : ℝ) (v z)
  let A : Fin N → ℝ≥0∞ := fun i => I i + 1
  have hIfin (i : Fin N) : I i ≠ ⊤ := (hL2 i).2.ne
  have hAfin (i : Fin N) : A i ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hIfin i, ENNReal.one_ne_top⟩
  have hApos (i : Fin N) : 0 < A i :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left bot_le)
  have hsumfin : (∑ i, A i) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hAfin i)
  let H : ℝ≥0∞ := (C + 1) * (1 + ∑ i, A i)
  have hHfin : H ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨hC, ENNReal.one_ne_top⟩)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hsumfin⟩)
  have hHpos : 0 < H := by
    dsimp [H]
    exact ENNReal.mul_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left bot_le)))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right bot_le)))
  have hHreal : H.log = (Real.log H.toReal : EReal) := by
    calc
      H.log = (ENNReal.ofReal H.toReal).log := by rw [ENNReal.ofReal_toReal hHfin]
      _ = (Real.log H.toReal : EReal) :=
        ENNReal.log_ofReal_of_pos (ENNReal.toReal_pos hHpos.ne' hHfin)
  let a : EReal := (((p : ℝ)⁻¹ : ℝ) : EReal)
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have ha_ne_top : a ≠ ⊤ := EReal.coe_ne_top _
  have hacancel : a * (p : EReal) = 1 := by
    dsimp [a]
    norm_cast
    field_simp
  refine ⟨(p : ℝ)⁻¹ * Real.log H.toReal, fun y hy => ?_⟩
  have hext (i : Fin N) : ENNReal.ofReal (‖g i y‖ ^ 2) ≤
      A i * bergmanSup D (fun z => multiplierWeight (p : ℝ) (v z)) y := by
    apply bergmanSup_extremal (hg i) (hApos i).ne' (hAfin i)
    exact le_add_of_nonneg_right bot_le
  have hsum : (∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) ≤
      (∑ i, A i) * bergmanSup D (fun z => multiplierWeight (p : ℝ) (v z)) y := by
    simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun i _ => hext i)
  have hexp : EReal.exp ((p : EReal) * P y) ≤
      H * bergmanSup D (fun z => multiplierWeight (p : ℝ) (v z)) y := by
    calc
      _ ≤ C * ∑ i, ENNReal.ofReal (‖g i y‖ ^ 2) := hdom y hy
      _ ≤ C * ((∑ i, A i) * bergmanSup D (fun z => multiplierWeight (p : ℝ) (v z)) y) :=
        mul_le_mul_of_nonneg_left hsum bot_le
      _ ≤ (C + 1) * ((1 + ∑ i, A i) *
          bergmanSup D (fun z => multiplierWeight (p : ℝ) (v z)) y) := by
        exact mul_le_mul'
          (le_add_of_nonneg_right bot_le)
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left bot_le) bot_le)
      _ = _ := by dsimp [H]; rw [mul_assoc]
  have hlog : (p : EReal) * P y ≤
      (Real.log H.toReal : EReal) + bergmanLog D (fun z => multiplierWeight (p : ℝ) (v z)) y := by
    simpa only [EReal.log_exp, ENNReal.log_mul_add, hHreal, bergmanLog] using
      ENNReal.log_le_log hexp
  have hscaled := mul_le_mul_of_nonneg_left hlog ha_nonneg
  rw [← mul_assoc, hacancel, one_mul,
    EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top] at hscaled
  simpa only [bergmanWeight, a, EReal.coe_mul, add_comm] using hscaled

omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
/-- Positive integers at the same canonical weighted germ predicate. -/
def IntegerTestsAt (u v : ComplexModel n → EReal) (x : ComplexModel n) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ p : ℕ, 0 < p → ∀ g : ComplexModel n → ℂ, AnalyticAt ℂ g x →
    MultiplierIntegrableAt u (p : ℝ) g x volume →
      MultiplierIntegrableAt v (p : ℝ) g x volume

omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
/-- The actual finite OT family and the actual transferred integrals produce
the pointwise Bergman error, without finiteness of either point reader. -/
theorem lelongNumber_le_add_error_of_integer_tests
    {u v : ComplexModel n → EReal} {x : ComplexModel n}
    (hu : QuasiPlurisubharmonicAt u x) (htests : IntegerTestsAt u v x)
    {p : ℕ} (hp : 0 < p) :
    lelongNumber (n := n) v x ≤ lelongNumber (n := n) u x +
      ENNReal.ofReal (2 * (n : ℝ) / (p : ℝ)) := by
  classical
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨P, h, ⟨Ω, hΩ, hxΩ, hdisc⟩, hh, heq⟩ := hu
  have hP : PlurisubharmonicOn P Ω := hdisc.plurisubharmonicOn hΩ
  have hu' : QuasiPlurisubharmonicAt u x :=
    ⟨P, h, ⟨Ω, hΩ, hxΩ, hdisc⟩, hh, heq⟩
  have hhc : ContinuousAt h x := hh.self_of_nhds.continuousAt
  have hreader : lelongNumber (n := n) P x = lelongNumber (n := n) u x := by
    have hc := LelongNumberComparison.lelongNumber_congr (n := n) heq
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
      (boundedRealGermAt_of_continuousAt hhc)] at hc
    exact hc.symm
  have hnear : ∀ᶠ t in 𝓝 x, |h t - h x| < 1 := by
    filter_upwards [hhc (Metric.ball_mem_nhds (h x) one_pos)] with t ht
    simpa only [mem_preimage, Metric.mem_ball, Real.dist_eq] using ht
  have hmore : MoreSingularAt P u x := by
    refine ⟨-h x + 1, ?_⟩
    filter_upwards [heq, hnear] with t ht hb
    rw [ht, add_assoc, ← EReal.coe_add]
    refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
    linarith [(abs_lt.mp hb).1]
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  obtain ⟨O, hO, hxO, _, N, g, C, hC, hgan, hgL2, hdom⟩ :=
    DemaillyApproximation.exists_weightedL2_generators Ω P hΩ hP x hxΩ p hp
  have htests' (i : Fin N) : ∃ U : Set (ComplexModel n), IsOpen U ∧ x ∈ U ∧
      DifferentiableOn ℂ (g i) U ∧ WeightedL2On v (p : ℝ) (g i) U volume := by
    have hPint : MultiplierIntegrableAt P (p : ℝ) (g i) x volume :=
      ⟨hpr, O, hO, hxO, (hgan i).differentiableOn, hgL2 i⟩
    exact (htests p hp (g i) (hgan i x hxO)
      (multiplierIntegrableAt_of_moreSingularAt hu' hmore hPint)).2
  choose U hU hxU hgU hL2U using htests'
  let D := O ∩ ⋂ i, U i
  have hD : IsOpen D := hO.inter (isOpen_iInter_of_finite hU)
  have hxD : x ∈ D := ⟨hxO, mem_iInter.mpr hxU⟩
  have hDsub (i : Fin N) : D ⊆ U i := fun _ hz => mem_iInter.mp hz.2 i
  obtain ⟨A, hA⟩ := exists_bergmanMajorant_of_weighted_generators hp g
    (fun i => (hgU i).mono (hDsub i))
    (fun i => (hL2U i).mono (hDsub i)) hC (fun y hy => hdom y hy.1)
  have hnearD : ∀ᶠ y in 𝓝 x, y ∈ D := hD.mem_nhds hxD
  have hmajor : ∀ᶠ y in 𝓝[≠] x, P y ≤ bergmanWeight D v p y + (A : EReal) :=
    (hnearD.mono (fun y hy => hA y hy)).filter_mono nhdsWithin_le_nhds
  have hkernel : lelongNumber (n := n) (bergmanWeight D v p) x ≤ lelongNumber (n := n) u x := by
    have hm := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := n) hmajor
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
      (boundedRealGermAt_of_continuousAt (continuousAt_const : ContinuousAt (fun _ : ComplexModel n => A) x)),
      hreader] at hm
    exact hm
  exact (BergmanPointLelongLowerBound.lelongNumber_le_bergmanWeight_add_error hD hxD v
    (by omega : 1 ≤ p)).trans (add_le_add hkernel le_rfl)

omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
/-- Closed extended order removes the actual dimension/level error. -/
theorem lelongNumber_le_of_integer_tests
    {u v : ComplexModel n → EReal} {x : ComplexModel n}
    (hu : QuasiPlurisubharmonicAt u x) (htests : IntegerTestsAt u v x) :
    lelongNumber (n := n) v x ≤ lelongNumber (n := n) u x := by
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal
      (2 * (n : ℝ) / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    have hreal := (tendsto_const_nhds (x := 2 * (n : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have ht : Tendsto (fun j : ℕ => 2 * (n : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using hreal
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hlimadd := (tendsto_const_nhds (x := lelongNumber (n := n) u x)).add hlim
  have hbound : ∀ j : ℕ, lelongNumber (n := n) v x ≤ lelongNumber (n := n) u x +
      ENNReal.ofReal (2 * (n : ℝ) / ((j : ℝ) + 1)) := by
    intro j
    simpa only [Nat.cast_add, Nat.cast_one] using
      lelongNumber_le_add_error_of_integer_tests hu htests (p := j + 1) (by omega)
  simpa only [add_zero] using ge_of_tendsto' hlimadd hbound

omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
/-- The same original point, via its actual complex chart. -/
theorem lelongNumber_le_of_iOrderOnManifold {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u v : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hI : IOrderOnManifold (n := n) u v) (x : M) :
    lelongNumber (n := n) v x ≤ lelongNumber (n := n) u x := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  let e : ComplexChart n M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have htests : IntegerTestsAt (chartFunction u e) (chartFunction v e) (e.val x) := by
    intro p hp g hg hmem
    exact hI (p : ℝ) (by exact_mod_cast hp) e (e.val x) hz g hg hmem
  have h := lelongNumber_le_of_integer_tests (hu e (e.val x) hz) htests
  simpa only [LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hx] using h

end SGPT.Foundations.Analysis.Pending.RawIntegerPointComparison
