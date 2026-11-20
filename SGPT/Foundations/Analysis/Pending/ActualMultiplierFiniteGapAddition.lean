import SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierFiniteGapAddition
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.StepFourLogSingularities

set_option autoImplicit false

/-! # Actual independent-background all-chart finite exponent-gap addition -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapAddition

open FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation IEquivalentMax
  ActualLocalMultiplierFiniteGapAddition MixedSummandCapacityDomination GlobalMultilinearExpansion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem genuineAdd {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h


private theorem exists_corrected_psh_type {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧ W ⊆ e.val.target ∧
      ∃ P : ComplexModel n → EReal, PlurisubharmonicOn P W ∧
        SameSingularityTypeOn (chartFunction u e) P W := by
  obtain ⟨O, ρ, hzO, hρ⟩ := hu.1.hasSmoothLocalPotentials e z hz
  have hP : PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) O :=
    chartCorrectedFamily_plurisubharmonicOn (F := {u})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hu) e hρ _
      ⟨u, mem_singleton _, rfl⟩
  have hclose : ∀ᶠ y in 𝓝 z, |ρ y - ρ z| < 1 := by
    simpa only [Real.dist_eq] using
      (hρ.2.2.1.continuousOn.continuousAt (hρ.1.mem_nhds hzO)).eventually
        (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨V, hVsub, hV, hzV⟩ := mem_nhds_iff.mp hclose
  let W := O ∩ V
  have hW : IsOpen W := hρ.1.inter hV
  have hbound : ∀ y ∈ W, -(|ρ z| + 1) ≤ ρ y ∧ ρ y ≤ |ρ z| + 1 := by
    intro y hy
    have h1 := hVsub hy.2
    change |ρ y - ρ z| < 1 at h1
    have h2 := abs_sub_abs_le_abs_sub (ρ y) (ρ z)
    constructor
    · have := neg_abs_le (ρ y)
      linarith
    · have := le_abs_self (ρ y)
      linarith
  refine ⟨W, hW, ⟨hzO, hzV⟩, inter_subset_left.trans hρ.2.1,
    (fun y => chartFunction u e y + (ρ y : EReal)), hP.mono inter_subset_left, ?_⟩
  refine ⟨⟨|ρ z| + 1, fun y hy => le_add_coe_add_coe (by linarith [(hbound y hy).1])⟩,
    ⟨|ρ z| + 1, fun y hy => ?_⟩⟩
  simpa only [EReal.coe_zero, add_zero] using
    (add_coe_add_coe_le (x := chartFunction u e y) (r := ρ y) (s := 0)
      (t := |ρ z| + 1) (by linarith [(hbound y hy).2]))

/-- Four actual backgrounds produce all local corrections and genuine sums internally;
only the natural single-level inclusions are supplied. -/
theorem multiplierIdealIncluded_add_of_finite_levels
    {θU θV θA θB : ClosedRealOneOneForm n M} {u v a b : M → EReal}
    (hu : IsThetaPshPotential θU.val u) (hv : IsThetaPshPotential θV.val v)
    (ha : IsThetaPshPotential θA.val a) (hb : IsThetaPshPotential θB.val b)
    {c q p : ℝ} {m : ℕ} (hc : 0 < c) (hq : 0 < q) (hp : 0 < p)
    (hm : 0 < m) (hgap : 2 * c ≤ p - (m : ℝ) * c / q)
    (hua : MultiplierIdealIncluded (n := n) u m a p)
    (hvb : MultiplierIdealIncluded (n := n) v m b p) :
    MultiplierIdealIncluded (n := n) (fun x => u x + v x) q
      (fun x => a x + b x) c := by
  intro e z hz f hf hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨WU, hWU0, hzWU, hWUt, U, hU0, hTU0⟩ := exists_corrected_psh_type hu e hz
  obtain ⟨WV, hWV0, hzWV, hWVt, V, hV0, hTV0⟩ := exists_corrected_psh_type hv e hz
  obtain ⟨WA, hWA0, hzWA, hWAt, A, hA0, hTA0⟩ := exists_corrected_psh_type ha e hz
  obtain ⟨WB, hWB0, hzWB, hWBt, B, hB0, hTB0⟩ := exists_corrected_psh_type hb e hz
  let W := ((WU ∩ WV) ∩ WA) ∩ WB
  have hW : IsOpen W := ((hWU0.inter hWV0).inter hWA0).inter hWB0
  have hzW : z ∈ W := ⟨⟨⟨hzWU, hzWV⟩, hzWA⟩, hzWB⟩
  have hWU : W ⊆ WU := fun _ hy => hy.1.1.1
  have hWV : W ⊆ WV := fun _ hy => hy.1.1.2
  have hWA : W ⊆ WA := fun _ hy => hy.1.2
  have hWB : W ⊆ WB := fun _ hy => hy.2
  have hWt : W ⊆ e.val.target := hWU.trans hWUt
  have hU : PlurisubharmonicOn U W := hU0.mono hWU
  have hV : PlurisubharmonicOn V W := hV0.mono hWV
  have hA : PlurisubharmonicOn A W := hA0.mono hWA
  have hB : PlurisubharmonicOn B W := hB0.mono hWB
  have hTU : SameSingularityTypeOn (chartFunction u e) U W :=
    ⟨hTU0.1.mono hWU, hTU0.2.mono hWU⟩
  have hTV : SameSingularityTypeOn (chartFunction v e) V W :=
    ⟨hTV0.1.mono hWV, hTV0.2.mono hWV⟩
  have hTA : SameSingularityTypeOn (chartFunction a e) A W :=
    ⟨hTA0.1.mono hWA, hTA0.2.mono hWA⟩
  have hTB : SameSingularityTypeOn (chartFunction b e) B W :=
    ⟨hTB0.1.mono hWB, hTB0.2.mono hWB⟩
  have horderU : ∀ y ∈ W, ∀ g : ComplexModel n → ℂ, AnalyticAt ℂ g y →
      MultiplierIntegrableAt U (m : ℝ) g y volume → MultiplierIntegrableAt A p g y volume := by
    intro y hy g hg hgm
    have hiu := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := (m : ℝ)) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (hu.1.quasiPlurisubharmonic e y (hWt hy)) (hU y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) hTU
    have hia := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := p) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (ha.1.quasiPlurisubharmonic e y (hWt hy)) (hA y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) hTA
    exact hia.mp (hua e y (hWt hy) g hg (hiu.mpr hgm))
  have horderV : ∀ y ∈ W, ∀ g : ComplexModel n → ℂ, AnalyticAt ℂ g y →
      MultiplierIntegrableAt V (m : ℝ) g y volume → MultiplierIntegrableAt B p g y volume := by
    intro y hy g hg hgm
    have hiv := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := (m : ℝ)) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (hv.1.quasiPlurisubharmonic e y (hWt hy)) (hV y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) hTV
    have hib := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := p) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (hb.1.quasiPlurisubharmonic e y (hWt hy)) (hB y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) hTB
    exact hib.mp (hvb e y (hWt hy) g hg (hiv.mpr hgm))
  have hsumU : SameSingularityTypeOn (chartFunction (fun x => u x + v x) e)
      (fun y => U y + V y) W := StepFourLogSingularities.sameSingularityTypeOn_add hTU hTV
  have hsumA : SameSingularityTypeOn (chartFunction (fun x => a x + b x) e)
      (fun y => A y + B y) W := StepFourLogSingularities.sameSingularityTypeOn_add hTA hTB
  have hiuv := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := q) (f := f)
    (μ := (volume : Measure (ComplexModel n)))
    ((genuineAdd hu hv).1.quasiPlurisubharmonic e z hz)
    ((hU.add hV) z hzW).quasiPlurisubharmonicAt (hW.mem_nhds hzW) hsumU
  have hiab := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := c) (f := f)
    (μ := (volume : Measure (ComplexModel n)))
    ((genuineAdd ha hb).1.quasiPlurisubharmonic e z hz)
    ((hA.add hB) z hzW).quasiPlurisubharmonicAt (hW.mem_nhds hzW) hsumA
  exact hiab.mpr (multiplierIntegrableAt_add_of_finite_levels hW hU hV hA hB hc hq hp hm
    hgap horderU horderV hzW (hiuv.mp hmem))

end

end SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapAddition
