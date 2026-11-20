import SGPT.Foundations.Analysis.Pending.CompactNonPluripolarChartWeightIntegrability
import SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotIntegrableDefect

set_option autoImplicit false

/-! # Actual compact smooth-slot data produce canonical NP regularizer integrability and the signed time-slot defect -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactNonPluripolarTimeSlotDefect

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  RelativeEnergy GlobalSlotStokes MixedNonPluripolar
  BedfordTaylor MixedDensityRankOneSlot BedfordTaylorTimeSlot
  CompactNonPluripolarChartWeightIntegrability
  NonPluripolarTimeSlotTruncationBalance NonPluripolarTimeSlotIntegrableDefect

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]
  [CompactSpace M] {η : Fin (n + 1) → ClosedRealOneOneForm (n + 1) M}
  {κ : ClosedRealOneOneForm (n + 1) M}
  {α β : SmoothRealForm (n + 1) M 2} {W Φ : M → EReal}
  {v : Fin (n + 1) → M → EReal}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

private theorem regularizer_weight_integrable (omega : KahlerBackground (n + 1) M)
    (hW : ThetaPlurisubharmonic α W) (hΦ : ThetaPlurisubharmonic β Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (J : SlotChart η κ)
    (hv : ∀ i, i ≠ Fin.last n → ThetaPlurisubharmonic (η i).val (v i))
    {g : M → ℝ} (hg : ThetaPlurisubharmonic (η (Fin.last n)).val fun x => (g x : EReal))
    (hu : ∀ i, PlurisubharmonicOn (u i) J.domain)
    (hfirst : ∀ i, i ≠ Fin.last n → EqOn (u i)
      (fun z => chartFunction (v i) J.chart z + (J.potential i z : EReal)) J.domain)
    {q : ComplexModel (n + 1) → ℝ} (hq : IsSmoothPsdOn J.domain q)
    (hlast : EqOn (fun z => g (J.chart.val.symm z) + J.potential (Fin.last n) z) q J.domain)
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (ρ : ComplexModel (n + 1) → ℝ) :
    Integrable (fun z => χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal)))
      (mixedTruncationLimitMeasure J.domain
        (Function.update u (Fin.last n) fun z => (q z : EReal))
        (plurisubharmonicOn_update_last hu hq)) := by
  classical
  let s : Fin (n + 1) → M → EReal := Function.update v (Fin.last n) fun x => (g x : EReal)
  have hs (i : Fin (n + 1)) : ThetaPlurisubharmonic (η i).val (s i) := by
    by_cases hi : i = Fin.last n
    · subst i
      simpa only [s, Function.update_self] using hg
    · simpa only [s, Function.update_of_ne hi] using hv i hi
  let P := J.patch s hs
  have heq : ∀ i, EqOn (P.corrected i)
      ((Function.update u (Fin.last n) fun z => (q z : EReal)) i) J.domain := by
    intro i z hz
    by_cases hi : i = Fin.last n
    · subst i
      simp only [Function.update_self]
      change chartFunction (s (Fin.last n)) J.chart z + (J.potential (Fin.last n) z : EReal) =
        (q z : EReal)
      simp only [s, Function.update_self, chartFunction]
      rw [← EReal.coe_add]
      exact congrArg (fun r : ℝ => (r : EReal)) (hlast hz)
    · simp only [Function.update_of_ne hi]
      change chartFunction (s i) J.chart z + (J.potential i z : EReal) = u i z
      simpa only [s, Function.update_of_ne hi] using (hfirst i hi hz).symm
  exact integrable_mul_corrected_canonicalDiff_of_eqOn omega hW hΦ hWΦ hs P
    (plurisubharmonicOn_update_last hu hq) heq hχ hχc ρ

/-- The actual compact global singular slots and smooth last-slot chart identities internally produce both regularizer-weight integrability facts. -/
theorem regularizer_weights_integrable (omega : KahlerBackground (n + 1) M)
    (hW : ThetaPlurisubharmonic α W) (hΦ : ThetaPlurisubharmonic β Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (J : SlotChart η κ)
    (hv : ∀ i, i ≠ Fin.last n → ThetaPlurisubharmonic (η i).val (v i))
    {a b : M → ℝ}
    (ha : ThetaPlurisubharmonic (η (Fin.last n)).val fun x => (a x : EReal))
    (hb : ThetaPlurisubharmonic (η (Fin.last n)).val fun x => (b x : EReal))
    (hu : ∀ i, PlurisubharmonicOn (u i) J.domain)
    (hfirst : ∀ i, i ≠ Fin.last n → EqOn (u i)
      (fun z => chartFunction (v i) J.chart z + (J.potential i z : EReal)) J.domain)
    {ψ : ℂ → ℝ} {p : ComplexModel (n + 1) → ℝ}
    (hp : IsSmoothPsdOn J.domain p)
    (hψp : IsSmoothPsdOn J.domain fun z => timeLift n ψ z + p z)
    (haLocal : EqOn (fun z => a (J.chart.val.symm z) + J.potential (Fin.last n) z)
      (fun z => timeLift n ψ z + p z) J.domain)
    (hbLocal : EqOn (fun z => b (J.chart.val.symm z) + J.potential (Fin.last n) z) p J.domain)
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (ρ : ComplexModel (n + 1) → ℝ) :
    Integrable (fun z => χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal)))
      (mixedTruncationLimitMeasure J.domain
        (Function.update u (Fin.last n) fun z => ((timeLift n ψ z + p z : ℝ) : EReal))
        (plurisubharmonicOn_update_last hu hψp)) ∧
    Integrable (fun z => χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal)))
      (mixedTruncationLimitMeasure J.domain
        (Function.update u (Fin.last n) fun z => (p z : EReal))
        (plurisubharmonicOn_update_last hu hp)) :=
  ⟨regularizer_weight_integrable omega hW hΦ hWΦ J hv ha hu hfirst hψp haLocal hχ hχc ρ,
    regularizer_weight_integrable omega hW hΦ hWΦ J hv hb hu hfirst hp hbLocal hχ hχc ρ⟩

/-- Natural actual compact-host data produce the canonical signed NP time-slot defect without weighted integrability, positive balance or raw last-slot finite-mass assumptions. -/
theorem integrable_defect_of_compact_host (omega : KahlerBackground (n + 1) M)
    (hW : ThetaPlurisubharmonic α W) (hΦ : ThetaPlurisubharmonic β Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (J : SlotChart η κ)
    (hv : ∀ i, i ≠ Fin.last n → ThetaPlurisubharmonic (η i).val (v i))
    {a b : M → ℝ}
    (ha : ThetaPlurisubharmonic (η (Fin.last n)).val fun x => (a x : EReal))
    (hb : ThetaPlurisubharmonic (η (Fin.last n)).val fun x => (b x : EReal))
    (hu : ∀ i, PlurisubharmonicOn (u i) J.domain)
    (hlast : u (Fin.last n) = fun z => (lastNormSq n z : EReal))
    (hfirst : ∀ i, i ≠ Fin.last n → EqOn (u i)
      (fun z => chartFunction (v i) J.chart z + (J.potential i z : EReal)) J.domain)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : ComplexModel (n + 1) → ℝ}
    (hp : IsSmoothPsdOn J.domain p)
    (hψp : IsSmoothPsdOn J.domain fun z => timeLift n ψ z + p z)
    (haLocal : EqOn (fun z => a (J.chart.val.symm z) + J.potential (Fin.last n) z)
      (fun z => timeLift n ψ z + p z) J.domain)
    (hbLocal : EqOn (fun z => b (J.chart.val.symm z) + J.potential (Fin.last n) z) p J.domain)
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ J.domain) (ρ : ComplexModel (n + 1) → ℝ) :
    Integrable (fun z => (χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal))) * timeLaplacian ψ (z (Fin.last n)))
      (mixedTruncationLimitMeasure J.domain u hu) ∧
    (∫ z, χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal))
      ∂mixedTruncationLimitMeasure J.domain
        (Function.update u (Fin.last n) fun z => ((timeLift n ψ z + p z : ℝ) : EReal))
        (plurisubharmonicOn_update_last hu hψp)) -
    (∫ z, χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal))
      ∂mixedTruncationLimitMeasure J.domain
        (Function.update u (Fin.last n) fun z => (p z : EReal))
        (plurisubharmonicOn_update_last hu hp)) =
    ∫ z, (χ z * canonicalERealDiffToReal
      (chartFunction W J.chart z + (ρ z : EReal))
      (chartFunction Φ J.chart z + (ρ z : EReal))) * timeLaplacian ψ (z (Fin.last n))
      ∂mixedTruncationLimitMeasure J.domain u hu := by
  have hi := regularizer_weights_integrable omega hW hΦ hWΦ J hv ha hb hu hfirst
    hp hψp haLocal hbLocal hχ hχc ρ
  exact integrable_mul_timeLaplacian_and_integral_timeLift_sub hu hlast hψ hp hψp hχc hχΩ
    hi.1 hi.2

end

end SGPT.Foundations.Analysis.Pending.CompactNonPluripolarTimeSlotDefect
