import SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapLocalIntegrability
import SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierOrderAddition

set_option autoImplicit false

/-! # Single finite multiplier levels internally supply true addition integrability -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierFiniteGapAddition

open FirstPass IEquivalentMax ActualMultiplierFiniteGapLocalIntegrability DemaillyApproximation

noncomputable section

variable {n : ℕ}

/-- Natural one-level inclusions produce both actual Demailly families and
all their target weighted integrability before the addition consumer. -/
theorem multiplierIntegrableAt_add_of_finite_levels
    [i : MeasurableSpace (ComplexModel n)] [hi : BorelSpace (ComplexModel n)]
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {U V A B : ComplexModel n → EReal}
    (hU : PlurisubharmonicOn U Ω) (hV : PlurisubharmonicOn V Ω)
    (hA : PlurisubharmonicOn A Ω) (hB : PlurisubharmonicOn B Ω)
    {c q p : ℝ} {m : ℕ} (hc : 0 < c) (hq : 0 < q) (hp : 0 < p)
    (hm : 0 < m) (hgap : 2 * c ≤ p - (m : ℝ) * c / q)
    (hUA : ∀ y ∈ Ω, ∀ g : ComplexModel n → ℂ,
      AnalyticAt ℂ g y → MultiplierIntegrableAt U (m : ℝ) g y volume →
        MultiplierIntegrableAt A p g y volume)
    (hVB : ∀ y ∈ Ω, ∀ g : ComplexModel n → ℂ,
      AnalyticAt ℂ g y → MultiplierIntegrableAt V (m : ℝ) g y volume →
        MultiplierIntegrableAt B p g y volume)
    {z : ComplexModel n} (hz : z ∈ Ω) {f : ComplexModel n → ℂ}
    (hmem : MultiplierIntegrableAt (fun y => U y + V y) q f z volume) :
    MultiplierIntegrableAt (fun y => A y + B y) c f z volume := by
  classical
  obtain rfl : i = borel _ := hi.measurable_eq
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  have hAB : PlurisubharmonicOn (fun y => A y + B y) Ω := hA.add hB
  have hm0r : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨OU, hOU, hzOU, hOUΩ, N₁, g, C, hC, hgan, hgL2, hdomU⟩ :=
    exists_weightedL2_generators Ω U hΩ hU z hz m hm
  obtain ⟨OV, hOV, hzOV, hOVΩ, N₂, h, D, hD, hhan, hhL2, hdomV⟩ :=
    exists_weightedL2_generators Ω V hΩ hV z hz m hm
  let O := OU ∩ OV
  have hO : IsOpen O := hOU.inter hOV
  have hzO : z ∈ O := ⟨hzOU, hzOV⟩
  have hOΩ : O ⊆ Ω := fun _ hy => hOUΩ hy.1
  have hgA : ∀ l, ∃ r > 0, Metric.ball z r ⊆ O ∧
      WeightedL2On A p (g l) (Metric.ball z r) volume := by
    intro l
    apply exists_ball_weightedL2On hO hzO
      (fun y hy => (hA y (hOΩ hy)).quasiPlurisubharmonicAt)
      ((hgan l).differentiableOn.mono inter_subset_left) hp
    intro y hy
    exact hUA y (hOΩ hy) (g l) (hgan l y hy.1)
      ⟨hm0r, OU, hOU, hy.1, (hgan l).differentiableOn, hgL2 l⟩
  have hhB : ∀ r, ∃ s > 0, Metric.ball z s ⊆ O ∧
      WeightedL2On B p (h r) (Metric.ball z s) volume := by
    intro r
    apply exists_ball_weightedL2On hO hzO
      (fun y hy => (hB y (hOΩ hy)).quasiPlurisubharmonicAt)
      ((hhan r).differentiableOn.mono inter_subset_right) hp
    intro y hy
    exact hVB y (hOΩ hy) (h r) (hhan r y hy.2)
      ⟨hm0r, OV, hOV, hy.2, (hhan r).differentiableOn, hhL2 r⟩
  choose rg hrg hrgO hrgL2 using hgA
  choose rh hrh hrhO hrhL2 using hhB
  let Q := (O ∩ ⋂ l, Metric.ball z (rg l)) ∩ ⋂ r, Metric.ball z (rh r)
  have hQ : IsOpen Q :=
    (hO.inter (isOpen_iInter_of_finite fun l => Metric.isOpen_ball)).inter
      (isOpen_iInter_of_finite fun r => Metric.isOpen_ball)
  have hzQ : z ∈ Q := ⟨⟨hzO, mem_iInter.mpr fun l => Metric.mem_ball_self (hrg l)⟩,
    mem_iInter.mpr fun r => Metric.mem_ball_self (hrh r)⟩
  have hQΩ : Q ⊆ Ω := fun _ hy => hOΩ hy.1.1
  exact multiplierIntegrableAt_add_of_generators hc hq hp hm0r hgap hmem hQ hzQ
    (fun y hy => (hA y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hB y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hU y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hV y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hAB y (hQΩ hy)).quasiPlurisubharmonicAt) hC hD
    (fun l => (hrgL2 l).mono fun y hy => mem_iInter.mp hy.1.2 l)
    (fun r => (hrhL2 r).mono fun y hy => mem_iInter.mp hy.2 r)
    (fun y hy => hdomU y hy.1.1.1) (fun y hy => hdomV y hy.1.1.2)


end

end SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierFiniteGapAddition
