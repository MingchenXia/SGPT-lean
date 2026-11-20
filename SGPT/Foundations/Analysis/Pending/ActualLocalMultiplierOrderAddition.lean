import SGPT.Foundations.Analysis.Pending.ActualMultiplierAdditionLocalIntegrability

set_option autoImplicit false

/-! # All-level local multiplier orders imply genuine addition order -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierOrderAddition

open FirstPass IEquivalentMax ActualMultiplierAdditionLocalIntegrability DemaillyApproximation

noncomputable section

variable {n : ℕ}

/-- Actual all-level germ orders supply both independent generator families internally. -/
theorem multiplierIntegrableAt_add_of_all_levels
    [i : MeasurableSpace (ComplexModel n)] [hi : BorelSpace (ComplexModel n)]
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {U V A B : ComplexModel n → EReal}
    (hU : PlurisubharmonicOn U Ω) (hV : PlurisubharmonicOn V Ω)
    (hA : PlurisubharmonicOn A Ω) (hB : PlurisubharmonicOn B Ω)
    (hUA : ∀ y ∈ Ω, ∀ r : ℝ, 0 < r → ∀ g : ComplexModel n → ℂ,
      AnalyticAt ℂ g y → MultiplierIntegrableAt U r g y volume →
        MultiplierIntegrableAt A r g y volume)
    (hVB : ∀ y ∈ Ω, ∀ r : ℝ, 0 < r → ∀ g : ComplexModel n → ℂ,
      AnalyticAt ℂ g y → MultiplierIntegrableAt V r g y volume →
        MultiplierIntegrableAt B r g y volume)
    {z : ComplexModel n} (hz : z ∈ Ω) {c : ℝ} (hc : 0 < c)
    {f : ComplexModel n → ℂ} (hf : AnalyticAt ℂ f z)
    (hmem : MultiplierIntegrableAt (fun y => U y + V y) c f z volume) :
    MultiplierIntegrableAt (fun y => A y + B y) c f z volume := by
  classical
  obtain rfl : i = borel _ := hi.measurable_eq
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  have hUV : PlurisubharmonicOn (fun y => U y + V y) Ω := hU.add hV
  have hAB : PlurisubharmonicOn (fun y => A y + B y) Ω := hA.add hB
  obtain ⟨L, hL⟩ : ∃ L : ℝ, U z + V z < (L : EReal) :=
    EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (hUV z hz).ne_top) |>.imp
      fun _ h => h.1
  obtain ⟨O1, hO1sub, hO1, hzO1⟩ := mem_nhds_iff.mp
    ((hUV z hz).quasiPlurisubharmonicAt.upperSemicontinuousAt (L : EReal) hL)
  let W := Ω ∩ O1
  have hW : IsOpen W := hΩ.inter hO1
  have hzW : z ∈ W := ⟨hz, hzO1⟩
  let P : ComplexModel n → EReal := fun y => (U y + V y) + ((-L : ℝ) : EReal)
  have hP : PlurisubharmonicOn P W := (hUV.mono inter_subset_left).add
    (fun y _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) y)
  have hP0 : ∀ y ∈ W, P y ≤ 0 := by
    intro y hy
    have h := add_le_add (hO1sub hy.2).le (le_refl ((-L : ℝ) : EReal))
    simpa only [P, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
  have hPmem : MultiplierIntegrableAt P c f z volume :=
    multiplierIntegrableAt_of_moreSingularAt (φ := fun y => U y + V y)
      (μ := (volume : Measure (ComplexModel n))) (hP z hzW).quasiPlurisubharmonicAt
      ⟨L, Eventually.of_forall fun y => by
        simp only [P, add_assoc, ← EReal.coe_add, neg_add_cancel,
          EReal.coe_zero, add_zero]
        exact le_rfl⟩ hmem
  obtain ⟨δ, hδ, hPq⟩ := exists_multiplierIntegrableAt_mul
    (increasingStrongOpenness_ofRegularRoute n) W P hW hP hP0 z hzW c hc f hf hPmem
  have hUVq : MultiplierIntegrableAt (fun y => U y + V y) (c * (1 + δ)) f z volume :=
    multiplierIntegrableAt_of_moreSingularAt (φ := P)
      (μ := (volume : Measure (ComplexModel n))) (hUV z hz).quasiPlurisubharmonicAt
      ⟨-L, Eventually.of_forall fun _ => le_rfl⟩ hPq
  let m : ℕ := ⌈2 * (c * (1 + δ)) / δ⌉₊
  have hm : 2 * (c * (1 + δ)) / δ ≤ (m : ℝ) := Nat.le_ceil _
  have hm0 : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hm0r : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨OU, hOU, hzOU, hOUΩ, N₁, g, C, hC, hgan, hgL2, hdomU⟩ :=
    exists_weightedL2_generators Ω U hΩ hU z hz m hm0
  obtain ⟨OV, hOV, hzOV, hOVΩ, N₂, h, D, hD, hhan, hhL2, hdomV⟩ :=
    exists_weightedL2_generators Ω V hΩ hV z hz m hm0
  let O := OU ∩ OV
  have hO : IsOpen O := hOU.inter hOV
  have hzO : z ∈ O := ⟨hzOU, hzOV⟩
  have hOΩ : O ⊆ Ω := fun _ hy => hOUΩ hy.1
  have hgA : ∀ l, ∃ r > 0, Metric.ball z r ⊆ O ∧
      WeightedL2On A (m : ℝ) (g l) (Metric.ball z r) volume := by
    intro l
    apply exists_ball_weightedL2On hO hzO
      (fun y hy => (hA y (hOΩ hy)).quasiPlurisubharmonicAt)
      ((hgan l).differentiableOn.mono inter_subset_left) hm0r
    intro y hy
    exact hUA y (hOΩ hy) m hm0r (g l) (hgan l y hy.1)
      ⟨hm0r, OU, hOU, hy.1, (hgan l).differentiableOn, hgL2 l⟩
  have hhB : ∀ r, ∃ s > 0, Metric.ball z s ⊆ O ∧
      WeightedL2On B (m : ℝ) (h r) (Metric.ball z s) volume := by
    intro r
    apply exists_ball_weightedL2On hO hzO
      (fun y hy => (hB y (hOΩ hy)).quasiPlurisubharmonicAt)
      ((hhan r).differentiableOn.mono inter_subset_right) hm0r
    intro y hy
    exact hVB y (hOΩ hy) m hm0r (h r) (hhan r y hy.2)
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
  exact multiplierIntegrableAt_add_of_generators hc hδ hm hUVq hQ hzQ
    (fun y hy => (hA y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hB y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hU y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hV y (hQΩ hy)).quasiPlurisubharmonicAt)
    (fun y hy => (hAB y (hQΩ hy)).quasiPlurisubharmonicAt) hC hD
    (fun l => (hrgL2 l).mono fun y hy => mem_iInter.mp hy.1.2 l)
    (fun r => (hrhL2 r).mono fun y hy => mem_iInter.mp hy.2 r)
    (fun y hy => hdomU y hy.1.1.1) (fun y hy => hdomV y hy.1.1.2)

end

end SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierOrderAddition
