import SGPT.Convex.Epigraph
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic

/-! Original finite real nodal heights plus one actual far-left point yield
a barycentre-inequality lower bound for any extended concave majorant.
No global EReal monotonicity or finite-value certificate for the majorant. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.HullAnalytic
open Set Filter
open scoped Topology BigOperators

/-- Actual finite Jensen directly in the source real-height epigraph. -/
theorem finite_realHeight_jensen {ι : Type*} [Fintype ι]
    (t c w : ι → ℝ) (f : ℝ → EReal)
    (hf : SGPT.Convex.IsConvex (fun r => -f r))
    (hc : ∀ i, (c i : EReal) ≤ f (t i))
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) :
    ((∑ i, w i * c i : ℝ) : EReal) ≤ f (∑ i, w i * t i) := by
  classical
  have hp : ∀ i ∈ (Finset.univ : Finset ι),
      (t i, -c i) ∈ SGPT.Convex.epigraph (fun r => -f r) := by
    intro i _
    change -f (t i) ≤ ((-c i : ℝ) : EReal)
    simpa only [EReal.coe_neg] using EReal.neg_le_neg_iff.mpr (hc i)
  have hmem := hf.sum_mem (t := Finset.univ) (w := w)
    (z := fun i => (t i, -c i)) (fun i _ => hw i) hwsum hp
  have heq : (∑ i, w i • (t i, -c i)) =
      (∑ i, w i * t i, -(∑ i, w i * c i)) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, mul_neg, Finset.sum_neg_distrib]
  rw [heq] at hmem
  change -f (∑ i, w i * t i) ≤ ((-(∑ i, w i * c i) : ℝ) : EReal) at hmem
  rw [EReal.coe_neg] at hmem
  exact EReal.neg_le_neg_iff.mp hmem

/-- A constant original left-tail lower bound upgrades the exact-barycentre
finite Jensen inequality to every smaller original parameter. The majorant
may take either infinite value elsewhere. -/
theorem finite_realHeight_le_of_leftTail {ι : Type*} [Fintype ι]
    (t c w : ι → ℝ) (f : ℝ → EReal)
    (hf : SGPT.Convex.IsConvex (fun r => -f r))
    (hc : ∀ i, (c i : EReal) ≤ f (t i))
    (T cTail : ℝ) (hTail : ∀ L : ℝ, L ≤ T → (cTail : EReal) ≤ f L)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (s : ℝ) (hs : s ≤ ∑ i, w i * t i) :
    ((∑ i, w i * c i : ℝ) : EReal) ≤ f s := by
  let b : ℝ := ∑ i, w i * t i
  let d : ℝ := ∑ i, w i * c i
  have hb : (d : EReal) ≤ f b := finite_realHeight_jensen t c w f hf hc hw hwsum
  by_cases heq : s = b
  · simpa only [heq] using hb
  have hsb : s < b := lt_of_le_of_ne hs heq
  let q : ℝ → ℝ := fun L => (b - s) / (b - L)
  have hden : Tendsto (fun L : ℝ => b - L) atBot atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_left atBot b tendsto_neg_atBot_atTop)
  have hq : Tendsto q atBot (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hcand : Tendsto (fun L : ℝ => (1 - q L) * d + q L * cTail) atBot (𝓝 d) := by
    convert ((tendsto_const_nhds.sub hq).mul_const d).add (hq.mul_const cTail) using 1
    simp
  have hcandE : Tendsto (fun L : ℝ => (((1 - q L) * d + q L * cTail : ℝ) : EReal))
      atBot (𝓝 (d : EReal)) := continuous_coe_real_ereal.continuousAt.tendsto.comp hcand
  apply le_of_tendsto hcandE
  filter_upwards [eventually_lt_atBot s, eventually_le_atBot T] with L hLs hLT
  have hpos : 0 < b - L := by linarith
  have hq0 : 0 ≤ q L := div_nonneg (by linarith) hpos.le
  have hq1 : q L ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have htime : (1 - q L) * b + q L * L = s := by
    dsimp only [q]
    field_simp [ne_of_gt hpos]
    ring
  have hp : (b, -d) ∈ SGPT.Convex.epigraph (fun r => -f r) := by
    change -f b ≤ ((-d : ℝ) : EReal)
    simpa only [EReal.coe_neg] using EReal.neg_le_neg_iff.mpr hb
  have hL : (L, -cTail) ∈ SGPT.Convex.epigraph (fun r => -f r) := by
    change -f L ≤ ((-cTail : ℝ) : EReal)
    simpa only [EReal.coe_neg] using EReal.neg_le_neg_iff.mpr (hTail L hLT)
  have hmix := hf hp hL (sub_nonneg.mpr hq1) hq0 (by ring : (1 - q L) + q L = 1)
  change -f ((1 - q L) * b + q L * L) ≤
    (((1 - q L) * -d + q L * -cTail : ℝ) : EReal) at hmix
  rw [htime] at hmix
  have hheight : (1 - q L) * -d + q L * -cTail = -((1 - q L) * d + q L * cTail) := by ring
  rw [hheight, EReal.coe_neg] at hmix
  exact EReal.neg_le_neg_iff.mp hmix
end SGPT.NAPotential.Berkovich.HullAnalytic
