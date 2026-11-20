import SGPT.NAPotential.FiniteNodeSimplex
import SGPT.Convex.Epigraph

/-!
Concavity of the actual finite-node feasible-simplex supremum in the revised
SGPT Remark 13.4.1 (source commit 69360cfd). Zero coefficients and negative-
infinite node values are retained in the original EReal expressions. The
proof uses actual mixed feasible weights and strict real-height approximation;
it assumes neither attainment nor equality with spatial regularization.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A convex mixture of actual node-weight vectors. -/
def mixedWeights {N : ℕ} (a b : ℝ) (w v : Fin (N + 1) → ℝ) :
    Fin (N + 1) → ℝ := fun i => a * w i + b * v i

/-- Feasibility is preserved by the same convex combination of parameter and weights. -/
theorem mixedWeights_mem (D : PiecewiseLinearData θ) {s t a b : ℝ}
    {w v : Fin (D.N + 1) → ℝ}
    (hw : w ∈ feasibleWeights D s) (hv : v ∈ feasibleWeights D t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    mixedWeights a b w v ∈ feasibleWeights D (a * s + b * t) := by
  constructor
  · intro i
    constructor
    · exact add_nonneg (mul_nonneg ha (hw.1 i).1) (mul_nonneg hb (hv.1 i).1)
    · change a * w i + b * v i ≤ 1
      have h := add_le_add (mul_le_mul_of_nonneg_left (hw.1 i).2 ha)
        (mul_le_mul_of_nonneg_left (hv.1 i).2 hb)
      simpa only [mul_one, hab] using h
  constructor
  · simp only [mixedWeights, Finset.sum_add_distrib, ← Finset.mul_sum, hw.2.1, hv.2.1,
      mul_one, hab]
  · calc
      a * s + b * t ≤ a * (∑ i, w i * D.τ i) + b * (∑ i, v i * D.τ i) :=
        add_le_add (mul_le_mul_of_nonneg_left hw.2.2 ha)
          (mul_le_mul_of_nonneg_left hv.2.2 hb)
      _ = ∑ i, mixedWeights a b w v i * D.τ i := by
        simp only [mixedWeights, add_mul, mul_assoc, Finset.sum_add_distrib,
          Finset.mul_sum]

private theorem coe_mul_finset_sum {ι : Type*} (S : Finset ι) (g : ι → EReal)
    {a : ℝ} (ha : 0 ≤ a) :
    (a : EReal) * (∑ i ∈ S, g i) = ∑ i ∈ S, (a : EReal) * g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ha)
        (EReal.coe_ne_top a), ih]

/-- The weighted-value identity for actual mixed weights, including polar nodes. -/
theorem weightedValue_mixedWeights (D : PiecewiseLinearData θ) (x : M)
    (a b : ℝ) (w v : Fin (D.N + 1) → ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    weightedValue D (mixedWeights a b w v) x =
      (a : EReal) * weightedValue D w x + (b : EReal) * weightedValue D v x := by
  unfold weightedValue mixedWeights
  rw [coe_mul_finset_sum Finset.univ _ ha, coe_mul_finset_sum Finset.univ _ hb,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [EReal.coe_add, EReal.right_distrib_of_nonneg
    (EReal.coe_nonneg.mpr (mul_nonneg ha (hw i)))
    (EReal.coe_nonneg.mpr (mul_nonneg hb (hv i))), EReal.coe_mul, EReal.coe_mul,
    mul_assoc, mul_assoc]

/-- The supremum expression in revised `rmk:pwlinhull` is genuinely concave,
with the original real-height epigraph convention and every polar value. -/
theorem simplexValue_concave (D : PiecewiseLinearData θ) (x : M) :
    SGPT.Convex.IsConvex (fun s : ℝ => -simplexValue D s x) := by
  apply SGPT.Convex.isConvex_iff_strict_combo.mpr
  intro s t r q a b hs ht ha hb hab
  have hs' : ((-r : ℝ) : EReal) < simplexValue D s x := by
    simpa only [EReal.coe_neg, neg_neg] using EReal.neg_lt_neg_iff.mpr hs
  have ht' : ((-q : ℝ) : EReal) < simplexValue D t x := by
    simpa only [EReal.coe_neg, neg_neg] using EReal.neg_lt_neg_iff.mpr ht
  obtain ⟨w, hw⟩ := lt_iSup_iff.mp hs'
  obtain ⟨hws, hwval⟩ := lt_iSup_iff.mp hw
  obtain ⟨v, hv⟩ := lt_iSup_iff.mp ht'
  obtain ⟨hvt, hvval⟩ := lt_iSup_iff.mp hv
  obtain ⟨r', hrlo, hrhi⟩ := EReal.exists_between_coe_real hwval
  obtain ⟨q', hqlo, hqhi⟩ := EReal.exists_between_coe_real hvval
  have hr : -r < r' := EReal.coe_lt_coe_iff.mp hrlo
  have hq : -q < q' := EReal.coe_lt_coe_iff.mp hqlo
  have hreal : a * (-r) + b * (-q) < a * r' + b * q' :=
    add_lt_add (mul_lt_mul_of_pos_left hr ha) (mul_lt_mul_of_pos_left hq hb)
  have hwm := mixedWeights_mem D hws hvt ha.le hb.le hab
  have hvalue : ((a * r' + b * q' : ℝ) : EReal) ≤
      weightedValue D (mixedWeights a b w v) x := by
    rw [weightedValue_mixedWeights D x a b w v ha.le hb.le
      (fun i => (hws.1 i).1) (fun i => (hvt.1 i).1), EReal.coe_add,
      EReal.coe_mul, EReal.coe_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hrhi.le (EReal.coe_nonneg.mpr ha.le))
      (mul_le_mul_of_nonneg_left hqhi.le (EReal.coe_nonneg.mpr hb.le))
  have hsup : weightedValue D (mixedWeights a b w v) x ≤
      simplexValue D (a * s + b * t) x :=
    le_iSup_of_le (mixedWeights a b w v) (le_iSup_of_le hwm le_rfl)
  have hstrict : ((a * (-r) + b * (-q) : ℝ) : EReal) <
      simplexValue D (a * s + b * t) x :=
    (EReal.coe_lt_coe hreal).trans_le (hvalue.trans hsup)
  have hneg := EReal.neg_lt_neg_iff.mpr hstrict
  have heq : -(a * (-r) + b * (-q)) = a * r + b * q := by ring
  simpa only [smul_eq_mul, ← EReal.coe_neg, heq] using hneg

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
