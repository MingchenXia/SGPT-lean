import SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
import SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-!
# The affine obstacle of Xia's Theorem 2.4.5: order, measurability, quasi-continuity

In the proof of Xia's Theorem 2.4.5 (`xia-sgpt:page-0083`, (2.30)) Theorem 2.4.4 is applied to
the affine obstacle `eta = a phi + (1-a) psi` with `a > 1` and `phi <= psi`.  The obstacle is not
upper semicontinuous (the coefficient `1 - a` is negative), so the upper semicontinuous form of
Xia's Step 1.2 (`Pending.RooftopTruncationConcentration`) does not apply to it.  What the measurable
form (`Pending.RooftopTruncationConcentrationMeasurable`) asks of the obstacle is proved here:

* `convexComb_le_left`: `eta <= phi` (pointwise, `EReal`, poles included);
* `measurable_convexComb`: `eta` is measurable;
* `refTruncationsQuasiContinuous_convexComb`: **every reference truncation
  `eta \/ (V_theta - C)` is quasi-continuous for `Cap_theta`** on compact subsets of open sets
  where `V_theta` is bounded.

The quasi-continuity rests on one identity: with `phi' = phi \/ (V_theta - C)` and
`psi' = psi \/ (V_theta - C)`,

  `eta \/ (V_theta - C) = (a phi' + (1-a) psi') \/ (V_theta - C)`,

because where `phi < V_theta - C` both sides equal `V_theta - C` (`eta <= phi`, and
`a (V_theta - C) + (1-a) psi' <= V_theta - C` as `psi' >= V_theta - C` and `1 - a < 0`).  The
three functions `phi'`, `psi'`, `V_theta` are `theta`-PSH potentials bounded wherever
`V_theta` is, so Xia's Theorem 2.3.2 in its local form
(`Pending.ThetaCapacityLocalQuasiContinuity`) applies to each of them.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopAffineObstacleQuasiContinuity

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
open SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

/-! ### Pointwise facts -/

/-- **The truncation identity, in real numbers.**  For `a >= 1` and `x <= y`, truncating the
affine combination at `t` is the same as truncating it after truncating both entries at `t`. -/
theorem max_affine_eq_max_affine_max {a x y t : ℝ} (ha : 1 ≤ a) (hxy : x ≤ y) :
    max (a * x + (1 - a) * y) t = max (a * max x t + (1 - a) * max y t) t := by
  rcases le_total t x with h | h
  · rw [max_eq_left h, max_eq_left (h.trans hxy)]
  · have h1 : a * x + (1 - a) * y ≤ t := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hxy)]
    have h2 : a * max x t + (1 - a) * max y t ≤ t := by
      rw [max_eq_right h]
      nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 (le_max_right y t))]
    rw [max_eq_right h1, max_eq_right h2]

/-- **The affine obstacle lies below its first entry**: for `a > 1`, `x <= y < top`,
`a x + (1-a) y <= x` in `EReal` (a pole of `x` is a pole of the combination). -/
theorem coe_mul_add_coe_mul_le {a : ℝ} (ha : 1 < a) {x y : EReal} (hxy : x ≤ y)
    (hy : y ≠ ⊤) : (a : EReal) * x + ((1 - a : ℝ) : EReal) * y ≤ x := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (by linarith), EReal.bot_add]
  | top => exact absurd (top_le_iff.mp hxy) hy
  | coe r =>
    have hyb : y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot r) hxy
    obtain ⟨s, rfl⟩ : ∃ s : ℝ, y = (s : EReal) := ⟨y.toReal, (EReal.coe_toReal hy hyb).symm⟩
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hrs : r ≤ s := EReal.coe_le_coe_iff.mp hxy
    nlinarith [mul_nonneg (sub_nonneg.2 ha.le) (sub_nonneg.2 hrs)]

/-- **The truncation identity, in `EReal`, read in real numbers.**  If `x <= y <= 0` and the
truncation level `s` is real, the real value of `(a x + (1-a) y) \/ s` is the truncation at `s`
of the affine combination of the real values of `x \/ s` and `y \/ s`. -/
theorem toReal_max_coe_mul_add_coe_mul {a : ℝ} (ha : 1 < a) {x y : EReal} (hxy : x ≤ y)
    (hy0 : y ≤ 0) (s : ℝ) :
    (max ((a : EReal) * x + ((1 - a : ℝ) : EReal) * y) (s : EReal)).toReal =
      max (a * (max x (s : EReal)).toReal + (1 - a) * (max y (s : EReal)).toReal) s := by
  have hy : y ≠ ⊤ := ne_top_of_le_ne_top (by simp) hy0
  induction x using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos (by linarith), EReal.bot_add, max_eq_right bot_le,
      EReal.toReal_coe]
    have hys : max y (s : EReal) ≠ ⊤ := max_ne_top hy (EReal.coe_ne_top s)
    have hysb : max y (s : EReal) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot s) (le_max_right _ _)
    have hq : s ≤ (max y (s : EReal)).toReal := by
      have h := EReal.coe_le_coe_iff.mp ((le_max_right y (s : EReal)).trans_eq
        (EReal.coe_toReal hys hysb).symm)
      exact h
    have hle : a * s + (1 - a) * (max y (s : EReal)).toReal ≤ s := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha.le) (sub_nonneg.2 hq)]
    exact (max_eq_right hle).symm
  | top => exact absurd (top_le_iff.mp hxy) hy
  | coe r =>
    have hyb : y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot r) hxy
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, y = (t : EReal) := ⟨y.toReal, (EReal.coe_toReal hy hyb).symm⟩
    have hrt : r ≤ t := EReal.coe_le_coe_iff.mp hxy
    have hcm : ∀ u v : ℝ, max (u : EReal) (v : EReal) = ((max u v : ℝ) : EReal) :=
      fun u v => (EReal.coe_strictMono.monotone.map_max).symm
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hcm, hcm, hcm, EReal.toReal_coe,
      EReal.toReal_coe, EReal.toReal_coe]
    exact max_affine_eq_max_affine_max ha.le hrt

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- **`eta <= phi`** for the affine obstacle `eta = a phi + (1-a) psi`, `a > 1`, `phi <= psi`. -/
theorem convexComb_le_left {a : ℝ} (ha : 1 < a) {phi psi : M → EReal}
    (hle : ∀ x, phi x ≤ psi x) (hpsi : ∀ x, psi x ≠ ⊤) (x : M) :
    convexComb a phi psi x ≤ phi x :=
  coe_mul_add_coe_mul_le ha (hle x) (hpsi x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The affine obstacle of two measurable functions is measurable. -/
theorem measurable_convexComb [MeasurableSpace M] {phi psi : M → EReal}
    (hphi : Measurable phi) (hpsi : Measurable psi) (a : ℝ) :
    Measurable (convexComb a phi psi) :=
  (measurable_const.mul hphi).add (measurable_const.mul hpsi)

/-! ### Quasi-continuity of the reference truncations -/

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Every reference truncation of the affine obstacle is quasi-continuous for
`Cap_theta`.**  For `theta`-PSH potentials `phi <= psi <= 0` and `a > 1`, the obstacle
`a phi + (1-a) psi` satisfies `RefTruncationsQuasiContinuous`, the obstacle hypothesis of Xia's
Step 1.2 (`Pending.RooftopTruncationConcentrationMeasurable`). -/
theorem refTruncationsQuasiContinuous_convexComb {theta : ClosedRealOneOneForm n M}
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hle : ∀ x, phi x ≤ psi x) (hpsi0 : ∀ x, psi x ≤ 0) {a : ℝ} (ha : 1 < a) :
    RefTruncationsQuasiContinuous theta (convexComb a phi psi) := by
  intro C hC Omega hOmega hVb K hK hKO eps heps
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  have hphi0 : ∀ x, phi x ≤ 0 := fun x => (hle x).trans (hpsi0 x)
  have hp' : IsThetaPshPotential theta.val
      (fun x => max (phi x) (V x + ((-C : ℝ) : EReal))) :=
    IsThetaPshPotential.max hphi (hV.add_const (-C))
  have hq' : IsThetaPshPotential theta.val
      (fun x => max (psi x) (V x + ((-C : ℝ) : EReal))) :=
    IsThetaPshPotential.max hpsi (hV.add_const (-C))
  have hpb := isBoundedPotentialOn_max_reference hphi0 hC hVb
  have hqb := isBoundedPotentialOn_max_reference hpsi0 hC hVb
  have heps4 : (0 : ℝ) < eps / 4 := by positivity
  obtain ⟨G1, hG1o, hG1c, hG1cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hp' hOmega hpb hVb hK hKO heps4
  obtain ⟨G2, hG2o, hG2c, hG2cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hq' hOmega hqb hVb hK hKO heps4
  obtain ⟨G3, hG3o, hG3c, hG3cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hV hOmega hVb hVb hK hKO heps4
  refine ⟨G1 ∪ G2 ∪ G3, (hG1o.union hG2o).union hG3o, ?_, ?_⟩
  · have hsum : thetaCapacity theta V (G1 ∪ G2 ∪ G3) ≤
        ENNReal.ofReal (eps / 4) + ENNReal.ofReal (eps / 4) + ENNReal.ofReal (eps / 4) :=
      (thetaCapacity_union_le theta V (G1 ∪ G2) G3).trans
        (add_le_add ((thetaCapacity_union_le theta V G1 G2).trans
          (add_le_add hG1c.le hG2c.le)) hG3c.le)
    refine lt_of_le_of_lt hsum ?_
    rw [← ENNReal.ofReal_add heps4.le heps4.le,
      ← ENNReal.ofReal_add (by positivity) heps4.le]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith)
  · have hc1 : ContinuousOn (fun y => (max (phi y) (V y + ((-C : ℝ) : EReal))).toReal)
        (K \ (G1 ∪ G2 ∪ G3)) :=
      hG1cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inl (Or.inl h))⟩
    have hc2 : ContinuousOn (fun y => (max (psi y) (V y + ((-C : ℝ) : EReal))).toReal)
        (K \ (G1 ∪ G2 ∪ G3)) :=
      hG2cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inl (Or.inr h))⟩
    have hc3 : ContinuousOn (fun y => (V y).toReal) (K \ (G1 ∪ G2 ∪ G3)) :=
      hG3cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
    have hcont : ContinuousOn (fun y =>
        max (a * (max (phi y) (V y + ((-C : ℝ) : EReal))).toReal +
          (1 - a) * (max (psi y) (V y + ((-C : ℝ) : EReal))).toReal) ((V y).toReal - C))
        (K \ (G1 ∪ G2 ∪ G3)) :=
      ContinuousOn.sup ((continuousOn_const.mul hc1).add (continuousOn_const.mul hc2))
        (hc3.sub continuousOn_const)
    refine hcont.congr fun y hy => ?_
    obtain ⟨cV, dV, hVbd⟩ := hVb
    have hyO : y ∈ Omega := hKO hy.1
    have hVbot : V y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot cV) (hVbd y hyO).1
    have hVtop : V y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top dV) (hVbd y hyO).2
    have hVs : V y + ((-C : ℝ) : EReal) = (((V y).toReal - C : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hVtop hVbot, ← EReal.coe_add, EReal.toReal_coe, sub_eq_add_neg]
    show (refTrunc theta (convexComb a phi psi) C y).toReal = _
    simp only [refTrunc, convexComb_apply, ← hVdef, hVs]
    exact toReal_max_coe_mul_add_coe_mul ha (hle y) (hpsi0 y) _

end

end SGPT.Foundations.Analysis.Pending.RooftopAffineObstacleQuasiContinuity
