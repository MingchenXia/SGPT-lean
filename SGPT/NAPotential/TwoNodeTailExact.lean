import SGPT.NAPotential.TwoNodeScalarHull

/-!
The source two-node max-tail repair. No output certificate is assumed: the
statement concerns the literal negative-LCE of the original source curve and
the actual curve of the max-tail replacement. The added hypothesis is that the
last node is finite at every point; the first node may have minus-infinity poles.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.TwoNodeRepair

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.Berkovich

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- At two finite node values, the original source curve has its exact scalar
profile, including both endpoints and both tails. -/
theorem twoNode_profile_real (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (x : M) (a b : ℝ)
    (ha : u x = (a : EReal)) (hb : v x = (b : EReal)) (s : ℝ) :
    (twoNodeData u v hu hv).curve s x = realTwoNodeInput a b s := by
  let D := twoNodeData u v hu hv
  by_cases hp : 0 < s
  · have h := D.curve_of_lt (show D.τ 0 < s from hp)
    rw [h]
    simp only [realTwoNodeInput, hp, if_true]
  by_cases ht : s ≤ -1
  · have h := D.curve_of_le_last (s := s) (show s ≤ D.τ (Fin.last D.N) from ht)
    change D.curve s = v at h
    rw [h, hb]
    simp only [realTwoNodeInput, hp, if_false, ht, if_true]
  by_cases hz : s = 0
  · subst s
    have h := D.curve_tau 0
    change D.curve 0 = u at h
    rw [h, ha]
    norm_num [realTwoNodeInput]
  have hsneg : s < 0 := lt_of_le_of_ne (not_lt.mp hp) hz
  have ht0 : 0 < -s := neg_pos.mpr hsneg
  have ht1 : -s < 1 := by linarith
  have h := D.curve_affine 0 (by change (0 : ℕ) < 1; decide) ht0 ht1
  change D.curve ((1 - -s) * 0 + -s * -1) =
    PiecewiseLinearData.affineComb (-s) u v at h
  have he : (1 - -s) * 0 + -s * -1 = s := by ring
  rw [he] at h
  rw [h]
  change (((1 - -s : ℝ) : EReal) * u x + ((-s : ℝ) : EReal) * v x) = _
  rw [ha, hb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  simp only [realTwoNodeInput, hp, if_false, ht]
  congr 1
  ring

/-- At a minus-infinity first node and finite last node, the entire source
trace is finite exactly on its left tail. -/
theorem twoNode_profile_bot_first (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (x : M) (b : ℝ)
    (ha : u x = ⊥) (hb : v x = (b : EReal)) (s : ℝ) :
    (twoNodeData u v hu hv).curve s x = botFirstTailHull b s := by
  let D := twoNodeData u v hu hv
  by_cases ht : s ≤ -1
  · have h := D.curve_of_le_last (s := s) (show s ≤ D.τ (Fin.last D.N) from ht)
    change D.curve s = v at h
    rw [h, hb]
    simp only [botFirstTailHull, ht, if_true]
  by_cases hp : 0 < s
  · have h := D.curve_of_lt (show D.τ 0 < s from hp)
    rw [h]
    simp only [botFirstTailHull, ht, if_false]
  by_cases hz : s = 0
  · subst s
    have h := D.curve_tau 0
    change D.curve 0 = u at h
    rw [h, ha]
    norm_num [botFirstTailHull]
  have hsneg : s < 0 := lt_of_le_of_ne (not_lt.mp hp) hz
  have ht0 : 0 < -s := neg_pos.mpr hsneg
  have ht1 : -s < 1 := by linarith
  have hcoeff : 0 < 1 - -s := by linarith
  have h := D.curve_affine 0 (by change (0 : ℕ) < 1; decide) ht0 ht1
  change D.curve ((1 - -s) * 0 + -s * -1) =
    PiecewiseLinearData.affineComb (-s) u v at h
  have he : (1 - -s) * 0 + -s * -1 = s := by ring
  rw [he] at h
  rw [h]
  change (((1 - -s : ℝ) : EReal) * u x + ((-s : ℝ) : EReal) * v x) = _
  rw [ha, EReal.coe_mul_bot_of_pos hcoeff, EReal.bot_add]
  simp only [botFirstTailHull, ht, if_false]

/-- Restricted exact repair: for a pointwise finite last source node, the
actual repaired source curve equals the literal pointwise upper concave
LCE envelope. No positive-dimensional or compactness assumption is added. -/
theorem corrected_curve_eq_literal_envelope (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hvfinite : ∀ x, v x ≠ ⊥) (s : ℝ) (x : M) :
    (correctedData u v hu hv).curve s x =
      (twoNodeData u v hu hv).pointwiseUpperConcaveEnvelope s x := by
  have hvt : v x ≠ ⊤ := hv.1 x
  have hb : v x = ((v x).toReal : EReal) := (EReal.coe_toReal hvt (hvfinite x)).symm
  by_cases huBot : u x = ⊥
  · have hmax : max (u x) (v x) = v x := by rw [huBot, max_eq_right bot_le]
    have ho : (fun t => (twoNodeData u v hu hv).curve t x) =
        botFirstTailHull ((v x).toReal) := by
      funext t
      exact twoNode_profile_bot_first u v hu hv x ((v x).toReal) huBot hb t
    have hc : (correctedData u v hu hv).curve s x = botFirstTailHull ((v x).toReal) s := by
      exact twoNode_profile_bot_first u (fun y => max (u y) (v y)) hu (hu.max hv)
        x ((v x).toReal) huBot (hmax.trans hb) s
    rw [hc]
    change botFirstTailHull ((v x).toReal) s =
      -SGPT.Convex.lowerConvexEnvelope (fun t => -(twoNodeData u v hu hv).curve t x) s
    have hneg : (fun t => -(twoNodeData u v hu hv).curve t x) =
        fun t => -botFirstTailHull ((v x).toReal) t := by
      funext t
      rw [congrFun ho t]
    rw [hneg]
    exact (literal_botFirst_envelope_eq_tail_repair ((v x).toReal) s).symm
  · have hut : u x ≠ ⊤ := hu.1 x
    have ha : u x = ((u x).toReal : EReal) := (EReal.coe_toReal hut huBot).symm
    let a : ℝ := (u x).toReal
    let b : ℝ := (v x).toReal
    have hmax : max (u x) (v x) = ((max a b : ℝ) : EReal) := by
      rw [ha, hb]
      rcases le_total a b with h | h
      · rw [max_eq_right (EReal.coe_le_coe h), max_eq_right h]
      · rw [max_eq_left (EReal.coe_le_coe h), max_eq_left h]
    have ho : (fun t => (twoNodeData u v hu hv).curve t x) = realTwoNodeInput a b := by
      funext t
      exact twoNode_profile_real u v hu hv x a b ha hb t
    have hc : (correctedData u v hu hv).curve s x = realTailHull a b s := by
      have h := twoNode_profile_real u (fun y => max (u y) (v y)) hu (hu.max hv)
        x a (max a b) ha hmax s
      exact h
    rw [hc]
    change realTailHull a b s =
      -SGPT.Convex.lowerConvexEnvelope (fun t => -(twoNodeData u v hu hv).curve t x) s
    have hneg : (fun t => -(twoNodeData u v hu hv).curve t x) =
        fun t => -realTwoNodeInput a b t := by
      funext t
      rw [congrFun ho t]
    rw [hneg]
    exact (literal_real_envelope_eq_tail_repair a b s).symm

end SGPT.NAPotential.TwoNodeRepair
