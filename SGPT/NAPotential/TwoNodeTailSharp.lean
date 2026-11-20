import SGPT.NAPotential.TwoNodeTailExact

/-!
Exact literal two-node envelope equality under the pointwise tail-pole
condition. The original source curve and literal pointwise LCE are retained.
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

/-- The genuine source curve is bottom when both nodes are bottom at x. -/
theorem twoNode_profile_both_bot (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (x : M)
    (ha : u x = ⊥) (hb : v x = ⊥) (s : ℝ) :
    (twoNodeData u v hu hv).curve s x = ⊥ := by
  let D := twoNodeData u v hu hv
  by_cases ht : s ≤ -1
  · have h := D.curve_of_le_last (s := s) (show s ≤ D.τ (Fin.last D.N) from ht)
    change D.curve s = v at h
    rw [h, hb]
  by_cases hp : 0 < s
  · have h := D.curve_of_lt (show D.τ 0 < s from hp)
    rw [h]
  by_cases hz : s = 0
  · subst s
    have h := D.curve_tau 0
    change D.curve 0 = u at h
    rw [h, ha]
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
  change (((1 - -s : ℝ) : EReal) * u x + ((-s : ℝ) : EReal) * v x) = ⊥
  rw [ha, EReal.coe_mul_bot_of_pos hcoeff, EReal.bot_add]

theorem corrected_curve_eq_literal_envelope_at (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (s : ℝ) (x : M) (hvfinite : v x ≠ ⊥) :
    (correctedData u v hu hv).curve s x =
      (twoNodeData u v hu hv).pointwiseUpperConcaveEnvelope s x := by
  have hvt : v x ≠ ⊤ := hv.1 x
  have hb : v x = ((v x).toReal : EReal) := (EReal.coe_toReal hvt hvfinite).symm
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

/-- Sharp pole condition: the literal max-tail identity remains valid when
the last node is bottom only where the first node is also bottom. -/
theorem corrected_curve_eq_literal_envelope_of_tail_poles (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hpoles : ∀ x, v x = ⊥ → u x = ⊥) (s : ℝ) (x : M) :
    (correctedData u v hu hv).curve s x =
      (twoNodeData u v hu hv).pointwiseUpperConcaveEnvelope s x := by
  by_cases hvbot : v x = ⊥
  · have hubot : u x = ⊥ := hpoles x hvbot
    have hmax : max (u x) (v x) = ⊥ := by rw [hubot, hvbot, max_self]
    have hc : (correctedData u v hu hv).curve s x = ⊥ :=
      twoNode_profile_both_bot u (fun y => max (u y) (v y)) hu (hu.max hv)
        x hubot hmax s
    have horig : (fun t => -(twoNodeData u v hu hv).curve t x) =
        (fun _ : ℝ => (⊤ : EReal)) := by
      funext t
      rw [twoNode_profile_both_bot u v hu hv x hubot hvbot t, EReal.neg_bot]
    rw [hc]
    change ⊥ = -SGPT.Convex.lowerConvexEnvelope
      (fun t => -(twoNodeData u v hu hv).curve t x) s
    rw [horig, SGPT.Convex.lowerConvexEnvelope_eq_self SGPT.Convex.isConvex_top]
    exact EReal.neg_top.symm
  · exact corrected_curve_eq_literal_envelope_at u v hu hv s x hvbot

end SGPT.NAPotential.TwoNodeRepair
