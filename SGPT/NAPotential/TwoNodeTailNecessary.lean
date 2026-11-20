import SGPT.NAPotential.TwoNodeTailSharp

/-!
The tail-pole condition is necessary and sufficient for the normalized
two-node max-tail curve to equal the literal pointwise upper envelope.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.TwoNodeRepair

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.Berkovich

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A finite spike at parameter zero, bottom at all other parameters. -/
def finiteSpike (a s : ℝ) : EReal := if s = 0 then (a : EReal) else ⊥

/-- The negative of a finite spike has an actual real-height half-strip
above the singleton parameter. -/
theorem epigraph_neg_finiteSpike (a : ℝ) :
    SGPT.Convex.epigraph (fun s => -finiteSpike a s) =
      {p : ℝ × ℝ | p.1 = 0 ∧ -a ≤ p.2} := by
  ext p
  by_cases hp : p.1 = 0
  · simp only [SGPT.Convex.epigraph, finiteSpike, hp, if_true,
      ← EReal.coe_neg, EReal.coe_le_coe_iff, Set.mem_ofPred_eq, true_and]
  · simp only [SGPT.Convex.epigraph, finiteSpike, hp, if_false, EReal.neg_bot,
      not_le.mpr (EReal.coe_lt_top p.2), Set.mem_ofPred_eq, false_and]

/-- The source epigraph convention permits a downward jump at the sole finite
parameter; no closedness is assumed or needed. -/
theorem isConvex_neg_finiteSpike (a : ℝ) :
    SGPT.Convex.IsConvex (fun s => -finiteSpike a s) := by
  rw [SGPT.Convex.IsConvex, epigraph_neg_finiteSpike]
  intro p hp q hq α β hα hβ hsum
  rcases hp with ⟨hp₀, hp₁⟩
  rcases hq with ⟨hq₀, hq₁⟩
  constructor
  · change α * p.1 + β * q.1 = 0
    rw [hp₀, hq₀]
    ring
  · change -a ≤ α * p.2 + β * q.2
    have h := add_le_add (mul_le_mul_of_nonneg_left hp₁ hα)
      (mul_le_mul_of_nonneg_left hq₁ hβ)
    have he : α * (-a) + β * (-a) = -a := by rw [← add_mul, hsum, one_mul]
    rwa [he] at h

/-- A last-node pole with finite first-node value gives a finite spike for
the actual original two-node source curve. -/
theorem twoNode_profile_bot_last (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (x : M) (a : ℝ)
    (ha : u x = (a : EReal)) (hb : v x = ⊥) (s : ℝ) :
    (twoNodeData u v hu hv).curve s x = finiteSpike a s := by
  let D := twoNodeData u v hu hv
  by_cases hz : s = 0
  · subst s
    have h := D.curve_tau 0
    change D.curve 0 = u at h
    rw [h, ha]
    simp only [finiteSpike, if_true]
  by_cases hp : 0 < s
  · have h := D.curve_of_lt (show D.τ 0 < s from hp)
    rw [h]
    simp only [finiteSpike, hz, if_false]
  by_cases ht : s ≤ -1
  · have h := D.curve_of_le_last (s := s) (show s ≤ D.τ (Fin.last D.N) from ht)
    change D.curve s = v at h
    rw [h, hb]
    simp only [finiteSpike, hz, if_false]
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
  rw [hb, EReal.coe_mul_bot_of_pos ht0, EReal.add_bot]
  simp only [finiteSpike, hz, if_false]

/-- A mismatched tail pole forces failure of literal equality at parameter −1. -/
theorem corrected_ne_literal_envelope_of_tail_pole_mismatch (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (x : M)
    (huFinite : u x ≠ ⊥) (hvBot : v x = ⊥) :
    (correctedData u v hu hv).curve (-1) x ≠
      (twoNodeData u v hu hv).pointwiseUpperConcaveEnvelope (-1) x := by
  have htop : u x ≠ ⊤ := hu.1 x
  let a := (u x).toReal
  have ha : u x = (a : EReal) := (EReal.coe_toReal htop huFinite).symm
  have hprofile : (fun t => -(twoNodeData u v hu hv).curve t x) =
      fun t => -finiteSpike a t := by
    funext t
    rw [twoNode_profile_bot_last u v hu hv x a ha hvBot t]
  have hraw : (twoNodeData u v hu hv).pointwiseUpperConcaveEnvelope (-1) x = ⊥ := by
    change -SGPT.Convex.lowerConvexEnvelope
      (fun t => -(twoNodeData u v hu hv).curve t x) (-1) = ⊥
    rw [hprofile, SGPT.Convex.lowerConvexEnvelope_eq_self (isConvex_neg_finiteSpike a)]
    norm_num [finiteSpike]
  have hcorrect : (correctedData u v hu hv).curve (-1) x = u x := by
    rw [corrected_curve_tail u v hu hv (s := -1) (by norm_num), hvBot, max_eq_left bot_le]
  rw [hcorrect, hraw]
  exact huFinite

/-- The two-node pole condition is necessary and sufficient for the proposed
max-tail source curve to equal the true literal hull at all parameters. -/
theorem corrected_curve_eq_literal_envelope_iff_tail_poles (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    (∀ s x, (correctedData u v hu hv).curve s x =
      (twoNodeData u v hu hv).pointwiseUpperConcaveEnvelope s x) ↔
      (∀ x, v x = ⊥ → u x = ⊥) := by
  constructor
  · intro heq x hvBot
    by_contra huFinite
    exact corrected_ne_literal_envelope_of_tail_pole_mismatch u v hu hv x huFinite hvBot
      (heq (-1) x)
  · intro hpoles s x
    exact corrected_curve_eq_literal_envelope_of_tail_poles u v hu hv hpoles s x

end SGPT.NAPotential.TwoNodeRepair
