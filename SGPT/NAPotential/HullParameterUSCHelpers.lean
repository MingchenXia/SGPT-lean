import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-! Generic parameter-USC producers for the opening clause of rmk:pwlinhull.
The actual original-D closed-interval reconstruction is owned by the LP lane.
Polar nodal spikes are retained; ordinary continuity is never asserted. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.HullParameterUSC
open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- A genuine nonnegative real scalar times a fixed non-top EReal stays non-top. -/
theorem coe_mul_fixed_ne_top {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊤) :
    (c : EReal) * a ≠ ⊤ :=
  (EReal.mul_ne_top _ _).mpr
    ⟨Or.inl (EReal.coe_ne_bot c), Or.inl (EReal.coe_nonneg.mpr hc),
      Or.inl (EReal.coe_ne_top c), Or.inr ha⟩

/-- Parameter USC includes the real zero-coefficient spike at a fixed pole. -/
theorem upperSemicontinuous_coe_mul_fixed {g : X → ℝ}
    (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x) {a : EReal} (ha : a ≠ ⊤) :
    UpperSemicontinuous (fun x => (g x : EReal) * a) := by
  by_cases hbot : a = ⊥
  · subst a
    intro x b hb
    by_cases hx : g x = 0
    · have hb0 : (0 : EReal) < b := by simpa only [hx, EReal.coe_zero, zero_mul] using hb
      exact Eventually.of_forall fun y =>
        (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (h0 y)) bot_le).trans_lt hb0
    · have hxpos : 0 < g x := lt_of_le_of_ne (h0 x) (Ne.symm hx)
      have hb' : (⊥ : EReal) < b := by
        simpa only [EReal.coe_mul_bot_of_pos hxpos] using hb
      filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hxpos)] with y hy
      simpa only [EReal.coe_mul_bot_of_pos hy] using hb'
  · have heq : (fun x => (g x : EReal) * a) =
        fun x => ((g x * a.toReal : ℝ) : EReal) := by
      funext x
      calc
        (g x : EReal) * a = (g x : EReal) * (a.toReal : EReal) := by
          exact congrArg (fun v : EReal => (g x : EReal) * v)
            (EReal.coe_toReal ha hbot).symm
        _ = ((g x * a.toReal : ℝ) : EReal) := (EReal.coe_mul _ _).symm
    rw [heq]
    exact (continuous_coe_real_ereal.comp (hg.mul_const a.toReal)).upperSemicontinuous

/-- The original relative-domain coefficient may be negative outside the domain;
only actual continuity and nonnegativity on K are required. -/
theorem upperSemicontinuousOn_coe_mul_fixed {K : Set X} {g : X → ℝ}
    (hg : ContinuousOn g K) (h0 : ∀ x ∈ K, 0 ≤ g x) {a : EReal} (ha : a ≠ ⊤) :
    UpperSemicontinuousOn (fun x => (g x : EReal) * a) K := by
  apply upperSemicontinuousOn_iff_restrict.mp
  exact upperSemicontinuous_coe_mul_fixed hg.domRestrict (fun x => h0 x x.property) ha

/-- Actual closed-domain truncation; it retains the original value on K. -/
def closedCut (K : Set X) (f : X → EReal) (x : X) : EReal := by
  classical
  exact if x ∈ K then f x else ⊥

/-- Genuine relative USC extends by bottom through an actual closed boundary. -/
theorem upperSemicontinuous_closedCut {K : Set X} (hK : IsClosed K) {f : X → EReal}
    (hf : UpperSemicontinuousOn f K) : UpperSemicontinuous (closedCut K f) := by
  intro x b hb
  by_cases hx : x ∈ K
  · have hb' : f x < b := by simpa only [closedCut, if_pos hx] using hb
    have hnear := eventually_nhdsWithin_iff.mp (hf x hx b hb')
    filter_upwards [hnear] with y hy
    by_cases hyK : y ∈ K
    · simpa only [closedCut, if_pos hyK] using hy hyK
    · simpa only [closedCut, if_neg hyK] using (bot_le : (⊥ : EReal) ≤ f x).trans_lt hb'
  · have hb' : (⊥ : EReal) < b := by simpa only [closedCut, if_neg hx] using hb
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    simpa only [closedCut, if_neg hy] using hb'

/-- Actual finite pointwise EReal supremum, including an empty index type. -/
theorem upperSemicontinuous_iSup_finite {ι : Type*} [Finite ι] {f : ι → X → EReal}
    (hf : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous (fun x => ⨆ i, f i x) := by
  apply upperSemicontinuousOn_univ_iff.mp
  exact SGPT.PSH.upperSemicontinuousOn_iSup_finite
    (fun i => UpperSemicontinuous.upperSemicontinuousOn (hf i) univ)
end SGPT.NAPotential.Berkovich.HullParameterUSC
