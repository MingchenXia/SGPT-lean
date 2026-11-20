import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicInteriorL1
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of vertical traces of strip subgeodesics

An interior strip subgeodesic restricts to a subgeodesic on every compact
subinterval.  The endpoint chord estimate on that restriction gives the
three-point extended-real chord inequality.  It also shows that a vertical
trace is either identically `⊥` or finite everywhere in the open time
interval; in the finite case its real trace is convex.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace IsSubgeodesicInterior

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}

/-- An interior value of a subgeodesic is never `⊤`. -/
theorem ne_top (h : IsSubgeodesicInterior θ curve)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) : curve t x ≠ ⊤ :=
  (h.thetaPshPotential ht).1.quasiPlurisubharmonic.ne_top x

private theorem eRealChord_bot_left (u : EReal) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : eRealChord ⊥ u s = ⊥ := by
  rw [eRealChord]
  rw [mul_comm, EReal.bot_mul_of_pos
    (EReal.coe_pos.mpr (sub_pos.mpr hs.2))]
  exact EReal.bot_add _

private theorem eRealChord_bot_right (u : EReal) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : eRealChord u ⊥ s = ⊥ := by
  rw [eRealChord]
  rw [mul_comm ((s : ℝ) : EReal),
    EReal.bot_mul_of_pos (EReal.coe_pos.mpr hs.1)]
  exact EReal.add_bot _

/-- The value at an intermediate interior time lies below the extended-real
chord through any two surrounding interior times. -/
theorem le_eRealChord_between (h : IsSubgeodesicInterior θ curve)
    {a t b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (_ht : t ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hat : a < t) (htb : t < b) (x : M) :
    curve t x ≤
      eRealChord (curve a x) (curve b x) ((t - a) / (b - a)) := by
  have hab : a < b := hat.trans htb
  have hleft :
      ManifoldL1LocallyTendsto (n := n) curve (𝓝[>] a) (curve a) :=
    (h.manifoldL1LocallyContinuousAt ha).mono_left nhdsWithin_le_nhds
  have hright :
      ManifoldL1LocallyTendsto (n := n) curve (𝓝[<] b) (curve b) :=
    (h.manifoldL1LocallyContinuousAt hb).mono_left nhdsWithin_le_nhds
  have hsub := h.affineReparametrized_isSubgeodesicFrom ha hb hab hleft hright
  have hs : (t - a) / (b - a) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hat) (sub_pos.mpr hab)
    · exact (div_lt_one (sub_pos.mpr hab)).2 (by linarith)
  have hchord := hsub.le_eRealChord hs x
  have hreparam : affineTimeReparam a b ((t - a) / (b - a)) = t := by
    rw [affineTimeReparam]
    field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  simpa [affineReparametrizedCurve, hreparam] using hchord

/-- If one value of a vertical trace is not a pole, then no interior value of
that trace is a pole. -/
theorem ne_bot_of_exists_ne_bot (h : IsSubgeodesicInterior θ curve) (x : M)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hc_bot : curve c x ≠ ⊥) :
    ∀ t ∈ Ioo (0 : ℝ) 1, curve t x ≠ ⊥ := by
  intro t ht ht_bot
  rcases lt_trichotomy t c with htc | htc | hct
  · let b : ℝ := (c + 1) / 2
    have hcb : c < b := by
      dsimp [b]
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      linarith [hc.2]
    have hb : b ∈ Ioo (0 : ℝ) 1 := by
      dsimp [b]
      constructor <;> linarith [hc.1, hc.2]
    have hs : (c - t) / (b - t) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (sub_pos.mpr htc) (sub_pos.mpr (htc.trans hcb))
      · exact (div_lt_one (sub_pos.mpr (htc.trans hcb))).2 (by linarith)
    have hchord := h.le_eRealChord_between ht hc hb htc hcb x
    rw [ht_bot, eRealChord_bot_left _ hs] at hchord
    exact hc_bot (le_antisymm hchord bot_le)
  · subst t
    exact hc_bot ht_bot
  · let a : ℝ := c / 2
    have hac : a < c := by
      dsimp [a]
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      linarith [hc.1]
    have ha : a ∈ Ioo (0 : ℝ) 1 := by
      dsimp [a]
      constructor <;> linarith [hc.1, hc.2]
    have hs : (c - a) / (t - a) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (sub_pos.mpr hac) (sub_pos.mpr (hac.trans hct))
      · exact (div_lt_one (sub_pos.mpr (hac.trans hct))).2 (by linarith)
    have hchord := h.le_eRealChord_between ha hc ht hac hct x
    rw [ht_bot, eRealChord_bot_right _ hs] at hchord
    exact hc_bot (le_antisymm hchord bot_le)

/-- A vertical trace has a uniform pole behavior throughout the open strip. -/
theorem all_bot_or_all_ne_bot (h : IsSubgeodesicInterior θ curve) (x : M) :
    (∀ t ∈ Ioo (0 : ℝ) 1, curve t x = ⊥) ∨
      (∀ t ∈ Ioo (0 : ℝ) 1, curve t x ≠ ⊥) := by
  classical
  by_cases hall : ∀ t ∈ Ioo (0 : ℝ) 1, curve t x = ⊥
  · exact Or.inl hall
  · rw [not_forall] at hall
    obtain ⟨c, hc⟩ := hall
    rw [Classical.not_imp] at hc
    exact Or.inr (h.ne_bot_of_exists_ne_bot x hc.1 hc.2)

/-- On the non-polar branch, every intermediate value lies below the ordinary
real chord through two surrounding interior values. -/
theorem toReal_le_chord_between (h : IsSubgeodesicInterior θ curve)
    {a t b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hat : a < t) (htb : t < b) (x : M)
    (hfinite : ∀ s ∈ Ioo (0 : ℝ) 1, curve s x ≠ ⊥) :
    (curve t x).toReal ≤
      (1 - (t - a) / (b - a)) * (curve a x).toReal +
        ((t - a) / (b - a)) * (curve b x).toReal := by
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.1.trans hat, htb.trans hb.2⟩
  have hchord := h.le_eRealChord_between ha ht hb hat htb x
  have hrhs :
      eRealChord (curve a x) (curve b x) ((t - a) / (b - a)) =
        (((1 - (t - a) / (b - a)) * (curve a x).toReal +
          ((t - a) / (b - a)) * (curve b x).toReal : ℝ) : EReal) := by
    unfold eRealChord
    conv_lhs =>
      rw [← EReal.coe_toReal (h.ne_top ha x) (hfinite a ha),
        ← EReal.coe_toReal (h.ne_top hb x) (hfinite b hb),
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  have hcoe : ((curve t x).toReal : EReal) = curve t x :=
    EReal.coe_toReal (h.ne_top ht x) (hfinite t ht)
  exact EReal.coe_le_coe_iff.mp (hcoe.trans_le (hchord.trans_eq hrhs))

/-- If a vertical trace has no pole in the open strip, its real-valued trace
is convex there. -/
theorem convexOn_toReal_of_forall_ne_bot
    (h : IsSubgeodesicInterior θ curve) (x : M)
    (hfinite : ∀ t ∈ Ioo (0 : ℝ) 1, curve t x ≠ ⊥) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun t => (curve t x).toReal) := by
  refine LinearOrder.convexOn_of_lt (convex_Ioo (0 : ℝ) 1) ?_
  intro a ha b hb hab α β hα hβ hsum
  let t : ℝ := α • a + β • b
  have hαeq : α = 1 - β := by linarith
  have htleft : t = a + β * (b - a) := by
    dsimp [t]
    rw [hαeq]
    ring
  have htright : t = b - α * (b - a) := by
    dsimp [t]
    have hβeq : β = 1 - α := by linarith
    rw [hβeq]
    ring
  have hat : a < t := by
    rw [htleft]
    exact lt_add_of_pos_right a (mul_pos hβ (sub_pos.mpr hab))
  have htb : t < b := by
    rw [htright]
    exact sub_lt_self b (mul_pos hα (sub_pos.mpr hab))
  have hchord := h.toReal_le_chord_between ha hb hat htb x hfinite
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hs : (t - a) / (b - a) = β := by
    have hnum : t - a = β * (b - a) := by
      rw [htleft]
      ring
    rw [hnum]
    field_simp [hba]
  rw [hs] at hchord
  simpa only [t, hαeq, smul_eq_mul] using hchord

/-- At a fixed spatial point, an interior strip subgeodesic is either
identically `⊥` in time, or is finite everywhere and has a convex real trace. -/
theorem verticalTrace_convexity_dichotomy
    (h : IsSubgeodesicInterior θ curve) (x : M) :
    (∀ t ∈ Ioo (0 : ℝ) 1, curve t x = ⊥) ∨
      ((∀ t ∈ Ioo (0 : ℝ) 1, curve t x ≠ ⊤ ∧ curve t x ≠ ⊥) ∧
        ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun t => (curve t x).toReal)) := by
  rcases h.all_bot_or_all_ne_bot x with hall | hfinite
  · exact Or.inl hall
  · exact Or.inr ⟨fun t ht => ⟨h.ne_top ht x, hfinite t ht⟩,
      h.convexOn_toReal_of_forall_ne_bot x hfinite⟩

end IsSubgeodesicInterior

namespace IsSubgeodesicFrom

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

/-- The vertical-trace dichotomy for a subgeodesic with prescribed endpoint
potentials. -/
theorem verticalTrace_convexity_dichotomy
    (h : IsSubgeodesicFrom θ curve u₀ u₁) (x : M) :
    (∀ t ∈ Ioo (0 : ℝ) 1, curve t x = ⊥) ∨
      ((∀ t ∈ Ioo (0 : ℝ) 1, curve t x ≠ ⊤ ∧ curve t x ≠ ⊥) ∧
        ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun t => (curve t x).toReal)) :=
  h.interior.verticalTrace_convexity_dichotomy x

end IsSubgeodesicFrom

end

end SGPT.Foundations.Analysis.FirstPass
