import SGPT.Envelopes.MADirichlet5Transport
import SGPT.PSH.PlurifineCompatibility

/-!
# Comparison of relative capacities on nested domains

For open sets `V ⊆ Q ⊆ ℂⁿ` with `Q` bounded and a compact `L ⊆ V` there is a constant `C` with

  `Cap_V(E ∩ L) ≤ C · Cap_Q(E)` for every `E ⊆ ℂⁿ`

(`exists_relCapacity_inter_le`; Błocki's lecture notes, the comparison of relative capacities;
used in Xia, *Foundations of pluripotential theory* (FPT) to pass from convergence in `Cap_Q` to
convergence in `Cap_V` in `cor:mixed-products-energy-capacity-continuity`). Here `Cap` is TN's
relative Monge–Ampère capacity `relCapacity`.

Proof. Domain monotonicity: `Cap_V(E) ≤ Cap_{V₁}(E)` for `E ⊆ V₁ ⊆ V`
(`relCapacity_le_of_le_opens`, locality of the Bedford–Taylor measure). For a ball
`B(x, 2R) ⊆ V` and a competitor `w` on `B(x, 2R)` (`-1 ≤ w ≤ 0`), the glued function
`W = max(w, g)` on `B(x, 2R)`, `W = g` outside, with the quadratic barrier
`g = 2R⁻²(|z - x|² - (3R/2)²)`, is plurisubharmonic on `ℂⁿ` (`g > 0 ≥ w` near `∂B(x, 2R)`),
bounded on `Q`, and equal to `w` on `B(x, 5R/4)` (`g < -1` there); hence
`(ddᶜw)ⁿ(E ∩ B̄(x, R)) = (ddᶜW)ⁿ(E ∩ B̄(x, R)) ≤ (sup_Q W - inf_Q W)ⁿ Cap_Q(E)`
(`relCapacity_inter_closedBall_le`). Finally `L` is covered by finitely many such balls.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- **Domain monotonicity of the relative capacity**: `Cap_V(E) ≤ Cap_{V₁}(E)` for
`E ⊆ V₁ ⊆ V`. -/
theorem relCapacity_le_of_le_opens {V V₁ : Opens (ComplexModel n)} (hV₁ : V₁ ≤ V)
    {E : Set (ComplexModel n)} (hE : E ⊆ V₁) : relCapacity V E ≤ relCapacity V₁ E := by
  refine relCapacity_le_of_forall fun w hw hwb => ?_
  have hw₁ : IsLocallyBoundedPshOn V₁ w := BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hw hV₁
  calc canonicalBedfordTaylorMeasure V w hw E
      = (canonicalBedfordTaylorMeasure V w hw).restrict V₁ E :=
        (Measure.restrict_eq_self _ hE).symm
    _ = canonicalBedfordTaylorMeasure V₁ w hw₁ E := by
        rw [canonicalBedfordTaylorMeasure_restrict_eq hV₁ hw hw₁]
    _ ≤ relCapacity V₁ E :=
        canonicalBedfordTaylorMeasure_le_relCapacity hw₁ (fun z hz => hwb z (hV₁ hz)) E

/-- **Capacity of a ball in a larger bounded domain**: if `B(x, 2R) ⊆ Q`, `Q` is bounded,
`|z - x| ≤ ρ` on `Q`, then `Cap_{B(x,2R)}(E ∩ B̄(x, R)) ≤ (9/2 + 2ρ²/R²)ⁿ Cap_Q(E)`. -/
theorem relCapacity_inter_closedBall_le {Q : Opens (ComplexModel n)} {x : ComplexModel n}
    {R ρ : ℝ} (hR : 0 < R) (hxQ : ball x (2 * R) ⊆ Q) (hρ : ∀ z ∈ Q, ‖z - x‖ ≤ ρ)
    (E : Set (ComplexModel n)) :
    relCapacity ⟨ball x (2 * R), isOpen_ball⟩ (E ∩ closedBall x R) ≤
      ENNReal.ofReal ((9 / 2 + 2 * ρ ^ 2 / R ^ 2) ^ n) * relCapacity Q E := by
  classical
  set B₂ : Opens (ComplexModel n) := ⟨ball x (2 * R), isOpen_ball⟩ with hB₂def
  set A : ℝ := 2 / R ^ 2 with hAdef
  have hA : 0 < A := by positivity
  set g : ComplexModel n → ℝ := fun z => A * ‖z - x‖ ^ 2 + (-(A * (3 * R / 2) ^ 2)) with hgdef
  have hg : PlurisubharmonicOn (fun z => ((g z : ℝ) : EReal)) univ :=
    SGPT.PSH.quadratic_barrier_plurisubharmonic x hA _
  have hgval : ∀ z, g z = 2 * ((‖z - x‖ / R) ^ 2 - 9 / 4) := fun z => by
    simp only [hgdef, hAdef]; field_simp; ring
  refine relCapacity_le_of_forall fun w hw hwb => ?_
  set W : ComplexModel n → ℝ := SGPT.Foundations.Analysis.gluedMax (ball x (2 * R)) w g with hWdef
  have hWpsh : PlurisubharmonicOn (fun z => ((W z : ℝ) : EReal)) univ := by
    refine SGPT.PSH.real_gluedMax_plurisubharmonic isOpen_ball
      (U' := ball x (7 * R / 4)) ?_ ?_ hw.1 hg
    · exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
    · rintro z ⟨hz2, hz7⟩
      have h1 : 7 * R / 4 ≤ ‖z - x‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hz7; exact hz7
      have h2 : 7 / 4 ≤ ‖z - x‖ / R := by rw [le_div_iff₀ hR]; linarith
      rw [hgval]
      have := (hwb z hz2).2
      nlinarith
  -- bounds on `Q`
  have hWb : ∀ z ∈ Q, -(9 / 2 : ℝ) ≤ W z ∧ W z ≤ 2 * ρ ^ 2 / R ^ 2 := by
    intro z hz
    have hgz : -(9 / 2 : ℝ) ≤ g z := by
      rw [hgval]; nlinarith [sq_nonneg (‖z - x‖ / R)]
    have hgz' : g z ≤ 2 * ρ ^ 2 / R ^ 2 := by
      rw [hgval]
      have h1 : ‖z - x‖ / R ≤ ρ / R := div_le_div_of_nonneg_right (hρ z hz) hR.le
      have h0 : 0 ≤ ‖z - x‖ / R := by positivity
      have h3 : (‖z - x‖ / R) ^ 2 ≤ ρ ^ 2 / R ^ 2 := by
        rw [← div_pow]; exact pow_le_pow_left₀ h0 h1 2
      have : 2 * ρ ^ 2 / R ^ 2 = 2 * (ρ ^ 2 / R ^ 2) := by ring
      rw [this]; linarith
    have hρ0 : 0 ≤ 2 * ρ ^ 2 / R ^ 2 := by positivity
    by_cases hz2 : z ∈ ball x (2 * R)
    · rw [hWdef, SGPT.Foundations.Analysis.gluedMax_eq_max hz2]
      exact ⟨hgz.trans (le_max_right _ _),
        max_le ((hwb z hz2).2.trans hρ0) hgz'⟩
    · simp only [hWdef, SGPT.Foundations.Analysis.gluedMax, hz2, if_false]
      exact ⟨hgz, hgz'⟩
  have hWQ : IsLocallyBoundedPshOn Q W :=
    isLocallyBoundedPshOn_of_abs_le (hWpsh.mono (subset_univ _))
      (C := 9 / 2 + 2 * ρ ^ 2 / R ^ 2) fun z hz => by
        have h1 := hWb z hz
        have hρ0 : 0 ≤ 2 * ρ ^ 2 / R ^ 2 := by positivity
        exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  -- `W = w` on `B(x, 5R/4)`
  set B₁ : Opens (ComplexModel n) := ⟨ball x (5 * R / 4), isOpen_ball⟩ with hB₁def
  have hB₁₂ : B₁ ≤ B₂ := ball_subset_ball (by linarith)
  have hB₁Q : B₁ ≤ Q := hB₁₂.trans hxQ
  have hWw : EqOn W w B₁ := by
    intro z hz
    have hz2 : z ∈ ball x (2 * R) := hB₁₂ hz
    rw [hWdef, SGPT.Foundations.Analysis.gluedMax_eq_max hz2]
    refine max_eq_left ?_
    have h1 : ‖z - x‖ < 5 * R / 4 := by rw [← dist_eq_norm]; exact hz
    have h2 : ‖z - x‖ / R < 5 / 4 := by rw [div_lt_iff₀ hR]; linarith
    have h0 : 0 ≤ ‖z - x‖ / R := by positivity
    rw [hgval]
    have := (hwb z hz2).1
    nlinarith
  have hw₁ : IsLocallyBoundedPshOn B₁ w := BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hw hB₁₂
  have hW₁ : IsLocallyBoundedPshOn B₁ W := BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hWQ hB₁Q
  have hsub : E ∩ closedBall x R ⊆ B₁ := fun z hz =>
    closedBall_subset_ball (by linarith) hz.2
  calc canonicalBedfordTaylorMeasure B₂ w hw (E ∩ closedBall x R)
      = (canonicalBedfordTaylorMeasure B₂ w hw).restrict B₁ (E ∩ closedBall x R) :=
        (Measure.restrict_eq_self _ hsub).symm
    _ = canonicalBedfordTaylorMeasure B₁ W hW₁ (E ∩ closedBall x R) := by
        rw [canonicalBedfordTaylorMeasure_restrict_eq hB₁₂ hw hw₁,
          canonicalBedfordTaylorMeasure_congr_eqOn hw₁ hW₁ (fun z hz => (hWw hz).symm)]
    _ = (canonicalBedfordTaylorMeasure Q W hWQ).restrict B₁ (E ∩ closedBall x R) := by
        rw [canonicalBedfordTaylorMeasure_restrict_eq hB₁Q hWQ hW₁]
    _ = canonicalBedfordTaylorMeasure Q W hWQ (E ∩ closedBall x R) :=
        Measure.restrict_eq_self _ hsub
    _ ≤ ENNReal.ofReal ((2 * ρ ^ 2 / R ^ 2 - -(9 / 2)) ^ n) * relCapacity Q (E ∩ closedBall x R) :=
        canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds hWQ
          (by have : 0 ≤ 2 * ρ ^ 2 / R ^ 2 := by positivity
              linarith) hWb _
    _ ≤ ENNReal.ofReal ((9 / 2 + 2 * ρ ^ 2 / R ^ 2) ^ n) * relCapacity Q E := by
        rw [show (2 * ρ ^ 2 / R ^ 2 - -(9 / 2) : ℝ) = 9 / 2 + 2 * ρ ^ 2 / R ^ 2 by ring]
        exact mul_le_mul' le_rfl (relCapacity_mono inter_subset_left)

/-- **Comparison of relative capacities** (Błocki): for open `V ⊆ Q ⊆ ℂⁿ`, `Q` bounded, and a
compact `L ⊆ V`, there is `C < ∞` with `Cap_V(E ∩ L) ≤ C · Cap_Q(E)` for all `E`. -/
theorem exists_relCapacity_inter_le {V Q : Opens (ComplexModel n)} (hVQ : V ≤ Q)
    (hQ : Bornology.IsBounded (Q : Set (ComplexModel n))) {L : Set (ComplexModel n)}
    (hL : IsCompact L) (hLV : L ⊆ V) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ E : Set (ComplexModel n), relCapacity V (E ∩ L) ≤ C * relCapacity Q E := by
  classical
  -- a radius at each point of `L`
  have hrad : ∀ x ∈ L, ∃ R : ℝ, 0 < R ∧ ball x (2 * R) ⊆ V := by
    intro x hx
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp V.isOpen x (hLV hx)
    exact ⟨ε / 2, by positivity, by rw [show 2 * (ε / 2) = ε by ring]; exact hεV⟩
  choose! R hR hRV using hrad
  obtain ⟨t, hcover⟩ := hL.elim_finite_subcover (fun x : L => ball (x : ComplexModel n) (R x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hR x hx)⟩)
  obtain ⟨ρ₀, hρ₀⟩ := hQ.subset_closedBall 0
  set C : ℝ≥0∞ := ∑ x ∈ t, ENNReal.ofReal ((9 / 2 + 2 * (ρ₀ + ‖(x : ComplexModel n)‖) ^ 2 /
    R x ^ 2) ^ n) with hCdef
  refine ⟨C, ?_, fun E => ?_⟩
  · exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top
  have hsub : E ∩ L ⊆ ⋃ x ∈ t, E ∩ closedBall (x : ComplexModel n) (R x) := by
    intro z ⟨hzE, hzL⟩
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hzL)
    exact mem_iUnion₂.mpr ⟨x, hxt, hzE, ball_subset_closedBall hzx⟩
  calc relCapacity V (E ∩ L)
      ≤ relCapacity V (⋃ x ∈ t, E ∩ closedBall (x : ComplexModel n) (R x)) := relCapacity_mono hsub
    _ ≤ ∑ x ∈ t, relCapacity V (E ∩ closedBall (x : ComplexModel n) (R x)) :=
        relCapacity_biUnion_finset_le V t _
    _ ≤ ∑ x ∈ t, ENNReal.ofReal ((9 / 2 + 2 * (ρ₀ + ‖(x : ComplexModel n)‖) ^ 2 /
          R x ^ 2) ^ n) * relCapacity Q E := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hx := hR x x.2
        have hxV := hRV x x.2
        refine (relCapacity_le_of_le_opens (V₁ := ⟨ball (x : ComplexModel n) (2 * R x), isOpen_ball⟩)
          hxV fun z hz => closedBall_subset_ball (by linarith) hz.2).trans ?_
        refine relCapacity_inter_closedBall_le hx (hxV.trans hVQ) (fun z hz => ?_) E
        have h1 := hρ₀ hz
        rw [mem_closedBall, dist_zero_right] at h1
        calc ‖z - (x : ComplexModel n)‖ ≤ ‖z‖ + ‖(x : ComplexModel n)‖ := norm_sub_le _ _
          _ ≤ ρ₀ + ‖(x : ComplexModel n)‖ := by linarith
    _ = C * relCapacity Q E := by rw [hCdef, Finset.sum_mul]

/-- **Convergence in capacity passes to smaller domains**: if `Cap_Q(L ∩ Fⱼ) → 0` for every
compact `L ⊆ Q`, then `Cap_V(T ∩ Fⱼ) → 0` for every open `V ⊆ Q` and compact `T ⊆ V`. -/
theorem tendsto_relCapacity_of_le_opens {V Q : Opens (ComplexModel n)} (hVQ : V ≤ Q)
    (hQ : Bornology.IsBounded (Q : Set (ComplexModel n))) {F : ℕ → Set (ComplexModel n)}
    {T : Set (ComplexModel n)} (hT : IsCompact T) (hTV : T ⊆ V)
    (hF : Tendsto (fun j => relCapacity Q (T ∩ F j)) atTop (𝓝 0)) :
    Tendsto (fun j => relCapacity V (T ∩ F j)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hcomp⟩ := exists_relCapacity_inter_le hVQ hQ hT hTV
  have hlim : Tendsto (fun j => C * relCapacity Q (T ∩ F j)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hF (Or.inr hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun j => ?_
  have := hcomp (T ∩ F j)
  rwa [inter_right_comm, inter_self] at this

end SGPT.Envelopes.MADirichlet
