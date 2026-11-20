import SGPT.Foundations.Analysis.FirstPass.SubgeodesicConvexity
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Order.Monotone

/-!
# Pointwise endpoint limits of subgeodesics

Xia, SGPT Corollary 4.1.1 (PDF page 0150). A finite convex vertical trace
becomes antitone near the left endpoint after subtracting one secant slope.
The complete ordered extended reals supply the limit. Poles are handled by
the established vertical-trace dichotomy, without replacing them by zero.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointLimits

open FirstPass

noncomputable section

/-- A finite real convex function on the open unit interval has an
extended-real right limit at zero. No endpoint boundedness is required. -/
theorem exists_tendsto_coe_convexOn_left {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioo (0 : ℝ) 1) f) :
    ∃ L : EReal, Tendsto (fun t => (f t : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let c : ℝ := 1 / 2
  let d : ℝ := 3 / 4
  let A : ℝ := (f d - f c) / (d - c)
  let g : ℝ → EReal := fun t => ((f t - A * t : ℝ) : EReal)
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  have hd : d ∈ Ioo (0 : ℝ) 1 := by norm_num [d]
  have hcd : c < d := by norm_num [c, d]
  have hanti : AntitoneOn g (Ioo (0 : ℝ) c) := by
    intro s hs t ht hst
    by_cases hst' : s = t
    · subst t
      exact le_rfl
    have hstlt : s < t := lt_of_le_of_ne hst hst'
    have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hc.2⟩
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hc.2⟩
    have hsl := (hf.slope_mono_adjacent hsI hc hstlt ht.2).trans
      (hf.slope_mono_adjacent htI hd ht.2 hcd)
    have hdiff : f t - f s ≤ A * (t - s) :=
      (div_le_iff₀ (sub_pos.mpr hstlt)).mp hsl
    change ((f t - A * t : ℝ) : EReal) ≤ ((f s - A * s : ℝ) : EReal)
    apply EReal.coe_le_coe_iff.mpr
    nlinarith
  let L : EReal := sSup (g '' Ioo (0 : ℝ) c)
  have hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    hanti.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hc.1) (OrderTop.bddAbove _)
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlin : Tendsto (fun t : ℝ => ((A * t : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using tendsto_const_nhds.mul ht
  have hadd := (EReal.continuousAt_add
    (p := (L, ((0 : ℝ) : EReal))) (Or.inr (EReal.coe_ne_bot 0))
      (Or.inr (EReal.coe_ne_top 0))).tendsto.comp (hlim.prodMk_nhds hlin)
  simp only [EReal.coe_zero, add_zero] at hadd
  refine ⟨L, hadd.congr fun t => ?_⟩
  change ((f t - A * t : ℝ) : EReal) + ((A * t : ℝ) : EReal) = (f t : EReal)
  rw [← EReal.coe_add]
  congr 1
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

/-- Every vertical trace of an interior subgeodesic has a right endpoint
limit at zero, including traces identically equal to minus infinity. -/
theorem exists_tendsto_left (h : FirstPass.IsSubgeodesicInterior θ curve) (x : M) :
    ∃ L : EReal, Tendsto (fun t => curve t x) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rcases h.verticalTrace_convexity_dichotomy x with hpole | ⟨hfinite, hconvex⟩
  · refine ⟨⊥, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (hpole t ht).symm
  · obtain ⟨L, hL⟩ := exists_tendsto_coe_convexOn_left hconvex
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact EReal.coe_toReal (hfinite t ht).1 (hfinite t ht).2

/-- The canonical pointwise right limit at the left endpoint. -/
def leftLimit (curve : ℝ → M → EReal) (x : M) : EReal :=
  limsup (fun t => curve t x) (𝓝[>] (0 : ℝ))

/-- The canonical left endpoint limit is an actual one-sided filter limit. -/
theorem tendsto_leftLimit (h : IsSubgeodesicInterior θ curve) (x : M) :
    Tendsto (fun t => curve t x) (𝓝[>] (0 : ℝ)) (𝓝 (leftLimit curve x)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_left h x
  simpa only [leftLimit, hL.limsup_eq] using hL

/-- Endpoint chord domination bounds every pointwise left limit by its
prescribed potential, even at poles of either endpoint. -/
theorem leftLimit_le (h : IsSubgeodesicFrom θ curve u₀ u₁) (x : M) :
    leftLimit curve x ≤ u₀ x := by
  by_cases hpole : u₀ x = ⊥ ∨ u₁ x = ⊥
  · have hbot : Tendsto (fun t => curve t x) (𝓝[>] (0 : ℝ)) (𝓝 (⊥ : EReal)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      have hchord := h.le_eRealChord ht x
      rw [SubgeodesicInfimum.eRealChord_eq_bot_of_endpoint_eq_bot hpole ht] at hchord
      exact (le_antisymm hchord bot_le).symm
    rw [tendsto_nhds_unique (tendsto_leftLimit h.interior x) hbot]
    exact bot_le
  · have h₀top := h.left_endpoint.1.quasiPlurisubharmonic.ne_top x
    have h₁top := h.right_endpoint.1.quasiPlurisubharmonic.ne_top x
    have h₀bot : u₀ x ≠ ⊥ := fun hx => hpole (Or.inl hx)
    have h₁bot : u₁ x ≠ ⊥ := fun hx => hpole (Or.inr hx)
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hchord : Tendsto (fun t => eRealChord (u₀ x) (u₁ x) t)
        (𝓝[>] (0 : ℝ)) (𝓝 (u₀ x)) := by
      have hreal : Tendsto
          (fun t : ℝ => (1 - t) * (u₀ x).toReal + t * (u₁ x).toReal)
          (𝓝[>] (0 : ℝ)) (𝓝 (u₀ x).toReal) := by
        have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
          tendsto_const_nhds
        have h0v : Tendsto (fun _ : ℝ => (u₀ x).toReal)
            (𝓝[>] (0 : ℝ)) (𝓝 (u₀ x).toReal) := tendsto_const_nhds
        have h1v : Tendsto (fun _ : ℝ => (u₁ x).toReal)
            (𝓝[>] (0 : ℝ)) (𝓝 (u₁ x).toReal) := tendsto_const_nhds
        simpa using ((h1.sub ht).mul h0v).add (ht.mul h1v)
      have hE := EReal.tendsto_coe.mpr hreal
      convert hE using 1
      · funext t
        unfold eRealChord
        conv_lhs => rw [← EReal.coe_toReal h₀top h₀bot,
          ← EReal.coe_toReal h₁top h₁bot, ← EReal.coe_mul, ← EReal.coe_mul,
          ← EReal.coe_add]
      · rw [EReal.coe_toReal h₀top h₀bot]
    exact le_of_tendsto_of_tendsto (tendsto_leftLimit h.interior x) hchord
      (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
        exact h.le_eRealChord ht x)

/-- The pointwise right endpoint limit, using time reversal. -/
def rightLimit (curve : ℝ → M → EReal) : M → EReal :=
  leftLimit (timeReversedCurve curve)

/-- Time reversal transports the canonical endpoint limit to the left
neighbourhood of one. -/
theorem tendsto_rightLimit (h : IsSubgeodesicInterior θ curve) (x : M) :
    Tendsto (fun t => curve t x) (𝓝[<] (1 : ℝ)) (𝓝 (rightLimit curve x)) := by
  have hh := (tendsto_leftLimit h.timeReversed x).comp tendsto_one_sub_nhdsLT_one
  simpa [rightLimit, timeReversedCurve, Function.comp_def] using hh

/-- The pointwise right limit is everywhere below its prescribed endpoint. -/
theorem rightLimit_le (h : IsSubgeodesicFrom θ curve u₀ u₁) (x : M) :
    rightLimit curve x ≤ u₁ x :=
  leftLimit_le h.timeReversed x

/-- Compactness and the endpoint chord give one finite upper bound for all
interior slices. No lower bound or boundedness of the endpoints is assumed. -/
theorem exists_uniform_upper_bound [CompactSpace M]
    (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    ∃ C : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, curve t x ≤ (C : EReal) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let _ : IsEmpty M := hM
    exact ⟨0, fun _ _ x => isEmptyElim x⟩
  · let _ : Nonempty M := hM
    obtain ⟨A, hA⟩ := h.left_endpoint.exists_global_upper_bound
    obtain ⟨B, hB⟩ := h.right_endpoint.exists_global_upper_bound
    let C : ℝ := max A B
    have h₀ : ∀ x, u₀ x ≤ (C : EReal) := fun x =>
      (hA x).trans (EReal.coe_le_coe_iff.mpr (le_max_left A B))
    have h₁ : ∀ x, u₁ x ≤ (C : EReal) := fun x =>
      (hB x).trans (EReal.coe_le_coe_iff.mpr (le_max_right A B))
    refine ⟨C, fun t ht x => (h.le_eRealChord ht x).trans ?_⟩
    have hchord : eRealChord (u₀ x) (u₁ x) t ≤ eRealChord (C : EReal) C t :=
      add_le_add
        (monotone_eReal_const_mul (sub_nonneg.mpr ht.2.le) (h₀ x))
        (monotone_eReal_const_mul ht.1.le (h₁ x))
    have hconst : eRealChord (C : EReal) C t = (C : EReal) := by
      unfold eRealChord
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring
    exact hchord.trans_eq hconst

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointLimits
