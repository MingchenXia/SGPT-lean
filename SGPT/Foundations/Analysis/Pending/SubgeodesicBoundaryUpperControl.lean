import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumSlices

/-!
# Joint upper control at subgeodesic endpoints

Endpoint chord domination and upper semicontinuity of the actual endpoint
give joint space/time upper control, including poles. At interior times,
the proved joint/slice regularization interchange supplies joint USC.
These are the actual boundary inputs for dominating subgeodesic replacement
in Xia, SGPT Lemma 4.1.1, PDF pages 0152--0153.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicBoundaryUpperControl

open FirstPass

noncomputable section

/-- The endpoint chord yields a joint local strict upper bound near the
left endpoint, in any topological spatial space and including poles. -/
theorem eventually_lt_left_of_upper_chord {X : Type*} [TopologicalSpace X]
    {curve : ℝ → X → EReal} {u : X → EReal} {C : ℝ}
    (hchord : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      curve t x ≤ eRealChord (u x) (C : EReal) t)
    {x : X} (husc : UpperSemicontinuousAt u x) {c : EReal} (hc : u x < c) :
    ∀ᶠ p : X × ℝ in 𝓝 (x, 0), p.2 ∈ Ioo (0 : ℝ) 1 → curve p.2 p.1 < c := by
  obtain ⟨K, huK, hKc⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  let L : ℝ → ℝ := fun t => (1 - t) * K + t * C
  have hL : Continuous (fun t => (L t : EReal)) :=
    continuous_coe_real_ereal.comp (by dsimp [L]; fun_prop)
  have hT : {t : ℝ | (L t : EReal) < c} ∈ 𝓝 0 :=
    hL.continuousAt (isOpen_Iio.mem_nhds (by simpa [L] using hKc))
  have hU : {y : X | u y < (K : EReal)} ∈ 𝓝 x := husc _ huK
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod hU hT] with p hp ht
  calc curve p.2 p.1
      ≤ eRealChord (u p.1) (C : EReal) p.2 := hchord _ ht _
    _ ≤ eRealChord (K : EReal) (C : EReal) p.2 :=
      eRealChord_mono hp.1.le le_rfl ht.1.le ht.2.le
    _ = (L p.2 : EReal) := by simp [eRealChord, L, EReal.coe_add, EReal.coe_mul]
    _ < c := hp.2

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A subgeodesic's actual left endpoint controls joint upper limits.
Only a finite upper bound on the opposite endpoint is required. -/
theorem eventually_lt_left_of_isSubgeodesicFrom
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) {C : ℝ}
    (hC : ∀ y, u₁ y ≤ (C : EReal)) {x : M} {c : EReal} (hc : u₀ x < c) :
    ∀ᶠ p : M × ℝ in 𝓝 (x, 0), p.2 ∈ Ioo (0 : ℝ) 1 → curve p.2 p.1 < c :=
  eventually_lt_left_of_upper_chord
    (fun _t ht y => (h.le_eRealChord ht y).trans
      (eRealChord_mono le_rfl (hC y) ht.1.le ht.2.le))
    (h.left_endpoint.1.quasiPlurisubharmonic.upperSemicontinuous x) hc

/-- Time reversal gives actual joint upper control at the right endpoint. -/
theorem eventually_lt_right_of_isSubgeodesicFrom
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) {C : ℝ}
    (hC : ∀ y, u₀ y ≤ (C : EReal)) {x : M} {c : EReal} (hc : u₁ x < c) :
    ∀ᶠ p : M × ℝ in 𝓝 (x, 1), p.2 ∈ Ioo (0 : ℝ) 1 → curve p.2 p.1 < c := by
  have hleft := eventually_lt_left_of_isSubgeodesicFrom h.timeReversed hC hc
  have hrev : Tendsto (fun p : M × ℝ => (p.1, 1 - p.2))
      (𝓝 (x, 1)) (𝓝 (x, 0)) := by
    simpa using (show Continuous (fun p : M × ℝ => (p.1, 1 - p.2)) by
      fun_prop).continuousAt.tendsto (x := (x, 1))
  filter_upwards [hrev.eventually hleft] with p hp ht
  have ht' : 1 - p.2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa [timeReversedCurve] using hp ht'

/-- Compactness supplies the opposite endpoint bound, giving actual joint
left upper control without an additional boundedness premise. -/
theorem eventually_lt_left_endpoint [CompactSpace M]
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) {x : M} {c : EReal} (hc : u₀ x < c) :
    ∀ᶠ p : M × ℝ in 𝓝 (x, 0), p.2 ∈ Ioo (0 : ℝ) 1 → curve p.2 p.1 < c := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨C, hC⟩ := h.right_endpoint.exists_global_upper_bound
  exact eventually_lt_left_of_isSubgeodesicFrom h hC hc

/-- Actual joint right endpoint upper control on a compact manifold. -/
theorem eventually_lt_right_endpoint [CompactSpace M]
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) {x : M} {c : EReal} (hc : u₁ x < c) :
    ∀ᶠ p : M × ℝ in 𝓝 (x, 1), p.2 ∈ Ioo (0 : ℝ) 1 → curve p.2 p.1 < c := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨C, hC⟩ := h.left_endpoint.exists_global_upper_bound
  exact eventually_lt_right_of_isSubgeodesicFrom h hC hc

/-- Three-point chord control and genuine USC slices imply actual joint
upper semicontinuity at interior times, without dimension or compactness
assumptions on the spatial topological space. -/
theorem upperSemicontinuousAt_of_chords {X : Type*} [TopologicalSpace X]
    {curve : ℝ → X → EReal} {C : ℝ}
    (hC : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, curve t x ≤ (C : EReal))
    (hchord : ∀ a t b : ℝ, a ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
      b ∈ Ioo (0 : ℝ) 1 → a < t → t < b → ∀ x,
      curve t x ≤ eRealChord (curve a x) (curve b x) ((t - a) / (b - a)))
    (husc : ∀ t ∈ Ioo (0 : ℝ) 1, UpperSemicontinuous (curve t))
    (x : X) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    UpperSemicontinuousAt (fun p : X × ℝ => curve p.2 p.1) (x, t) := by
  let F : X × ℝ → EReal := fun p => curve p.2 p.1
  have heq : ∀ y : X, ∀ s ∈ Ioo (0 : ℝ) 1,
      uscRegularization F (y, s) = curve s y := by
    intro y s hs
    have hreg := SubgeodesicSupremumSlices.uscRegularization_time_slice_eq curve
      id continuous_id hC hchord y hs
    simpa only [F, id_eq, uscRegularization_eq (husc s hs)] using hreg
  intro c hc
  have hreg : uscRegularization F (x, t) < c := by rw [heq x t ht]; exact hc
  have hT : ∀ᶠ p : X × ℝ in 𝓝 (x, t), p.2 ∈ Ioo (0 : ℝ) 1 :=
    continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [upperSemicontinuous_uscRegularization F (x, t) c hreg, hT]
    with p hp hpT
  rw [heq p.1 p.2 hpT] at hp
  exact hp

/-- An interior subgeodesic with a genuine finite common upper bound is
jointly USC in space and real time. -/
theorem upperSemicontinuousAt_of_isSubgeodesicInterior
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve) {C : ℝ}
    (hC : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, curve t x ≤ (C : EReal))
    (x : M) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    UpperSemicontinuousAt (fun p : M × ℝ => curve p.2 p.1) (x, t) :=
  upperSemicontinuousAt_of_chords hC
    (fun _a _t _b ha ht hb hat htb x => h.le_eRealChord_between ha ht hb hat htb x)
    (fun _t ht => (h.thetaPshPotential ht).1.quasiPlurisubharmonic.upperSemicontinuous) x ht

/-- Compact genuine endpoints supply the finite common bound required by
the actual joint USC producer. -/
theorem upperSemicontinuousAt_of_isSubgeodesicFrom [CompactSpace M]
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) (x : M) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    UpperSemicontinuousAt (fun p : M × ℝ => curve p.2 p.1) (x, t) := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨A, hA⟩ := h.left_endpoint.exists_global_upper_bound
  obtain ⟨B, hB⟩ := h.right_endpoint.exists_global_upper_bound
  have hC := SubgeodesicSupremumSlices.uniform_upper_bound_of_endpoint_bounds
    (curve := fun _ : Unit => curve) (u₀ := fun _ => u₀) (u₁ := fun _ => u₁)
    (fun _ => h) (C := max A B)
    (fun _ y => (hA y).trans (EReal.coe_le_coe_iff.mpr (le_max_left A B)))
    (fun _ y => (hB y).trans (EReal.coe_le_coe_iff.mpr (le_max_right A B)))
  exact upperSemicontinuousAt_of_isSubgeodesicInterior h.interior (hC ()) x ht

/-- Joint space/complex-time USC of an actual subgeodesic on the open strip. -/
theorem upperSemicontinuousAt_complexified_of_isSubgeodesicFrom
    [CompactSpace M]
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) (x : M) {τ : ℂ}
    (hτ : τ.re ∈ Ioo (0 : ℝ) 1) :
    UpperSemicontinuousAt (fun p : M × ℂ => curve p.2.re p.1) (x, τ) := by
  exact UpperSemicontinuousAt.comp (g := fun p : M × ℂ => (p.1, p.2.re))
    (c := (x, τ)) (upperSemicontinuousAt_of_isSubgeodesicFrom h x hτ)
    (by fun_prop)

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicBoundaryUpperControl
