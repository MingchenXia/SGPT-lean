import SGPT.Toric.BigToricNewtonBody
import SGPT.PSH.SourceEnvelopeRooftop
import SGPT.Toric.ToricEnvelopeClosure

/-!
# The envelope `P_θ[φ]` of a toric potential in a big toric class

Source `chapter_toric_big.tex`, `prop:GPenvelopebig`: for `φ ∈ PSH_tor(X, θ)`,
`P_θ[φ] ∈ PSH_tor(X, θ)` and `G_{P_θ[φ]} = G_{V_θ}` on `Δ(θ, φ)` and `+∞` elsewhere
(`eq:toricPenvbig`).

The proof follows the source: `P_θ[φ] = usc sup_C ((φ + C) ∧ V_θ)` (`eq:Penvsups`), the
rooftop, constant and regularized-supremum formulas give
`G_{P_θ[φ]} = cl inf_C (G_{V_θ} ∨ (G_φ - C))`, and the closure is computed using that
`G_{V_θ}` is finite and continuous on `P_D`.  The continuity (asserted in the source) is
proved here: `G_{V_θ}` is bounded on `P_D` (`thm:FVtheta`), closed convex, and a convex
function bounded above on a polyhedron (a finite intersection of closed half-spaces) is
upper semicontinuous relative to it (`continuousOn_toReal_of_convex_bounded`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Classical

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Convex functions on the polyhedron `P_D` -/

/-- For `m ∈ P_D` there is `δ > 0` such that every point `m'` of `P_D` with
`‖m' - m‖ ≤ δ` lies on a segment `[m, p]` with `p ∈ P_D`, `‖p - m‖ = δ`. -/
theorem exists_radius_toricDivisorPolytope (D : ToricDivisor γ hs)
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ toricDivisorPolytope D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m' ∈ toricDivisorPolytope D, m' ≠ m →
      m + (δ / ‖m' - m‖) • (m' - m) ∈ toricDivisorPolytope D := by
  have hfin := finite_polytopeToricRays γ hs
  let _ := hfin.fintype
  let U : Set (EuclideanSpace ℝ (Fin n)) := ⋂ ρ : PolytopeToricRays γ hs,
    {z | latticeFunctional ρ.val m = -(D ρ : ℝ) ∨ -(D ρ : ℝ) < latticeFunctional ρ.val (m + z)}
  have hcont (ρ : PolytopeToricRays γ hs) : Continuous (latticeFunctional ρ.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro ρ
    by_cases hρ : latticeFunctional ρ.val m = -(D ρ : ℝ)
    · simp only [hρ, true_or, ofPred_true, isOpen_univ]
    · simp only [hρ, false_or]
      exact isOpen_lt continuous_const ((hcont ρ).comp (continuous_const.add continuous_id))
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by
    simp only [U, mem_iInter, mem_ofPred_eq, add_zero]
    intro ρ
    rcases (hm ρ).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  refine ⟨ε / 2, half_pos hε, fun m' hm' hne => ?_⟩
  have hnorm : 0 < ‖m' - m‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set s : ℝ := ε / 2 / ‖m' - m‖
  have hs0 : 0 < s := div_pos (half_pos hε) hnorm
  have hz : s • (m' - m) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs0.le]
    simp only [s]
    rw [div_mul_cancel₀ _ hnorm.ne']
    linarith
  intro ρ
  have hzρ := mem_iInter.mp hz ρ
  rcases hzρ with hact | hin
  · -- active constraint: the direction `m' - m` points into the half-space
    have h1 := hm' ρ
    change -(D ρ : ℝ) ≤ latticeFunctional ρ.val m' at h1
    rw [map_add, map_smul, smul_eq_mul, map_sub]
    have h2 : 0 ≤ s * (latticeFunctional ρ.val m' - latticeFunctional ρ.val m) :=
      mul_nonneg hs0.le (by linarith)
    linarith
  · exact hin.le

/-- Upper semicontinuity relative to `P_D`: a convex function bounded above by `M` on
`P_D` satisfies `G(m') ≤ G(m) + ε` for `m' ∈ P_D` near `m ∈ P_D`. -/
theorem eventually_le_add_of_convex_bounded (D : ToricDivisor γ hs)
    {G : EuclideanSpace ℝ (Fin n) → EReal} (hG : IsConvex G) {M : ℝ}
    (hM : ∀ m ∈ toricDivisorPolytope D, G m ≤ (M : EReal))
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ toricDivisorPolytope D) {g : ℝ}
    (hg : G m = (g : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m' in 𝓝[toricDivisorPolytope D] m, G m' ≤ ((g + ε : ℝ) : EReal) := by
  obtain ⟨δ, hδ, hseg⟩ := exists_radius_toricDivisorPolytope D hm
  set c : ℝ := |M - g| + 1
  have hc : 0 < c := by positivity
  set κ : ℝ := min (ε / c) 1
  have hκ : 0 < κ := lt_min (div_pos hε hc) one_pos
  have hball : Metric.ball m (δ * κ / 2) ∈ 𝓝 m := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with m' hm'b hm'P
  by_cases hne : m' = m
  · rw [hne, hg]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hnorm : 0 < ‖m' - m‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set t : ℝ := ‖m' - m‖ / δ
  have ht0 : 0 < t := div_pos hnorm hδ
  have hdist : ‖m' - m‖ < δ * κ / 2 := by
    rw [← dist_eq_norm]; exact hm'b
  have htκ : t < κ / 2 := by
    simp only [t]
    rw [div_lt_iff₀ hδ]
    linarith
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκε : κ ≤ ε / c := min_le_left _ _
  have ht1 : t ≤ 1 := by linarith
  set p := m + (δ / ‖m' - m‖) • (m' - m)
  have hp := hseg m' hm'P hne
  have hk : t * (δ / ‖m' - m‖) = 1 := by
    simp only [t]
    field_simp
  have hcomb : (1 - t) • m + t • p = m' := by
    simp only [p, smul_add, smul_smul, hk, one_smul, sub_smul]
    abel
  have hepi1 : (m, g) ∈ epigraph G := by
    change G m ≤ (g : EReal); rw [hg]
  have hepi2 : (p, M) ∈ epigraph G := hM p hp
  have hmem := hG hepi1 hepi2 (sub_nonneg.mpr ht1) ht0.le (by ring)
  have hval : G m' ≤ (((1 - t) * g + t * M : ℝ) : EReal) := by
    have h' : G ((1 - t) • m + t • p) ≤ (((1 - t) • (m, g) + t • (p, M)).2 : EReal) := hmem
    rw [hcomb] at h'
    simpa [smul_eq_mul] using h'
  refine hval.trans (EReal.coe_le_coe_iff.mpr ?_)
  have htc : t * c ≤ ε := by
    have h1 : t * c ≤ κ / 2 * c := mul_le_mul_of_nonneg_right htκ.le hc.le
    have h2 : κ / 2 * c ≤ ε / c / 2 * c := mul_le_mul_of_nonneg_right (by linarith) hc.le
    have h3 : ε / c / 2 * c = ε / 2 := by field_simp
    linarith
  have hMg : M - g ≤ c := by
    simp only [c]; linarith [le_abs_self (M - g)]
  nlinarith [mul_le_mul_of_nonneg_left hMg ht0.le]

/-- A closed convex function which is finite and bounded above on `P_D` is continuous
relative to `P_D` (as a real function there). -/
theorem continuousOn_toReal_of_convex_bounded (D : ToricDivisor γ hs)
    {G : EuclideanSpace ℝ (Fin n) → EReal} (hG : IsConvex G) (hlsc : LowerSemicontinuous G)
    {a M : ℝ} (hM : ∀ m ∈ toricDivisorPolytope D, (a : EReal) ≤ G m ∧ G m ≤ (M : EReal)) :
    ContinuousOn (fun m => (G m).toReal) (toricDivisorPolytope D) := by
  have hreal : ∀ m ∈ toricDivisorPolytope D, G m = ((G m).toReal : EReal) := by
    intro m hm
    exact (EReal.coe_toReal (ne_of_lt ((hM m hm).2.trans_lt (EReal.coe_lt_top M)))
      (ne_of_gt ((EReal.bot_lt_coe a).trans_le (hM m hm).1))).symm
  intro m hm
  apply tendsto_order.2
  constructor
  · intro b hb
    have hb' : (b : EReal) < G m := by rw [hreal m hm]; exact EReal.coe_lt_coe_iff.mpr hb
    filter_upwards [nhdsWithin_le_nhds (hlsc m b hb'), self_mem_nhdsWithin] with m' h1 h2
    rw [hreal m' h2] at h1
    exact EReal.coe_lt_coe_iff.mp h1
  · intro b hb
    have hε : 0 < (b - (G m).toReal) / 2 := by linarith
    filter_upwards [eventually_le_add_of_convex_bounded D hG (fun m hm => (hM m hm).2) hm
      (hreal m hm) hε, self_mem_nhdsWithin] with m' h1 h2
    rw [hreal m' h2] at h1
    have := EReal.coe_le_coe_iff.mp h1
    linarith

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The real values of `G_{V_θ}` on `P_D`. -/
def minimalLegendreReal (m : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (h.legendre h.minimalEnvelope m).toReal

theorem legendre_minimalEnvelope_eq_real (hP : (toricDivisorPolytope D).Nonempty)
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ toricDivisorPolytope D) :
    h.legendre h.minimalEnvelope m = (h.minimalLegendreReal m : EReal) := by
  obtain ⟨a, b, hab⟩ := h.legendre_minimalEnvelope_bounds hP
  exact (EReal.coe_toReal (ne_of_lt ((hab m hm).2.trans_lt (EReal.coe_lt_top b)))
    (ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab m hm).1))).symm

/-- Source `prop:GPenvelopebig` (proof): `G_{V_θ}` is finite and continuous on `P_D`. -/
theorem continuousOn_minimalLegendreReal (hP : (toricDivisorPolytope D).Nonempty) :
    ContinuousOn h.minimalLegendreReal (toricDivisorPolytope D) := by
  obtain ⟨a, b, hab⟩ := h.legendre_minimalEnvelope_bounds hP
  have hG := h.legendre_mem_closedProperOnBody hP (h.minimalEnvelope_mem hP)
  exact continuousOn_toReal_of_convex_bounded D hG.1.1 hG.2.1 hab

/-- The rooftop `(φ + C) ∧ V_θ` of `eq:Penvsups`. -/
def shiftedRooftop (u : PolytopeToricVariety γ hs → EReal) (C : ℝ) :
    PolytopeToricVariety γ hs → EReal :=
  thetaRooftop h.atlasForm (fun p => u p + (C : EReal)) h.minimalEnvelope

/-- Source `prop:GPenvelopebig` (proof, rooftop step): for each `C ∈ ℝ`,
`(φ + C) ∧ V_θ` is a toric potential with `G = G_{V_θ} ∨ (G_φ - C)`. -/
theorem shiftedRooftop_spec (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) (C : ℝ) :
    h.shiftedRooftop u C ≠ ⊥ ∧ h.shiftedRooftop u C ∈ h.PSHTor ∧
      h.legendre (h.shiftedRooftop u C) =
        fun m => max (h.legendre h.minimalEnvelope m) (h.legendre u m - (C : EReal)) := by
  have hus := h.mem_PSHTor_add_const hu C
  have hV := h.minimalEnvelope_mem hP
  obtain ⟨B, hB⟩ := h.exists_upper_bound hu.1
  have hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm
      (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) :=
    hu.1.add_const (C - max (B + C) 0)
  have hwu : (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) ≤
      fun p => u p + (C : EReal) := by
    intro p
    have hc : C - max (B + C) 0 ≤ C := by linarith [le_max_right (B + C) 0]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hc)
  have hw0 : (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) ≤ 0 := by
    intro p
    have hc : B + (C - max (B + C) 0) ≤ 0 := by linarith [le_max_left (B + C) 0]
    calc u p + ((C - max (B + C) 0 : ℝ) : EReal)
        ≤ (B : EReal) + ((C - max (B + C) 0 : ℝ) : EReal) := add_le_add (hB p) le_rfl
      _ = ((B + (C - max (B + C) 0) : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ ((0 : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hc
      _ = (0 : PolytopeToricVariety γ hs → EReal) p := by simp
  have hwV : (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) ≤ h.minimalEnvelope := fun p =>
    le_iSup (fun w : {w : PolytopeToricVariety γ hs → EReal //
        (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm w ∧ w ≤ 0} => w.1 p)
      ⟨_, hw, hw0⟩
  have hne : h.shiftedRooftop u C ≠ ⊥ := by
    intro hR
    obtain ⟨y, _, hy⟩ := hw.locallyNondegenerate (Classical.arbitrary _) (mem_univ _) univ
      isOpen_univ (mem_univ _)
    apply hy
    have hle := le_thetaRooftop hw hwu hwV y
    change _ ≤ h.shiftedRooftop u C y at hle
    rw [hR] at hle
    exact le_bot_iff.mp hle
  refine ⟨hne, h.mem_PSHTor_thetaRooftop hus hV hne, ?_⟩
  unfold shiftedRooftop
  rw [h.legendre_thetaRooftop hP hus hV hne, h.legendre_add_const]
  funext m
  exact max_comm _ _

/-- The pointwise infimum `inf_C (G_{V_θ} ∨ (G_φ - C))`, with the real values of `G_{V_θ}`. -/
theorem iInf_shifted_legendre (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (fun C : ℝ => h.legendre (h.shiftedRooftop u C)) =
      fun (C : ℝ) m => max (h.minimalLegendreReal m : EReal) (h.legendre u m - (C : EReal)) := by
  have hGu := h.legendre_mem_closedProperOnBody hP hu
  funext C m
  simp only [(h.shiftedRooftop_spec hP hu C).2.2]
  by_cases hm : m ∈ toricDivisorPolytope D
  · rw [h.legendre_minimalEnvelope_eq_real hP hm]
  · have hGV := h.legendre_mem_closedProperOnBody hP (h.minimalEnvelope_mem hP)
    rw [hGV.2.2 m hm, hGu.2.2 m hm]
    simp

/-- Source `prop:GPenvelopebig`: `P_θ[φ] ∈ PSH_tor(X, θ)` and `eq:toricPenvbig`:
`G_{P_θ[φ]} = G_{V_θ}` on `Δ(θ, φ)` and `+∞` outside. -/
theorem sourceSingularityEnvelope_spec (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    sourceSingularityEnvelope h.atlasForm u ∈ h.PSHTor ∧
      ∀ m, h.legendre (sourceSingularityEnvelope h.atlasForm u) m =
        if m ∈ h.newtonBody u then h.legendre h.minimalEnvelope m else ⊤ := by
  have heq : sourceSingularityEnvelope h.atlasForm u =
      uscSup (fun C : ℝ => h.shiftedRooftop u C) := by
    rw [sourceSingularityEnvelope_eq_uscSup_thetaRooftop]
    congr 1
    funext C
    exact (thetaRooftop_sourceMinimalEnvelope_eq_zero _ _).symm
  have hmem : ∀ C : ℝ, h.shiftedRooftop u C ∈ h.PSHTor :=
    fun C => (h.shiftedRooftop_spec hP hu C).2.1
  have hbd : ∀ (C : ℝ) p, h.shiftedRooftop u C p ≤ ((0 : ℝ) : EReal) := by
    intro C p
    have h1 := thetaRooftop_le_right h.atlasForm (fun q => u q + (C : EReal)) h.minimalEnvelope p
    exact h1.trans (by simpa using sourceMinimalEnvelope_le_zero h.atlasForm p)
  refine ⟨by rw [heq]; exact h.mem_PSHTor_uscSup hP hmem hbd, ?_⟩
  have hGu := h.legendre_mem_closedProperOnBody hP hu
  have hDP : effectiveDomain (h.legendre u) ⊆ toricDivisorPolytope D := by
    intro m hm
    by_contra hmP
    exact (ne_of_lt hm) (hGu.2.2 m hmP)
  have hclP : closure (effectiveDomain (h.legendre u)) ⊆ toricDivisorPolytope D :=
    closure_minimal hDP (isCompact_toricDivisorPolytope D).isClosed
  have hinf := iInf_max_sub_realReference h.minimalLegendreReal (h.legendre u)
  have hGV := h.legendre_mem_closedProperOnBody hP (h.minimalEnvelope_mem hP)
  have hconv : IsConvex (realReferenceOnDomain h.minimalLegendreReal
      (effectiveDomain (h.legendre u))) := by
    have hepi : epigraph (realReferenceOnDomain h.minimalLegendreReal
        (effectiveDomain (h.legendre u))) =
        epigraph (h.legendre h.minimalEnvelope) ∩
          (effectiveDomain (h.legendre u) ×ˢ (univ : Set ℝ)) := by
      ext p
      by_cases hp : p.1 ∈ effectiveDomain (h.legendre u)
      · simp [epigraph, realReferenceOnDomain, hp,
          h.legendre_minimalEnvelope_eq_real hP (hDP hp)]
      · simp [epigraph, realReferenceOnDomain, hp]
    change Convex ℝ (epigraph _)
    rw [hepi]
    exact hGV.1.1.inter ((convex_effectiveDomain hGu.1.1).prod convex_univ)
  have hclosure : convexClosure (realReferenceOnDomain h.minimalLegendreReal
      (effectiveDomain (h.legendre u))) =
      realReferenceOnDomain h.minimalLegendreReal
        (closure (effectiveDomain (h.legendre u))) := by
    rw [convexClosure_of_forall_ne_bot]
    · exact regularization_realReferenceOnDomain _ _
        ((h.continuousOn_minimalLegendreReal hP).mono hclP)
    · intro x
      by_cases hx : x ∈ effectiveDomain (h.legendre u) <;>
        simp [realReferenceOnDomain, hx]
  intro m
  rw [heq, h.legendre_uscSup hP hmem hbd, h.iInf_shifted_legendre hP hu]
  change convexClosure (lowerConvexEnvelope (fun m => ⨅ C : ℝ,
    max (h.minimalLegendreReal m : EReal) (h.legendre u m - (C : EReal)))) m = _
  rw [hinf, lowerConvexEnvelope_eq_self hconv, hclosure,
    h.newtonBody_eq_closure_effectiveDomain hP hu]
  by_cases hm : m ∈ closure (effectiveDomain (h.legendre u))
  · have hmP : m ∈ toricDivisorPolytope D := hclP hm
    have hmΔ : m ∈ convexNewtonBody (h.legendre u) := hm
    simp only [realReferenceOnDomain, if_pos hm, if_pos hmΔ,
      h.legendre_minimalEnvelope_eq_real hP hmP]
  · have hmΔ : m ∉ convexNewtonBody (h.legendre u) := hm
    simp only [realReferenceOnDomain, if_neg hm, if_neg hmΔ]

end BigToricMetric

end SGPT.Toric
