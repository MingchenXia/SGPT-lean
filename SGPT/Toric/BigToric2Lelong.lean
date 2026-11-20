import SGPT.Toric.BigToric2Orbits
import SGPT.PSH.SourceGenericLelong

/-!
# Generic Lelong numbers of toric potentials along toric strata

Source `chapter_toric_big.tex`, section `sec:toricpob`: `cor:toricLelong`
(`ν(φ, D_ρ) = inf {⟨m - m_ρ, u_ρ⟩ : m ∈ Δ(θ, φ)}`) and `cor:toricLelong2`
(`ν(φ, V(σ)) = 0 ⇔ Δ(θ, φ) meets the face Q_σ`).

The source deduces `cor:toricLelong` from `thm:toricpob` (partial Okounkov bodies) and
`thm:nuOk`, and `cor:toricLelong2` from a toric blow-up.  Here both are proved directly from
the convex description of toric potentials: in the vertex chart `U_v ≅ ℂ^n` with coordinates
`z_i = χ^{b_i(v)}`, a toric `θ`-psh function is `φ = F_φ(x) - ⟨m_v, x⟩ - ψ_v` on the torus, where
`x = ∑_i log|z_i|² u_i(v)` and `ψ_v` is the smooth weight of `h`; hence
`F_φ ≤ Supp_{Δ(θ,φ)} + C` and `⟨m - m_v, u_i(v)⟩ ≥ 0` on `Δ(θ, φ) ⊆ P_D` give the upper bound
`φ ≤ ∑_{i ∈ J} c_i log|z_i|² + C`, and the Fenchel–Young inequality
`F_φ(x) ≥ ⟨x, m⟩ - G_φ(m)` gives the lower bound along the rays.  The generic Lelong number is the
book's `ν(φ, Y) = inf_{y ∈ Y} ν(φ, y)` (`sourceGenericLelong`, with the squared-log normalization
`ν(log|z|², 0) = 1` of `sourceLelong`).

The positive mass hypothesis `φ ∈ PSH_tor(X, θ)_{>0}` of the source is not needed.

## Main results

* `BigToricMetric.sourceGenericLelong_toricPrimeDivisor`: source `cor:toricLelong`;
* `BigToricMetric.sourceGenericLelong_toricOrbitClosure`: the generic Lelong number along
  `V(σ)` is `inf {⟨m - m_σ, ∑_{ρ ∈ σ(1)} u_ρ⟩ : m ∈ Δ(θ, φ)}` (`eq:nuvarphiYtoric1`);
* `BigToricMetric.sourceGenericLelong_toricOrbitClosure_eq_zero_iff`: source `cor:toricLelong2`;
* `BigToricMetric.sum_sourceGenericLelong_le`: `ν(φ, V(σ)) ≥ ∑_{ρ ∈ σ(1)} ν(φ, D_ρ)` (the
  remark after `cor:toricLelong2`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators ENNReal NNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

theorem latticeBasisLogMap_logInverse (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (y : EuclideanSpace ℝ (Fin n)) :
    latticeBasisLogMap b (latticeBasisLogInverse b y) = y := by
  have hleft : latticeBasisLogInverse b * latticeBasisLogMap b = 1 :=
    LinearMap.ext (latticeBasisLogInverse_logMap b)
  have hright := mul_eq_one_comm.mp hleft
  exact LinearMap.congr_fun hright y

variable (hs) in
/-- `⟨b_i(v), ∑_k y_k u_k(v)⟩ = y_i`. -/
theorem latticeFunctional_basis_logInverse (v : latticePolytopeVertices γ)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    latticeFunctional (originalPolytopeNativeBasis γ hs v i)
      (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) = y i := by
  have := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i)
    (latticeBasisLogMap_logInverse (originalPolytopeNativeBasis γ hs v) y)
  simpa only [latticeBasisLogMap_apply, latticeFunctional_apply] using this

variable (D : ToricDivisor γ hs)

/-- The slack `⟨m - m_v, u_i(v)⟩` of `m ∈ M_ℝ` along the ray `u_i(v)` of `σ_v`. -/
def cartierSlack (v : latticePolytopeVertices γ) (i : Fin n) (m : EuclideanSpace ℝ (Fin n)) : ℝ :=
  latticeFunctional (polytopeToricRayGenerator γ hs v i) m -
    intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v i)

/-- `⟨m - m_v, u_i(v)⟩ = ⟨m, u_ρ⟩ + a_ρ` for `ρ = u_i(v)`. -/
theorem cartierSlack_eq (v : latticePolytopeVertices γ) (i : Fin n) (m : EuclideanSpace ℝ (Fin n)) :
    cartierSlack D v i m = latticeFunctional (polytopeToricRayGenerator γ hs v i) m +
      D (polytopeToricRay γ hs v i) := by
  rw [cartierSlack, toricCartierDatum_pairing]; push_cast; ring

theorem cartierSlack_nonneg (v : latticePolytopeVertices γ) (i : Fin n)
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ toricDivisorPolytope D) : 0 ≤ cartierSlack D v i m := by
  have h := toricDivisorPolytope_sub_cartier_nonneg D v hm i
  rw [latticeFunctional_latticeVector, intPairing_comm] at h
  exact h

theorem continuous_cartierSlack (v : latticePolytopeVertices γ) (i : Fin n) :
    Continuous (cartierSlack D v i) :=
  (LinearMap.continuous_of_finiteDimensional _).sub continuous_const

/-- `⟨x, m⟩ - ⟨m_v, x⟩ = ∑_i ⟨b_i(v), x⟩ ⟨m - m_v, u_i(v)⟩`. -/
theorem inner_sub_cartier_eq_sum (v : latticePolytopeVertices γ) (x m : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x m - latticeFunctional (toricCartierDatum D v) x =
      ∑ i, latticeFunctional (originalPolytopeNativeBasis γ hs v i) x * cartierSlack D v i m := by
  rw [real_inner_comm, inner_eq_sum_basis hs v m x, latticeFunctional_eq_sum_basis hs v _ x,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cartierSlack]; ring

/-- The rays of a maximal cone are distinct. -/
theorem polytopeToricRayGenerator_injective (v : latticePolytopeVertices γ) :
    Function.Injective (polytopeToricRayGenerator γ hs v) := by
  intro i j hij
  by_contra hne
  have h1 := intPairing_basis_rayGenerator γ hs v i i
  have h2 := intPairing_basis_rayGenerator γ hs v i j
  rw [if_pos rfl] at h1
  rw [if_neg hne, ← hij] at h2
  omega

namespace BigToricMetric

variable {D} (h : BigToricMetric D)

/-- In the vertex chart `U_v`, on the torus, `φ = F_φ(x) - ⟨m_v, x⟩ - ψ_v` with
`x = ∑_i log|z_i|² u_i(v)`. -/
theorem chart_symm_eq {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    u ((originalPolytopeNativeModelChart γ hs v).symm z) =
      ((h.realProfile u (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v)
          (tropicalization z)) -
        latticeFunctional (toricCartierDatum D v) (latticeBasisLogInverse
          (originalPolytopeNativeBasis γ hs v) (tropicalization z)) - h.weight v z : ℝ) : EReal) := by
  have h1 := h.vertexChart_corrected_eq (fun a => hu.2.embedding_eq γ hs a) v hz
  rw [tropicalPullback, (h.realProfile_mem hu).2, ← EReal.coe_add] at h1
  rw [EReal.eq_coe_sub_of_add_coe_eq h1]
  ring_nf

/-- `F_φ ≤ Supp_{Δ(θ,φ)} + F_φ(0)`. -/
theorem realProfile_le_of_forall_inner_le
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) (x : EuclideanSpace ℝ (Fin n))
    {A : ℝ} (hA : ∀ m ∈ h.newtonBody u, inner ℝ x m ≤ A) :
    h.realProfile u x ≤ A + h.realProfile u 0 := by
  have hmem := h.realProfile_mem hu
  have hproper : IsProper (h.profile u) := by
    rw [hmem.2]; exact isProper_coe_of_convexOn hmem.1.1
  have hdom : effectiveDomain (h.profile u) = univ := by
    rw [hmem.2]; ext y; simp [effectiveDomain]
  have hle := le_support_add_zero_of_full_domain_rawSubgradientImage_subset
    (innerₗ (EuclideanSpace ℝ (Fin n))) hproper hdom (subset_closure (s := rawSubgradientImage
      (innerₗ (EuclideanSpace ℝ (Fin n))) (h.profile u))) x
  have hsupp : support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody u) x ≤ (A : EReal) := by
    apply iSup_le
    intro m
    exact EReal.coe_le_coe_iff.mpr (hA m.val m.property)
  have h2 : h.profile u x ≤ (A : EReal) + h.profile u 0 :=
    hle.trans (add_le_add hsupp le_rfl)
  rw [hmem.2, ← EReal.coe_add] at h2
  exact EReal.coe_le_coe_iff.mp h2

/-- The Fenchel–Young inequality `F_φ(x) ≥ ⟨x, m⟩ - G_φ(m)`. -/
theorem inner_sub_legendre_le_realProfile (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) {m : EuclideanSpace ℝ (Fin n)}
    (hm : h.legendre u m ≠ ⊤) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x m - (h.legendre u m).toReal ≤ h.realProfile u x := by
  have hG := h.legendre_mem_closedProperOnBody hP hu
  have hbot : h.legendre u m ≠ ⊥ := hG.1.2.2 m
  have hle : ((inner ℝ x m : ℝ) : EReal) - h.profile u x ≤ h.legendre u m :=
    le_iSup (fun y => (((innerₗ (EuclideanSpace ℝ (Fin n))) y m : ℝ) : EReal) - h.profile u y) x
  rw [(h.realProfile_mem hu).2, ← EReal.coe_toReal hm hbot, ← EReal.coe_sub] at hle
  have := EReal.coe_le_coe_iff.mp hle
  linarith

/-- Upper bound of a toric potential near a point `z₀` of the coordinate subspace
`{z_j = 0, j ∈ J}` of the chart `U_v`: if `c ≤ ∑_{j ∈ J} ⟨m - m_v, u_j(v)⟩` on `Δ(θ, φ)`, then
`φ ≤ c log ‖z - z₀‖² + C` on the punctured unit ball around `z₀`. -/
theorem exists_le_log_near {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Finset (Fin n)) {z₀ : ComplexModel n}
    (hz₀ : ∀ j ∈ J, z₀ j = 0) {c : ℝ}
    (hc : ∀ m ∈ h.newtonBody u, c ≤ ∑ j ∈ J, cartierSlack D v j m) :
    ∃ C : ℝ, ∀ z, z ≠ z₀ → z ∈ Metric.ball z₀ 1 →
      u ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
        ((c * Real.log (‖z - z₀‖ ^ 2) + C : ℝ) : EReal) := by
  classical
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨-, hcomp, -, hsub⟩ := h.newtonBody_properties hP hu
  -- a bound for the slacks on `Δ(θ, φ)`
  obtain ⟨E, hE0, hEb⟩ : ∃ E : ℝ, 0 ≤ E ∧ ∀ m ∈ h.newtonBody u, ∀ i, cartierSlack D v i m ≤ E := by
    choose E hE using fun i => hcomp.bddAbove_image (continuous_cartierSlack D v i).continuousOn
    refine ⟨∑ i, |E i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), fun m hm i => ?_⟩
    exact (hE i ⟨m, hm, rfl⟩).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |E j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  -- a bound for the weight
  obtain ⟨Ψ, hΨ⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    (h.smooth v).continuous.continuousOn
  set Y : ℝ := 2 * Real.log (‖z₀‖ + 1)
  have hY0 : 0 ≤ Y := by
    have := Real.log_nonneg (by linarith [norm_nonneg z₀] : (1 : ℝ) ≤ ‖z₀‖ + 1)
    simp only [Y]; linarith
  set C : ℝ := (n : ℝ) * (Y * E) + h.realProfile u 0 + Ψ
  set e := originalPolytopeNativeModelChart γ hs v
  have htorus : ∀ z ∈ complexTorus n, z ≠ z₀ → z ∈ Metric.ball z₀ 1 →
      u (e.symm z) ≤ ((c * Real.log (‖z - z₀‖ ^ 2) + C : ℝ) : EReal) := by
    intro z hz hzz hzb
    rw [h.chart_symm_eq hu v hz]
    apply EReal.coe_le_coe_iff.mpr
    set y := tropicalization z
    set x := latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y
    set L := Real.log (‖z - z₀‖ ^ 2)
    have hd : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
    have hd1 : ‖z - z₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hzb
    have hL : L ≤ 0 := Real.log_nonpos (sq_nonneg _) (by nlinarith)
    have hyi : ∀ i, latticeFunctional (originalPolytopeNativeBasis γ hs v i) x = y i :=
      latticeFunctional_basis_logInverse hs v y
    have hzi : ∀ i, 0 < ‖z i‖ := fun i => norm_pos_iff.mpr (hz i)
    have hyY : ∀ i, y i ≤ Y := by
      intro i
      rw [tropicalization_apply_eq_log_norm_sq, Real.log_pow]
      have h1 : ‖z i‖ ≤ ‖z₀‖ + 1 := by
        calc ‖z i‖ ≤ ‖z‖ := PiLp.norm_apply_le z i
          _ ≤ ‖z₀‖ + ‖z - z₀‖ := by
              have := norm_add_le z₀ (z - z₀); rwa [add_sub_cancel] at this
          _ ≤ ‖z₀‖ + 1 := by linarith
      have := Real.log_le_log (hzi i) h1
      push_cast; simp only [Y]; linarith
    have hyL : ∀ i ∈ J, y i ≤ L := by
      intro i hi
      rw [tropicalization_apply_eq_log_norm_sq]
      apply Real.log_le_log (pow_pos (hzi i) 2)
      have : ‖z i‖ ≤ ‖z - z₀‖ := by
        have h1 := PiLp.norm_apply_le (z - z₀) i
        rwa [PiLp.sub_apply, hz₀ i hi, sub_zero] at h1
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hbound : ∀ m ∈ h.newtonBody u, inner ℝ x m ≤
        latticeFunctional (toricCartierDatum D v) x + (c * L + (n : ℝ) * (Y * E)) := by
      intro m hm
      have hsum := inner_sub_cartier_eq_sum D v x m
      simp only [hyi] at hsum
      have hterm : ∀ i, y i * cartierSlack D v i m ≤
          (if i ∈ J then L * cartierSlack D v i m else 0) + Y * E := by
        intro i
        have hs0 := cartierSlack_nonneg D v i (hsub hm)
        have hsE := hEb m hm i
        by_cases hi : i ∈ J
        · rw [if_pos hi]
          have := mul_le_mul_of_nonneg_right (hyL i hi) hs0
          nlinarith [mul_nonneg hY0 hE0]
        · rw [if_neg hi, zero_add]
          calc y i * cartierSlack D v i m ≤ Y * cartierSlack D v i m :=
                mul_le_mul_of_nonneg_right (hyY i) hs0
            _ ≤ Y * E := mul_le_mul_of_nonneg_left hsE hY0
      have h2 : ∑ i, y i * cartierSlack D v i m ≤
          L * ∑ j ∈ J, cartierSlack D v j m + (n : ℝ) * (Y * E) := by
        calc ∑ i, y i * cartierSlack D v i m ≤
              ∑ i, ((if i ∈ J then L * cartierSlack D v i m else 0) + Y * E) :=
              Finset.sum_le_sum fun i _ => hterm i
          _ = L * ∑ j ∈ J, cartierSlack D v j m + (n : ℝ) * (Y * E) := by
              rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
              simp
      have h3 : L * ∑ j ∈ J, cartierSlack D v j m ≤ c * L := by
        rw [mul_comm c L]
        exact mul_le_mul_of_nonpos_left (hc m hm) hL
      linarith
    have hR := h.realProfile_le_of_forall_inner_le hu x hbound
    have hψ : -Ψ ≤ h.weight v z := by
      have := hΨ z (Metric.mem_closedBall.mpr (le_of_lt (by rwa [Metric.mem_ball] at hzb)))
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (h.weight v z)]
    simp only [C]
    linarith
  refine ⟨C, fun z hzz hzb => ?_⟩
  -- extension across the boundary: `φ` is the upper regularization of its torus values
  have hsrc : e.symm z ∈ e.source := e.map_target
    (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ z)
  have hright : e (e.symm z) = z := e.right_inv
    (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ z)
  rw [congrFun (h.eq_analyticExtension hu.1) (e.symm z), analyticExtension]
  set g : PolytopeToricVariety γ hs → EReal := fun q =>
    ((c * Real.log (‖e q - z₀‖ ^ 2) + C : ℝ) : EReal)
  have hgz : g (e.symm z) = ((c * Real.log (‖z - z₀‖ ^ 2) + C : ℝ) : EReal) := by
    simp only [g, hright]
  rw [← hgz]
  apply SGPT.Foundations.Analysis.FirstPass.uscRegularization_le_of_eventually_le
  · apply ContinuousAt.upperSemicontinuousAt
    apply continuous_coe_real_ereal.continuousAt.comp
    have hne : ‖e (e.symm z) - z₀‖ ^ 2 ≠ 0 := by
      rw [hright]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzz))
    apply ContinuousAt.add _ continuousAt_const
    apply continuousAt_const.mul
    exact ContinuousAt.log (((e.continuousAt hsrc).sub continuousAt_const).norm.pow 2) hne
  · have hO : IsOpen (e.source ∩ e ⁻¹' ({w | w ≠ z₀} ∩ Metric.ball z₀ 1)) :=
      e.isOpen_inter_preimage (isOpen_ne.inter Metric.isOpen_ball)
    have hmem : e.symm z ∈ e.source ∩ e ⁻¹' ({w | w ≠ z₀} ∩ Metric.ball z₀ 1) := by
      refine ⟨hsrc, ?_⟩
      rw [Set.mem_preimage, hright]; exact ⟨hzz, hzb⟩
    filter_upwards [hO.mem_nhds hmem] with q ⟨hqs, hqne, hqb⟩
    by_cases hqB : q ∈ polytopeToricBoundary γ hs
    · simp [hqB]
    · simp only [hqB, if_false]
      have hleft : e.symm (e q) = q := e.left_inv hqs
      have hqT : e q ∈ complexTorus n := by
        apply (polytopeToricVertexChart_symm_mem_compl_iff γ hs v (e q)).mp
        rw [hleft]; exact hqB
      have := htorus (e q) hqT hqne hqb
      rwa [hleft] at this

/-- The coordinates `z₀ = (0 on J, 1 off J)` of the generic point of `V(σ)` in the chart `U_v`. -/
def genericChartPoint (J : Finset (Fin n)) : ComplexModel n :=
  modelPoint fun i => if i ∈ J then 0 else 1

/-- Lower bound for the Lelong number at the generic point of `V(σ)` (Fenchel–Young along the
curve `t ↦ (t on J, 1 + t off J)`): if `φ ≤ γ log ‖z - z₀‖² + C` near `z₀`, then
`γ ≤ ∑_{j ∈ J} ⟨m - m_v, u_j(v)⟩` for every `m` with `G_φ(m) < ∞`. -/
theorem le_sum_cartierSlack_of_bound {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (hn : n ≠ 0) {J : Finset (Fin n)} {γ' C : ℝ}
    (hev : ∀ᶠ z in 𝓝[≠] genericChartPoint J,
      u ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
        ((γ' * Real.log (‖z - genericChartPoint J‖ ^ 2) + C : ℝ) : EReal))
    {m : EuclideanSpace ℝ (Fin n)} (hm : h.legendre u m ≠ ⊤) :
    γ' ≤ ∑ j ∈ J, cartierSlack D v j m := by
  classical
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  set z₀ := genericChartPoint (n := n) J
  set e := originalPolytopeNativeModelChart γ hs v
  let zt : ℝ → ComplexModel n := fun t => modelPoint fun i => if i ∈ J then (t : ℂ) else 1 + t
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hcard : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hdiff : ∀ t : ℝ, ∀ i, (zt t - z₀) i = (t : ℂ) := by
    intro t i
    simp only [zt, z₀, genericChartPoint, PiLp.sub_apply, modelPoint_apply]
    split_ifs <;> ring
  have hnorm : ∀ t : ℝ, ‖zt t - z₀‖ ^ 2 = n * t ^ 2 := by
    intro t
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hdiff, Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcont : Continuous zt := by
    apply continuous_modelPoint.comp
    apply continuous_pi
    intro i
    by_cases hi : i ∈ J
    · simp only [hi, if_true]; exact Complex.continuous_ofReal
    · simp only [hi, if_false]; exact continuous_const.add Complex.continuous_ofReal
  have hzt0 : zt 0 = z₀ := by
    ext i; simp only [zt, z₀, genericChartPoint, modelPoint_apply]; split_ifs <;> simp
  have htend : Tendsto zt (𝓝[>] 0) (𝓝[≠] z₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have := hcont.tendsto 0
      rw [hzt0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro heq
      have := hdiff t i₀
      rw [heq, sub_self, PiLp.zero_apply] at this
      exact (ne_of_gt (show (0 : ℝ) < t from ht)) (Complex.ofReal_eq_zero.mp this.symm)
  have hev' := htend.eventually hev
  -- the weight is bounded along the curve
  obtain ⟨Ψ, hΨ⟩ := (isCompact_closedBall z₀ (n : ℝ)).exists_bound_of_continuousOn
    (h.smooth v).continuous.continuousOn
  set G := (h.legendre u m).toReal
  set S := ∑ j ∈ J, cartierSlack D v j m
  set S' := ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), cartierSlack D v i m
  set K₀ := C + G + Ψ + γ' * Real.log n + Real.log 4 * |S'|
  by_contra hlt
  push Not at hlt
  set δ := γ' - S
  have hδ : 0 < δ := by simp only [δ]; linarith
  set M := -(|K₀| + 1) / δ
  have hlog := (Real.tendsto_log_nhdsGT_zero).eventually (eventually_lt_atBot (M / 2))
  obtain ⟨t, ⟨⟨hb, ht1⟩, hlogt⟩, htpos⟩ := (((hev'.and
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))).and
    hlog).and (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0)).exists
  have htpos' : (0 : ℝ) < t := htpos
  set s := Real.log (t ^ 2)
  set s' := Real.log ((1 + t) ^ 2)
  have hs'0 : 0 ≤ s' := Real.log_nonneg (by nlinarith)
  have hs'4 : s' ≤ Real.log 4 := Real.log_le_log (by positivity) (by nlinarith)
  have hT : zt t ∈ complexTorus n := by
    intro i
    simp only [zt, modelPoint_apply]
    split_ifs
    · exact_mod_cast htpos'.ne'
    · exact_mod_cast (show (1 + t : ℝ) ≠ 0 by linarith)
  have htrop : ∀ i, tropicalization (zt t) i = if i ∈ J then s else s' := by
    intro i
    rw [tropicalization_apply_eq_log_norm_sq]
    simp only [zt, modelPoint_apply]
    split_ifs
    · simp [s, Complex.norm_real, sq_abs]
    · have : ((1 : ℂ) + (t : ℂ)) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  set x := latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization (zt t))
  have hinner : inner ℝ x m - latticeFunctional (toricCartierDatum D v) x = s * S + s' * S' := by
    rw [inner_sub_cartier_eq_sum D v x m]
    have hxi : ∀ i, latticeFunctional (originalPolytopeNativeBasis γ hs v i) x =
        if i ∈ J then s else s' := fun i => by
      rw [latticeFunctional_basis_logInverse hs v, htrop]
    simp only [hxi]
    have hite : ∀ i, (if i ∈ J then s else s') * cartierSlack D v i m =
        if i ∈ J then s * cartierSlack D v i m else s' * cartierSlack D v i m := fun i => by
      split_ifs <;> rfl
    simp only [hite]
    rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum,
      Finset.mul_sum]
  have hFY := h.inner_sub_legendre_le_realProfile hP hu hm x
  have hψ : h.weight v (zt t) ≤ Ψ := by
    have hmem : zt t ∈ Metric.closedBall z₀ (n : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖zt t - z₀‖ ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [hnorm]
        have : t ^ 2 ≤ 1 := by nlinarith
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
    have := hΨ _ hmem
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hS' : -(Real.log 4 * |S'|) ≤ s' * S' := by
    have h1 : |s' * S'| ≤ Real.log 4 * |S'| := by
      rw [abs_mul, abs_of_nonneg hs'0]
      exact mul_le_mul_of_nonneg_right hs'4 (abs_nonneg _)
    linarith [neg_abs_le (s' * S')]
  rw [h.chart_symm_eq hu v hT, hnorm] at hb
  have hb' := EReal.coe_le_coe_iff.mp hb
  have hlogs : Real.log (n * t ^ 2) = Real.log n + s :=
    Real.log_mul (by positivity) (by positivity)
  rw [hlogs] at hb'
  have hs : s < M := by
    have : s = 2 * Real.log t := by simp only [s]; rw [Real.log_pow]; push_cast; ring
    rw [this]; linarith
  have hkey : -s * δ ≤ K₀ := by
    simp only [K₀, δ]
    nlinarith
  have hMδ : M * δ = -(|K₀| + 1) := by simp only [M]; field_simp
  have : -s * δ > |K₀| + 1 := by
    have := mul_lt_mul_of_pos_right hs hδ
    linarith
  linarith [le_abs_self K₀]

/-- Lower bound for the Lelong number at a point of the coordinate subspace
`{z_j = 0, j ∈ J}` of the chart `U_v`. -/
theorem ofReal_le_sourceLelong {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Finset (Fin n)) {q : PolytopeToricVariety γ hs}
    (hq : q ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hqJ : ∀ j ∈ J, originalPolytopeNativeModelChart γ hs v q j = 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ m ∈ h.newtonBody u, c ≤ ∑ j ∈ J, cartierSlack D v j m) :
    ENNReal.ofReal c ≤ (ofFixedModel n (PolytopeToricVariety γ hs)).sourceLelong u q := by
  rcases hc0.eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero]; exact bot_le
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨⟨m, hm⟩, -, -, -⟩ := h.newtonBody_properties hP hu
  have hJ : J.Nonempty := by
    by_contra hJ
    rw [Finset.not_nonempty_iff_eq_empty] at hJ
    have := hc m hm
    rw [hJ, Finset.sum_empty] at this
    linarith
  obtain ⟨j₀, -⟩ := hJ
  have hn : n ≠ 0 := by have := j₀.pos; omega
  set e := originalPolytopeNativeModelChart γ hs v
  obtain ⟨C, hC⟩ := h.exists_le_log_near hu v J hqJ hc
  rw [sourceLelong_eq_growth_sup _ u q (polytopeToricVertexChart γ hs v) hq hn]
  rw [ENNReal.ofReal_eq_coe_nnreal hc0]
  refine le_iSup₂_of_le (⟨c, hc0⟩ : ℝ≥0) ⟨C, ?_⟩ le_rfl
  change ∀ᶠ z in 𝓝[≠] (e q), u (e.symm z) ≤ ((c * Real.log (‖z - e q‖ ^ 2) + C : ℝ) : EReal)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (e q) one_pos)]
    with z hz hzb
  exact hC z hz hzb

/-- Upper bound for the Lelong number at the generic point of the stratum `{z_j = 0, j ∈ J}` of
the chart `U_v`. -/
theorem sourceLelong_genericPoint_le {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (hn : n ≠ 0) (J : Finset (Fin n))
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ h.newtonBody u) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).sourceLelong u
        ((originalPolytopeNativeModelChart γ hs v).symm (genericChartPoint J)) ≤
      ENNReal.ofReal (∑ j ∈ J, cartierSlack D v j m) := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  set e := originalPolytopeNativeModelChart γ hs v
  have hsrc : e.symm (genericChartPoint J) ∈ e.source := e.map_target
    (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)
  have hright : e (e.symm (genericChartPoint J)) = genericChartPoint J := e.right_inv
    (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)
  rw [sourceLelong_eq_growth_sup _ u _ (polytopeToricVertexChart γ hs v) hsrc hn]
  refine iSup₂_le fun γ' ⟨C, hev⟩ => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  change ∀ᶠ z in 𝓝[≠] (e (e.symm (genericChartPoint J))), u (e.symm z) ≤
    (((γ' : ℝ) * Real.log (‖z - e (e.symm (genericChartPoint J))‖ ^ 2) + C : ℝ) : EReal) at hev
  rw [hright] at hev
  have hdom : effectiveDomain (h.legendre u) ⊆ {m | (γ' : ℝ) ≤ ∑ j ∈ J, cartierSlack D v j m} :=
    fun m hm => h.le_sum_cartierSlack_of_bound hu v hn hev (ne_of_lt hm)
  have hclosed : IsClosed {m : EuclideanSpace ℝ (Fin n) |
      (γ' : ℝ) ≤ ∑ j ∈ J, cartierSlack D v j m} :=
    isClosed_le continuous_const (continuous_finsetSum _ fun j _ => continuous_cartierSlack D v j)
  rw [h.newtonBody_eq_closure_effectiveDomain hP hu] at hm
  exact closure_minimal hdom hclosed hm

/-- The generic Lelong number of a toric potential along the toric subvariety `V(σ)`, `σ` the
cone of `Σ` spanned by the rays `u_j(v)`, `j ∈ J` (`σ = 0`, `V(σ) = X` for `J = ∅`):
`ν(φ, V(σ)) = inf {∑_{j ∈ J} ⟨m - m_v, u_j(v)⟩ : m ∈ Δ(θ, φ)}`, i.e.
`inf {⟨m - m_σ, ∑_{ρ ∈ σ(1)} u_ρ⟩ : m ∈ Δ(θ, φ)}` (source `eq:nuvarphiYtoric1`). -/
theorem sourceGenericLelong_toricOrbitClosure {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (v : latticePolytopeVertices γ) (J : Finset (Fin n)) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u
        (toricOrbitClosure (polytopeToricRay γ hs v '' (J : Set (Fin n)))) =
      ⨅ m ∈ h.newtonBody u, ENNReal.ofReal (∑ j ∈ J, cartierSlack D v j m) := by
  classical
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨hne, hcomp, -, hsub⟩ := h.newtonBody_properties hP hu
  set S : EuclideanSpace ℝ (Fin n) → ℝ := fun m => ∑ j ∈ J, cartierSlack D v j m
  have hScont : Continuous S := continuous_finsetSum _ fun j _ => continuous_cartierSlack D v j
  obtain ⟨m₀, hm₀, hmin⟩ := hcomp.exists_isMinOn hne hScont.continuousOn
  have hc0 : 0 ≤ S m₀ :=
    Finset.sum_nonneg fun j _ => cartierSlack_nonneg D v j (hsub hm₀)
  have hRHS : (⨅ m ∈ h.newtonBody u, ENNReal.ofReal (S m)) = ENNReal.ofReal (S m₀) :=
    le_antisymm (iInf₂_le m₀ hm₀) (le_iInf₂ fun m hm => ENNReal.ofReal_le_ofReal (hmin hm))
  change _ = ⨅ m ∈ h.newtonBody u, ENNReal.ofReal (S m)
  rw [hRHS]
  apply le_antisymm
  · -- the generic point of `V(σ)` in `U_v`
    set e := originalPolytopeNativeModelChart γ hs v
    have hsrc : e.symm (genericChartPoint J) ∈ e.source := e.map_target
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)
    have hright : e (e.symm (genericChartPoint J)) = genericChartPoint J := e.right_inv
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)
    have hmem : e.symm (genericChartPoint J) ∈
        toricOrbitClosure (polytopeToricRay γ hs v '' (J : Set (Fin n))) := by
      refine (mem_toricOrbitClosure_iff_chart hsrc).mpr ?_
      rintro ρ ⟨j, hj, rfl⟩
      refine ⟨j, rfl, ?_⟩
      rw [hright]
      simp [genericChartPoint, Finset.mem_coe.mp hj]
    refine (iInf₂_le _ hmem).trans ?_
    by_cases hn : n = 0
    · rw [sourceLelong_eq_chart _ u _ (polytopeToricVertexChart γ hs v) hsrc]
      unfold SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization.squaredLogLelongNumber
      split_ifs with h0
      · exact bot_le
      · exact absurd hn h0
    · exact h.sourceLelong_genericPoint_le hu v hn J hm₀
  · refine le_iInf₂ fun q hq => ?_
    obtain ⟨w, hw⟩ := originalPolytopeNativeModelChart_cover γ hs q
    have hq' := (mem_toricOrbitClosure_iff_chart hw).mp hq
    have hex : ∀ j ∈ J, ∃ i, polytopeToricRayGenerator γ hs w i = polytopeToricRayGenerator γ hs v j ∧
        originalPolytopeNativeModelChart γ hs w q i = 0 := fun j hj =>
      hq' (polytopeToricRay γ hs v j) ⟨j, hj, rfl⟩
    choose! f hf using hex
    have hinj : Set.InjOn f J := by
      intro j hj j' hj' hjj
      apply polytopeToricRayGenerator_injective (hs := hs) v
      rw [← (hf j hj).1, ← (hf j' hj').1, hjj]
    have hsum : ∀ m, ∑ i ∈ J.image f, cartierSlack D w i m = S m := by
      intro m
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hray : polytopeToricRay γ hs w (f j) = polytopeToricRay γ hs v j :=
        Subtype.ext (hf j hj).1
      rw [cartierSlack_eq, cartierSlack_eq, hray, (hf j hj).1]
    apply h.ofReal_le_sourceLelong hu w (J.image f) hw _ hc0
    · intro m hm
      rw [hsum]; exact hmin hm
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact (hf j hj).2

/-- Source `cor:toricLelong`: for a toric potential `φ ∈ PSH_tor(X, θ)` and the torus-invariant
prime divisor `E = D_ρ`, `ν(φ, E) = inf {⟨m - m_ρ, u_ρ⟩ : m ∈ Δ(θ, φ)}`; here
`⟨m - m_ρ, u_ρ⟩ = ⟨m, u_ρ⟩ + a_ρ` (`cartierSlack_eq`). The positive mass hypothesis is not
needed. -/
theorem sourceGenericLelong_toricPrimeDivisor {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (ρ : PolytopeToricRays γ hs) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u (toricPrimeDivisor ρ) =
      ⨅ m ∈ h.newtonBody u, ENNReal.ofReal (latticeFunctional ρ.val m + D ρ) := by
  obtain ⟨v, j, hvj⟩ := ρ.property
  have hρ : ρ = polytopeToricRay γ hs v j := Subtype.ext hvj.symm
  subst hρ
  have hset : toricOrbitClosure (polytopeToricRay γ hs v '' ((({j} : Finset (Fin n)) : Set (Fin n)))) =
      toricPrimeDivisor (polytopeToricRay γ hs v j) := by
    simp [toricOrbitClosure]
  rw [← hset, h.sourceGenericLelong_toricOrbitClosure hu v {j}]
  simp only [Finset.sum_singleton, cartierSlack_eq]
  rfl

/-- Source `cor:toricLelong2`: for the toric subvariety `Y = V(σ)` of a cone `σ ∈ Σ`
(spanned by the rays `u_j(v)`, `j ∈ J`), the following are equivalent:
(1) `ν(φ, Y) = 0`;
(2) some `m ∈ Δ(θ, φ)` has `⟨m - m_ρ, u_ρ⟩ = 0` for all `ρ ∈ σ(1)`;
(3) `Δ(θ, φ) ∩ Q_σ ≠ ∅`, `Q_σ = {m ∈ P_D : ⟨m, u_ρ⟩ = -a_ρ ∀ ρ ∈ σ(1)}` (`eq:Qsigma`). -/
theorem sourceGenericLelong_toricOrbitClosure_eq_zero_tfae {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (v : latticePolytopeVertices γ) (J : Finset (Fin n)) :
    List.TFAE [
      (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u
        (toricOrbitClosure (polytopeToricRay γ hs v '' (J : Set (Fin n)))) = 0,
      ∃ m ∈ h.newtonBody u, ∀ j ∈ J, cartierSlack D v j m = 0,
      (h.newtonBody u ∩ {m ∈ toricDivisorPolytope D | ∀ ρ ∈ polytopeToricRay γ hs v '' (J : Set (Fin n)),
        latticeFunctional ρ.val m = -(D ρ : ℝ)}).Nonempty] := by
  classical
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨hne, hcomp, -, hsub⟩ := h.newtonBody_properties hP hu
  set S : EuclideanSpace ℝ (Fin n) → ℝ := fun m => ∑ j ∈ J, cartierSlack D v j m
  have hScont : Continuous S := continuous_finsetSum _ fun j _ => continuous_cartierSlack D v j
  obtain ⟨m₀, hm₀, hmin⟩ := hcomp.exists_isMinOn hne hScont.continuousOn
  have hnn : ∀ m ∈ h.newtonBody u, ∀ j, 0 ≤ cartierSlack D v j m :=
    fun m hm j => cartierSlack_nonneg D v j (hsub hm)
  have hval : (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u
      (toricOrbitClosure (polytopeToricRay γ hs v '' (J : Set (Fin n)))) = ENNReal.ofReal (S m₀) := by
    rw [h.sourceGenericLelong_toricOrbitClosure hu v J]
    exact le_antisymm (iInf₂_le m₀ hm₀) (le_iInf₂ fun m hm => ENNReal.ofReal_le_ofReal (hmin hm))
  tfae_have 1 → 2 := by
    intro h0
    rw [hval, ENNReal.ofReal_eq_zero] at h0
    refine ⟨m₀, hm₀, fun j hj => ?_⟩
    have hsum0 : S m₀ = 0 := le_antisymm h0 (Finset.sum_nonneg fun j _ => hnn m₀ hm₀ j)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn m₀ hm₀ j).mp hsum0 j hj
  tfae_have 2 → 1 := by
    rintro ⟨m, hm, hzero⟩
    rw [hval, ENNReal.ofReal_eq_zero]
    calc S m₀ ≤ S m := hmin hm
      _ = 0 := Finset.sum_eq_zero hzero
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨m, hm, hzero⟩
      refine ⟨m, hm, hsub hm, ?_⟩
      rintro ρ ⟨j, hj, rfl⟩
      have := hzero j hj
      rw [cartierSlack_eq] at this
      change latticeFunctional (polytopeToricRayGenerator γ hs v j) m = _
      linarith
    · rintro ⟨m, hm, -, hQ⟩
      refine ⟨m, hm, fun j hj => ?_⟩
      have := hQ (polytopeToricRay γ hs v j) ⟨j, hj, rfl⟩
      rw [cartierSlack_eq]
      change latticeFunctional (polytopeToricRayGenerator γ hs v j) m = _ at this
      linarith
  tfae_finish

/-- The remark after source `cor:toricLelong2`: `ν(φ, V(σ)) ≥ ∑_{ρ ∈ σ(1)} ν(φ, D_ρ)`. -/
theorem sum_sourceGenericLelong_le {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Finset (Fin n)) :
    ∑ j ∈ J, (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u
        (toricPrimeDivisor (polytopeToricRay γ hs v j)) ≤
      (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u
        (toricOrbitClosure (polytopeToricRay γ hs v '' (J : Set (Fin n)))) := by
  classical
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨hne, -, -, hsub⟩ := h.newtonBody_properties hP hu
  rw [h.sourceGenericLelong_toricOrbitClosure hu v J]
  refine le_iInf₂ fun m hm => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => cartierSlack_nonneg D v j (hsub hm)]
  apply Finset.sum_le_sum
  intro j _
  rw [h.sourceGenericLelong_toricPrimeDivisor hu]
  refine iInf₂_le_of_le m hm ?_
  rw [cartierSlack_eq]
  exact le_rfl

end BigToricMetric

end SGPT.Toric
