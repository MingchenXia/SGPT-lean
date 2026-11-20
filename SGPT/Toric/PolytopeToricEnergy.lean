import SGPT.Toric.PolytopeToricFullMass
import SGPT.Toric.GlobalTropicalLegendreEnergy
import SGPT.Convex.ConjugateTruncationLimit
import SGPT.Convex.ExtendedSignedIntegralUpperBound
import SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyDecreasing
import SGPT.Toric.GlobalTropicalFiniteEnergyConverse
import SGPT.PSH.SourceDarvasMetric

/-!
# The Monge–Ampère energy of a toric potential

Source `chapter_toric_ample.tex`, for `X = PolytopeToricVariety γ hs` (arbitrary Delzant
lattice polytope `P`, Kähler form `ω`, `V_ω = 0`):

* `prop:Etoric`: `E_ω(φ) = n! ∫_P (G_0 - G_φ) dvol` for every `φ ∈ PSH_tor(X, ω)`, the
  integral being the extended signed integral (`-∞` allowed);
* `cor:toric-ample:L1092`: `φ ∈ 𝓔^1(X, ω)` iff `F_φ ∈ 𝓔^1(N_ℝ, P)` iff `G_φ ∈ L^1(P)`;
* `cor:toricd1`: `d_1(φ, ψ) = n! ∫_P (2 (G_φ ∨ G_ψ) - G_φ - G_ψ) dvol` on `𝓔^1_tor`.

The proof follows the source: first `φ` in `𝓔^1` through the tropical chart energy identity
of the base vertex chart (transported to `M_ℝ` by the unimodular affine change of
coordinates), then `φ ≤ 0` through the canonical truncations `max(φ, -j)` and monotone
convergence of the Legendre gaps, and finally all `φ` by adding a constant.  A toric pole
function — the toric potential with linear profile `⟨m₀, ·⟩` for an interior point `m₀` of
`P` — is `-∞` along the toric boundary (since `F_0 - ⟨m₀,·⟩ ≥ r ‖·‖ - D`); it feeds the
tropical chart energy producers.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ContDiff BigOperators RealInnerProductSpace ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

include hs in
/-- An interior ball of the moment polytope. -/
theorem exists_closedBall_subset_polytopeToricMomentPolytope :
    ∃ (m₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧
      Metric.closedBall m₀ r ⊆ polytopeToricMomentPolytope γ := by
  obtain ⟨m₀, hm⟩ := interior_polytopeToricMomentPolytope_nonempty γ hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior m₀ hm
  exact ⟨m₀, ε / 2, by positivity,
    (Metric.closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)⟩

omit [Fintype K] [Nonempty K] in
/-- `Supp_P(x) ≥ ⟨m₀, x⟩ + r ‖x‖` when `B̄(m₀, r) ⊆ P`. -/
theorem support_ge_of_closedBall {m₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall m₀ r ⊆ polytopeToricMomentPolytope γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ((⟪m₀, x⟫ + r * ‖x‖ : ℝ) : EReal) ≤
      support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ) x := by
  let m := m₀ + (r / ‖x‖) • x
  have hm : m ∈ polytopeToricMomentPolytope γ := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, show m - m₀ = (r / ‖x‖) • x by simp [m], norm_smul,
      Real.norm_eq_abs, abs_div, abs_norm, abs_of_nonneg hr]
    by_cases hx : ‖x‖ = 0
    · rw [hx]; simp [hr]
    · rw [div_mul_cancel₀ _ hx]
  have hval : (innerₗ (EuclideanSpace ℝ (Fin n))).flip m x = ⟪m₀, x⟫ + r * ‖x‖ := by
    rw [LinearMap.flip_apply, innerₗ_apply_apply, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm]
    by_cases hx : ‖x‖ = 0
    · rw [hx]; simp
    · field_simp
  rw [← hval]
  exact le_iSup (fun m : polytopeToricMomentPolytope γ =>
    (((innerₗ (EuclideanSpace ℝ (Fin n))).flip m x : ℝ) : EReal)) ⟨m, hm⟩


omit [Fintype K] [Nonempty K] in
/-- The linear profile `⟨m₀, ·⟩` lies in `𝓟(N_ℝ, P)` for `m₀ ∈ P`. -/
theorem inner_mem_realGrowthClass {m₀ : EuclideanSpace ℝ (Fin n)}
    (hm₀ : m₀ ∈ polytopeToricMomentPolytope γ) :
    (fun x => ⟪m₀, x⟫) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) := by
  refine ⟨?_, ?_⟩
  · exact (innerₗ (EuclideanSpace ℝ (Fin n)) m₀).convexOn convex_univ
  · refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => ?_⟩
    have h := support_ge_of_closedBall γ (r := 0) le_rfl
      (by rw [Metric.closedBall_zero]; exact singleton_subset_iff.mpr hm₀) x
    simpa using h

/-- A toric pole function: the toric potential with profile `⟨m₀, ·⟩`. -/
def polytopeToricPoleFunction {m₀ : EuclideanSpace ℝ (Fin n)}
    (hm₀ : m₀ ∈ polytopeToricMomentPolytope γ) : PolytopeToricVariety γ hs → EReal :=
  polytopeToricExtension γ hs _ (inner_mem_realGrowthClass γ hm₀)

/-- The toric pole function is `-∞` on the toric boundary when `m₀` is interior. -/
theorem polytopeToricPoleFunction_eq_bot {m₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall m₀ r ⊆ polytopeToricMomentPolytope γ)
    {p : PolytopeToricVariety γ hs} (hp : p ∈ polytopeToricBoundary γ hs) :
    polytopeToricPoleFunction γ hs (hball (Metric.mem_closedBall_self hr.le)) p = ⊥ := by
  have hm₀ := hball (Metric.mem_closedBall_self hr.le)
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪m₀, x⟫
  have hf := inner_mem_realGrowthClass γ hm₀
  let u := polytopeToricOffPotential γ hs f
  have hu := isThetaPSHOn_polytopeToricOffPotential γ hs hf.1
  have hZ := (hasAnalyticChartEquations_polytopeToricBoundary γ hs).isClosed
  obtain ⟨C, hC⟩ := exists_upper_bound_polytopeToricOffPotential γ hs hf
  have hb : LocallyBoundedAboveOff (polytopeToricBoundary γ hs) u :=
    fun _ => ⟨univ, univ_mem, C, fun q _ _ => hC q⟩
  have hext : analyticExtension (polytopeToricBoundary γ hs) u =
      polytopeToricPoleFunction γ hs hm₀ :=
    polytopeToricExtension_unique γ hs f hf _
      (hu.analyticExtension_isThetaPSH (hasAnalyticChartEquations_polytopeToricBoundary γ hs)
        (interior_polytopeToricBoundary γ hs) hb)
      (fun x hx => hu.analyticExtension_eq_off hZ hx)
  rw [← hext]
  -- the bound `u ≤ D - r ‖log‖`
  obtain ⟨_, h2⟩ := (SGPT.PSH.singularityEquiv_iff _ _).mp
    (polytopeToricReference_singularityEquiv_support γ hs)
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h2
  have hbound : ∀ x, f x - polytopeToricReference γ hs x ≤ D - r * ‖x‖ := by
    intro x
    have h1 := (support_ge_of_closedBall γ hr.le hball x).trans (hD x)
    rw [← EReal.coe_add] at h1
    have h1' := EReal.coe_le_coe_iff.mp h1
    simp only [f]
    linarith
  -- a chart around `p` in which some coordinate of `p` vanishes
  obtain ⟨v, hpv⟩ := originalPolytopeNativeModelChart_cover γ hs p
  let c := originalPolytopeNativeModelChart γ hs v
  have hpoly : originalPolytopeNativeBoundaryPolynomial n (c p) = 0 := by
    apply (originalPolytopeNativeBoundary_chart_iff γ hs v (c p)).mp
    rw [c.left_inv hpv]
    exact hp
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hpoly
  let Bc :=
    LinearMap.toContinuousLinearMap (latticeBasisLogMap (originalPolytopeNativeBasis γ hs v))
  let Kc : ℝ := ‖Bc‖ + 1
  have hK : 0 < Kc := by positivity
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  let ε : ℝ := Real.exp (-(Kc * (D - M + 1)) / (2 * r))
  have hε : 0 < ε := Real.exp_pos _
  let U := c.source ∩ c ⁻¹' {w : ComplexModel n | ‖w j‖ < ε}
  have hU : U ∈ 𝓝 p := by
    apply (c.isOpen_inter_preimage (isOpen_lt
      (continuous_norm.comp (PiLp.continuous_apply 2 _ j)) continuous_const)).mem_nhds
    refine ⟨hpv, ?_⟩
    change ‖(c p) j‖ < ε
    have : (c p) j = 0 := hj
    rw [this, norm_zero]
    exact hε
  have hUb : ∀ y ∈ U, y ∉ polytopeToricBoundary γ hs → u y ≤ ((M - 1 : ℝ) : EReal) := by
    intro y hy hyZ
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs y).mp hyZ
    rw [show u (polytopeToricEmbedding γ hs a) = _ from
      polytopeToricOffPotential_embedding γ hs f a]
    apply EReal.coe_le_coe_iff.mpr
    set x := unitTorusLog a
    have htrop := tropicalization_polytopeToricVertexChart_embedding γ hs v a
    have hjcoord : tropicalization (c (polytopeToricEmbedding γ hs a)) j =
        Real.log (‖(c (polytopeToricEmbedding γ hs a)) j‖ ^ 2) :=
      tropicalization_apply_eq_log_norm_sq _ j
    have hne : (c (polytopeToricEmbedding γ hs a)) j ≠ 0 := by
      have htor : c (polytopeToricEmbedding γ hs a) ∈ complexTorus n := by
        apply (polytopeToricVertexChart_symm_mem_compl_iff γ hs v _).mp
        rw [c.left_inv hy.1]
        exact hyZ
      exact htor j
    have hlt : Real.log (‖(c (polytopeToricEmbedding γ hs a)) j‖ ^ 2) < Real.log (ε ^ 2) :=
      Real.log_lt_log (by positivity) (pow_lt_pow_left₀ hy.2 (norm_nonneg _) two_ne_zero)
    have hlogε : Real.log (ε ^ 2) = -(Kc * (D - M + 1)) / r := by
      rw [Real.log_pow, Real.log_exp]
      field_simp
      ring
    have hcoord : |latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) x j| ≤ Kc * ‖x‖ := by
      have h1 := PiLp.norm_apply_le (latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) x) j
      have h2 : ‖latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) x‖ ≤ ‖Bc‖ * ‖x‖ :=
        Bc.le_opNorm x
      rw [Real.norm_eq_abs] at h1
      nlinarith [norm_nonneg x]
    rw [← htrop, hjcoord] at hcoord
    have hxK : (D - M + 1) / r < ‖x‖ := by
      have h3 : Kc * (D - M + 1) / r < Kc * ‖x‖ := by
        have := neg_abs_le (Real.log (‖(c (polytopeToricEmbedding γ hs a)) j‖ ^ 2))
        rw [hlogε] at hlt
        have h4 : Kc * (D - M + 1) / r = -(-(Kc * (D - M + 1)) / r) := by ring
        linarith
      rw [mul_div_assoc] at h3
      exact lt_of_mul_lt_mul_left h3 hK.le
    have hrx : D - M + 1 < r * ‖x‖ := by
      rwa [div_lt_iff₀ hr, mul_comm] at hxK
    linarith [hbound x]
  classical
  calc analyticExtension (polytopeToricBoundary γ hs) u p
      ≤ ⨆ y ∈ U, (if y ∈ polytopeToricBoundary γ hs then (⊥ : EReal) else u y) :=
        uscRegularization_le_localSup _ hU
    _ ≤ ((M - 1 : ℝ) : EReal) := by
        refine iSup₂_le fun y hy => ?_
        split_ifs with h
        · exact bot_le
        · exact hUb y hy h
    _ < (M : EReal) := by exact_mod_cast (by linarith : M - 1 < M)

/-! ### The chart profiles and their Legendre transforms -/

/-- The zero potential is a model potential for the native Kähler form `ω`. -/
theorem isModelPotential_polytopeToricZero :
    IsModelPotential (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) := by
  have h := (polytopeToric_sourceModelPotential_minimalEnvelope γ hs).toNative
  rw [polytopeToric_sourceMinimalEnvelope_eq_zero γ hs] at h
  exact h

theorem isThetaPshPotential_of_mem_polytopeToricPSH {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    IsThetaPshPotential (polytopeToricKahlerForm γ hs).val u :=
  (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) u).mp hu.1

/-- The chart profile as a finite convex function. -/
def polytopeToricChartConvex {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) : RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
  ⟨polytopeToricChartProfile γ hs u, convexOn_polytopeToricChartProfile γ hs hu⟩

/-- The affine change of variables from `M_ℝ` to the dual coordinates of the base chart. -/
def polytopeToricChartAffine : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (latticeBasisUnimodularChange
    (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ))).affine
    (polytopeToricVertexVector γ (polytopeToricBaseVertex γ))

theorem measurePreserving_polytopeToricChartAffine :
    MeasurePreserving (polytopeToricChartAffine γ hs) volume volume :=
  ⟨(polytopeToricChartAffine γ hs).continuous.measurable,
    (latticeBasisUnimodularChange _).measurePreserving_affine _⟩

/-- `G_φ(p) = f_φ^*(A (p - v))` for the chart profile `f_φ`. -/
theorem polytopeToricLegendre_eq_chart {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (p : EuclideanSpace ℝ (Fin n)) :
    polytopeToricLegendre γ hs u p =
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun y => (polytopeToricChartProfile γ hs u y : EReal))
        (polytopeToricChartAffine γ hs p) := by
  have h := congrFun ((latticeBasisUnimodularChange (originalPolytopeNativeBasis γ hs
    (polytopeToricBaseVertex γ))).conjugate_comp (polytopeToricChartProfile γ hs u)
      (polytopeToricVertexVector γ (polytopeToricBaseVertex γ))) p
  rw [polytopeToricChartAffine, ← h]
  unfold polytopeToricLegendre
  rw [(polytopeToricRealProfile_mem γ hs hu).2]
  congr 2
  funext x
  rw [polytopeToricRealProfile_eq_chartProfile]

/-- The chart Legendre transform in terms of `G_φ`. -/
theorem conjugate_chart_eq_polytopeToricLegendre {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (q : EuclideanSpace ℝ (Fin n)) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun y => (polytopeToricChartProfile γ hs u y : EReal)) q =
      polytopeToricLegendre γ hs u ((polytopeToricChartAffine γ hs).symm q) := by
  rw [polytopeToricLegendre_eq_chart γ hs hu, Homeomorph.apply_symm_apply]

/-- The reference Newton body in chart coordinates is the affine image of `P`. -/
theorem closure_rawSubgradientImage_chartZero :
    closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun a => ((polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs)).val a :
          EReal))) =
      polytopeToricChartAffine γ hs '' polytopeToricMomentPolytope γ := by
  let f₀ := polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs)
  have hdom : effectiveDomain (fun a => (f₀.val a : EReal)) = univ := by
    ext a
    simp [effectiveDomain]
  have hp := isProper_coe_of_convexOn f₀.property
  have hlower := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_isProper_full_domain hp hdom)
  rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate _ hp hlower]
  have hD : effectiveDomain (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => (f₀.val a : EReal))) =
      polytopeToricChartAffine γ hs '' polytopeToricMomentPolytope γ := by
    ext q
    rw [(polytopeToricChartAffine γ hs).image_eq_preimage_symm]
    change conjugate _ (fun y => (polytopeToricChartProfile γ hs (fun _ => (0 : EReal)) y : EReal))
      q < ⊤ ↔ _
    rw [conjugate_chart_eq_polytopeToricLegendre γ hs (zero_mem_polytopeToricPSH γ hs),
      polytopeToricLegendre_zero, ← effectiveDomain_originalCanonicalEntropyEuclidean γ hs]
    rfl
  rw [hD]
  exact ((isCompact_polytopeToricMomentPolytope γ).image
    (polytopeToricChartAffine γ hs).continuous).isClosed.closure_eq

theorem isCompact_closure_rawSubgradientImage_chartZero :
    IsCompact (closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun a => ((polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs)).val a :
          EReal)))) := by
  rw [closure_rawSubgradientImage_chartZero]
  exact (isCompact_polytopeToricMomentPolytope γ).image (polytopeToricChartAffine γ hs).continuous

/-- Change of variables from the chart coordinates to `M_ℝ`. -/
theorem integral_chart_gap_eq {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    (∫ q in closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun a => ((polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs)).val a :
          EReal))),
      (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
          (fun a => ((polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs)).val a :
            EReal)) q).toReal -
        (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
          (fun a => ((polytopeToricChartConvex γ hs hu).val a : EReal)) q).toReal) =
      ∫ p in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) p).toReal -
          (polytopeToricLegendre γ hs u p).toReal := by
  rw [closure_rawSubgradientImage_chartZero,
    (measurePreserving_polytopeToricChartAffine γ hs).setIntegral_image_emb
      (polytopeToricChartAffine γ hs).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only [polytopeToricChartConvex]
  rw [conjugate_chart_eq_polytopeToricLegendre γ hs (zero_mem_polytopeToricPSH γ hs),
    conjugate_chart_eq_polytopeToricLegendre γ hs hu, Homeomorph.symm_apply_apply]

theorem isGlobalQuasiPshPotential_polytopeToricPoleFunction {m₀ : EuclideanSpace ℝ (Fin n)}
    (hm₀ : m₀ ∈ polytopeToricMomentPolytope γ) :
    IsGlobalQuasiPshPotential (n := n) (polytopeToricPoleFunction γ hs hm₀) := by
  have h := isThetaPshPotential_of_mem_polytopeToricPSH γ hs
    (polytopeToricExtension_mem γ hs _ (inner_mem_realGrowthClass γ hm₀))
  exact ⟨h.1.quasiPlurisubharmonic, h.2⟩

theorem polytopeToricBaseChart_domain_eq :
    (polytopeToricBaseChart γ hs).val.source ∩
        (polytopeToricBaseChart γ hs).val ⁻¹' (tropicalSmoothDomain n : Set (ComplexModel n)) =
      (polytopeToricBoundary γ hs)ᶜ :=
  polytopeToric_patchSource_eq γ hs (zero_mem_polytopeToricPSH γ hs)

theorem isBoundedPotential_polytopeToricZero :
    IsBoundedPotential (fun _ : PolytopeToricVariety γ hs => (0 : EReal)) :=
  ⟨0, 0, fun _ => by simp⟩

theorem relativeFiniteEnergyPreceq_polytopeToricZero :
    RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
      (fun _ => (0 : EReal)) (isModelPotential_polytopeToricZero γ hs) := by
  have h0b := isBoundedPotential_polytopeToricZero γ hs
  rw [relativeFiniteEnergyPreceq_iff_bot_lt_energy (polytopeToricKahlerBackground γ hs) h0b
    ((relativePSHPreceq_iff_of_bounded h0b).mpr
      (isModelPotential_polytopeToricZero γ hs).plurisubharmonic),
    RelativeGeodesicRays.energy_self (polytopeToricKahlerBackground γ hs) h0b]
  exact EReal.bot_lt_zero

/-- Source `prop:Etoric` on `𝓔^1`: `E_ω(φ) = n! ∫_P (G_0 - G_φ) dvol` (real form). -/
theorem polytopeToric_energy_toReal_eq_integral {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs)
    (hE : RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) u
      (isModelPotential_polytopeToricZero γ hs)) :
    (RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
        (isModelPotential_polytopeToricZero γ hs) u).toReal =
      (n.factorial : ℝ) * ∫ p in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) p).toReal -
          (polytopeToricLegendre γ hs u p).toReal := by
  have h0b := isBoundedPotential_polytopeToricZero γ hs
  obtain ⟨m₀, r, hr, hball⟩ := exists_closedBall_subset_polytopeToricMomentPolytope γ hs
  have hpole : ((polytopeToricBaseChart γ hs).val.source ∩
      (polytopeToricBaseChart γ hs).val ⁻¹' (tropicalSmoothDomain n : Set (ComplexModel n)))ᶜ ⊆
        {x | polytopeToricPoleFunction γ hs (hball (Metric.mem_closedBall_self hr.le)) x = ⊥} := by
    intro p hp
    rw [polytopeToricBaseChart_domain_eq, compl_compl] at hp
    exact polytopeToricPoleFunction_eq_bot γ hs hr hball hp
  have h := energy_sub_eq_factorial_conjugate_gap_integral (polytopeToricKahlerBackground γ hs)
    hE (relativeFiniteEnergyPreceq_polytopeToricZero γ hs)
    (polytopeToricBaseChart γ hs) (polytopeToricBaseChart_localPotential γ hs).2.1
    (polytopeToricBaseChart_localPotential γ hs)
    (polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs))
    (polytopeToricChartConvex γ hs hu)
    (polytopeToricChartConvex γ hs (zero_mem_polytopeToricPSH γ hs))
    (polytopeToricBaseChart_corrected γ hs (zero_mem_polytopeToricPSH γ hs))
    (polytopeToricBaseChart_corrected γ hs hu)
    (polytopeToricBaseChart_corrected γ hs (zero_mem_polytopeToricPSH γ hs))
    (isGlobalQuasiPshPotential_polytopeToricPoleFunction γ hs _) hpole
    (isCompact_closure_rawSubgradientImage_chartZero γ hs)
  rw [RelativeGeodesicRays.energy_self (polytopeToricKahlerBackground γ hs) h0b,
    EReal.toReal_zero, sub_zero] at h
  rw [h, integral_chart_gap_eq γ hs hu]

/-! ### Bounded potentials -/

theorem polytopeToricProfile_mem_boundedGrowthClass_of_bounded
    {v : PolytopeToricVariety γ hs → EReal}
    (hv : v ∈ PolytopeToricPSH γ hs) (hb : IsBoundedPotential v) :
    polytopeToricProfile γ hs v ∈
      BoundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) := by
  apply (polytopeToric_mem_eInfinity_iff_boundedGrowthClass γ hs hv).mp
  refine ⟨hv.1, ?_⟩
  rw [polytopeToric_sourceMinimalEnvelope_eq_zero]
  obtain ⟨a, b, hab⟩ := hb
  refine (SGPT.PSH.singularityEquiv_iff _ _).mpr
    ⟨(SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨b, fun p => ?_⟩,
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨-a, fun p => ?_⟩⟩
  · simpa using (hab p).2
  · have h := add_le_add (hab p).1 (le_refl ((-a : ℝ) : EReal))
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    exact h

theorem polytopeToricLegendre_bounds_of_bounded {v : PolytopeToricVariety γ hs → EReal}
    (hv : v ∈ PolytopeToricPSH γ hs) (hb : IsBoundedPotential v) :
    ∃ a b : ℝ, ∀ m ∈ polytopeToricMomentPolytope γ,
      (a : EReal) ≤ polytopeToricLegendre γ hs v m ∧
        polytopeToricLegendre γ hs v m ≤ (b : EReal) :=
  conjugate_bounds_of_mem_boundedGrowthClass _ (isCompact_polytopeToricMomentPolytope γ)
    (convex_polytopeToricMomentPolytope γ)
    (polytopeToricProfile_mem_boundedGrowthClass_of_bounded γ hs hv hb)

theorem polytopeToricLegendre_coe_toReal_of_bounded {v : PolytopeToricVariety γ hs → EReal}
    (hv : v ∈ PolytopeToricPSH γ hs) (hb : IsBoundedPotential v) {m : EuclideanSpace ℝ (Fin n)}
    (hm : m ∈ polytopeToricMomentPolytope γ) :
    ((polytopeToricLegendre γ hs v m).toReal : EReal) = polytopeToricLegendre γ hs v m := by
  obtain ⟨a, b, hab⟩ := polytopeToricLegendre_bounds_of_bounded γ hs hv hb
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab m hm).1)

omit [Nonempty K] in
theorem isFiniteMeasure_restrict_polytopeToricMomentPolytope :
    IsFiniteMeasure (volume.restrict (polytopeToricMomentPolytope γ)) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using volume_polytopeToricMomentPolytope_lt_top γ⟩

theorem integrableOn_polytopeToricLegendre_of_bounded {v : PolytopeToricVariety γ hs → EReal}
    (hv : v ∈ PolytopeToricPSH γ hs) (hb : IsBoundedPotential v) :
    IntegrableOn (fun m => (polytopeToricLegendre γ hs v m).toReal)
      (polytopeToricMomentPolytope γ) := by
  obtain ⟨a, b, hab⟩ := polytopeToricLegendre_bounds_of_bounded γ hs hv hb
  have := isFiniteMeasure_restrict_polytopeToricMomentPolytope γ
  refine Integrable.of_bound
    ((measurable_conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (polytopeToricProfile γ hs v)).ereal_toReal.aestronglyMeasurable) (max |a| |b|) ?_
  filter_upwards [ae_restrict_mem (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet]
    with m hm
  have h1 := (hab m hm).1
  have h2 := (hab m hm).2
  rw [← polytopeToricLegendre_coe_toReal_of_bounded γ hs hv hb hm, EReal.coe_le_coe_iff] at h1 h2
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [le_max_left |a| |b|, neg_abs_le a]
  · linarith [le_max_right |a| |b|, le_abs_self b]

theorem polytopeToricLegendre_zero_le_of_nonpos {v : PolytopeToricVariety γ hs → EReal}
    (hle : v ≤ fun _ => (0 : EReal)) :
    polytopeToricLegendre γ hs (fun _ => (0 : EReal)) ≤ polytopeToricLegendre γ hs v := by
  unfold polytopeToricLegendre
  apply conjugate_antitone
  intro x
  exact add_le_add (hle _) le_rfl

/-- The bounded case of `prop:Etoric` (Step 1), for `φ ≤ 0`. -/
theorem polytopeToric_relativeEnergyOfMinimalType_of_bounded {v : PolytopeToricVariety γ hs → EReal}
    (hv : v ∈ PolytopeToricPSH γ hs) (hb : IsBoundedPotential v) (hle : v ≤ fun _ => (0 : EReal)) :
    (relativeEnergyOfMinimalType (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) v
        (isModelPotential_polytopeToricZero γ hs).plurisubharmonic
        (isThetaPshPotential_of_mem_polytopeToricPSH γ hs hv) : EReal) =
      -((((n.factorial : ℝ≥0∞) * ∫⁻ m in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs v m -
          polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) : ℝ≥0∞) : EReal) := by
  have h0b := isBoundedPotential_polytopeToricZero γ hs
  have h0 := zero_mem_polytopeToricPSH γ hs
  have hn := isThetaPshPotential_of_mem_polytopeToricPSH γ hs hv
  have hrel : RelativePSH (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) v := ⟨hn, hle⟩
  have hEv : RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
      (isModelPotential_polytopeToricZero γ hs) v =
      (relativeEnergyOfMinimalType (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) v
        (isModelPotential_polytopeToricZero γ hs).plurisubharmonic hn : EReal) := by
    rw [RelativeDarvasDistance.energy_eq hrel]
    exact BoundedMongeAmpereEnergy.relativeMongeAmpereEnergy_eq_of_bounded
      (polytopeToricKahlerBackground γ hs) _ _ hrel h0b hb
  have hE : RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) v
      (isModelPotential_polytopeToricZero γ hs) := by
    rw [relativeFiniteEnergyPreceq_iff_bot_lt_energy (polytopeToricKahlerBackground γ hs) h0b
      ((relativePSHPreceq_iff_of_bounded h0b).mpr hn), hEv]
    exact EReal.bot_lt_coe _
  have hreal := polytopeToric_energy_toReal_eq_integral γ hs hv hE
  rw [hEv, EReal.toReal_coe] at hreal
  rw [hreal]
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun m => (polytopeToricLegendre γ hs v m).toReal -
    (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toReal
  have iq : Integrable q (volume.restrict (polytopeToricMomentPolytope γ)) :=
    (integrableOn_polytopeToricLegendre_of_bounded γ hs hv hb).sub
      (integrableOn_polytopeToricLegendre_of_bounded γ hs h0 h0b)
  have hord := polytopeToricLegendre_zero_le_of_nonpos γ hs hle
  have hqn : 0 ≤ᵐ[volume.restrict (polytopeToricMomentPolytope γ)] q := by
    filter_upwards
      [ae_restrict_mem (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet]
      with m hm
    have h := hord m
    rw [← polytopeToricLegendre_coe_toReal_of_bounded γ hs hv hb hm,
      ← polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm, EReal.coe_le_coe_iff] at h
    exact sub_nonneg.mpr h
  have hlin : (∫⁻ m in polytopeToricMomentPolytope γ,
      (polytopeToricLegendre γ hs v m -
        polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) =
      ∫⁻ m, ENNReal.ofReal (q m) ∂volume.restrict (polytopeToricMomentPolytope γ) := by
    apply setLIntegral_congr_fun (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet
    intro m hm
    have h1 := polytopeToricLegendre_coe_toReal_of_bounded γ hs hv hb hm
    have h2 := polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm
    change _ = ENNReal.ofReal ((polytopeToricLegendre γ hs v m).toReal -
      (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toReal)
    rw [← EReal.real_coe_toENNReal, EReal.coe_sub, h1, h2]
  have hiq : 0 ≤ ∫ m, q m ∂volume.restrict (polytopeToricMomentPolytope γ) :=
    integral_nonneg_of_ae hqn
  have hcoe : (((∫⁻ m in polytopeToricMomentPolytope γ,
      (polytopeToricLegendre γ hs v m -
        polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) : ℝ≥0∞) : EReal) =
      (((∫ m, q m ∂volume.restrict (polytopeToricMomentPolytope γ)) : ℝ) : EReal) := by
    rw [hlin, ← ofReal_integral_eq_lintegral_ofReal iq hqn]
    simpa only [EReal.real_coe_toENNReal] using EReal.coe_toENNReal (EReal.coe_nonneg.mpr hiq)
  have hcn : (((n.factorial : ℝ) : EReal)) = ((n.factorial : ℝ≥0∞) : EReal) := by
    simpa only [ENNReal.toReal_natCast] using
      (EReal.coe_ennreal_toReal (x := (n.factorial : ℝ≥0∞)) (by simp))
  have hneg : (∫ p in polytopeToricMomentPolytope γ,
      (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) p).toReal -
        (polytopeToricLegendre γ hs v p).toReal) =
      -∫ m, q m ∂volume.restrict (polytopeToricMomentPolytope γ) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by simp only [q]; ring)
  rw [EReal.coe_ennreal_mul, ← hcn, hcoe, hneg, ← EReal.coe_mul, ← EReal.coe_neg]
  congr 1
  ring

/-! ### Canonical truncations -/

/-- The canonical truncation `max(φ, -j)` of a toric potential `φ ≤ 0` is toric. -/
theorem truncation_mem_polytopeToricPSH {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hle : u ≤ fun _ => (0 : EReal)) (j : ℕ) :
    MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j ∈ PolytopeToricPSH γ hs := by
  refine ⟨(isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) _).mpr
    (MongeAmpereEnergyDecreasing.isThetaPshPotential_truncation
      (isModelPotential_polytopeToricZero γ hs).plurisubharmonic.1
      (isThetaPshPotential_of_mem_polytopeToricPSH γ hs hu).1
      (isBoundedPotential_polytopeToricZero γ hs) hle j), ?_⟩
  intro a ha p
  simp only [MongeAmpereEnergyDecreasing.truncation, hu.2 a ha p]

/-- `F_{max(φ, -j)} = max(F_φ, F_0 - j)`. -/
theorem polytopeToricProfile_truncation {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (j : ℕ) :
    polytopeToricProfile γ hs (MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j) =
      fun x => (realLowerTruncation (polytopeToricRealProfile γ hs u)
        (polytopeToricReference γ hs) j x : EReal) := by
  funext x
  have h := congrFun (polytopeToricRealProfile_mem γ hs hu).2 x
  simp only [polytopeToricProfile] at h ⊢
  simp only [MongeAmpereEnergyDecreasing.truncation, realLowerTruncation, zero_sub]
  rw [EReal.eq_coe_sub_of_add_coe_eq h]
  rw [← EReal.coe_neg, ← EReal.coe_strictMono.monotone.map_max, ← EReal.coe_add,
    ← max_add_add_right]
  congr 2
  · ring
  · ring

theorem polytopeToricLegendre_eq_conjugate_realProfile {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricLegendre γ hs u = conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun x => (polytopeToricRealProfile γ hs u x : EReal)) := by
  unfold polytopeToricLegendre
  rw [(polytopeToricRealProfile_mem γ hs hu).2]

theorem polytopeToricLegendre_zero_eq_conjugate_reference :
    polytopeToricLegendre γ hs (fun _ => (0 : EReal)) =
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun x => (polytopeToricReference γ hs x : EReal)) := by
  unfold polytopeToricLegendre
  rw [polytopeToricProfile_zero]

theorem polytopeToricReference_mem_boundedGrowthClass :
    (fun x => (polytopeToricReference γ hs x : EReal)) ∈
      BoundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) := by
  rw [← polytopeToricProfile_zero]
  exact polytopeToricProfile_mem_boundedGrowthClass_of_bounded γ hs (zero_mem_polytopeToricPSH γ hs)
    (isBoundedPotential_polytopeToricZero γ hs)

private theorem coe_iSup_ennreal (a : ℕ → ℝ≥0∞) :
    (((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) = ⨆ j : ℕ, (a j : EReal) := by
  let s : EReal := ⨆ j : ℕ, (a j : EReal)
  have hs : 0 ≤ s := (EReal.coe_ennreal_nonneg (a 0)).trans
    (le_iSup (fun j : ℕ => (a j : EReal)) 0)
  have hall : ∀ j, a j ≤ s.toENNReal := by
    intro j
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal (le_iSup (fun i : ℕ => (a i : EReal)) j)
  apply le_antisymm
  · have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iSup_le hall)
    rwa [EReal.coe_toENNReal hs] at h
  · exact iSup_le (fun j => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j))

private theorem iInf_neg_coe_ennreal (a : ℕ → ℝ≥0∞) :
    (⨅ j : ℕ, -(a j : EReal)) = -(((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) := by
  apply le_antisymm
  · have hall : ∀ j : ℕ, (a j : EReal) ≤ -(⨅ i : ℕ, -(a i : EReal)) := by
      intro j
      simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr (iInf_le (fun i => -(a i : EReal)) j)
    have h : (((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) ≤ -(⨅ i : ℕ, -(a i : EReal)) := by
      rw [coe_iSup_ennreal]
      exact iSup_le hall
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr h
  · apply le_iInf
    intro j
    exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j))

/-- Source `prop:Etoric` for `φ ≤ 0` (Step 2 of the source proof, via canonical truncations
and monotone convergence): `E_ω(φ) = -n! ∫_P (G_φ - G_0)`, infinite values included. -/
theorem polytopeToric_energy_eq_neg_gap_lintegral_of_nonpos {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
        (isModelPotential_polytopeToricZero γ hs) u =
      -((((n.factorial : ℝ≥0∞) * ∫⁻ m in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs u m -
          polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) : ℝ≥0∞) : EReal) := by
  have h0b := isBoundedPotential_polytopeToricZero γ hs
  have hn := isThetaPshPotential_of_mem_polytopeToricPSH γ hs hu
  have hrel : RelativePSH (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) u := ⟨hn, hle⟩
  have hInf := MongeAmpereEnergyDecreasing.relativeMongeAmpereEnergy_eq_iInf_truncation
    (polytopeToricKahlerBackground γ hs) (polytopeToricKahlerForm γ hs)
    (isModelPotential_polytopeToricZero γ hs) hrel h0b
  have htle (j : ℕ) : MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j ≤
      fun _ => (0 : EReal) := fun p =>
    max_le (hle p) (by
      rw [zero_sub, ← EReal.coe_neg]
      exact EReal.coe_nonpos.mpr (neg_nonpos.mpr (Nat.cast_nonneg j)))
  have hgap : (∫⁻ m in polytopeToricMomentPolytope γ,
      (polytopeToricLegendre γ hs u m -
        polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) =
      ⨆ j : ℕ, ∫⁻ m in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs
            (MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j) m -
          polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal := by
    have h := lintegral_conjugate_gap_eq_iSup_realLowerTruncation volume
      (isCompact_polytopeToricMomentPolytope γ) (nonempty_polytopeToricMomentPolytope γ)
      (convex_polytopeToricMomentPolytope γ) (polytopeToricRealProfile γ hs u)
      (polytopeToricReference γ hs) (polytopeToricReference_mem_boundedGrowthClass γ hs)
    have htr (j : ℕ) : polytopeToricLegendre γ hs
        (MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j) =
        conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun x => (realLowerTruncation
          (polytopeToricRealProfile γ hs u) (polytopeToricReference γ hs) j x : EReal)) := by
      unfold polytopeToricLegendre
      rw [polytopeToricProfile_truncation γ hs hu j]
    simp only [htr, polytopeToricLegendre_eq_conjugate_realProfile γ hs hu,
      polytopeToricLegendre_zero_eq_conjugate_reference γ hs]
    exact h
  calc RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
        (isModelPotential_polytopeToricZero γ hs) u
      = ⨅ j : ℕ, (relativeEnergyOfMinimalType (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
          (MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j)
          (isModelPotential_polytopeToricZero γ hs).plurisubharmonic
          (isThetaPshPotential_of_mem_polytopeToricPSH γ hs
            (truncation_mem_polytopeToricPSH γ hs hu hle j)) : EReal) := by
        rw [RelativeDarvasDistance.energy_eq hrel, hInf]
    _ = ⨅ j : ℕ, -((((n.factorial : ℝ≥0∞) * ∫⁻ m in polytopeToricMomentPolytope γ,
          (polytopeToricLegendre γ hs
              (MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j) m -
            polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) : ℝ≥0∞) : EReal) := by
        apply iInf_congr
        intro j
        exact polytopeToric_relativeEnergyOfMinimalType_of_bounded γ hs
          (truncation_mem_polytopeToricPSH γ hs hu hle j)
          (MongeAmpereEnergyDecreasing.truncation_bounded h0b hle j) (htle j)
    _ = -(((⨆ j : ℕ, (n.factorial : ℝ≥0∞) * ∫⁻ m in polytopeToricMomentPolytope γ,
          (polytopeToricLegendre γ hs
              (MongeAmpereEnergyDecreasing.truncation (fun _ => (0 : EReal)) u j) m -
            polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) : ℝ≥0∞) : EReal) :=
        iInf_neg_coe_ennreal _
    _ = _ := by rw [← ENNReal.mul_iSup, ← hgap]

/-! ### The general case -/

/-- `∫_X ω^n = n! vol P`, as the model volume of `0`. -/
theorem polytopeToric_modelVolume_zero :
    modelVolume (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
        (isModelPotential_polytopeToricZero γ hs) =
      (n.factorial : ℝ) * (volume (polytopeToricMomentPolytope γ)).toReal := by
  have h := congrArg ENNReal.toReal (polytopeToricMA_zero_univ γ hs)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  exact h

private theorem ereal_finite_sub_le (r C : ℝ) (z : EReal)
    (h : (r : EReal) ≤ z - ((-C : ℝ) : EReal)) : (r : EReal) - z ≤ (C : EReal) := by
  induction z using EReal.rec with
  | bot => simp at h
  | top => simp
  | coe z =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

private theorem ereal_gap_shift (r C : ℝ) (z : EReal) :
    (C : EReal) - ((r : EReal) - z) = (z - ((-C : ℝ) : EReal)) - (r : EReal) := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe z =>
    simp only [← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring

/-- Source `prop:Etoric`: for every `φ ∈ PSH_tor(X, ω)`,
`E_ω(φ) = n! ∫_P (G_0 - G_φ) dvol`, the integral being the extended signed integral
(`-∞` exactly when `(G_φ - G_0)⁺` is not integrable). -/
theorem polytopeToric_energy_eq_extendedSignedIntegral {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
        (isModelPotential_polytopeToricZero γ hs) u =
      ((n.factorial : ℝ) : EReal) *
        extendedSignedIntegral (volume.restrict (polytopeToricMomentPolytope γ))
          (fun m => polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m -
            polytopeToricLegendre γ hs u m) := by
  have h0b := isBoundedPotential_polytopeToricZero γ hs
  have h0 := zero_mem_polytopeToricPSH γ hs
  obtain ⟨A, hA⟩ := exists_upper_bound_polytopeToricPSH γ hs hu.1
  let C : ℝ := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  let v : PolytopeToricVariety γ hs → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : v ∈ PolytopeToricPSH γ hs := mem_polytopeToricPSH_add_const γ hs hu (-C)
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    have h1 : u p ≤ (C : EReal) := (hA p).trans (EReal.coe_le_coe_iff.mpr (le_max_left A 0))
    have h := add_le_add h1 (le_refl ((-C : ℝ) : EReal))
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    exact h
  have hGv : polytopeToricLegendre γ hs v =
      fun m => polytopeToricLegendre γ hs u m - ((-C : ℝ) : EReal) :=
    polytopeToricLegendre_add_const γ hs u (-C)
  let H : EuclideanSpace ℝ (Fin n) → EReal := fun m =>
    polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m - polytopeToricLegendre γ hs u m
  have hH : Measurable H := (measurable_conjugate _ _).sub (measurable_conjugate _ _)
  have horder := polytopeToricLegendre_zero_le_of_nonpos γ hs hv0
  have hHupper : H ≤ᵐ[volume.restrict (polytopeToricMomentPolytope γ)] fun _ => (C : EReal) := by
    filter_upwards
      [ae_restrict_mem (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet]
      with m hm
    dsimp only [H]
    rw [← polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm]
    have h := horder m
    rw [hGv, ← polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm] at h
    exact ereal_finite_sub_le _ C _ h
  have hgap : (∫⁻ m, ((C : EReal) - H m).toENNReal
      ∂volume.restrict (polytopeToricMomentPolytope γ)) =
      ∫⁻ m in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs v m -
          polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal := by
    apply setLIntegral_congr_fun (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet
    intro m hm
    simp only [H, hGv]
    rw [← polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm]
    exact congrArg EReal.toENNReal (ereal_gap_shift _ C _)
  have := isFiniteMeasure_restrict_polytopeToricMomentPolytope γ
  have hsigned := extendedSignedIntegral_eq_upper_gap
    (volume.restrict (polytopeToricMomentPolytope γ)) hH C hC hHupper
  rw [Measure.restrict_apply_univ, hgap] at hsigned
  have he := energy_add_const (hφ := isModelPotential_polytopeToricZero γ hs)
    (polytopeToricKahlerBackground γ hs) h0b v C
  have hefun : (fun p => v p + (C : EReal)) = u := by
    simpa only [neg_neg] using translate_translate_neg u (-C)
  rw [hefun, polytopeToric_modelVolume_zero,
    polytopeToric_energy_eq_neg_gap_lintegral_of_nonpos γ hs hv hv0] at he
  have hvolfin := volume_polytopeToricMomentPolytope_lt_top γ
  have hcV : (((ENNReal.ofReal C * volume (polytopeToricMomentPolytope γ) : ℝ≥0∞)) : EReal) =
      ((C * (volume (polytopeToricMomentPolytope γ)).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolfin.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
  have hcn : (((n.factorial : ℝ) : EReal)) = ((n.factorial : ℝ≥0∞) : EReal) := by
    simpa only [ENNReal.toReal_natCast] using
      (EReal.coe_ennreal_toReal (x := (n.factorial : ℝ≥0∞)) (by simp))
  rw [he, hsigned, hcV, EReal.mul_sub_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (Nat.cast_nonneg n.factorial)) (EReal.coe_ne_top _)]
  rw [show ((n.factorial : ℝ) : EReal) * ((∫⁻ m in polytopeToricMomentPolytope γ,
      (polytopeToricLegendre γ hs v m -
        polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal : ℝ≥0∞) : EReal) =
      (((n.factorial : ℝ≥0∞) * ∫⁻ m in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs v m -
          polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal : ℝ≥0∞) : EReal) by
    rw [EReal.coe_ennreal_mul, ← hcn]]
  rw [← EReal.coe_mul, sub_eq_add_neg, add_comm]
  congr 2
  ring

/-- Source `prop:Etoric` in the source interface: the energy `E_ω = E(X, ω; V_ω)` with
`V_ω = 0`. -/
theorem polytopeToric_sourceEnergy_eq_extendedSignedIntegral {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    sourceRelativeEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) =
      ((n.factorial : ℝ) : EReal) *
        extendedSignedIntegral (volume.restrict (polytopeToricMomentPolytope γ))
          (fun m => polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m -
            polytopeToricLegendre γ hs u m) := by
  rw [sourceRelativeEnergy_eq_native]
  have key : ∀ (φ : PolytopeToricVariety γ hs → EReal)
      (hφ : IsModelPotential (polytopeToricKahlerForm γ hs) φ), φ = 0 →
      RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) φ hφ u =
        ((n.factorial : ℝ) : EReal) *
          extendedSignedIntegral (volume.restrict (polytopeToricMomentPolytope γ))
            (fun m => polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m -
              polytopeToricLegendre γ hs u m) := by
    rintro φ hφ rfl
    exact polytopeToric_energy_eq_extendedSignedIntegral γ hs hu
  exact key _ _ (polytopeToric_sourceMinimalEnvelope_eq_zero γ hs)

/-- The source energy `E_ω` is the native energy relative to the model potential `0`. -/
theorem polytopeToric_sourceEnergy_eq_native (u : PolytopeToricVariety γ hs → EReal) :
    sourceRelativeEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) =
      RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
        (isModelPotential_polytopeToricZero γ hs) u := by
  rw [sourceRelativeEnergy_eq_native]
  have key : ∀ (φ : PolytopeToricVariety γ hs → EReal)
      (hφ : IsModelPotential (polytopeToricKahlerForm γ hs) φ), φ = 0 →
      RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) φ hφ u =
        RelativeDarvasDistance.energy (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal))
          (isModelPotential_polytopeToricZero γ hs) u := by
    rintro φ hφ rfl
    rfl
  exact key _ _ (polytopeToric_sourceMinimalEnvelope_eq_zero γ hs)

/-- The source class `𝓔^1(X, ω)` is the native class relative to `0`. -/
theorem polytopeToric_sourceFiniteEnergy_iff_native (u : PolytopeToricVariety γ hs → EReal) :
    SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) ↔
      RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) u
        (isModelPotential_polytopeToricZero γ hs) := by
  rw [sourceRelativeFiniteEnergy_iff_native]
  have key : ∀ (φ : PolytopeToricVariety γ hs → EReal)
      (hφ : IsModelPotential (polytopeToricKahlerForm γ hs) φ), φ = 0 →
      (RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) φ u hφ ↔
        RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) u
          (isModelPotential_polytopeToricZero γ hs)) := by
    rintro φ hφ rfl
    rfl
  exact key _ _ (polytopeToric_sourceMinimalEnvelope_eq_zero γ hs)

/-! ### The finite-energy criterion -/

private theorem toENNReal_sub_coe_le (z : EReal) {r a : ℝ} (h : a ≤ r) :
    (z - (r : EReal)).toENNReal ≤ z.toENNReal + ENNReal.ofReal (-a) := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe z =>
    rw [← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
    calc ENNReal.ofReal (z - r) ≤ ENNReal.ofReal (z + -a) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := ENNReal.ofReal_add_le

private theorem toENNReal_le_sub_coe (z : EReal) {r b : ℝ} (h : r ≤ b) :
    z.toENNReal ≤ (z - (r : EReal)).toENNReal + ENNReal.ofReal b := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe z =>
    rw [← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
    calc ENNReal.ofReal z ≤ ENNReal.ofReal (z - r + b) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := ENNReal.ofReal_add_le

private theorem sub_coe_sub_coe (z : EReal) (s t : ℝ) :
    z - (s : EReal) - (t : EReal) = z - ((s + t : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => simp
  | top => rw [EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_sub_coe]
  | coe z =>
    simp only [← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring

omit [Nonempty K] in
/-- Bounded shifts do not change finiteness of the positive integral. -/
theorem lintegral_sub_bounded_lt_top_iff {G : EuclideanSpace ℝ (Fin n) → EReal} (hG : Measurable G)
    {R : EuclideanSpace ℝ (Fin n) → ℝ} {a b : ℝ}
    (hR : ∀ m ∈ polytopeToricMomentPolytope γ, a ≤ R m ∧ R m ≤ b) :
    (∫⁻ m in polytopeToricMomentPolytope γ, (G m - (R m : EReal)).toENNReal) < ⊤ ↔
      (∫⁻ m in polytopeToricMomentPolytope γ, (G m).toENNReal) < ⊤ := by
  have hfin := volume_polytopeToricMomentPolytope_lt_top γ
  have hGm : Measurable fun m => (G m).toENNReal := EReal.continuous_toENNReal.measurable.comp hG
  constructor
  · intro h
    calc (∫⁻ m in polytopeToricMomentPolytope γ, (G m).toENNReal)
        ≤ ∫⁻ m in polytopeToricMomentPolytope γ,
            ((G m - (R m : EReal)).toENNReal + ENNReal.ofReal b) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem
            (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet] with m hm
          exact toENNReal_le_sub_coe (G m) (hR m hm).2
      _ = (∫⁻ m in polytopeToricMomentPolytope γ, (G m - (R m : EReal)).toENNReal) +
            ENNReal.ofReal b * volume (polytopeToricMomentPolytope γ) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩
  · intro h
    calc (∫⁻ m in polytopeToricMomentPolytope γ, (G m - (R m : EReal)).toENNReal)
        ≤ ∫⁻ m in polytopeToricMomentPolytope γ, ((G m).toENNReal + ENNReal.ofReal (-a)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem
            (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet] with m hm
          exact toENNReal_sub_coe_le (G m) (hR m hm).1
      _ = (∫⁻ m in polytopeToricMomentPolytope γ, (G m).toENNReal) +
            ENNReal.ofReal (-a) * volume (polytopeToricMomentPolytope γ) := by
          rw [lintegral_add_left hGm, lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

/-- `φ ∈ 𝓔^1` (native, relative to `0`) iff `∫_P G_φ^+ < ∞`. -/
theorem polytopeToric_relativeFiniteEnergyPreceq_iff_legendre_positive
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs) :
    RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) u
        (isModelPotential_polytopeToricZero γ hs) ↔
      (∫⁻ m in polytopeToricMomentPolytope γ, (polytopeToricLegendre γ hs u m).toENNReal) < ⊤ := by
  have h0b := isBoundedPotential_polytopeToricZero γ hs
  have h0 := zero_mem_polytopeToricPSH γ hs
  obtain ⟨A, hA⟩ := exists_upper_bound_polytopeToricPSH γ hs hu.1
  let C : ℝ := max A 0
  let v : PolytopeToricVariety γ hs → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : v ∈ PolytopeToricPSH γ hs := mem_polytopeToricPSH_add_const γ hs hu (-C)
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    have h1 : u p ≤ (C : EReal) := (hA p).trans (EReal.coe_le_coe_iff.mpr (le_max_left A 0))
    have h := add_le_add h1 (le_refl ((-C : ℝ) : EReal))
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    exact h
  have hclass : RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) u
        (isModelPotential_polytopeToricZero γ hs) ↔
      RelativeFiniteEnergyPreceq (polytopeToricKahlerForm γ hs) (fun _ => (0 : EReal)) v
        (isModelPotential_polytopeToricZero γ hs) := by
    constructor
    · intro h
      exact h.add_const (polytopeToricKahlerBackground γ hs) (-C)
    · intro h
      have h' := h.add_const (polytopeToricKahlerBackground γ hs) C
      have hfun : (fun p => v p + (C : EReal)) = u := by
        simpa only [neg_neg] using translate_translate_neg u (-C)
      rwa [hfun] at h'
  rw [hclass, relativeFiniteEnergyPreceq_iff_bot_lt_energy (polytopeToricKahlerBackground γ hs) h0b
    ((relativePSHPreceq_iff_of_bounded h0b).mpr
      (isThetaPshPotential_of_mem_polytopeToricPSH γ hs hv)),
    polytopeToric_energy_eq_neg_gap_lintegral_of_nonpos γ hs hv hv0]
  have hGv : polytopeToricLegendre γ hs v =
      fun m => polytopeToricLegendre γ hs u m - ((-C : ℝ) : EReal) :=
    polytopeToricLegendre_add_const γ hs u (-C)
  obtain ⟨a₀, b₀, hab₀⟩ := polytopeToricLegendre_bounds_of_bounded γ hs h0 h0b
  have hshift : (∫⁻ m in polytopeToricMomentPolytope γ,
      (polytopeToricLegendre γ hs v m -
        polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toENNReal) =
      ∫⁻ m in polytopeToricMomentPolytope γ, (polytopeToricLegendre γ hs u m -
        ((-C + (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toReal : ℝ) :
          EReal)).toENNReal := by
    apply setLIntegral_congr_fun (isCompact_polytopeToricMomentPolytope γ).isClosed.measurableSet
    intro m hm
    simp only [hGv]
    rw [← polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm, sub_coe_sub_coe,
      EReal.toReal_coe]
  have hiff := lintegral_sub_bounded_lt_top_iff γ (G := polytopeToricLegendre γ hs u)
    (measurable_conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricProfile γ hs u))
    (R := fun m => -C + (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toReal)
    (a := -C + a₀) (b := -C + b₀) (fun m hm => by
      have h1 := (hab₀ m hm).1
      have h2 := (hab₀ m hm).2
      rw [← polytopeToricLegendre_coe_toReal_of_bounded γ hs h0 h0b hm,
        EReal.coe_le_coe_iff] at h1 h2
      constructor <;> linarith)
  rw [← hiff, ← hshift]
  have hfact : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [bot_lt_iff_ne_bot, Ne, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff, lt_top_iff_ne_top]
  constructor
  · intro h hL
    exact h (by rw [hL, ENNReal.mul_top hfact])
  · intro h hL
    exact h ((ENNReal.mul_eq_top.mp hL).elim (fun h' => h'.2) (fun h' => absurd h'.1
      (ENNReal.natCast_ne_top _)))

/-- Source `cor:toric-ample:L1092`, (1) ⇔ (3): `φ ∈ 𝓔^1(X, ω)` iff `G_φ ∈ L^1(P)`. -/
theorem polytopeToric_mem_finiteEnergy_iff_legendre_L1 {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) ↔
      (∫⁻ m in polytopeToricMomentPolytope γ, (polytopeToricLegendre γ hs u m).toENNReal +
        (-polytopeToricLegendre γ hs u m).toENNReal) < ⊤ := by
  rw [polytopeToric_sourceFiniteEnergy_iff_native,
    polytopeToric_relativeFiniteEnergyPreceq_iff_legendre_positive γ hs hu]
  have hm : Measurable (fun m => (polytopeToricLegendre γ hs u m).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp (measurable_conjugate _ _)
  rw [lintegral_add_left hm]
  have hn := lintegral_neg_conjugate_lt_top_of_mem_growthClass volume
    (innerₗ (EuclideanSpace ℝ (Fin n))) (isCompact_polytopeToricMomentPolytope γ)
    (nonempty_polytopeToricMomentPolytope γ) (polytopeToricProfile_mem_growthClass γ hs hu)
  exact ⟨fun h => ENNReal.add_lt_top.mpr ⟨h, hn⟩, fun h => (ENNReal.add_lt_top.mp h).1⟩

/-- Source `cor:toric-ample:L1092`, (1) ⇔ (2): `φ ∈ 𝓔^1(X, ω)` iff `F_φ ∈ 𝓔^1(N_ℝ, P)`. -/
theorem polytopeToric_mem_finiteEnergy_iff_energyOneClass {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) ↔
      polytopeToricProfile γ hs u ∈ EnergyOneClass (innerₗ (EuclideanSpace ℝ (Fin n)))
        (polytopeToricMomentPolytope γ) volume := by
  rw [mem_energyOneClass_iff volume _ (isCompact_polytopeToricMomentPolytope γ)
    (nonempty_polytopeToricMomentPolytope γ)]
  have hpos : SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) ↔
      (∫⁻ m in polytopeToricMomentPolytope γ, (polytopeToricLegendre γ hs u m).toENNReal) < ⊤ := by
    rw [polytopeToric_sourceFiniteEnergy_iff_native,
      polytopeToric_relativeFiniteEnergyPreceq_iff_legendre_positive γ hs hu]
  constructor
  · intro h
    refine ⟨(polytopeToric_mem_fullMassClass_iff γ hs hu).mpr
      ((polytopeToric_mem_fullMass_iff γ hs hu).mp h.1), hpos.mp h⟩
  · intro h
    exact hpos.mpr h.2

/-- On `𝓔^1_tor`, `G_φ` is finite almost everywhere and integrable on `P`. -/
theorem polytopeToricLegendre_ae_finite_and_integrable {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs)
    (hE : SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
      (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
      (polytopeToric_sourceModelPotential_minimalEnvelope γ hs)) :
    (∀ᵐ m ∂volume.restrict (polytopeToricMomentPolytope γ),
      polytopeToricLegendre γ hs u m ≠ ⊤ ∧ polytopeToricLegendre γ hs u m ≠ ⊥) ∧
    Integrable (fun m => (polytopeToricLegendre γ hs u m).toReal)
      (volume.restrict (polytopeToricMomentPolytope γ)) := by
  have h2 := (polytopeToric_mem_finiteEnergy_iff_energyOneClass γ hs hu).mp hE
  let f : RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
    ⟨polytopeToricRealProfile γ hs u, (polytopeToricRealProfile_mem γ hs hu).1.1⟩
  rw [(polytopeToricRealProfile_mem γ hs hu).2] at h2
  have h := conjugate_finite_ae_and_integrable_of_energyOneClass
    (isCompact_polytopeToricMomentPolytope γ) (nonempty_polytopeToricMomentPolytope γ) f h2
  rw [polytopeToricLegendre_eq_conjugate_realProfile γ hs hu]
  exact h

private theorem toReal_max_of_finite {a b : EReal} (ha : a ≠ ⊤ ∧ a ≠ ⊥) (hb : b ≠ ⊤ ∧ b ≠ ⊥) :
    (max a b).toReal = max a.toReal b.toReal := by
  rw [← EReal.coe_toReal ha.1 ha.2, ← EReal.coe_toReal hb.1 hb.2,
    ← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe]

/-- Source `cor:toricd1`: for `φ, ψ ∈ 𝓔^1_tor(X, ω)`,
`d_1(φ, ψ) = n! ∫_P (2 (G_φ ∨ G_ψ) - G_φ - G_ψ) dvol`. -/
theorem polytopeToric_darvasDistance_eq {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricFiniteEnergy γ hs) (hv : v ∈ PolytopeToricFiniteEnergy γ hs) :
    sourceDarvasDistance (polytopeToricOmega γ hs) (sourceMinimalEnvelope (polytopeToricOmega γ hs))
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) ⟨u, hu.1⟩ ⟨v, hv.1⟩ =
      (n.factorial : ℝ) * ∫ m in polytopeToricMomentPolytope γ,
        (2 * max (polytopeToricLegendre γ hs u m).toReal (polytopeToricLegendre γ hs v m).toReal -
          (polytopeToricLegendre γ hs u m).toReal - (polytopeToricLegendre γ hs v m).toReal) := by
  let R := thetaRooftop (polytopeToricOmega γ hs) u v
  have hRE : SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
      (sourceMinimalEnvelope (polytopeToricOmega γ hs)) R
      (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) :=
    sourceRelativeFiniteEnergy_rooftop (polytopeToricKahlerBackground γ hs) hu.1 hv.1
  have hne : R ≠ ⊥ := by
    intro h
    have hn := (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) R).mp hRE.1.choose
    obtain ⟨y, -, hy⟩ := hn.2 (Classical.arbitrary (PolytopeToricVariety γ hs)) univ isOpen_univ
      (mem_univ _)
    exact hy (congrFun h y)
  have hR : R ∈ PolytopeToricPSH γ hs := mem_polytopeToricPSH_thetaRooftop γ hs hu.2 hv.2 hne
  have hGR := polytopeToricLegendre_thetaRooftop γ hs hu.2 hv.2 hne
  have hEnergy (w : PolytopeToricVariety γ hs → EReal) (hw : w ∈ PolytopeToricPSH γ hs)
      (hwE : SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) w
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs)) :
      (sourceRelativeEnergy (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) w
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs)).toReal =
      (n.factorial : ℝ) * ∫ m in polytopeToricMomentPolytope γ,
        (polytopeToricLegendre γ hs (fun _ => (0 : EReal)) m).toReal -
          (polytopeToricLegendre γ hs w m).toReal := by
    rw [polytopeToric_sourceEnergy_eq_native]
    exact polytopeToric_energy_toReal_eq_integral γ hs hw
      ((polytopeToric_sourceFiniteEnergy_iff_native γ hs w).mp hwE)
  obtain ⟨hFu, hIu⟩ := polytopeToricLegendre_ae_finite_and_integrable γ hs hu.2 hu.1
  obtain ⟨hFv, hIv⟩ := polytopeToricLegendre_ae_finite_and_integrable γ hs hv.2 hv.1
  have hIR := (polytopeToricLegendre_ae_finite_and_integrable γ hs hR hRE).2
  have hI0 := integrableOn_polytopeToricLegendre_of_bounded γ hs (zero_mem_polytopeToricPSH γ hs)
    (isBoundedPotential_polytopeToricZero γ hs)
  have hIM : Integrable (fun m => max (polytopeToricLegendre γ hs u m).toReal
      (polytopeToricLegendre γ hs v m).toReal) (volume.restrict (polytopeToricMomentPolytope γ)) :=
    hIu.sup hIv
  have hItwo : Integrable (fun m => 2 * max (polytopeToricLegendre γ hs u m).toReal
      (polytopeToricLegendre γ hs v m).toReal) (volume.restrict (polytopeToricMomentPolytope γ)) :=
    hIM.const_mul 2
  have hIsub : Integrable (fun m => 2 * max (polytopeToricLegendre γ hs u m).toReal
      (polytopeToricLegendre γ hs v m).toReal - (polytopeToricLegendre γ hs u m).toReal)
      (volume.restrict (polytopeToricMomentPolytope γ)) := hItwo.sub hIu
  have hRM : (∫ m in polytopeToricMomentPolytope γ, (polytopeToricLegendre γ hs R m).toReal) =
      ∫ m in polytopeToricMomentPolytope γ, max (polytopeToricLegendre γ hs u m).toReal
        (polytopeToricLegendre γ hs v m).toReal := by
    apply integral_congr_ae
    filter_upwards [hFu, hFv] with m hmu hmv
    rw [hGR]
    exact toReal_max_of_finite hmu hmv
  change (sourceRelativeEnergy _ _ u _).toReal + (sourceRelativeEnergy _ _ v _).toReal -
    2 * (sourceRelativeEnergy _ _ R _).toReal = _
  rw [hEnergy u hu.2 hu.1, hEnergy v hv.2 hv.1, hEnergy R hR hRE,
    integral_sub hI0 hIu, integral_sub hI0 hIv, integral_sub hI0 hIR, hRM,
    integral_sub hIsub hIv, integral_sub hItwo hIu, integral_const_mul]
  ring

end SGPT.Toric
