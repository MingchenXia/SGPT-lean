import SGPT.Toric.BigToricDivisor

/-!
# Torus-invariant metrics on the line bundle of a toric divisor

Source `chapter_toric_big.tex`, section `sec:toricpob` (before `lma:exist_Ftheta`):
"We shall fix a `T_c`-invariant Hermitian metric `h` on `L = O_X(D)` so that `θ = c_1(L, h)`,
and a rational section `s_D` of `L` corresponding to `D`."

On the vertex chart `U_σ ≅ ℂ^n` of the maximal cone `σ = σ_v`, `D|_{U_σ} = Div(χ^{-m_σ})`
(`eq:DUsigma`), so `e_σ = χ^{m_σ} s_D` is a holomorphic frame of `L` on `U_σ`.  A Hermitian
metric `h` on `L` is the same as the family of local weights `ψ_σ = -log |e_σ|²_h`, smooth on
`U_σ`, subject to the transition law `ψ_σ + log |χ^{m_σ}|² = ψ_τ + log |χ^{m_τ}|²`
(both sides equal `-log |s_D|²_h`); by continuity it suffices to require it on the dense
torus `T(ℂ)`.  `h` is `T_c`-invariant iff every `ψ_σ` is (the frames are `T`-eigen-sections
and `|χ^{m}| = 1` on `T_c`).  The curvature form is `θ = c_1(L, h) = ddᶜ ψ_σ` on `U_σ`.

`BigToricMetric D` records exactly these data: the closed real `(1,1)`-form `θ`, the smooth
`T_c`-invariant weights `ψ_v` on the whole vertex charts, `θ = ddᶜ ψ_v` in every vertex chart
(all charts of `X` are vertex charts), and the transition law on `T(ℂ)` (with
`log |χ^m(a)|² = ⟨m, Trop(a)⟩`).

## Main definitions

* `BigToricMetric D`: the data `(L = O(D), h, s_D, θ = c_1(L, h))`;
* `BigToricMetric.potential h`: the function `F_θ` on `N_ℝ` with
  `Trop^* F_θ = -log |s_D|²_h` on `T(ℂ)` (the normalization `eq:normF0`).

## Main results

* `BigToricMetric.contDiff_potential`, `BigToricMetric.form_coeff_torus`:
  source `lma:exist_Ftheta`, `F_θ` is smooth and `θ = ddᶜ Trop^* F_θ` on `T(ℂ)`;
* `BigToricMetric.weight_chart_embedding`: `ψ_v = Trop^*(F_θ - ⟨m_v, ·⟩)` on `T(ℂ)`;
* `BigToricMetric.exists_abs_potential_sub_le`: `F_θ - ⟨m_v, ·⟩` is bounded on `-σ_v`;
* `BigToricMetric.exists_support_le_potential`: `Supp_{P_D} ≤ F_θ + C`;
* `BigToricMetric.form_compact_pullback_eq`: `θ` is `T_c`-invariant.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Manifold

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Source `sec:toricpob`: a `T_c`-invariant smooth Hermitian metric `h` on `L = O_X(D)`
together with the rational section `s_D` and the curvature form `θ = c_1(L, h)`, recorded
by the local weights `ψ_v = -log |χ^{m_v} s_D|²_h` on the vertex charts. -/
structure BigToricMetric (D : ToricDivisor γ hs) where
  /-- The curvature form `θ = c_1(L, h)`. -/
  form : ClosedRealOneOneForm n (PolytopeToricVariety γ hs)
  /-- The weight `ψ_v = -log |e_v|²_h` of the frame `e_v = χ^{m_v} s_D` on the chart `U_{σ_v}`. -/
  weight : latticePolytopeVertices γ → ComplexModel n → ℝ
  smooth : ∀ v, ContDiff ℝ ∞ (weight v)
  /-- `θ = ddᶜ ψ_v` on the whole vertex chart. -/
  coeff : ∀ v z, form.val.coeff (polytopeToricVertexChart γ hs v) z = smoothDDC (weight v) z
  /-- `T_c`-invariance of `h`. -/
  invariant : ∀ v (a : Fin n → ℂˣ), IsCompactTorusElement a → ∀ z,
    weight v (originalPolytopeNativeModelActionLinear γ hs v a z) = weight v z
  /-- The transition law `ψ_v + log |χ^{m_v}|² = ψ_w + log |χ^{m_w}|²` on `T(ℂ)`. -/
  transition : ∀ v w (a : Fin n → ℂˣ),
    weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum D v) (unitTorusLog a) =
      weight w (originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum D w) (unitTorusLog a)

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The curvature form `θ` in the source atlas interface used by `IsThetaPSH`. -/
def atlasForm : AtlasClosedRealOneOneForm (ofFixedModel n (PolytopeToricVariety γ hs)) :=
  nativeClosedFormToAtlas h.form

theorem atlasForm_coeff_vertexChart (v : latticePolytopeVertices γ) :
    EqOn (smoothDDC (h.weight v)) (h.atlasForm.coeff (polytopeToricVertexChart γ hs v))
      ((ofFixedModel n (PolytopeToricVariety γ hs)).chart (polytopeToricVertexChart γ hs v)).target :=
  fun z _ => (h.coeff v z).symm

/-- Source `lma:exist_Ftheta` and `eq:normF0`: the function `F_θ` on `N_ℝ` with
`Trop^* F_θ = -log |s_D|²_h` on `T(ℂ)`, read through a base vertex chart. -/
def potential (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  h.weight (polytopeToricBaseVertex γ) (originalPolytopeNativeModelChart γ hs
      (polytopeToricBaseVertex γ) (polytopeToricEmbedding γ hs (positiveTorusPoint x))) +
    latticeFunctional (toricCartierDatum D (polytopeToricBaseVertex γ)) x

/-- Compact torus elements act on vertex charts by the linear chart action. -/
theorem weight_chart_embedding_compact_mul (v : latticePolytopeVertices γ)
    {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t) (b : Fin n → ℂˣ) :
    h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs (t * b))) =
      h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs b)) := by
  have hsrc : polytopeToricEmbedding γ hs b ∈ (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v b
  rw [← polytopeToricAction_embedding]
  change h.weight v (originalPolytopeNativeModelChart γ hs v
    (originalPolytopeNativeAction γ t (polytopeToricEmbedding γ hs b))) = _
  rw [originalPolytopeNativeModelChart_action γ hs v t _ hsrc]
  exact h.invariant v t ht _

/-- The weight at a torus point only depends on its tropicalization. -/
theorem weight_chart_embedding_positive (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      h.weight v (originalPolytopeNativeModelChart γ hs v
        (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a)))) := by
  conv_lhs => rw [← torusAngularPart_mul_positiveTorusPoint a]
  exact h.weight_chart_embedding_compact_mul v (isCompactTorusElement_torusAngularPart a) _

/-- `ψ_v = Trop^*(F_θ - ⟨m_v, ·⟩)` on `T(ℂ)`. -/
theorem weight_chart_embedding (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      h.potential (unitTorusLog a) - latticeFunctional (toricCartierDatum D v) (unitTorusLog a) := by
  have ht := h.transition v (polytopeToricBaseVertex γ) a
  rw [h.weight_chart_embedding_positive (polytopeToricBaseVertex γ) a] at ht
  unfold potential
  linarith

/-- The vertex chart of a positive torus point. -/
theorem norm_chart_positive_le_one (v : latticePolytopeVertices γ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ polytopeToricNegCone hs v) (j : Fin n) :
    ‖originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs (positiveTorusPoint x)) j‖ ≤ 1 := by
  have htr := congrArg (fun y : EuclideanSpace ℝ (Fin n) => y j)
    (tropicalization_polytopeToricVertexChart_embedding γ hs v (positiveTorusPoint x))
  simp only [unitTorusLog_positiveTorusPoint] at htr
  change 2 * Real.log ‖_‖ = _ at htr
  rw [latticeBasisLogMap_apply] at htr
  have hj := hx j
  rw [latticeFunctional_apply] at hj
  have hlog : Real.log ‖originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs (positiveTorusPoint x)) j‖ ≤ 0 := by linarith
  by_contra hcon
  push Not at hcon
  have := Real.log_pos hcon
  linarith

/-- `F_θ - ⟨m_v, ·⟩` is bounded on `-σ_v` (the weight `ψ_v` is continuous on the closed
unit polydisc of the vertex chart). -/
theorem exists_abs_potential_sub_le (v : latticePolytopeVertices γ) :
    ∃ C : ℝ, ∀ x ∈ polytopeToricNegCone hs v,
      |h.potential x - latticeFunctional (toricCartierDatum D v) x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ComplexModel n) (Real.sqrt n)).exists_bound_of_continuousOn
    (h.smooth v).continuous.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have heq := h.weight_chart_embedding v (positiveTorusPoint x)
  rw [unitTorusLog_positiveTorusPoint] at heq
  rw [← heq]
  apply hC
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ j, ‖originalPolytopeNativeModelChart γ hs v
        (polytopeToricEmbedding γ hs (positiveTorusPoint x)) j‖ ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h1 := norm_chart_positive_le_one v hx j
        have h0 := norm_nonneg (originalPolytopeNativeModelChart γ hs v
          (polytopeToricEmbedding γ hs (positiveTorusPoint x)) j)
        nlinarith
    _ = n := by simp

/-- The upper bounds `F_θ ≤ ⟨m_v, ·⟩ + C` on `-σ_v`. -/
theorem exists_potential_le_cartier (v : latticePolytopeVertices γ) :
    ∃ C : ℝ, ∀ x ∈ polytopeToricNegCone hs v,
      h.potential x ≤ latticeFunctional (toricCartierDatum D v) x + C := by
  obtain ⟨C, hC⟩ := h.exists_abs_potential_sub_le v
  exact ⟨C, fun x hx => by linarith [(abs_le.mp (hC x hx)).2]⟩

/-- `Supp_{P_D} ≤ F_θ + C` on `N_ℝ`. -/
theorem exists_support_le_potential :
    ∃ C : ℝ, ∀ x, support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x ≤
      ((h.potential x + C : ℝ) : EReal) := by
  have hv := finite_latticePolytopeVertices γ
  let _ := hv.fintype
  choose c hc using fun v => h.exists_abs_potential_sub_le v
  refine ⟨∑ v, |c v|, fun x => ?_⟩
  obtain ⟨v, hxv⟩ := exists_vertex_mem_negCone (γ := γ) (hs := hs) x
  have h1 := support_le_latticeFunctional_cartier D v hxv
  have h2 : latticeFunctional (toricCartierDatum D v) x ≤ h.potential x + ∑ v, |c v| := by
    have h3 := (abs_le.mp (hc v x hxv)).1
    have h4 : c v ≤ ∑ v, |c v| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun v => |c v|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v))
    linarith
  exact h1.trans (EReal.coe_le_coe_iff.mpr h2)

/-! ### Source `lma:exist_Ftheta` -/

/-- The vertex chart of `e^{x/2}` is `expCoordinates (B_v x)`. -/
theorem chart_positive_eq_expCoordinates (v : latticePolytopeVertices γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs (positiveTorusPoint x)) =
      expCoordinates (latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) x) := by
  ext j
  have hj : (originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs (positiveTorusPoint x))) j =
      (latticeCharacter (originalPolytopeNativeBasis γ hs v j) (positiveTorusPoint x) : ℂ) :=
    originalPolytopeNativePiChart_orbit γ hs v (positiveTorusPoint x) j
  rw [hj]
  change (∏ k, (positiveTorusPoint x k) ^ (originalPolytopeNativeBasis γ hs v j k) : ℂˣ).val =
    (Real.exp (latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) x j / 2) : ℂ)
  rw [latticeBasisLogMap_apply, Units.coe_prod]
  simp only [positiveTorusPoint, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [show (∑ i, (originalPolytopeNativeBasis γ hs v j i : ℝ) * x i) / 2 =
      ∑ i, (originalPolytopeNativeBasis γ hs v j i : ℝ) * (x i / 2) by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring]
  rw [Real.exp_sum, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm, Real.exp_mul, Real.rpow_intCast, Complex.ofReal_zpow]

theorem contDiff_expCoordinates : ContDiff ℝ ∞ (expCoordinates (n := n)) := by
  have h : expCoordinates (n := n) = ((EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ) ∘
      (fun x : EuclideanSpace ℝ (Fin n) => fun i => ((Real.exp (x i / 2) : ℝ) : ℂ)) := by
    funext x; rfl
  rw [h]
  apply ((EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply Complex.ofRealCLM.contDiff.comp
  exact Real.contDiff_exp.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.div_const 2)

theorem contDiff_linearMap_euclidean {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] F) : ContDiff ℝ ∞ f := by
  have h := (LinearMap.toContinuousLinearMap f).contDiff (n := ∞)
  simpa using h

/-- Source `lma:exist_Ftheta`: `F_θ` is smooth. -/
theorem contDiff_potential : ContDiff ℝ ∞ h.potential := by
  have heq : h.potential = fun x =>
      h.weight (polytopeToricBaseVertex γ)
          (expCoordinates (latticeBasisLogMap
            (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)) x)) +
        latticeFunctional (toricCartierDatum D (polytopeToricBaseVertex γ)) x := by
    funext x
    rw [potential, chart_positive_eq_expCoordinates]
  rw [heq]
  exact ((h.smooth _).comp (contDiff_expCoordinates.comp
    (contDiff_linearMap_euclidean _))).add (contDiff_linearMap_euclidean _)

/-- `log |∏_j z_j^{c_j}|² = ∑_j c_j log |z_j|²` on the torus. -/
theorem log_normSq_prod_zpow {c : Fin n → ℤ} {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    Real.log (Complex.normSq (∏ j, z j ^ c j)) =
      ∑ j, (c j : ℝ) * Real.log (‖z j‖ ^ 2) := by
  rw [map_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow₀, Real.log_zpow, Complex.normSq_eq_norm_sq]
  · intro j _
    rw [map_zpow₀]
    exact zpow_ne_zero _ (Complex.normSq_pos.mpr (hz j)).ne'

/-- Source `lma:exist_Ftheta`: `θ = ddᶜ Trop^* F_θ` on `T(ℂ)`, in every vertex chart (and
every chart of `X` is a vertex chart). -/
theorem form_coeff_torus (v : latticePolytopeVertices γ) {z : ComplexModel n}
    (hz : z ∈ complexTorus n) :
    h.form.val.coeff (polytopeToricVertexChart γ hs v) z =
      smoothDDC (fun y => h.potential (latticeBasisLogInverse
        (originalPolytopeNativeBasis γ hs v) (tropicalization y))) z := by
  set b := originalPolytopeNativeBasis γ hs v
  set c : Fin n → ℤ := fun j => intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j)
  let L : ComplexModel n → ℝ := fun y => ∑ j, (c j : ℝ) * Real.log (‖y j‖ ^ 2)
  have hT : IsOpen (complexTorus n) := isOpen_complexTorus n
  -- on the torus, `F_θ ∘ B⁻¹ ∘ trop = ψ_v + L`
  have heq : ∀ y ∈ complexTorus n,
      h.potential (latticeBasisLogInverse b (tropicalization y)) = h.weight v y + L y := by
    intro y hy
    obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hy
    have hyt : y ∈ (originalPolytopeNativeModelChart γ hs v).target := by
      rw [originalPolytopeNativeModelChart_target]; exact mem_univ y
    have hya : originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) = y := by
      rw [ha]; exact (originalPolytopeNativeModelChart γ hs v).right_inv hyt
    have hlog : latticeBasisLogInverse b (tropicalization y) = unitTorusLog a := by
      rw [← hya, tropicalization_polytopeToricVertexChart_embedding,
        latticeBasisLogInverse_logMap]
    have hw := h.weight_chart_embedding v a
    rw [hya] at hw
    have hL : L y = latticeFunctional (toricCartierDatum D v) (unitTorusLog a) := by
      rw [← hlog, latticeFunctional_logInverse hs v]
      simp only [L, c, tropicalization_apply_eq_log_norm_sq]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hlog, hw, hL]
    ring
  have hLsmooth : ContDiffOn ℝ ∞ L (complexTorus n) := by
    apply ContDiffOn.sum
    intro j _
    apply contDiffOn_const.mul
    apply ContDiffOn.log
    · exact (contDiff_norm_sq ℝ).comp_contDiffOn
        ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).contDiff.contDiffOn
    · intro y hy
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hy j))
  have hLzero : smoothDDC L z = 0 := by
    have hcongr : L =ᶠ[𝓝 z] fun y => Real.log (Complex.normSq (∏ j, y j ^ c j)) := by
      filter_upwards [hT.mem_nhds hz] with y hy
      exact (log_normSq_prod_zpow hy).symm
    rw [smoothDDC_congr hcongr]
    apply Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
    · filter_upwards [hT.mem_nhds hz] with y hy
      apply AnalyticAt.differentiableAt
      apply Finset.analyticAt_fun_prod
      intro j _
      exact ((EuclideanSpace.proj (𝕜 := ℂ) j).analyticAt y).zpow (hy j)
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hz j)
  have hcongr : (fun y => h.potential (latticeBasisLogInverse b (tropicalization y))) =ᶠ[𝓝 z]
      fun y => h.weight v y + L y := by
    filter_upwards [hT.mem_nhds hz] with y hy
    exact heq y hy
  rw [smoothDDC_congr hcongr, smoothDDC_add hT (h.smooth v).contDiffOn hLsmooth hz, hLzero,
    add_zero, h.coeff v z]

/-- In the vertex chart at `v`, the tropicalization of `X` (read in the base chart) is
`B_v⁻¹ ∘ trop` on the coordinate torus. -/
theorem polytopeToricLog_vertexChart_symm (v : latticePolytopeVertices γ) {y : ComplexModel n}
    (hy : y ∈ complexTorus n) :
    polytopeToricLog γ hs ((originalPolytopeNativeModelChart γ hs v).symm y) =
      latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization y) := by
  obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hy
  have hyt : y ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ y
  have hya : originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) = y := by
    rw [ha]; exact (originalPolytopeNativeModelChart γ hs v).right_inv hyt
  rw [← ha, polytopeToricLog_embedding, ← hya, tropicalization_polytopeToricVertexChart_embedding,
    latticeBasisLogInverse_logMap]

/-- Source `lma:exist_Ftheta`, chart form: in every vertex chart (all charts of `X` are
vertex charts), on `T(ℂ)`, `θ = ddᶜ (F_θ ∘ Trop)`. -/
theorem form_coeff_torus_trop (v : latticePolytopeVertices γ) {z : ComplexModel n}
    (hz : z ∈ complexTorus n) :
    h.form.val.coeff (polytopeToricVertexChart γ hs v) z =
      smoothDDC (fun y => h.potential
        (polytopeToricLog γ hs ((originalPolytopeNativeModelChart γ hs v).symm y))) z := by
  rw [h.form_coeff_torus v hz]
  apply smoothDDC_congr
  filter_upwards [(isOpen_complexTorus n).mem_nhds hz] with y hy
  rw [polytopeToricLog_vertexChart_symm v hy]

/-! ### `T_c`-invariance of `θ` -/

/-- The form `θ` is invariant under every compact torus element. -/
theorem form_compact_pullback_eq (a : Fin n → ℂˣ) (ha : IsCompactTorusElement a) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    SmoothRealForm.pullback (contMDiff_originalPolytopeNativeAction γ hs a ∞)
      (h.form.val : SmoothRealForm n (originalPolytopeNativeSpace γ) 2) = h.form.val := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  apply originalNativeSmoothForm_ext_of_torus γ hs
  intro v z _
  let e := originalPolytopeNativeComplexChart γ hs v
  have hz : z ∈ e.val.target := by
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ z
  have hp : e.val.symm z ∈ e.val.source := e.val.map_target hz
  have hpa : originalPolytopeNativeAction γ a (e.val.symm z) ∈ e.val.source := by
    change (originalPolytopeNativeModelChart γ hs v).symm z ∈
      (originalPolytopeNativeModelChart γ hs v).source at hp
    change originalPolytopeNativeAction γ a ((originalPolytopeNativeModelChart γ hs v).symm z) ∈
      (originalPolytopeNativeModelChart γ hs v).source
    rw [originalPolytopeNativeModelChart_source] at hp ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a _).mpr hp
  have hdomain : z ∈ HolomorphicMaps.coordinateDomain (originalPolytopeNativeAction γ a) e e :=
    ⟨hz, hpa⟩
  rw [SmoothRealForm.pullback_coeff (contMDiff_originalPolytopeNativeAction γ hs a ∞)
    h.form.val e e hdomain]
  have hcoord : HolomorphicMaps.coordinateMap (originalPolytopeNativeAction γ a) e e =
      originalPolytopeNativeModelActionLinear γ hs v a :=
    funext (originalPolytopeNativeModelChart_action_symm γ hs v a)
  rw [hcoord]
  change (h.form.val.coeff (polytopeToricVertexChart γ hs v)
    (originalPolytopeNativeModelActionLinear γ hs v a z)).compContinuousLinearMap _ =
      h.form.val.coeff (polytopeToricVertexChart γ hs v) z
  rw [h.coeff, h.coeff]
  have hpull := HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ
    (originalPolytopeNativeModelActionLinear γ hs v a).contDiff.contDiffOn
    (h.smooth v).contDiffOn (mapsTo_univ _ _) (mem_univ z)
  have hfun : (fun y => h.weight v (originalPolytopeNativeModelActionLinear γ hs v a y)) =
      h.weight v := funext (h.invariant v a ha)
  rw [hfun] at hpull
  exact hpull.symm

/-- Holomorphic compact-torus pullback preserves `θ`-psh functions. -/
theorem isThetaPSH_comp_action {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u)
    {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm
      (fun p => u (polytopeToricAction γ hs a p)) := by
  have hn := (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu
  apply (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mpr
  have hne : LocallyNondegenerate (fun p => u (polytopeToricAction γ hs a p)) :=
    Pending.AdmissiblePresentationHolomorphicPullback.locallyNondegenerate_comp_of_isOpenMap
      (polytopeToricAction γ hs a).isOpenMap hn.2
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (polytopeToricAction γ hs a : PolytopeToricVariety γ hs → PolytopeToricVariety γ hs) :=
    contMDiff_originalPolytopeNativeAction γ hs a ∞
  have hpull := Pending.GlobalPotentialPullback.isThetaPshPotential_comp hf hn.1 hne
  have heq : SmoothRealForm.pullback hf h.form.val = h.form.val :=
    h.form_compact_pullback_eq a ha
  change IsThetaPshPotential h.form.val _
  rw [← heq]
  exact hpull

end BigToricMetric

end SGPT.Toric
