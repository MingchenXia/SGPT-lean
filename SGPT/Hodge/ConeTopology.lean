import SGPT.Hodge.FiniteDimensional
import SGPT.BDivisor.NefBDivisor
import SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
import SGPT.Foundations.Analysis.Pending.SmoothDDCForm
import SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration

/-!
# The Euclidean topology of `H^{1,1}(X, ℝ)` is the quotient `C⁰` topology

Blueprint `claude-hodge` (lane HODGE-TOP, package `HodgeTopology`), node
`claude-hodge:thm-euclidean-c0` of `claude-hodge-top`; Xia, *Foundations of pluripotential
theory*, q07, `prop:cohomology-cone-topology` ("`H^{1,1}(X, ℝ)` is a finite-dimensional real vector
space; we give it its Euclidean topology, which is also the quotient topology of the `C⁰`
topology on closed forms").  Used without proof in Xia, *Singularities in global pluripotential
theory*, `chap:bdiv` (`def:nefb`, `lma:volbdivnet`, `prop:dscontbdiv`).

Let `(X, ω)` be a compact connected Kähler manifold.  TN puts on `H^{1,1}(X, ℝ)` the quotient
topology `classC0Topology ω` of the `C⁰` topology of closed real `(1,1)`-forms (sup of
`|θ(v, iv)| / ω(v, iv)`, `XiaoFormC0Topology`).  The project's Euclidean topology is the
intrinsic one, `SGPT.BDivisor.euclideanTopology` (the coarsest topology making every linear
functional continuous).

* The quotient `C⁰` topology is a vector space topology (`classC0Topology_isTopologicalAddGroup`,
  `classC0Topology_continuousSMul`: the quotient map is open).
* It is **Hausdorff** (`classC0Topology_t2Space`): for a constant-trace (`ω`-harmonic)
  form `γ`, the `L²` pairing `θ ↦ ⟪γ, θ⟫` vanishes on `ddᶜ`-exact forms, since
  `⟪γ, ddᶜh⟫ = ⟪γ, d(dᶜh)⟫ = ⟪d*γ, dᶜh⟫ = 0` (TN's formal adjoint and the coclosedness
  `SGPT.Hodge.constantTraceCoclosed`), so it descends to a linear functional `harmonicPairing ω γ`
  on `H^{1,1}`; it is `C⁰`-continuous because `|θ|_g² ≤ n ‖θ‖_{C⁰}²` pointwise (adapted frame,
  `originalFormMetric_self_le`); and it separates classes because `⟪γ, γ⟫ > 0` for the
  constant-trace representative `γ ≠ 0` of a class `α ≠ 0`.
* Hence, `H^{1,1}` being finite dimensional (`SGPT.Hodge.finiteDimensional_realBottChern`),
  **`classC0Topology ω = euclideanTopology`** (`classC0Topology_eq_euclideanTopology`), and
  every Hausdorff vector space topology on `H^{1,1}` is this topology.
* **Linear representatives** (`claude-hodge:lem-linear-representatives`): a linear section
  `α ↦ θ_α` of the class map, continuous from the Euclidean topology to the `C⁰` topology, with
  `‖θ_α‖_{C⁰} ≤ C ∑ⱼ |αⱼ|` in the coordinates of a basis (`exists_linear_representatives`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
  SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
  SGPT.Foundations.Analysis.Pending.NaturalHermitianFormL2
  SGPT.Foundations.Analysis.Pending.NaturalHermitianSmoothFormMetric
  SGPT.Foundations.Analysis.Pending.NaturalHermitianOriginalFormMetric
  SGPT.Foundations.Analysis.Pending.NaturalHermitianCodifferential
  SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration
  SGPT.Foundations.Analysis.Pending.NaturalHermitianVolumeMeasure
  SGPT.Foundations.Analysis.Pending.SmoothDDCForm
  SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct

/-! ### The pointwise norm of a real `(1,1)`-covector is bounded by its `C⁰` size -/

section Pointwise

variable {n : ℕ}

/-- **Pointwise bound** (adapted frame): if `|G(v, iv)| ≤ r a(v, iv)` for all `v`, then the
metric norm of `G` for the metric of `a` satisfies `|G|_a² ≤ n r²`. -/
theorem originalFormMetric_self_le {a G : CoordinateRealTwoForm n} (hJ : IsOneOne a)
    (hp : IsStrictlyPositive a) (hG : IsOneOne G) {r : ℝ}
    (hr : ∀ v : ComplexModel n, |G ![v, Complex.I • v]| ≤ r * a ![v, Complex.I • v]) :
    originalFormMetric a hJ hp 2 G G ≤ n * r ^ 2 := by
  obtain ⟨T, d, hdet, haT, hblock, -⟩ := exists_adapted_frame a G hJ hp hG
  rw [originalFormMetric_eq_sum_of_adapted hJ hp hdet haT hblock G]
  have hfv1 (k : Fin n) : frameVec (k, 1) = Complex.I • frameVec (k, 0) := by
    simp [frameVec, coordinateRealFrame_finProdFinEquiv]
  have hterm (k : Fin n) : d k * G ![T (frameVec (k, 0)), T (frameVec (k, 1))] ≤ r ^ 2 := by
    have hGk : G ![T (frameVec (k, 0)), T (frameVec (k, 1))] = d k := by
      rw [← compLinearMap_apply]
      exact hblock.block k
    have hak : a ![T (frameVec (k, 0)), T (frameVec (k, 1))] = 1 := by
      rw [← compLinearMap_apply, haT]
      have := (standardHermitianTwoForm_isBlockDiagonal (n := n)).block k
      simpa using this
    have hb := hr (T (frameVec (k, 0)))
    rw [show Complex.I • T (frameVec (k, 0)) = T (frameVec (k, 1)) by
      rw [hfv1, T.map_smul], hGk, hak, mul_one] at hb
    rw [hGk, ← sq]
    have h0 : 0 ≤ r := (abs_nonneg _).trans hb
    calc d k ^ 2 = |d k| ^ 2 := (sq_abs _).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  calc ∑ k, d k * G ![T (frameVec (k, 0)), T (frameVec (k, 1))]
      ≤ ∑ _k : Fin n, r ^ 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = n * r ^ 2 := by simp

end Pointwise

/-! ### `L²` norm versus `C⁰` size of closed `(1,1)`-forms -/

section L2

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- Pointwise `|θ|_g² ≤ n ‖θ‖²_{C⁰}` for a closed real `(1,1)`-form. -/
theorem pointwisePair_self_le_formC0Seminorm (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (x : M) :
    pointwisePair w.form.val θ.val θ.val x ≤ n * formC0Seminorm w θ ^ 2 := by
  set r := formC0Seminorm w θ with hrdef
  have hr0 : 0 ≤ r := apply_nonneg _ _
  obtain ⟨hlow, hupp⟩ := (formC0Seminorm_le_iff w θ hr0).mp le_rfl
  let e := complexChartAt (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  change formMetricCoefficients w.form.val e (e.val x) 2 (θ.val.coeff e (e.val x))
    (θ.val.coeff e (e.val x)) ≤ _
  rw [formMetricCoefficients_eq_original w.form.val w.isKahler.1 e (e.val x) hz 2]
  apply originalFormMetric_self_le _ _ (θ.property.2 e (e.val x) hz)
  intro v
  have hl := hlow e (e.val x) hz v
  have hu := hupp e (e.val x) hz v
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable [MeasurableSpace M] [BorelSpace M]

/-- **`‖θ‖_{L²} ≤ C ‖θ‖_{C⁰}`** for closed real `(1,1)`-forms, with `C² = n vol(X)`. -/
theorem norm_toL2_le (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) :
    ‖toL2 w θ‖ ≤ Real.sqrt (n * (hermitianVolumeMeasure w.form.val w.isKahler.1).real univ) *
      formC0Seminorm w θ := by
  have : IsFiniteMeasure (hermitianVolumeMeasure w.form.val w.isKahler.1) :=
    isFiniteMeasure_hermitianVolumeMeasure w.form.val w.isKahler.1
  set μ := hermitianVolumeMeasure w.form.val w.isKahler.1 with hμ
  set r := formC0Seminorm w θ
  have hr0 : 0 ≤ r := apply_nonneg _ _
  have hsq : ‖toL2 w θ‖ ^ 2 ≤ n * μ.real univ * r ^ 2 := by
    rw [toL2_apply, hilbert_norm_sq, integralPair]
    calc ∫ x, pointwisePair w.form.val θ.val θ.val x ∂μ
        ≤ ∫ _x, (n * r ^ 2 : ℝ) ∂μ :=
          integral_mono (pointwisePair_integrable _ _ _ _) (integrable_const _)
            (pointwisePair_self_le_formC0Seminorm w θ)
      _ = n * μ.real univ * r ^ 2 := by
          rw [integral_const, smul_eq_mul]
          ring
  have hV : 0 ≤ (n : ℝ) * μ.real univ := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (toL2 w θ)), ← Real.sqrt_sq hr0, ← Real.sqrt_mul hV]
  exact Real.sqrt_le_sqrt (by linarith [hsq])

/-- **`L²` orthogonality of constant-trace forms and `ddᶜ`-exact forms**:
`⟪γ, ddᶜh⟫ = ⟪d*γ, dᶜh⟫ = 0`. -/
theorem inner_toL2_ddcForm_eq_zero (w : KahlerBackground n M) {γ : ClosedRealOneOneForm n M}
    (hγ : γ ∈ constantTraceSubmodule w) (h : M → ℝ) (hh : ChartSmooth (n := n) h) :
    inner ℝ (toL2 w γ) (toHilbertFormL2 w.form.val w.isKahler.1 (ddcForm h hh)) = 0 := by
  rw [toL2_apply]
  refine (real_inner_comm (toHilbertFormL2 w.form.val w.isKahler.1 (ddcForm h hh))
    (toHilbertFormL2 w.form.val w.isKahler.1 γ.val)).trans ?_
  have hadj := hilbert_smooth_image_formal_adjoint w 1 (dcForm h hh) γ.val
  have hco : (castSmoothForm (show (1 + 1) - 1 = 1 by omega)
      (coderivativeForm w.form.val w.isKahler.1 (1 + 1) γ.val)).GeometricallyEq
      (castSmoothForm (show (1 + 1) - 1 = 1 by omega) 0) :=
    castSmoothForm_geometricallyEq _ (constantTraceCoclosed w γ hγ)
  rw [map_zero] at hco
  rw [toHilbertFormL2_eq_zero_of_geometricallyEq_zero w hco, inner_zero_right] at hadj
  exact hadj

/-- Cohomologous forms have the same `L²` pairing with a constant-trace form. -/
theorem inner_toL2_eq_of_bottChernRel (w : KahlerBackground n M)
    {γ : ClosedRealOneOneForm n M} (hγ : γ ∈ constantTraceSubmodule w)
    {θ θ' : ClosedRealOneOneForm n M} (hrel : ClosedRealOneOneForm.BottChernRel θ θ') :
    inner ℝ (toL2 w γ) (toL2 w θ') = inner ℝ (toL2 w γ) (toL2 w θ) := by
  obtain ⟨h, hh, heq⟩ := hrel
  have hgeo : θ'.val.GeometricallyEq (θ.val + ddcForm h hh) := by
    intro e z hz
    rw [heq e z hz, ProductTestForms.coeff_add, ddcForm_coeff]
  have hL : toL2 w θ' = toL2 w θ + toHilbertFormL2 w.form.val w.isKahler.1 (ddcForm h hh) := by
    rw [toL2_apply, toL2_apply, (toHilbertFormL2_eq_iff _ _ _ _).mpr hgeo]
    exact (toHilbertFormL2Linear w.form.val w.isKahler.1 2).map_add _ _
  rw [hL, inner_add_right, inner_toL2_ddcForm_eq_zero w hγ h hh, add_zero]

/-- The **harmonic pairing** `α ↦ ⟪γ, θ_α⟫_{L²}` with a constant-trace form `γ`, as a linear
functional on `H^{1,1}(X, ℝ)` (well defined by `inner_toL2_eq_of_bottChernRel`). -/
def harmonicPairing (w : KahlerBackground n M) (γ : constantTraceSubmodule w) :
    RealBottChern n M →ₗ[ℝ] ℝ where
  toFun α := Quotient.liftOn α (fun θ => inner ℝ (toL2 w γ.val) (toL2 w θ))
    (fun _ _ h => (inner_toL2_eq_of_bottChernRel w γ.property h).symm)
  map_add' α β := by
    induction α using Quotient.inductionOn with
    | h θ =>
    induction β using Quotient.inductionOn with
    | h η =>
    change inner ℝ (toL2 w γ.val) (toL2 w (θ + η)) =
      inner ℝ (toL2 w γ.val) (toL2 w θ) + inner ℝ (toL2 w γ.val) (toL2 w η)
    rw [map_add, inner_add_right]
  map_smul' c α := by
    induction α using Quotient.inductionOn with
    | h θ =>
    change inner ℝ (toL2 w γ.val) (toL2 w (c • θ)) = c • inner ℝ (toL2 w γ.val) (toL2 w θ)
    rw [map_smul]
    exact (real_inner_smul_right (toL2 w γ.val) (toL2 w θ) c).trans (smul_eq_mul _ _).symm

theorem harmonicPairing_ofRepresentative (w : KahlerBackground n M)
    (γ : constantTraceSubmodule w) (θ : ClosedRealOneOneForm n M) :
    harmonicPairing w γ (RealBottChern.ofRepresentative θ) =
      inner ℝ (toL2 w γ.val) (toL2 w θ) := rfl

/-- The harmonic pairing is `C⁰`-continuous: `|⟪γ, θ⟫| ≤ C ‖γ‖_{L²} ‖θ‖_{C⁰}`. -/
theorem abs_harmonicPairing_ofRepresentative_le (w : KahlerBackground n M)
    (γ : constantTraceSubmodule w) (θ : ClosedRealOneOneForm n M) :
    |harmonicPairing w γ (RealBottChern.ofRepresentative θ)| ≤
      ‖toL2 w γ.val‖ *
        Real.sqrt (n * (hermitianVolumeMeasure w.form.val w.isKahler.1).real univ) *
          formC0Seminorm w θ := by
  rw [harmonicPairing_ofRepresentative, mul_assoc]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_toL2_le w θ) (norm_nonneg _))

/-- The harmonic pairing is continuous for TN's quotient `C⁰` topology of `H^{1,1}`. -/
theorem continuous_harmonicPairing (w : KahlerBackground n M) (γ : constantTraceSubmodule w) :
    Continuous[classC0Topology w, inferInstance] (harmonicPairing w γ) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  rw [← (isOpenQuotientMap_ofRepresentative w).continuous_comp_iff]
  set K := ‖toL2 w γ.val‖ *
    Real.sqrt (n * (hermitianVolumeMeasure w.form.val w.isKahler.1).real univ) with hK
  have hK0 : 0 ≤ K := by positivity
  rw [continuous_iff_continuousAt]
  intro θ₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (K + 1) := div_pos hε (by linarith)
  filter_upwards [(isOpen_formC0Seminorm_ball w θ₀ (ε / (K + 1))).mem_nhds
    ((formC0Seminorm w).mem_ball_self hδ)] with θ hθ
  have hθ' : formC0Seminorm w (θ - θ₀) < ε / (K + 1) := (formC0Seminorm w).mem_ball.mp hθ
  rw [Real.dist_eq]
  change |harmonicPairing w γ (RealBottChern.ofRepresentative θ) -
    harmonicPairing w γ (RealBottChern.ofRepresentative θ₀)| < ε
  have hsub : RealBottChern.ofRepresentative θ - RealBottChern.ofRepresentative θ₀ =
      RealBottChern.ofRepresentative (θ - θ₀) :=
    (map_sub (RealBottChern.ofRepresentativeLinearMap (n := n) (M := M)) θ θ₀).symm
  rw [← map_sub, hsub]
  calc |harmonicPairing w γ (RealBottChern.ofRepresentative (θ - θ₀))|
      ≤ K * formC0Seminorm w (θ - θ₀) := abs_harmonicPairing_ofRepresentative_le w γ _
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hθ'.le hK0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

variable [ConnectedSpace M]

/-- **The harmonic pairings separate classes**: a class on which every harmonic pairing vanishes
is zero (pair it with its own constant-trace representative). -/
theorem eq_zero_of_forall_harmonicPairing_eq_zero (w : KahlerBackground n M)
    {α : RealBottChern n M} (h : ∀ γ, harmonicPairing w γ α = 0) : α = 0 := by
  obtain ⟨γ, hγ, rfl⟩ := exists_constantTrace_representative w α
  have h0 : inner ℝ (toL2 w γ) (toL2 w γ) = 0 := h ⟨γ, hγ⟩
  have h1 : ‖toL2 w γ‖ ^ 2 = 0 := (real_inner_self_eq_norm_sq (toL2 w γ)).symm.trans h0
  rw [toL2_apply, hilbert_norm_sq] at h1
  have hgeo := (integralPair_self_eq_zero_iff _ _ _).mp h1
  rw [← RealBottChern.ofRepresentative_zero]
  apply RealBottChern.ofRepresentative_eq_of_geometricallyEq
  exact hgeo

end L2

/-! ### The quotient `C⁰` topology is a Hausdorff vector space topology -/

section Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- The quotient `C⁰` topology makes `H^{1,1}` a topological additive group. -/
theorem classC0Topology_isTopologicalAddGroup (w : KahlerBackground n M) :
    @IsTopologicalAddGroup (RealBottChern n M) (classC0Topology w) _ := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  have : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
    formC0Topology_isTopologicalAddGroup w
  have hq := isOpenQuotientMap_ofRepresentative w
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · rw [← (hq.prodMap hq).continuous_comp_iff]
    have : (fun p : RealBottChern n M × RealBottChern n M => p.1 + p.2) ∘
        Prod.map RealBottChern.ofRepresentative RealBottChern.ofRepresentative =
        RealBottChern.ofRepresentative ∘ fun p : ClosedRealOneOneForm n M ×
          ClosedRealOneOneForm n M => p.1 + p.2 := by
      funext p
      rfl
    rw [this]
    exact hq.continuous.comp continuous_add
  · rw [← hq.continuous_comp_iff]
    have : (fun α : RealBottChern n M => -α) ∘ RealBottChern.ofRepresentative =
        RealBottChern.ofRepresentative ∘ fun θ : ClosedRealOneOneForm n M => -θ := by
      funext θ
      rfl
    rw [this]
    exact hq.continuous.comp continuous_neg

/-- Scalar multiplication is continuous for the quotient `C⁰` topology. -/
theorem classC0Topology_continuousSMul (w : KahlerBackground n M) :
    @ContinuousSMul ℝ (RealBottChern n M) _ _ (classC0Topology w) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  have : ContinuousSMul ℝ (ClosedRealOneOneForm n M) := formC0Topology_continuousSMul w
  have hq := isOpenQuotientMap_ofRepresentative w
  refine ⟨?_⟩
  rw [← ((IsOpenQuotientMap.id (X := ℝ)).prodMap hq).continuous_comp_iff]
  have : (fun p : ℝ × RealBottChern n M => p.1 • p.2) ∘
      Prod.map id RealBottChern.ofRepresentative =
      RealBottChern.ofRepresentative ∘ fun p : ℝ × ClosedRealOneOneForm n M => p.1 • p.2 := by
    funext p
    rfl
  rw [this]
  exact hq.continuous.comp continuous_smul

/-- **Linear representatives** (`claude-hodge:lem-linear-representatives`): for a finite basis
`b` of `H^{1,1}` there is a linear choice `α ↦ θ_α` of representatives, continuous from the
Euclidean topology of `H^{1,1}` to the `C⁰` topology of forms, with
`‖θ_α‖_{C⁰} ≤ C ∑ⱼ |αⱼ|` in the coordinates `αⱼ` of `b`; that is,
`-C ∑ⱼ|αⱼ| ω ≤ θ_α ≤ C ∑ⱼ|αⱼ| ω` (`formC0Seminorm_le_iff`). -/
theorem exists_linear_representatives (w : KahlerBackground n M) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (RealBottChern n M)) :
    ∃ s : RealBottChern n M →ₗ[ℝ] ClosedRealOneOneForm n M,
      (∀ α, RealBottChern.ofRepresentative (s α) = α) ∧
      Continuous[SGPT.BDivisor.euclideanTopology (RealBottChern n M), formC0Topology w] s ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ α, formC0Seminorm w (s α) ≤ C * ∑ j, |b.coord j α| := by
  classical
  let B : _ → ClosedRealOneOneForm n M := fun j => Quotient.out (b j)
  have hB (j) : RealBottChern.ofRepresentative (B j) = b j := Quotient.out_eq _
  let s : RealBottChern n M →ₗ[ℝ] ClosedRealOneOneForm n M := b.constr ℝ B
  have hs (α : RealBottChern n M) : s α = ∑ j, b.coord j α • B j := by
    simp only [s, Module.Basis.constr_apply, Module.Basis.coord_apply]
    rw [Finsupp.sum_fintype _ _ (fun j => zero_smul ℝ (B j))]
  refine ⟨s, fun α => ?_, ?_, ∑ j, formC0Seminorm w (B j), ?_, fun α => ?_⟩
  · rw [hs]
    change RealBottChern.ofRepresentativeLinearMap (∑ j, b.coord j α • B j) = α
    rw [map_sum]
    · conv_rhs => rw [← b.sum_repr α]
      refine Finset.sum_congr rfl fun j _ => ?_
      change RealBottChern.ofRepresentative (b.coord j α • B j) = b.repr α j • b j
      rw [RealBottChern.ofRepresentative_smul, hB, Module.Basis.coord_apply]
  · let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
    let : TopologicalSpace (RealBottChern n M) := SGPT.BDivisor.euclideanTopology _
    have : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
      formC0Topology_isTopologicalAddGroup w
    have : ContinuousSMul ℝ (ClosedRealOneOneForm n M) := formC0Topology_continuousSMul w
    have hfun : (s : RealBottChern n M → ClosedRealOneOneForm n M) =
        fun α => ∑ j, b.coord j α • B j := funext hs
    rw [hfun]
    exact continuous_finsetSum _ fun j _ =>
      (SGPT.BDivisor.continuous_euclideanTopology (b.coord j)).smul continuous_const
  · exact Finset.sum_nonneg fun j _ => apply_nonneg _ _
  · rw [hs]
    calc formC0Seminorm w (∑ j, b.coord j α • B j)
        ≤ ∑ j, formC0Seminorm w (b.coord j α • B j) := by
          simp only [formC0Seminorm_eq, map_sum]
          exact norm_sum_le _ _
      _ = ∑ j, |b.coord j α| * formC0Seminorm w (B j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ ∑ j, (∑ i, |b.coord i α|) * formC0Seminorm w (B j) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _)
          exact Finset.single_le_sum (f := fun i => |b.coord i α|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ j)
      _ = (∑ j, formC0Seminorm w (B j)) * ∑ j, |b.coord j α| := by
          rw [← Finset.mul_sum, mul_comm]

variable [ConnectedSpace M]

/-- **The quotient `C⁰` topology of `H^{1,1}(X, ℝ)` is Hausdorff**, for a compact connected
Kähler manifold: the harmonic pairings are continuous and separate classes. -/
theorem classC0Topology_t2Space (w : KahlerBackground n M) :
    @T2Space (RealBottChern n M) (classC0Topology w) := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  let F : RealBottChern n M → (constantTraceSubmodule w → ℝ) :=
    fun α γ => harmonicPairing w γ α
  have hF : Continuous F := continuous_pi fun γ => continuous_harmonicPairing w γ
  have hinj : Function.Injective F := by
    intro α β hαβ
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_harmonicPairing_eq_zero w
    intro γ
    rw [map_sub, sub_eq_zero]
    exact congrFun hαβ γ
  exact T2Space.of_injective_continuous hinj hF

/-- **The Euclidean topology of `H^{1,1}(X, ℝ)` is TN's quotient `C⁰` topology**, for a
compact connected Kähler manifold (`claude-hodge-top:thm-euclidean-c0`). -/
theorem classC0Topology_eq_euclideanTopology (w : KahlerBackground n M) :
    classC0Topology w = SGPT.BDivisor.euclideanTopology (RealBottChern n M) := by
  have := finiteDimensional_realBottChern w
  let τ : TopologicalSpace (RealBottChern n M) := classC0Topology w
  have := classC0Topology_isTopologicalAddGroup w
  have := classC0Topology_continuousSMul w
  have := classC0Topology_t2Space w
  exact SGPT.BDivisor.eq_euclideanTopology

/-- **Uniqueness of the vector space topology on `H^{1,1}(X, ℝ)`**: on a compact connected
Kähler manifold every Hausdorff vector space topology on `H^{1,1}(X, ℝ)` is the Euclidean
topology, and equals TN's quotient `C⁰` topology. -/
theorem eq_classC0Topology_of_t2 (w : KahlerBackground n M) [τ : TopologicalSpace (RealBottChern n M)]
    [IsTopologicalAddGroup (RealBottChern n M)] [ContinuousSMul ℝ (RealBottChern n M)]
    [T2Space (RealBottChern n M)] : τ = classC0Topology w := by
  have := finiteDimensional_realBottChern w
  rw [classC0Topology_eq_euclideanTopology w]
  exact SGPT.BDivisor.eq_euclideanTopology

end Topology

end SGPT.Hodge
