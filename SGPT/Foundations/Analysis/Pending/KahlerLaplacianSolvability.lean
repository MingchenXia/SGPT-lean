import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.ManifoldSchauderRegularity
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Solvability of the Laplace equation on a compact Kähler manifold

Let `(M, ω)` be a compact connected Kähler manifold of dimension `N` (`w : KahlerBackground N M`)
with a Hölder atlas `A`, let `Δ_ω` be the Laplacian of `ω` (`KahlerLaplacianChart.laplacian`;
`Δ_ω u ω^N = N ddᶜu ∧ ω^{N-1}`, `KahlerLaplacianStokes.chartDensity_mul_chartLaplacian`), and let
`0 < r < 1`, `k ∈ ℕ`. This module proves blueprint `bou:kahler-laplacian-solvability` (2):

* **`exists_laplacian_eq_of_integral_eq_zero`**: for every `h ∈ C^{k,r}(M)` with `∫ h ω^N = 0`
  there is `u ∈ C^{k+2,r}(M)` with `Δ_ω u = h`;
* **`exists_eq_add_const_of_laplacian_eq`**: `u` is unique up to an additive constant;
* **`laplacianConstEquiv`**: `(v, σ) ↦ Δ_ω v - σ` is an isomorphism of Banach spaces
  `{v ∈ C^{k+2,r}(M) : ∫ v ω^N = 0} × ℝ ≃L C^{k,r}(M)`.

Item (1) of the node, a harmonic `C²` function is constant, is
`KahlerLaplacianStokes.exists_eq_const_of_laplacian_eq_zero`.

## Proof

* `k = 0` (`bijective_laplacianCLM_add`). Let `T u = Δ_ω u + (∫ u ω^N) · 1 : C^{2,r} → C^{0,r}`.
  `T` is one-to-one: integrating `T u = 0` with Stokes (`integral_laplacian_eq_zero`) gives
  `∫ u = 0`, so `Δ_ω u = 0`, so `u` is constant by (1), so `u = 0`. Write
  `T = (Δ_ω - 1)(I + K)` with `K = (Δ_ω - 1)⁻¹ (ι + P)`. Here `Δ_ω - 1` is an isomorphism
  (`KahlerLaplacianChart.laplacianSubEquiv`), `ι : C^{2,r} ⊂ C^{0,r}` is compact (through `C^{0,1}`,
  `isCompactOperator_toZeroCLM`) and `P u = (∫ u) · 1` has rank one. By the Fredholm alternative
  (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`), `I + K` is invertible, so `T` is
  bijective. For `∫ h = 0`, the solution of `T u = h` has `∫ u = 0` (Stokes), so `Δ_ω u = h`.
* Regularity (`exists_holderMap_of_laplacian_eq`): `Δ_ω` is `a : D²` in every chart with smooth,
  symmetric, positive definite `a`. The interior regularity `LinearRegularity.holderAt_of_hessTrace_eq`
  bootstraps `u ∈ C^{2,r}` to `C^{k+2,r}` when `Δ_ω u ∈ C^{k,r}`
  (`ManifoldSchauderRegularity.exists_holderMap_of_holderAt`).
* `Δ_ω : C^{k+2,r} → C^{k,r}` is a bounded operator (`laplacianCLMk`), by the closed graph theorem.
  The isomorphism then follows from the open mapping theorem.

TN.5, blueprint `bou:kahler-laplacian-solvability`.
-/

noncomputable section

open Set Filter Topology MeasureTheory Function
open scoped NNReal ContDiff RealInnerProductSpace ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.KahlerLaplacianSolvability

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses IntegrationCurrent
  KahlerLaplacianChart KahlerLaplacianStokes HolderAtlas.HolderMap HolderGerm EllipticMeanValue

/-! ### The compact inclusion `C^{k,r}(M) ⊂ C^{0,r}(M)`, `k ≥ 1`, `r < 1` -/

section Inclusion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k : ℕ} {r : ℝ≥0}

/-- `C^{k,r}_b ⊂ C^{0,1}_b` for `k ≥ 1`: a `C¹` map with bounded derivative is Lipschitz. -/
def toZeroOne (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    BoundedContDiffHolderMap 0 1 E F :=
  BoundedContDiffHolderMap.ofContDiff le_rfl f (f.contDiff.of_le (by exact_mod_cast hk))
    (M := ‖f‖) fun _ hi x => f.norm_iteratedFDeriv_apply_le (hi.trans hk) x

@[simp]
theorem coe_toZeroOne (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    ⇑(toZeroOne hk f) = f :=
  rfl

theorem norm_toZeroOne_le (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    ‖toZeroOne hk f‖ ≤ 3 * ‖f‖ := by
  have h := BoundedContDiffHolderMap.norm_ofContDiff_le (k := 0) (le_rfl : (1 : ℝ≥0) ≤ 1)
    (f : E → F) (f.contDiff.of_le (by exact_mod_cast hk)) (M := ‖f‖)
    fun _ hi x => f.norm_iteratedFDeriv_apply_le (hi.trans hk) x
  exact h.trans_eq (by push_cast; ring)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {G : Type} [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- `C^{k,r}(M) ⊂ C^{0,1}(M)` for `k ≥ 1`. -/
def holderToZeroOne (hk : 1 ≤ k) (u : A.HolderMap k r G) : A.HolderMap 0 1 G :=
  ⟨u, fun a => ⟨toZeroOne hk (u.rep a), by rw [coe_toZeroOne, coe_rep]⟩⟩

@[simp]
theorem coe_holderToZeroOne (hk : 1 ≤ k) (u : A.HolderMap k r G) :
    ⇑(holderToZeroOne hk u) = u :=
  rfl

theorem norm_holderToZeroOne_le (hk : 1 ≤ k) (u : A.HolderMap k r G) :
    ‖holderToZeroOne hk u‖ ≤ 3 * ‖u‖ := by
  rw [norm_def, norm_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have he : (holderToZeroOne hk u).rep a = toZeroOne hk (u.rep a) :=
    BoundedContDiffHolderMap.ext fun _ => rfl
  rw [he]
  exact norm_toZeroOne_le hk _

/-- `C^{k,r}(M) ⊂ C^{0,1}(M)` as a continuous linear map. -/
def holderToZeroOneCLM (hk : 1 ≤ k) : A.HolderMap k r G →L[ℝ] A.HolderMap 0 1 G :=
  LinearMap.mkContinuous
    { toFun := holderToZeroOne hk
      map_add' := fun _ _ => HolderAtlas.HolderMap.ext fun _ => rfl
      map_smul' := fun _ _ => HolderAtlas.HolderMap.ext fun _ => rfl }
    3 (norm_holderToZeroOne_le hk)

/-- **The inclusion `C^{k,r}(M) ⊂ C^{0,r}(M)` is compact** for `k ≥ 1`, `r < 1` and `G`
finite-dimensional: it factors through `C^{0,1}(M) ⊂⊂ C^{0,r}(M)`. -/
theorem isCompactOperator_toZeroCLM [FiniteDimensional ℝ G] (hr1 : r < 1) (hk : 1 ≤ k) :
    IsCompactOperator (toZeroCLM (A := A) (F := G) hr1.le hk) := by
  have h := (isCompactOperator_ofLE (A := A) (k := 0) (F := G) (r := 1) le_rfl hr1).comp_clm
    (holderToZeroOneCLM (A := A) (G := G) (r := r) hk)
  have hfun : ⇑(toZeroCLM (A := A) (F := G) hr1.le hk) =
      ofLE (A := A) (k := 0) (F := G) hr1.le ∘ ⇑(holderToZeroOneCLM (A := A) (G := G) (r := r) hk) := by
    funext u
    exact HolderAtlas.HolderMap.ext fun _ => rfl
  rw [hfun]
  exact h

/-- A continuous linear functional is a compact operator. -/
theorem isCompactOperator_of_real {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ℓ : X →L[ℝ] ℝ) : IsCompactOperator ℓ :=
  (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, Metric.closedBall 0 ‖ℓ‖,
      isCompact_closedBall 0 _, by
        rintro _ ⟨x, hx, rfl⟩
        rw [mem_closedBall_zero_iff] at hx ⊢
        exact (ℓ.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hx)⟩

end Inclusion

/-! ### Lowering the order, evaluation, constants, the integral -/

section Maps

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {r : ℝ≥0} {G : Type} [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- `C^{k+1,r}(M) ⊂ C^{k,r}(M)` as a continuous linear map. -/
def lowerCLM {k : ℕ} (hr : r ≤ 1) : A.HolderMap (k + 1) r G →L[ℝ] A.HolderMap k r G :=
  LinearMap.mkContinuous
    { toFun := lowerMap hr
      map_add' := fun _ _ => HolderAtlas.HolderMap.ext fun _ => rfl
      map_smul' := fun _ _ => HolderAtlas.HolderMap.ext fun _ => rfl }
    (k + 3) (norm_lowerMap_le hr)

/-- `C^{k+2,r}(M) ⊂ C^{2,r}(M)` as a continuous linear map. -/
def lowerToTwo (hr : r ≤ 1) : (k : ℕ) → A.HolderMap (k + 2) r G →L[ℝ] A.HolderMap 2 r G
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (lowerToTwo hr k).comp (lowerCLM (k := k + 2) hr)

@[simp]
theorem coe_lowerToTwo (hr : r ≤ 1) : ∀ (k : ℕ) (u : A.HolderMap (k + 2) r G),
    ⇑(lowerToTwo hr k u) = ⇑u
  | 0, _ => rfl
  | k + 1, u => by
    change ⇑(lowerToTwo hr k (lowerMap hr u)) = _
    rw [coe_lowerToTwo hr k, coe_lowerMap]

/-- Evaluation at a point, `|u(y)| ≤ ‖u‖`. -/
def evalCLM {k : ℕ} (y : M) : A.HolderMap k r ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => u y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun u => by
      rw [one_mul, Real.norm_eq_abs]
      exact ManifoldContinuity.abs_apply_le_norm u y

@[simp]
theorem evalCLM_apply {k : ℕ} (y : M) (u : A.HolderMap k r ℝ) : evalCLM y u = u y :=
  rfl

/-- The constant function `1` in `C^{k,r}(M)`. -/
def one {k : ℕ} (hr : r ≤ 1) : A.HolderMap k r ℝ :=
  ofChartSmooth hr (fun _ => 1) (ProductTestForms.chartSmooth_const 1)

@[simp]
theorem one_apply {k : ℕ} (hr : r ≤ 1) (y : M) : one (A := A) (k := k) hr y = 1 :=
  rfl

/-- Maps of `C^{k+2,r}(M)` are `C²` in every chart. -/
theorem contDiffOn_comp_symm {k : ℕ} (hr : r ≤ 1) (u : A.HolderMap (k + 2) r ℝ)
    (e : ComplexChart n M) : ContDiffOn ℝ 2 (fun z => u (e.val.symm z)) e.val.target :=
  fun _ hz => ((holderAt_comp_symm hr u e hz).contDiffAt.of_le
    (by exact_mod_cast Nat.le_add_left 2 k)).contDiffWithinAt

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem integrable_holderMap {k : ℕ} (μ : Measure M) [IsFiniteMeasure μ]
    (u : A.HolderMap k r ℝ) : Integrable u μ :=
  (HolderAtlas.HolderMap.continuous u).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- The integral `u ↦ ∫ u dμ` on `C^{k,r}(M)`, for a finite measure `μ`. -/
def integralCLM {k : ℕ} (μ : Measure M) [IsFiniteMeasure μ] : A.HolderMap k r ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, u x ∂μ
      map_add' := fun u v => by
        simp only [coe_add, Pi.add_apply]
        exact integral_add (integrable_holderMap μ u) (integrable_holderMap μ v)
      map_smul' := fun c u => by
        simp only [coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    (μ.real univ) fun u => by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => u x) (C := ‖u‖)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact ManifoldContinuity.abs_apply_le_norm u x)
      show ‖∫ x, u x ∂μ‖ ≤ μ.real univ * ‖u‖
      rw [mul_comm]
      exact h

@[simp]
theorem integralCLM_apply {k : ℕ} (μ : Measure M) [IsFiniteMeasure μ] (u : A.HolderMap k r ℝ) :
    integralCLM μ u = ∫ x, u x ∂μ :=
  rfl

end Maps

/-! ### The Laplacian on `C^{k+2,r}(M)` -/

section LaplacianK

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {r : ℝ≥0}

/-- The Laplacian of a constant vanishes. -/
theorem laplacian_const (g : SmoothRealForm n M 2) (c : ℝ) (y : M) :
    laplacian g (fun _ => c) y = 0 := by
  simp [laplacian, chartLaplacian]

/-- **Regularity** (blueprint `bou:kahler-laplacian-solvability`, through `bou:schauder-global`):
if `u ∈ C^{2,r}(M)` and `Δ_g u = h ∈ C^{k,r}(M)`, then `u ∈ C^{k+2,r}(M)`. -/
theorem exists_holderMap_of_laplacian_eq {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (hr0 : 0 < r) (hr1 : r < 1) {k : ℕ} (u : A.HolderMap 2 r ℝ) (h : A.HolderMap k r ℝ)
    (heq : ∀ y, laplacian g u y = h y) : ∃ v : A.HolderMap (k + 2) r ℝ, ⇑v = ⇑u := by
  refine ManifoldSchauderRegularity.exists_holderMap_of_holderAt hr1.le fun i z hz => ?_
  set e := A.chart i with he
  obtain ⟨a, ha⟩ : ∃ a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n,
      a = fun x => lapCoeff (normalizedHermitianMatrix (g.coeff e x)) := ⟨_, rfl⟩
  have hsymm : ∀ x ∈ e.val.target, ∀ p q, ⟪a x p, q⟫ = ⟪p, a x q⟫ := fun x hx p q => by
    rw [ha]
    exact lapCoeff_symm (posDef_coeff hg hx).isHermitian p q
  have hpos : ∀ x ∈ e.val.target, ∀ p, p ≠ 0 → 0 < ⟪a x p, p⟫ := fun x hx p hp => by
    rw [ha]
    exact lapCoeff_pos (posDef_coeff hg hx) hp
  have hsm : ContDiffOn ℝ ∞ a e.val.target := by
    rw [ha]
    exact contDiffOn_lapCoeff e.val.open_target (g.smooth e) fun x hx =>
      isUnit_iff_ne_zero.mpr (posDef_coeff hg hx).det_pos.ne'
  have haH : ∀ j : ℕ, ∀ x ∈ e.val.target, HolderAt j r a x := fun j x hx =>
    holderAt_of_contDiffAt hr1.le ((hsm.contDiffAt (e.val.open_target.mem_nhds hx)).of_le
      (by exact_mod_cast le_top))
  have hh : ∀ x ∈ e.val.target, HolderAt k r (fun y => h (e.val.symm y)) x := fun x hx =>
    holderAt_comp_symm hr1.le h e hx
  have hu2 := contDiffOn_comp_symm (k := 0) hr1.le u
  have heqU : ∀ x ∈ e.val.target,
      hessTrace realBasis (a x) (fderiv ℝ (fderiv ℝ (fun y => u (e.val.symm y))) x) =
        h (e.val.symm x) := by
    intro x hx
    rw [← heq, laplacian_eq hg hu2 (e.val.map_target hx), e.val.right_inv hx,
      chartLaplacian_eq_hessTrace realBasis, ha]
  have key : ∀ j, j ≤ k → ∀ x ∈ e.val.target,
      HolderAt (j + 2) r (fun y => u (e.val.symm y)) x := by
    intro j
    induction j with
    | zero => exact fun _ x hx => holderAt_comp_symm hr1.le u e hx
    | succ j ih =>
      intro hjk
      exact LinearRegularity.holderAt_of_hessTrace_eq realBasis hr0 hr1 e.val.open_target hsymm
        hpos (j + 1) (by omega) (fun y => h (e.val.symm y)) (fun y => u (e.val.symm y))
        (fun x hx => haH (j + 1) x hx) (fun x hx => (hh x hx).of_le hr1.le (by omega))
        (ih (by omega)) heqU
  exact key k le_rfl z hz

/-- `Δ_g` maps `C^{k+2,r}(M)` into `C^{k,r}(M)`. -/
theorem exists_holderMap_laplacian {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (hr1 : r < 1) {k : ℕ} (v : A.HolderMap (k + 2) r ℝ) :
    ∃ f : A.HolderMap k r ℝ, ⇑f = laplacian g v := by
  refine ManifoldSchauderRegularity.exists_holderMap_of_holderAt hr1.le fun i z hz => ?_
  set e := A.chart i with he
  obtain ⟨a, ha⟩ : ∃ a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n,
      a = fun x => lapCoeff (normalizedHermitianMatrix (g.coeff e x)) := ⟨_, rfl⟩
  have hsm : ContDiffOn ℝ ∞ a e.val.target := by
    rw [ha]
    exact contDiffOn_lapCoeff e.val.open_target (g.smooth e) fun x hx =>
      isUnit_iff_ne_zero.mpr (posDef_coeff hg hx).det_pos.ne'
  have haH : HolderAt k r a z :=
    holderAt_of_contDiffAt hr1.le ((hsm.contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (by exact_mod_cast le_top))
  have hV : HolderAt (k + 2) r (fun y => v (e.val.symm y)) z := holderAt_comp_symm hr1.le v e hz
  have hD2 : HolderAt k r (fderiv ℝ (fderiv ℝ (fun y => v (e.val.symm y)))) z :=
    hV.derivative.derivative
  have hF : HolderAt k r (fun x => hessTrace realBasis (a x)
      (fderiv ℝ (fderiv ℝ (fun y => v (e.val.symm y))) x)) z := by
    unfold hessTrace
    refine HolderAt.sum _ fun i _ => ?_
    have h1 := hD2.clm hr1.le
      (ContinuousLinearMap.apply ℝ (ComplexModel n →L[ℝ] ℝ) (realBasis i))
    have h2 := haH.clm hr1.le (ContinuousLinearMap.apply ℝ (ComplexModel n) (realBasis i))
    exact h1.bilinear hr1.le (ContinuousLinearMap.id ℝ _) h2
  refine hF.congr ?_
  filter_upwards [e.val.open_target.mem_nhds hz] with x hx
  rw [laplacian_eq hg (contDiffOn_comp_symm hr1.le v) (e.val.map_target hx), e.val.right_inv hx,
    chartLaplacian_eq_hessTrace realBasis, ha]

/-- `Δ_g v` through `C^{2,r}(M)`: `Δ_g v = laplacianCLM (v as an element of C^{2,r})`. -/
theorem laplacian_eq_laplacianCLM {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (hr0 : 0 < r)
    (hr1 : r < 1) {k : ℕ} (v : A.HolderMap (k + 2) r ℝ) (y : M) :
    laplacian g v y = laplacianCLM hg A hr0 hr1 (lowerToTwo hr1.le k v) y := by
  rw [laplacianCLM_apply, coe_lowerToTwo]

/-- **The Laplacian `C^{k+2,r}(M) → C^{k,r}(M)`** as a linear map. -/
def laplacianLMk {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) : A.HolderMap (k + 2) r ℝ →ₗ[ℝ] A.HolderMap k r ℝ where
  toFun v := (exists_holderMap_laplacian hg hr1 v).choose
  map_add' u v := HolderAtlas.HolderMap.ext fun y => by
    have e1 := congrFun (exists_holderMap_laplacian hg hr1 (u + v)).choose_spec y
    have e2 := congrFun (exists_holderMap_laplacian hg hr1 u).choose_spec y
    have e3 := congrFun (exists_holderMap_laplacian hg hr1 v).choose_spec y
    change (exists_holderMap_laplacian hg hr1 (u + v)).choose y =
      (exists_holderMap_laplacian hg hr1 u).choose y + (exists_holderMap_laplacian hg hr1 v).choose y
    rw [e1, e2, e3, laplacian_eq_laplacianCLM hg hr0 hr1 (u + v),
      laplacian_eq_laplacianCLM hg hr0 hr1 u, laplacian_eq_laplacianCLM hg hr0 hr1 v, map_add,
      map_add, coe_add, Pi.add_apply]
  map_smul' c v := HolderAtlas.HolderMap.ext fun y => by
    have e1 := congrFun (exists_holderMap_laplacian hg hr1 (c • v)).choose_spec y
    have e2 := congrFun (exists_holderMap_laplacian hg hr1 v).choose_spec y
    change (exists_holderMap_laplacian hg hr1 (c • v)).choose y =
      c • (exists_holderMap_laplacian hg hr1 v).choose y
    rw [e1, e2, laplacian_eq_laplacianCLM hg hr0 hr1 (c • v),
      laplacian_eq_laplacianCLM hg hr0 hr1 v, map_smul, map_smul, coe_smul, Pi.smul_apply]

theorem laplacianLMk_apply {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) (v : A.HolderMap (k + 2) r ℝ) (y : M) :
    laplacianLMk hg hr0 hr1 k v y = laplacian g v y :=
  congrFun (exists_holderMap_laplacian hg hr1 v).choose_spec y

/-- **`Δ_g : C^{k+2,r}(M) → C^{k,r}(M)` is bounded** (closed graph theorem: convergence in
`C^{k+2,r}` gives convergence of `Δ_g` in `C^{0,r}`, hence pointwise). -/
theorem continuous_laplacianLMk {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) : Continuous (laplacianLMk (A := A) hg hr0 hr1 k) := by
  refine (laplacianLMk (A := A) hg hr0 hr1 k).continuous_of_seq_closed_graph fun u x f hu hf => ?_
  refine HolderAtlas.HolderMap.ext fun y => ?_
  have h1 : Tendsto (fun j => laplacianLMk hg hr0 hr1 k (u j) y) atTop (𝓝 (f y)) :=
    ((evalCLM (A := A) (r := r) (k := k) y).continuous.tendsto f).comp hf
  have h2 : Tendsto (fun j => laplacianLMk hg hr0 hr1 k (u j) y) atTop
      (𝓝 (laplacianLMk hg hr0 hr1 k x y)) := by
    simp only [laplacianLMk_apply, laplacian_eq_laplacianCLM hg hr0 hr1]
    exact (((evalCLM (A := A) (r := r) (k := 0) y).continuous.comp
      ((laplacianCLM hg A hr0 hr1).continuous.comp
        (lowerToTwo hr1.le k).continuous)).tendsto x).comp hu
  exact tendsto_nhds_unique h1 h2

/-- **The Laplacian `C^{k+2,r}(M) →L C^{k,r}(M)`.** -/
def laplacianCLMk {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) : A.HolderMap (k + 2) r ℝ →L[ℝ] A.HolderMap k r ℝ :=
  ⟨laplacianLMk hg hr0 hr1 k, continuous_laplacianLMk hg hr0 hr1 k⟩

@[simp]
theorem laplacianCLMk_apply {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) (v : A.HolderMap (k + 2) r ℝ) (y : M) :
    laplacianCLMk hg hr0 hr1 k v y = laplacian g v y :=
  laplacianLMk_apply hg hr0 hr1 k v y

end LaplacianK

/-! ### Solvability -/

section Solvability

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {A : HolderAtlas n M} {r : ℝ≥0}

/-- The Kähler volume of `M` is positive. -/
theorem kahlerVolume_real_univ_pos (w : KahlerBackground n M) : 0 < (kahlerVolume w).real univ := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (kahlerVolume_pos_of_isOpen w isOpen_univ univ_nonempty).ne'
    (measure_ne_top _ _)

/-- Stokes for maps of `C^{k+2,r}(M)`. -/
theorem integral_laplacian_holderMap (w : KahlerBackground n M) (hr1 : r < 1) {k : ℕ}
    (u : A.HolderMap (k + 2) r ℝ) : ∫ x, laplacian w.form.val u x ∂(kahlerVolume w) = 0 :=
  integral_laplacian_eq_zero w (contDiffOn_comp_symm hr1.le u)

/-- **`T u = Δ_ω u + ∫ u ω^N` is one-to-one** on `C^{2,r}(M)`. -/
theorem eq_zero_of_laplacian_add_integral (w : KahlerBackground n M) (hr1 : r < 1) {k : ℕ}
    (u : A.HolderMap (k + 2) r ℝ)
    (h : ∀ y, laplacian w.form.val u y + ∫ x, u x ∂(kahlerVolume w) = 0) : u = 0 := by
  set μ := kahlerVolume w with hμ
  set c := ∫ x, u x ∂μ with hc
  have hV := kahlerVolume_real_univ_pos w
  have h1 : ∀ y, laplacian w.form.val u y = -c := fun y => by linarith [h y]
  have hint := integral_laplacian_holderMap w hr1 u
  simp only [h1, integral_const, smul_eq_mul] at hint
  have hc0 : c = 0 := by
    have : μ.real univ * c = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hV.ne'
  have hΔ : ∀ y, laplacian w.form.val u y = 0 := fun y => by rw [h1, hc0, neg_zero]
  obtain ⟨d, hd⟩ := exists_eq_const_of_laplacian_eq_zero w (contDiffOn_comp_symm hr1.le u) hΔ
  have hd0 : d = 0 := by
    have : c = μ.real univ * d := by
      rw [hc]
      simp only [hd, integral_const, smul_eq_mul]
    rw [hc0] at this
    exact ((mul_eq_zero.1 this.symm).resolve_left hV.ne')
  exact HolderAtlas.HolderMap.ext fun y => by rw [hd, hd0]; rfl

/-- **The Fredholm step** (`k = 0`): `T u = Δ_ω u + (∫ u ω^N) · 1` is a bijection
`C^{2,r}(M) → C^{0,r}(M)`. -/
theorem bijective_laplacianCLM_add (w : KahlerBackground n M) (A : HolderAtlas n M)
    (hr0 : 0 < r) (hr1 : r < 1) :
    Function.Bijective (laplacianCLM w.isKahler.1 A hr0 hr1 +
      (integralCLM (A := A) (k := 2) (r := r) (kahlerVolume w)).smulRight
        (one (A := A) (k := 0) hr1.le)) := by
  set g := w.form.val with hgdef
  have hg : g.IsHermitian := w.isKahler.1
  set ℓ := integralCLM (A := A) (k := 2) (r := r) (kahlerVolume w) with hℓ
  set P := ℓ.smulRight (one (A := A) (k := 0) hr1.le) with hP
  set T := laplacianCLM hg A hr0 hr1 + P with hT
  set L1 := laplacianSubEquiv hg A hr0 hr1 (s := 1) one_pos with hL1
  set ι := toZeroCLM (A := A) (F := ℝ) (k := 2) hr1.le (by norm_num) with hι
  set K : A.HolderMap 2 r ℝ →L[ℝ] A.HolderMap 2 r ℝ :=
    (L1.symm : A.HolderMap 0 r ℝ →L[ℝ] A.HolderMap 2 r ℝ).comp (ι + P) with hK
  have hTK : T = (L1 : A.HolderMap 2 r ℝ →L[ℝ] A.HolderMap 0 r ℝ).comp (1 + K) := by
    refine ContinuousLinearMap.ext fun u => HolderAtlas.HolderMap.ext fun y => ?_
    simp only [hT, hK, ContinuousLinearMap.comp_apply, _root_.add_apply,
      one_apply_eq_self, map_add, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, coe_add, Pi.add_apply, hL1,
      laplacianSubEquiv_apply, laplacianCLM_apply, hι, coe_toZeroCLM, hP,
      ContinuousLinearMap.smulRight_apply, coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  -- compactness of `K`
  have hιc : IsCompactOperator ι := isCompactOperator_toZeroCLM hr1 (by norm_num)
  have hPc : IsCompactOperator P := by
    have h := (isCompactOperator_of_real ℓ).continuous_comp
      (g := fun t : ℝ => t • one (A := A) (k := 0) hr1.le) (continuous_id.smul continuous_const)
    have hfun : ⇑P = (fun t : ℝ => t • one (A := A) (k := 0) hr1.le) ∘ ⇑ℓ := by
      funext u
      rfl
    rw [hfun]
    exact h
  have hKc : IsCompactOperator K := by
    have h := (hιc.add hPc).clm_comp (L1.symm : A.HolderMap 0 r ℝ →L[ℝ] A.HolderMap 2 r ℝ)
    have hfun : ⇑K = ⇑(L1.symm : A.HolderMap 0 r ℝ →L[ℝ] A.HolderMap 2 r ℝ) ∘ (⇑ι + ⇑P) := by
      funext u
      rfl
    rw [hfun]
    exact h
  -- `T` and `1 + K` are one-to-one
  have hTinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun u hu => ?_
    refine eq_zero_of_laplacian_add_integral (k := 0) w hr1 u fun y => ?_
    have := congrArg (fun f : A.HolderMap 0 r ℝ => f y) hu
    simpa [hT, hP, hℓ] using this
  have hinj : Function.Injective ((1 + K : A.HolderMap 2 r ℝ →L[ℝ] A.HolderMap 2 r ℝ)) := by
    intro u v huv
    apply hTinj
    rw [hTK, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, huv]
  -- the Fredholm alternative for `K` at `-1`
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet hKc (μ := (-1 : ℝ)) (by norm_num)
    with hev | hres
  · exfalso
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hKv : K v = -v := by
      have := hv.apply_eq_smul
      simpa using this
    refine hv.right (hinj ?_)
    simp [hKv]
  · rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, neg_one_smul, ← neg_add',
      IsUnit.neg_iff, ContinuousLinearMap.isUnit_iff_bijective] at hres
    rw [hTK, ContinuousLinearMap.coe_comp]
    exact L1.bijective.comp hres

/-- **Solvability for `k = 0`**: for `h ∈ C^{0,r}(M)` with `∫ h ω^N = 0` there is
`u ∈ C^{2,r}(M)` with `Δ_ω u = h`. -/
theorem exists_laplacian_eq_of_integral_eq_zero_zero (w : KahlerBackground n M)
    (A : HolderAtlas n M) (hr0 : 0 < r) (hr1 : r < 1) (h : A.HolderMap 0 r ℝ)
    (hh : ∫ x, h x ∂(kahlerVolume w) = 0) :
    ∃ u : A.HolderMap 2 r ℝ, ∀ y, laplacian w.form.val u y = h y := by
  obtain ⟨u, hu⟩ := (bijective_laplacianCLM_add w A hr0 hr1).2 h
  have hpt : ∀ y, laplacian w.form.val u y + ∫ x, u x ∂(kahlerVolume w) = h y := fun y => by
    have := congrArg (fun f : A.HolderMap 0 r ℝ => f y) hu
    simpa using this
  have hV := kahlerVolume_real_univ_pos w
  have hint := integral_laplacian_holderMap w hr1 (k := 0) u
  have hΔ : ∀ y, laplacian w.form.val u y = h y - ∫ x, u x ∂(kahlerVolume w) := fun y => by
    linarith [hpt y]
  simp only [hΔ] at hint
  rw [integral_sub (integrable_holderMap _ h) (integrable_const _), hh, integral_const,
    smul_eq_mul, zero_sub, neg_eq_zero] at hint
  have hc : ∫ x, u x ∂(kahlerVolume w) = 0 := (mul_eq_zero.1 hint).resolve_left hV.ne'
  exact ⟨u, fun y => by rw [hΔ, hc, sub_zero]⟩

/-- **Blueprint `bou:kahler-laplacian-solvability` (2), existence**: for every `h ∈ C^{k,r}(M)` with
`∫ h ω^N = 0` there is `u ∈ C^{k+2,r}(M)` with `Δ_ω u = h`. -/
theorem exists_laplacian_eq_of_integral_eq_zero (w : KahlerBackground n M) (A : HolderAtlas n M)
    (hr0 : 0 < r) (hr1 : r < 1) {k : ℕ} (h : A.HolderMap k r ℝ)
    (hh : ∫ x, h x ∂(kahlerVolume w) = 0) :
    ∃ u : A.HolderMap (k + 2) r ℝ, ∀ y, laplacian w.form.val u y = h y := by
  obtain ⟨h0, hh0⟩ : ∃ h0 : A.HolderMap 0 r ℝ, ⇑h0 = ⇑h := by
    rcases k with _ | k
    · exact ⟨h, rfl⟩
    · exact ⟨toZero hr1.le (by omega) h, rfl⟩
  obtain ⟨u0, hu0⟩ := exists_laplacian_eq_of_integral_eq_zero_zero w A hr0 hr1 h0
    (by rw [hh0]; exact hh)
  have hu0' : ∀ y, laplacian w.form.val u0 y = h y := fun y => by rw [hu0, hh0]
  obtain ⟨u, hu⟩ := exists_holderMap_of_laplacian_eq w.isKahler.1 hr0 hr1 u0 h hu0'
  exact ⟨u, fun y => by rw [hu]; exact hu0' y⟩

/-- **Blueprint `bou:kahler-laplacian-solvability` (2), uniqueness**: two solutions differ by a
constant. -/
theorem exists_eq_add_const_of_laplacian_eq (w : KahlerBackground n M) (hr1 : r < 1) {k : ℕ}
    (u v : A.HolderMap (k + 2) r ℝ) (h : ∀ y, laplacian w.form.val u y = laplacian w.form.val v y) :
    ∃ c, ∀ y, u y = v y + c := by
  have hd : ∀ e : ComplexChart n M,
      ContDiffOn ℝ 2 (fun z => (fun x => u x - v x) (e.val.symm z)) e.val.target := fun e =>
    (contDiffOn_comp_symm hr1.le u e).sub (contDiffOn_comp_symm hr1.le v e)
  have hΔ : ∀ y, laplacian w.form.val (fun x => u x - v x) y = 0 := by
    intro y
    have hs := laplacian_sum w.form.val (Finset.univ : Finset (Fin 2))
      (f := ![fun x => u x, fun x => -v x]) (by
        intro i _ e
        fin_cases i
        · exact contDiffOn_comp_symm hr1.le u e
        · exact (contDiffOn_comp_symm hr1.le v e).neg) y
    have hn : laplacian w.form.val (fun x => -v x) y = -laplacian w.form.val v y := by
      have hs' := laplacian_sum w.form.val (Finset.univ : Finset (Fin 2))
        (f := ![fun x => v x, fun x => -v x]) (by
          intro i _ e
          fin_cases i
          · exact contDiffOn_comp_symm hr1.le v e
          · exact (contDiffOn_comp_symm hr1.le v e).neg) y
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        add_neg_cancel] at hs'
      rw [laplacian_const] at hs'
      linarith
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← sub_eq_add_neg] at hs
    rw [hs, hn, h y]
    ring
  obtain ⟨c, hc⟩ := exists_eq_const_of_laplacian_eq_zero w hd hΔ
  exact ⟨c, fun y => by linarith [hc y]⟩

/-- The map `(v, σ) ↦ Δ_ω v - σ`, `{v ∈ C^{k+2,r}(M) : ∫ v ω^N = 0} × ℝ →L C^{k,r}(M)`. -/
def laplacianConstCLM (w : KahlerBackground n M) (A : HolderAtlas n M) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :
    (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker × ℝ →L[ℝ]
      A.HolderMap k r ℝ :=
  ((laplacianCLMk w.isKahler.1 hr0 hr1 k).comp
    (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker.subtypeL).coprod
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (-one (A := A) (k := k) hr1.le))

theorem laplacianConstCLM_apply (w : KahlerBackground n M) (A : HolderAtlas n M) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) (p : (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker × ℝ)
    (y : M) :
    laplacianConstCLM w A hr0 hr1 k p y =
      laplacian w.form.val (p.1 : A.HolderMap (k + 2) r ℝ) y - p.2 := by
  simp [laplacianConstCLM, sub_eq_add_neg]

/-- **The isomorphism** of blueprint `bou:kahler-laplacian-solvability`:
`(v, σ) ↦ Δ_ω v - σ`, `{v ∈ C^{k+2,r}(M) : ∫ v ω^N = 0} × ℝ → C^{k,r}(M)`, is bijective. -/
theorem bijective_laplacianConstCLM (w : KahlerBackground n M) (A : HolderAtlas n M)
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    Function.Bijective (laplacianConstCLM w A hr0 hr1 k) := by
  set μ := kahlerVolume w with hμ
  have hV := kahlerVolume_real_univ_pos w
  set S := (integralCLM (A := A) (k := k + 2) (r := r) μ).ker with hS
  have hΦapp := laplacianConstCLM_apply w A hr0 hr1 k
  constructor
  · refine (injective_iff_map_eq_zero (laplacianConstCLM w A hr0 hr1 k)).2 fun p hp => ?_
    have hpt : ∀ y, laplacian w.form.val (p.1 : A.HolderMap (k + 2) r ℝ) y = p.2 := fun y => by
      have := congrArg (fun f : A.HolderMap k r ℝ => f y) hp
      simp only [hΦapp, coe_zero, Pi.zero_apply] at this
      linarith
    have hint := integral_laplacian_holderMap w hr1 (p.1 : A.HolderMap (k + 2) r ℝ)
    simp only [hpt, integral_const, smul_eq_mul] at hint
    have hσ : p.2 = 0 := (mul_eq_zero.1 hint).resolve_left hV.ne'
    have hΔ : ∀ y, laplacian w.form.val (p.1 : A.HolderMap (k + 2) r ℝ) y = 0 := fun y => by
      rw [hpt, hσ]
    obtain ⟨c, hc⟩ := exists_eq_const_of_laplacian_eq_zero w
      (contDiffOn_comp_symm hr1.le (p.1 : A.HolderMap (k + 2) r ℝ)) hΔ
    have hmem : ∫ x, (p.1 : A.HolderMap (k + 2) r ℝ) x ∂μ = 0 := p.1.2
    simp only [hc, integral_const, smul_eq_mul] at hmem
    have hc0 : c = 0 := (mul_eq_zero.1 hmem).resolve_left hV.ne'
    have hp1 : p.1 = 0 := Subtype.ext (HolderAtlas.HolderMap.ext fun y => by rw [hc, hc0]; rfl)
    exact Prod.ext hp1 hσ
  · intro f
    set σ := -(∫ x, f x ∂μ) / μ.real univ with hσ
    obtain ⟨u, hu⟩ := exists_laplacian_eq_of_integral_eq_zero w A hr0 hr1
      (f + σ • one (A := A) (k := k) hr1.le) (by
        simp only [coe_add, coe_smul, Pi.add_apply, Pi.smul_apply, one_apply, smul_eq_mul,
          mul_one]
        rw [integral_add (integrable_holderMap μ f) (integrable_const _), integral_const,
          smul_eq_mul, hσ, mul_div_cancel₀ _ hV.ne', add_neg_cancel])
    set m := (∫ x, u x ∂μ) / μ.real univ with hm
    set v : A.HolderMap (k + 2) r ℝ := u - m • one (A := A) (k := k + 2) hr1.le with hv
    have hvS : v ∈ S := by
      show ∫ x, v x ∂μ = 0
      simp only [hv, coe_sub, coe_smul, Pi.sub_apply, Pi.smul_apply, one_apply, smul_eq_mul,
        mul_one]
      rw [integral_sub (integrable_holderMap μ u) (integrable_const _), integral_const,
        smul_eq_mul, hm, mul_div_cancel₀ _ hV.ne', sub_self]
    refine ⟨(⟨v, hvS⟩, σ), HolderAtlas.HolderMap.ext fun y => ?_⟩
    rw [hΦapp]
    have hΔv : laplacian w.form.val v y = laplacian w.form.val u y := by
      rw [← laplacianCLMk_apply w.isKahler.1 hr0 hr1 k v, hv, map_sub, map_smul, coe_sub,
        coe_smul, Pi.sub_apply, Pi.smul_apply, laplacianCLMk_apply, laplacianCLMk_apply]
      have h1 : laplacian w.form.val (one (A := A) (k := k + 2) hr1.le) y = 0 :=
        laplacian_const _ 1 y
      rw [h1, smul_zero, sub_zero]
    show laplacian w.form.val v y - σ = f y
    rw [hΔv, hu]
    simp [smul_eq_mul]

/-- **Blueprint `bou:kahler-laplacian-solvability`, the isomorphism** `(v, σ) ↦ Δ_ω v - σ`,
`{v ∈ C^{k+2,r}(M) : ∫ v ω^N = 0} × ℝ ≃L C^{k,r}(M)` (a bounded bijection between Banach spaces,
hence an isomorphism by the open mapping theorem). -/
def laplacianConstEquiv (w : KahlerBackground n M) (A : HolderAtlas n M) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :=
  ContinuousLinearEquiv.ofBijective
    (E := (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker × ℝ)
    (F := A.HolderMap k r ℝ) (𝕜 := ℝ) (laplacianConstCLM w A hr0 hr1 k)
    (by exact LinearMap.ker_eq_bot.mpr (bijective_laplacianConstCLM w A hr0 hr1 k).1)
    (by exact LinearMap.range_eq_top.mpr (bijective_laplacianConstCLM w A hr0 hr1 k).2)

theorem laplacianConstEquiv_apply (w : KahlerBackground n M) (A : HolderAtlas n M) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) (p : (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker × ℝ)
    (y : M) :
    laplacianConstEquiv w A hr0 hr1 k p y =
      laplacian w.form.val (p.1 : A.HolderMap (k + 2) r ℝ) y - p.2 := by
  rw [laplacianConstEquiv, ContinuousLinearEquiv.coeFn_ofBijective, laplacianConstCLM_apply]

end Solvability

end SGPT.Foundations.Analysis.Pending.KahlerLaplacianSolvability
