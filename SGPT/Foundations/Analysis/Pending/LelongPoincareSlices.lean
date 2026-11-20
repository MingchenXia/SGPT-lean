import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable

/-!
# The Lelong--Poincaré formula in several variables, in slice form

Let `E` be a finite-dimensional real normed space with a σ-finite measure `μ` (in the applications
`E = ℂ^{n-1}` with Lebesgue measure, so that `ℂ × E = ℂ^n`), let `U ⊆ ℂ × E` be open, and let `G`
be a function on `U` whose slices `s ↦ G (s, w)` are meromorphic and nowhere locally zero (for
`μ`-almost every `w`).  For a smooth test function `χ` with compact support in `U`,

  `∫ log ‖G‖ · Δ_s χ d(λ ⊗ μ) = 2π ∫_w ∑_s ord_s (G (·, w)) · χ (s, w) dμ(w)`

(`integral_log_norm_mul_sliceLaplacian`), where `Δ_s` is the Laplacian in the first variable
(`sliceLaplacian`).  With `ddᶜ = (i/2π) ∂∂̄`, the left side is `4π` times the pairing of
`ddᶜ log ‖G‖²` with `χ` times the volume form of `E` read as a form on `ℂ × E`; the right side
counts the zeros minus the poles of `G` on every complex line `ℂ × {w}`, with multiplicities:
the Levi form of `ddᶜ log |G|²` in the direction of the first factor is the slice measure of the
divisor of `G`.  No analysis of the singular set of the divisor enters.

The proof is Fubini and the one-variable formula
(`LelongPoincareOneVariable.integral_log_norm_mul_laplacian`) on each slice.  The local model of the
divisor at a regular point, `G (s, w) = sᵐ v (s, w)` with `v` without zeros, gives
`∫ log ‖G‖ Δ_s χ = 2π m ∫ χ (0, w) dμ(w)` (`integral_log_norm_mul_sliceLaplacian_pow_mul`): the
current of the hyperplane `{s = 0}` with multiplicity `m`.

This is step (LP3) of the formalization of the blueprint lemma `ana:divisor-lelong-poincare`
(`ana:lelong-poincare-slices`).  Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Laplacian

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.LelongPoincareSlices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The Laplacian in the first variable -/

/-- The Laplacian of `χ` in the first variable: `Δ_s χ (s, w) = Δ (s ↦ χ (s, w)) s`. -/
def sliceLaplacian (χ : ℂ × E → ℝ) (z : ℂ × E) : ℝ :=
  Δ (fun s : ℂ => χ (s, z.2)) z.1

/-- The first-variable Laplacian through the second derivative of `χ` on `ℂ × E`. -/
theorem sliceLaplacian_eq {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ 2 χ) (z : ℂ × E) :
    sliceLaplacian χ z =
      iteratedFDeriv ℝ 2 χ z ![((1 : ℂ), (0 : E)), ((1 : ℂ), (0 : E))] +
        iteratedFDeriv ℝ 2 χ z ![(Complex.I, (0 : E)), (Complex.I, (0 : E))] := by
  obtain ⟨s, w⟩ := z
  have hcomp : (fun t : ℂ => χ (t, w)) =
      (fun p : ℂ × E => χ (p + ((0 : ℂ), w))) ∘ (ContinuousLinearMap.inl ℝ ℂ E) := by
    funext t
    simp
  have hsh : ContDiff ℝ 2 (fun p : ℂ × E => χ (p + ((0 : ℂ), w))) :=
    hχ.comp (contDiff_id.add contDiff_const)
  have key : ∀ v : ℂ, iteratedFDeriv ℝ 2 (fun t : ℂ => χ (t, w)) s ![v, v] =
      iteratedFDeriv ℝ 2 χ (s, w) ![(v, (0 : E)), (v, (0 : E))] := by
    intro v
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hsh _ le_rfl,
      iteratedFDeriv_comp_add_right]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [sliceLaplacian, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [key, key]

theorem continuous_sliceLaplacian {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (sliceLaplacian χ) := by
  have h2 : ContDiff ℝ 2 χ := hχ.of_le ENat.LEInfty.out
  have hc : Continuous (fun z => iteratedFDeriv ℝ 2 χ z) :=
    hχ.continuous_iteratedFDeriv ENat.LEInfty.out
  have : sliceLaplacian χ = fun z =>
      iteratedFDeriv ℝ 2 χ z ![((1 : ℂ), (0 : E)), ((1 : ℂ), (0 : E))] +
        iteratedFDeriv ℝ 2 χ z ![(Complex.I, (0 : E)), (Complex.I, (0 : E))] :=
    funext fun z => sliceLaplacian_eq h2 z
  rw [this]
  exact (hc.eval_const _).add (hc.eval_const _)

theorem support_sliceLaplacian_subset {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Function.support (sliceLaplacian χ) ⊆ tsupport χ := by
  intro z hz
  by_contra hnot
  apply hz
  have h2 : ContDiff ℝ 2 χ := hχ.of_le ENat.LEInfty.out
  have h0 : iteratedFDeriv ℝ 2 χ z = 0 := by
    by_contra hne
    exact hnot (support_iteratedFDeriv_subset 2 hne)
  rw [sliceLaplacian_eq h2 z, h0]
  simp

theorem hasCompactSupport_sliceLaplacian {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) : HasCompactSupport (sliceLaplacian χ) :=
  hχc.mono' (support_sliceLaplacian_subset hχ)

/-! ### Slices of test functions and of open sets -/

/-- The slice `s ↦ χ (s, w)` of a smooth function is smooth. -/
theorem contDiff_slice {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) (w : E) :
    ContDiff ℝ ∞ (fun s : ℂ => χ (s, w)) :=
  hχ.comp (contDiff_id.prodMk contDiff_const)

omit [NormedSpace ℝ E] in
/-- The topological support of a slice lies in the slice of the topological support. -/
theorem tsupport_slice_subset (χ : ℂ × E → ℝ) (w : E) :
    tsupport (fun s : ℂ => χ (s, w)) ⊆ (fun s : ℂ => (s, w)) ⁻¹' tsupport χ :=
  closure_minimal (fun _ hs => subset_tsupport χ hs)
    ((isClosed_tsupport χ).preimage (continuous_id.prodMk continuous_const))

omit [NormedSpace ℝ E] in
theorem hasCompactSupport_slice {χ : ℂ × E → ℝ} (hχc : HasCompactSupport χ) (w : E) :
    HasCompactSupport (fun s : ℂ => χ (s, w)) :=
  IsCompact.of_isClosed_subset (hχc.image continuous_fst) (isClosed_tsupport _)
    fun s hs => ⟨(s, w), tsupport_slice_subset χ w hs, rfl⟩

/-- The slice `{s | (s, w) ∈ U}` of a set `U ⊆ ℂ × E`. -/
def sliceSet (U : Set (ℂ × E)) (w : E) : Set ℂ := {s | (s, w) ∈ U}

omit [NormedSpace ℝ E] in
theorem isOpen_sliceSet {U : Set (ℂ × E)} (hU : IsOpen U) (w : E) : IsOpen (sliceSet U w) :=
  hU.preimage (continuous_id.prodMk continuous_const)

omit [NormedSpace ℝ E] in
theorem tsupport_slice_subset_sliceSet {χ : ℂ × E → ℝ} {U : Set (ℂ × E)}
    (hχU : tsupport χ ⊆ U) (w : E) : tsupport (fun s : ℂ => χ (s, w)) ⊆ sliceSet U w :=
  fun _ hs => hχU (tsupport_slice_subset χ w hs)

/-! ### The formula -/

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SFinite μ]

omit [SFinite μ] in
theorem integrable_log_norm_mul_sliceLaplacian {U : Set (ℂ × E)} {G : ℂ × E → ℂ}
    (hint : LocallyIntegrableOn (fun z => Real.log ‖G z‖) U (volume.prod μ))
    {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    Integrable (fun z => Real.log ‖G z‖ * sliceLaplacian χ z) (volume.prod μ) := by
  have hK : IntegrableOn (fun z => Real.log ‖G z‖) (tsupport χ) (volume.prod μ) :=
    hint.integrableOn_compact_subset hχU hχc
  have hKmul : IntegrableOn (fun z => Real.log ‖G z‖ * sliceLaplacian χ z) (tsupport χ)
      (volume.prod μ) :=
    hK.mul_continuousOn (continuous_sliceLaplacian hχ).continuousOn hχc
  refine hKmul.integrable_of_forall_notMem_eq_zero fun z hz => ?_
  have : sliceLaplacian χ z = 0 := by
    by_contra hne
    exact hz (support_sliceLaplacian_subset hχ hne)
  rw [this, mul_zero]

/-- **The Lelong--Poincaré formula in slice form.**  If the slices `s ↦ G (s, w)` are
meromorphic and nowhere locally zero on the slices of the open set `U` (for `μ`-almost every
`w`) and `log ‖G‖` is locally integrable on `U`, then for every smooth `χ` with compact support
in `U`,
`∫ log ‖G‖ · Δ_s χ = 2π ∫_w ∑_s ord_s (G (·, w)) χ (s, w) dμ(w)`. -/
theorem integral_log_norm_mul_sliceLaplacian {U : Set (ℂ × E)} (hU : IsOpen U)
    {G : ℂ × E → ℂ}
    (hG : ∀ᵐ w ∂μ, MeromorphicOn (fun s => G (s, w)) (sliceSet U w) ∧
      ∀ s : sliceSet U w, meromorphicOrderAt (fun s => G (s, w)) s ≠ ⊤)
    (hint : LocallyIntegrableOn (fun z => Real.log ‖G z‖) U (volume.prod μ))
    {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, Real.log ‖G z‖ * sliceLaplacian χ z ∂(volume.prod μ) =
      2 * Real.pi * ∫ w, ∑ᶠ s, (MeromorphicOn.divisor (fun s => G (s, w)) (sliceSet U w) s : ℝ) *
        χ (s, w) ∂μ := by
  rw [integral_prod_symm _ (integrable_log_norm_mul_sliceLaplacian hint hχ hχc hχU),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hG] with w hw
  have h := LelongPoincareOneVariable.integral_log_norm_mul_laplacian (isOpen_sliceSet hU w)
    (f := fun s => G (s, w)) hw.1 hw.2 (χ := fun s => χ (s, w))
    (contDiff_slice hχ w) (hasCompactSupport_slice hχc w) (tsupport_slice_subset_sliceSet hχU w)
  exact h

/-! ### The local model `sᵐ v` -/

/-- The order of the model slice `t ↦ tᵐ v t` (with `v` analytic and without zeros on `V`) at a
point of `V`: `m` at `0`, and `0` elsewhere. -/
theorem meromorphicOrderAt_pow_mul {V : Set ℂ} {v : ℂ → ℂ} (hva : AnalyticOnNhd ℂ v V)
    (hv0 : ∀ s ∈ V, v s ≠ 0) (m : ℕ) {s : ℂ} (hs : s ∈ V) :
    meromorphicOrderAt (fun t => t ^ m * v t) s = if s = 0 then (m : ℤ) else 0 := by
  have han : AnalyticAt ℂ (fun t => t ^ m * v t) s := (analyticAt_id.pow m).mul (hva s hs)
  rw [han.meromorphicOrderAt_eq]
  split_ifs with h0
  · subst h0
    have : analyticOrderAt (fun t => t ^ m * v t) 0 = m :=
      han.analyticOrderAt_eq_natCast.mpr ⟨v, hva 0 hs, hv0 0 hs,
        Eventually.of_forall fun z => by simp [smul_eq_mul]⟩
    rw [this]
    rfl
  · have : analyticOrderAt (fun t => t ^ m * v t) s = 0 :=
      han.analyticOrderAt_eq_zero.mpr (mul_ne_zero (pow_ne_zero _ h0) (hv0 s hs))
    rw [this]
    rfl

open Classical in
/-- The divisor of the model slice: `m` at `0` if `0 ∈ V`, and `0` elsewhere. -/
theorem divisor_pow_mul {V : Set ℂ} {v : ℂ → ℂ} (hva : AnalyticOnNhd ℂ v V)
    (hv0 : ∀ s ∈ V, v s ≠ 0) (m : ℕ) (s : ℂ) :
    MeromorphicOn.divisor (fun t => t ^ m * v t) V s = if s = 0 ∧ s ∈ V then (m : ℤ) else 0 := by
  have han : AnalyticOnNhd ℂ (fun t => t ^ m * v t) V := fun t ht =>
    (analyticAt_id.pow m).mul (hva t ht)
  by_cases hs : s ∈ V
  · rw [MeromorphicOn.divisor_apply han.meromorphicOn hs, meromorphicOrderAt_pow_mul hva hv0 m hs]
    by_cases h0 : s = 0
    · subst h0
      simp [hs]
    · simp [h0]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hs, if_neg fun h => hs h.2]

/-- **The local model of the Lelong--Poincaré formula** (step LP3): for
`G (s, w) = sᵐ v (s, w)` with `v` analytic in `s` and without zeros on `U`,
`∫ log ‖G‖ Δ_s χ = 2π m ∫ χ (0, w) dμ(w)`: the first-variable Levi form of `ddᶜ log |G|²` is
`m` times the current of the hyperplane `{s = 0}`. -/
theorem integral_log_norm_mul_sliceLaplacian_pow_mul {U : Set (ℂ × E)} (hU : IsOpen U) (m : ℕ)
    {v : ℂ × E → ℂ} (hva : ∀ w, AnalyticOnNhd ℂ (fun s => v (s, w)) (sliceSet U w))
    (hv0 : ∀ z ∈ U, v z ≠ 0)
    (hint : LocallyIntegrableOn (fun z : ℂ × E => Real.log ‖z.1 ^ m * v z‖) U (volume.prod μ))
    {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, Real.log ‖z.1 ^ m * v z‖ * sliceLaplacian χ z ∂(volume.prod μ) =
      2 * Real.pi * m * ∫ w, χ (0, w) ∂μ := by
  have hv0' : ∀ w, ∀ s ∈ sliceSet U w, v (s, w) ≠ 0 := fun w s hs => hv0 _ hs
  have hG : ∀ᵐ w ∂μ, MeromorphicOn (fun s => s ^ m * v (s, w)) (sliceSet U w) ∧
      ∀ s : sliceSet U w, meromorphicOrderAt (fun s => s ^ m * v (s, w)) s ≠ ⊤ := by
    refine Eventually.of_forall fun w => ⟨fun t ht => ((analyticAt_id.pow m).mul
      (hva w t ht)).meromorphicAt, fun s => ?_⟩
    rw [meromorphicOrderAt_pow_mul (hva w) (hv0' w) m s.2]
    split_ifs <;> simp
  rw [integral_log_norm_mul_sliceLaplacian hU (G := fun z => z.1 ^ m * v z) hG hint hχ hχc hχU,
    mul_assoc (2 * Real.pi), ← integral_const_mul (m : ℝ)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change ∑ᶠ s, (MeromorphicOn.divisor (fun s => s ^ m * v (s, w)) (sliceSet U w) s : ℝ) *
      χ (s, w) = (m : ℝ) * χ (0, w)
  rw [finsum_eq_single _ 0 fun s hs => by
    rw [divisor_pow_mul (hva w) (hv0' w) m s, if_neg fun h => hs h.1]
    simp]
  rw [divisor_pow_mul (hva w) (hv0' w) m 0]
  by_cases h0 : (0 : ℂ) ∈ sliceSet U w
  · simp [h0]
  · have : χ (0, w) = 0 := image_eq_zero_of_notMem_tsupport fun h => h0 (hχU h)
    simp [h0, this]

/-! ### Local integrability -/

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem locallyIntegrable_log_norm_fst [IsLocallyFiniteMeasure μ] :
    LocallyIntegrable (fun z : ℂ × E => Real.log ‖z.1‖) (volume.prod μ) := by
  intro z
  obtain ⟨V, hV, hμV⟩ := μ.finiteAt_nhds z.2
  have : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.mpr hμV.ne
  refine ⟨Metric.closedBall z.1 1 ×ˢ V,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) hV, ?_⟩
  have h1 : IntegrableOn (fun s : ℂ => Real.log ‖s‖) (Metric.closedBall z.1 1) :=
    LelongPoincareOneVariable.locallyIntegrable_log_norm.integrableOn_isCompact
      (isCompact_closedBall _ _)
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact h1.comp_fst (μ.restrict V)

omit [NormedSpace ℝ E] in
/-- `log ‖sᵐ v‖` is locally integrable on `U` when `v` is continuous without zeros on `U`. -/
theorem locallyIntegrableOn_log_norm_pow_mul [SecondCountableTopology E]
    [IsLocallyFiniteMeasure μ] {U : Set (ℂ × E)} (hU : IsOpen U) (m : ℕ) {v : ℂ × E → ℂ}
    (hvc : ContinuousOn v U) (hv0 : ∀ z ∈ U, v z ≠ 0) :
    LocallyIntegrableOn (fun z : ℂ × E => Real.log ‖z.1 ^ m * v z‖) U (volume.prod μ) := by
  have h1 : LocallyIntegrableOn (fun z : ℂ × E => (m : ℝ) * Real.log ‖z.1‖) U
      (volume.prod μ) :=
    (locallyIntegrable_log_norm_fst.locallyIntegrableOn U).smul (m : ℝ)
  have h2 : LocallyIntegrableOn (fun z => Real.log ‖v z‖) U (volume.prod μ) :=
    ContinuousOn.locallyIntegrableOn (fun z hz =>
      ((hvc z hz).norm.log (norm_ne_zero_iff.mpr (hv0 z hz)))) hU.measurableSet
  have hnull : (volume.prod μ) {z : ℂ × E | z.1 = 0} = 0 := by
    have : {z : ℂ × E | z.1 = 0} = ({0} : Set ℂ) ×ˢ (univ : Set E) := by
      ext z; simp
    rw [this, Measure.prod_prod, measure_singleton, zero_mul]
  refine (h1.add h2).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hzU
  have hz1 : z.1 ≠ 0 := hz
  simp only [Pi.add_apply]
  rw [norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hz1))
    (norm_ne_zero_iff.mpr (hv0 z hzU)), Real.log_pow]

/-- **The local model, with no integrability hypothesis** (`μ` locally finite, `v` continuous
and without zeros on `U`, analytic in the first variable):
`∫ log ‖sᵐ v‖ Δ_s χ = 2π m ∫ χ (0, w) dμ(w)`. -/
theorem integral_log_norm_mul_sliceLaplacian_pow_mul' [SecondCountableTopology E]
    [IsLocallyFiniteMeasure μ] {U : Set (ℂ × E)} (hU : IsOpen U) (m : ℕ) {v : ℂ × E → ℂ}
    (hvc : ContinuousOn v U) (hva : ∀ w, AnalyticOnNhd ℂ (fun s => v (s, w)) (sliceSet U w))
    (hv0 : ∀ z ∈ U, v z ≠ 0)
    {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, Real.log ‖z.1 ^ m * v z‖ * sliceLaplacian χ z ∂(volume.prod μ) =
      2 * Real.pi * m * ∫ w, χ (0, w) ∂μ :=
  integral_log_norm_mul_sliceLaplacian_pow_mul hU m hva hv0
    (locallyIntegrableOn_log_norm_pow_mul hU m hvc hv0) hχ hχc hχU

end SGPT.Foundations.Analysis.Pending.LelongPoincareSlices
