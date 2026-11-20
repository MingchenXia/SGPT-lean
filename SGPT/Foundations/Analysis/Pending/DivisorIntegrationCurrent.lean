import SGPT.Foundations.Analysis.Pending.DivisorCoarea
import SGPT.Foundations.Analysis.Pending.LelongPoincareLevi
import SGPT.Foundations.Analysis.Pending.LocalCurrents
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.PlurisubharmonicIntegrability
import SGPT.Foundations.Analysis.PositiveDistributionMeasure

set_option autoImplicit false

/-!
# The integration current of a divisor and the Lelong--Poincaré equation on `ℂⁿ`

Let `g` be holomorphic on an open set `Ω ⊆ ℂⁿ`, vanishing identically near no point of `Ω`.  Then
`log |g|²` is locally integrable on `Ω` (`locallyIntegrableOn_log_normSq`; it is plurisubharmonic).
The *integration current of the divisor of `g`* is the distribution-valued real two-form

  `[div g](v, w)(φ) = ∫_{Z_reg} φ(x) m_g(x) τ_x(v, w) dμHE[2n-2](x)`

(`divisorCurrent`, density `divisorDensity`): integration over the regular part of the zero set,
with the Euclidean Hausdorff measure, the multiplicity `m_g` and the transverse form `τ` of
`DivisorRegularLocus`.  Its density is locally integrable
(`locallyIntegrableOn_divisorDensity`): the regular part of the zero set, counted with
multiplicity, has locally finite `(2n-2)`-dimensional measure
(`lintegral_indicator_divisorMult_lt_top`).  We prove the **Lelong--Poincaré equation**

  `ddᶜ log |g|² = [div g]`

as distribution-valued two-forms on `Ω` (`ddC_log_normSq_eq_divisorCurrent`, coefficientwise
`ddC_log_normSq_apply`), with `ddᶜ = (i/2π) ∂∂̄` (`LocalCurrents.ddC`).

## Proof

Both sides are of type `(1,1)`, so it suffices to compare them on `(u, iu)` for unit vectors `u`
(`eq_of_isOneOne`), and on nonnegative tests (`eq_of_forall_nonneg`).  Fix `u` and an orthogonal
splitting `ℂⁿ = ℂ u ⊕ ι(ℂⁿ⁻¹)`; the map `(s, w) ↦ s u + ι w` preserves Lebesgue measure
(`measurePreserving_splitMap`).

* Left side: `ddᶜ log|g|²(u, iu)(φ) = ∫_w Σ_s ord_s g(· u + ι w) φ(s u + ι w) dw` by the slice form
  of Lelong--Poincaré (`LelongPoincareSlices`) (`ddC_apply_I_eq_integral_sliceSum`).
* For almost every `w` all zeros on the line are transverse regular points
  (`DivisorSingularProjection`), where the order of `g` along the line is the multiplicity
  (`ofReal_sliceSum`).
* Right side: the coarea formula (`DivisorCoarea`) rewrites `∫_{Z_tr} τ(u, iu) m φ dμHE` as the
  integral over `w` of the same sums (`lintegral_transverse_eq_ofReal_ddC`).

The local finiteness of `m · μHE` on the regular part, needed to define the current, follows from
the same identity summed over an orthonormal basis (`Σ_j τ(e_j, i e_j) = 1`,
`sum_lineForm_basis`), tested against a bump function equal to `1` on the compact set.
-/

open Set Filter Function MeasureTheory Metric Module
open scoped Topology InnerProductSpace ContDiff ENNReal Distributions

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent

open DivisorRegularLocus HausdorffAreaFormula DivisorCoarea DivisorSingularProjection
  LelongPoincareSlices

section Split

variable {n m : ℕ} {u : EuclideanSpace ℂ (Fin n)}

/-- The real-linear map `(s, w) ↦ s u + ι w` of a splitting. -/
def splitMap (S : Splitting u (EuclideanSpace ℂ (Fin m))) :
    ℂ × EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin m))).smulRight u +
    (S.ι.toContinuousLinearMap.restrictScalars ℝ).comp
      (ContinuousLinearMap.snd ℝ ℂ (EuclideanSpace ℂ (Fin m)))

@[simp] theorem splitMap_apply (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (p : ℂ × EuclideanSpace ℂ (Fin m)) : splitMap S p = p.1 • u + S.ι p.2 := rfl

theorem norm_splitMap_sq (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (s : ℂ) (w : EuclideanSpace ℂ (Fin m)) :
    ‖s • u + S.ι w‖ ^ 2 = ‖s‖ ^ 2 + ‖w‖ ^ 2 := by
  have horth : ⟪s • u, S.ι w⟫_ℂ = 0 := by rw [inner_smul_left, S.inner_ι, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [sq, h, norm_smul, hu, mul_one, LinearIsometry.norm_map]
  ring

/-- The splitting map as a linear isometry from the `L²` product. -/
def splitIsometry (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m))) :
    WithLp 2 (ℂ × EuclideanSpace ℂ (Fin m)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (splitMap S : ℂ × EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)).comp
        (WithLp.linearEquiv 2 ℝ (ℂ × EuclideanSpace ℂ (Fin m))).toLinearMap
      norm_map' := by
        intro p
        have h1 := WithLp.prod_norm_sq_eq_of_L2 p
        have h2 := norm_splitMap_sq hu S p.fst p.snd
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
          ContinuousLinearMap.coe_coe, splitMap_apply]
        have : ‖(WithLp.linearEquiv 2 ℝ (ℂ × EuclideanSpace ℂ (Fin m)) p).1 • u +
            S.ι (WithLp.linearEquiv 2 ℝ (ℂ × EuclideanSpace ℂ (Fin m)) p).2‖ ^ 2 = ‖p‖ ^ 2 := by
          rw [h1]; exact h2
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this }
    (by
      intro y
      refine ⟨WithLp.toLp 2 (⟪u, y⟫_ℂ, S.π y), ?_⟩
      simp only [LinearIsometry.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        ContinuousLinearMap.coe_coe, splitMap_apply]
      exact (S.decomp y).symm)

theorem splitIsometry_toLp (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (p : ℂ × EuclideanSpace ℂ (Fin m)) : splitIsometry hu S (WithLp.toLp 2 p) = splitMap S p :=
  rfl

/-- **The splitting map preserves Lebesgue measure.** -/
theorem measurePreserving_splitMap (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m))) :
    MeasurePreserving (splitMap S) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.toLp 2 (ℂ × EuclideanSpace ℂ (Fin m)))
      (volume.prod volume) volume :=
    (WithLp.volume_preserving_ofLp ℂ (EuclideanSpace ℂ (Fin m))).symm
      (MeasurableEquiv.toLp 2 (ℂ × EuclideanSpace ℂ (Fin m))).symm
  have h2 := (splitIsometry hu S).measurePreserving
  exact h2.comp h1

/-- The splitting map as a homeomorphism. -/
def splitHomeomorph (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m))) :
    ℂ × EuclideanSpace ℂ (Fin m) ≃ₜ EuclideanSpace ℂ (Fin n) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ (EuclideanSpace ℂ (Fin m))).symm.toHomeomorph).trans
    (splitIsometry hu S).toHomeomorph

theorem splitHomeomorph_apply (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (p : ℂ × EuclideanSpace ℂ (Fin m)) : splitHomeomorph hu S p = splitMap S p := rfl

theorem measurableEmbedding_splitMap (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) : MeasurableEmbedding (splitMap S) :=
  (splitHomeomorph hu S).measurableEmbedding

end Split

section Slices

variable {n m : ℕ} {u : EuclideanSpace ℂ (Fin n)}

/-- The Levi form of `φ` in the direction `u` is a quarter of the Laplacian of `φ ∘ splitMap` in the
first variable. -/
theorem leviForm_splitMap (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {φ : EuclideanSpace ℂ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : ℂ × EuclideanSpace ℂ (Fin m)) :
    leviForm φ (splitMap S z) u = sliceLaplacian (φ ∘ splitMap S) z / 4 := by
  have hχ : ContDiff ℝ ∞ (φ ∘ splitMap S) := hφ.comp (splitMap S).contDiff
  rw [sliceLaplacian_eq (hχ.of_le ENat.LEInfty.out) z,
    ContinuousLinearMap.iteratedFDeriv_comp_right (splitMap S) hφ z ENat.LEInfty.out]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h1 : (fun i => splitMap S (![((1 : ℂ), (0 : EuclideanSpace ℂ (Fin m))),
      ((1 : ℂ), (0 : EuclideanSpace ℂ (Fin m)))] i)) = ![u, u] := by
    ext1 i; fin_cases i <;> simp
  have h2 : (fun i => splitMap S (![(Complex.I, (0 : EuclideanSpace ℂ (Fin m))),
      (Complex.I, (0 : EuclideanSpace ℂ (Fin m)))] i)) = ![Complex.I • u, Complex.I • u] := by
    ext1 i; fin_cases i <;> simp
  rw [h1, h2, leviForm, realHessian, realHessian]

theorem locallyIntegrableOn_comp_splitMap (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (hf : LocallyIntegrableOn f Ω volume) :
    LocallyIntegrableOn (f ∘ splitMap S) (splitMap S ⁻¹' Ω) (volume.prod volume) := by
  intro z hz
  obtain ⟨s, hs, hint⟩ := hf (splitMap S z) hz
  refine ⟨splitMap S ⁻¹' s, ?_, ?_⟩
  · have hc : ContinuousWithinAt (splitMap S) (splitMap S ⁻¹' Ω) z :=
      (splitMap S).continuous.continuousWithinAt
    exact hc.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset _ _) hs)
  · exact ((measurePreserving_splitMap hu S).integrableOn_comp_preimage
      (measurableEmbedding_splitMap hu S)).mpr hint

/-- The slice of `g` along `u` over `w`. -/
def sliceFun (S : Splitting u (EuclideanSpace ℂ (Fin m))) (g : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℂ → ℂ := fun s => g (splitMap S (s, w))

theorem sliceFun_eq (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (g : EuclideanSpace ℂ (Fin n) → ℂ) (w : EuclideanSpace ℂ (Fin m)) :
    sliceFun S g w = fun s => g (S.ι w + s • u) := by
  funext s; simp [sliceFun, add_comm]

/-- Off the null set of lines through non-transverse zeros, the slices are analytic and vanish
identically near no point. -/
theorem ae_slice_good (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) :
    ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      w ∉ S.π '' {y | y ∈ Ω ∧ g y = 0 ∧ y ∉ transverseLocus g u} := by
  have h0 := measure_image_bad_eq_zero (volume : Measure (EuclideanSpace ℂ (Fin m))) hΩ hg hg0 hu S
  exact measure_eq_zero_iff_ae_notMem.mp h0

theorem analyticOnNhd_sliceFun (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (w : EuclideanSpace ℂ (Fin m)) :
    AnalyticOnNhd ℂ (sliceFun S g w) (sliceSet (splitMap S ⁻¹' Ω) w) := by
  have hopen : IsOpen (sliceSet (splitMap S ⁻¹' Ω) w) :=
    isOpen_sliceSet (hΩ.preimage (splitMap S).continuous) w
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro s hs
  have hd : DifferentiableAt ℂ g (splitMap S (s, w)) :=
    (hg _ hs).differentiableAt (hΩ.mem_nhds hs)
  have hl : DifferentiableAt ℂ (fun s : ℂ => splitMap S (s, w)) s := by
    simp only [splitMap_apply]
    fun_prop
  exact (hd.comp s hl).differentiableWithinAt

/-- At a transverse zero, the order of the slice is the multiplicity. -/
theorem analyticOrderAt_sliceFun (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {w : EuclideanSpace ℂ (Fin m)} {s : ℂ}
    (hs : splitMap S (s, w) ∈ transverseLocus g u) :
    analyticOrderAt (sliceFun S g w) s = divisorMult g (splitMap S (s, w)) := by
  have hreg := hs.1
  set P := Classical.choice hreg
  have hgy : g (splitMap S (s, w)) = 0 := eq_zero_of_mem_regularLocus hreg
  have htr := (P.mem_transverseLocus_iff P.mem hgy u).mp hs
  rw [sliceFun_eq, P.analyticOrderAt_line (S.ι w) (s₀ := s) (by simp [add_comm]) htr,
    P.divisorMult_eq]

end Slices

section SliceIdentity

variable {n m : ℕ} {u : EuclideanSpace ℂ (Fin n)}

/-- The slice sum `w ↦ Σ_s ord_s (g(· u + ι w)) φ(s u + ι w)`. -/
def sliceSum (S : Splitting u (EuclideanSpace ℂ (Fin m))) (g : EuclideanSpace ℂ (Fin n) → ℂ)
    (Ω : Set (EuclideanSpace ℂ (Fin n))) (φ : EuclideanSpace ℂ (Fin n) → ℝ)
    (w : EuclideanSpace ℂ (Fin m)) : ℝ :=
  ∑ᶠ s, (MeromorphicOn.divisor (sliceFun S g w) (sliceSet (splitMap S ⁻¹' Ω) w) s : ℝ) *
    φ (splitMap S (s, w))

theorem ae_meromorphic_slices (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) :
    ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      MeromorphicOn (fun s => (g ∘ splitMap S) (s, w)) (sliceSet (splitMap S ⁻¹' Ω) w) ∧
      ∀ s : sliceSet (splitMap S ⁻¹' Ω) w,
        meromorphicOrderAt (fun s => (g ∘ splitMap S) (s, w)) s ≠ ⊤ := by
  filter_upwards [ae_slice_good hu S hΩ hg hg0] with w hw
  have han := analyticOnNhd_sliceFun S hΩ hg w
  refine ⟨han.meromorphicOn, ?_⟩
  rintro ⟨s, hs⟩ htop
  have hsa := han s hs
  change meromorphicOrderAt (sliceFun S g w) s = ⊤ at htop
  rw [hsa.meromorphicOrderAt_eq] at htop
  have htop' : analyticOrderAt (sliceFun S g w) s = ⊤ := by
    cases h : analyticOrderAt (sliceFun S g w) s with
    | top => rfl
    | coe k => rw [h] at htop; exact absurd htop (by simp)
  have hgy : g (splitMap S (s, w)) = 0 := by
    have := (analyticOrderAt_eq_top.mp htop').self_of_nhds
    simpa [sliceFun] using this
  by_cases htr : splitMap S (s, w) ∈ transverseLocus g u
  · rw [analyticOrderAt_sliceFun S htr] at htop'
    exact ENat.natCast_ne_top _ htop'
  · apply hw
    refine ⟨splitMap S (s, w), ⟨hs, hgy, htr⟩, ?_⟩
    simp [S.π_smul_add]

/-- **The left side on the direction `u`.**  The `(u, iu)`-coefficient of `ddᶜ log |g|²` is the
integral of the slice sums, and the slice sums are integrable. -/
theorem ddC_apply_I_eq_integral_sliceSum (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (hint : LocallyIntegrableOn (fun x => Real.log (‖g x‖ ^ 2)) Ω volume) (φ : 𝓓(Ω, ℝ)) :
    LocalCurrents.ddC (regularDistribution volume (fun x => Real.log (‖g x‖ ^ 2)) hint)
        ![u, Complex.I • u] φ = ∫ w, sliceSum S g Ω φ w ∧
      Integrable (sliceSum S g Ω φ) := by
  set U : Set (ℂ × EuclideanSpace ℂ (Fin m)) := splitMap S ⁻¹' Ω with hUdef
  have hU : IsOpen U := Ω.isOpen.preimage (splitMap S).continuous
  set G : ℂ × EuclideanSpace ℂ (Fin m) → ℂ := g ∘ splitMap S with hGdef
  set χ : ℂ × EuclideanSpace ℂ (Fin m) → ℝ := φ ∘ splitMap S with hχdef
  have hG := ae_meromorphic_slices hu S Ω.isOpen hg hg0
  have hint1 : LocallyIntegrableOn (fun x => Real.log ‖g x‖) Ω volume := by
    refine (hint.smul (1 / 2 : ℝ)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Real.log_pow]
    push_cast
    ring
  have hint' : LocallyIntegrableOn (fun z => Real.log ‖G z‖) U (volume.prod volume) :=
    locallyIntegrableOn_comp_splitMap hu S hint1
  have hχ : ContDiff ℝ ∞ χ := φ.contDiff.comp (splitMap S).contDiff
  have hχc : HasCompactSupport χ := φ.hasCompactSupport.comp_homeomorph (splitHomeomorph hu S)
  have hχU : tsupport χ ⊆ U := by
    rw [show χ = φ ∘ splitHomeomorph hu S from rfl, tsupport_comp_eq_preimage]
    exact preimage_mono φ.tsupport_subset
  have hslices := integral_log_norm_mul_sliceLaplacian hU hG hint' hχ hχc hχU
  constructor
  · rw [LocalCurrents.ddC_complexLine, smul_apply, distributionalLeviCLM_regularDistribution_apply,
      smul_eq_mul, ← (measurePreserving_splitMap hu S).integral_comp
        (measurableEmbedding_splitMap hu S)]
    have hpt : ∀ z : ℂ × EuclideanSpace ℂ (Fin m),
        Real.log (‖g (splitMap S z)‖ ^ 2) * leviForm φ (splitMap S z) u =
          (1 / 2 : ℝ) * (Real.log ‖G z‖ * sliceLaplacian χ z) := by
      intro z
      rw [leviForm_splitMap S φ.contDiff z, Real.log_pow]
      simp only [hGdef, hχdef, comp_apply]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, hslices]
    simp only [sliceSum, hχdef, comp_apply]
    field_simp
    rfl
  · have hInt := (integrable_log_norm_mul_sliceLaplacian hint' hχ hχc hχU).integral_prod_right
    refine (hInt.const_mul (2 * Real.pi)⁻¹).congr ?_
    filter_upwards [hG] with w hw
    have h := LelongPoincareOneVariable.integral_log_norm_mul_laplacian (isOpen_sliceSet hU w)
      (f := fun s => G (s, w)) hw.1 hw.2 (χ := fun s => χ (s, w))
      (contDiff_slice hχ w) (hasCompactSupport_slice hχc w) (tsupport_slice_subset_sliceSet hχU w)
    have h' : ∫ s, Real.log ‖G (s, w)‖ * sliceLaplacian χ (s, w) =
        2 * Real.pi * ∑ᶠ s, (MeromorphicOn.divisor (fun s => G (s, w)) (sliceSet U w) s : ℝ) *
          χ (s, w) := h
    show (2 * Real.pi)⁻¹ * ∫ s, Real.log ‖G (s, w)‖ * sliceLaplacian χ (s, w) =
      sliceSum S g Ω φ w
    rw [h']
    simp only [sliceSum]
    field_simp
    rfl

end SliceIdentity

section Fiber

variable {n m : ℕ} {u : EuclideanSpace ℂ (Fin n)}

/-- A function with locally finite support in `U` has finite support on every compact subset of
`U`. -/
theorem finite_inter_support {X Y : Type*} [TopologicalSpace X] [Zero Y] {U : Set X}
    (D : Function.locallyFinsuppWithin U Y) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ Function.support D).Finite := by
  classical
  choose! t ht hfin using fun z (hz : z ∈ U) => D.supportLocallyFiniteWithinDomain z hz
  obtain ⟨F, hFK, hcov⟩ := hK.elim_nhds_subcover t fun z hz => ht z (hKU hz)
  refine ((F.finite_toSet.biUnion fun z hz => hfin z (hKU (hFK z hz)))).subset ?_
  rintro x ⟨hxK, hxs⟩
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcov hxK)
  exact mem_iUnion₂.mpr ⟨z, hz, hxz, hxs⟩

/-- **The fibre identity.**  Over a line meeting the zero set only at transverse regular points,
the slice divisor counts the zeros with their multiplicities. -/
theorem sliceSum_eq_finsum (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {φ : EuclideanSpace ℂ (Fin n) → ℝ} {w : EuclideanSpace ℂ (Fin m)}
    (hw : w ∉ S.π '' {y | y ∈ Ω ∧ g y = 0 ∧ y ∉ transverseLocus g u}) (s : ℂ) :
    (MeromorphicOn.divisor (sliceFun S g w) (sliceSet (splitMap S ⁻¹' Ω) w) s : ℝ) *
        φ (splitMap S (s, w)) =
      (transverseLocus g u ∩ Ω).indicator (fun y => (divisorMult g y : ℝ) * φ y)
        (splitMap S (s, w)) := by
  set y := splitMap S (s, w) with hy
  by_cases hs : s ∈ sliceSet (splitMap S ⁻¹' Ω) w
  · have han := analyticOnNhd_sliceFun S hΩ hg w
    rw [MeromorphicOn.divisor_apply han.meromorphicOn hs, (han s hs).meromorphicOrderAt_eq]
    by_cases hgy : g y = 0
    · have htr : y ∈ transverseLocus g u := by
        by_contra htr
        have hmem : y ∈ {y | y ∈ Ω ∧ g y = 0 ∧ y ∉ transverseLocus g u} := by
          refine ⟨?_, hgy, htr⟩
          exact hs
        exact hw ⟨y, hmem, by simp [hy, S.π_smul_add]⟩
      rw [analyticOrderAt_sliceFun S htr,
        indicator_of_mem (show y ∈ transverseLocus g u ∩ Ω from ⟨htr, hs⟩)]
      simp only [ENat.map_natCast, WithTop.untop₀_coe, Int.cast_natCast]
      rfl
    · have h0 : analyticOrderAt (sliceFun S g w) s = 0 :=
        (han s hs).analyticOrderAt_eq_zero.mpr (by simp only [sliceFun]; exact hgy)
      rw [h0, indicator_of_notMem fun h => hgy (eq_zero_of_mem_regularLocus h.1.1)]
      simp
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hs,
      indicator_of_notMem fun h => hs h.2]
    simp

/-- The slice sum is the sum over the transverse zeros on the line, with multiplicities. -/
theorem ofReal_sliceSum (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {φ : EuclideanSpace ℂ (Fin n) → ℝ}
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x)
    (hu : ‖u‖ = 1) {w : EuclideanSpace ℂ (Fin m)}
    (hw : w ∉ S.π '' {y | y ∈ Ω ∧ g y = 0 ∧ y ∉ transverseLocus g u}) :
    0 ≤ sliceSum S g Ω φ w ∧ ENNReal.ofReal (sliceSum S g Ω φ w) =
      ∑' s : ℂ, (transverseLocus g u ∩ Ω).indicator
        (fun y => (divisorMult g y : ℝ≥0∞) * ENNReal.ofReal (φ y)) (splitMap S (s, w)) := by
  classical
  have heq := sliceSum_eq_finsum S hΩ hg (φ := φ) hw
  set a : ℂ → ℝ := fun s => (transverseLocus g u ∩ Ω).indicator
    (fun y => (divisorMult g y : ℝ) * φ y) (splitMap S (s, w)) with ha
  have hsum : sliceSum S g Ω φ w = ∑ᶠ s, a s := by
    simp only [sliceSum, heq, ha]
  -- finiteness of the support
  set K : Set ℂ := (fun s : ℂ => splitMap S (s, w)) ⁻¹' tsupport φ with hK
  have hKc : IsCompact K := by
    have : K = Prod.fst '' ((splitHomeomorph hu S) ⁻¹' tsupport φ ∩ {p | p.2 = w}) := by
      ext s
      simp [hK, splitHomeomorph_apply]
    have hc : IsCompact ((splitHomeomorph hu S) ⁻¹' tsupport φ) :=
      (splitHomeomorph hu S).isCompact_preimage.mpr hφc
    rw [this]
    exact (hc.inter_right (isClosed_eq continuous_snd continuous_const)).image continuous_fst
  have hKU : K ⊆ sliceSet (splitMap S ⁻¹' Ω) w := fun s hs => hφΩ hs
  have hfin : (Function.support a).Finite := by
    refine (finite_inter_support (MeromorphicOn.divisor (sliceFun S g w)
      (sliceSet (splitMap S ⁻¹' Ω) w)) hKc hKU).subset ?_
    intro s hs
    have hs' := hs
    simp only [Function.mem_support, ha] at hs'
    rw [← heq] at hs'
    refine ⟨?_, ?_⟩
    · by_contra hsK
      apply hs'
      rw [image_eq_zero_of_notMem_tsupport hsK, mul_zero]
    · intro h0
      apply hs'
      simp [h0]
  have ha0 : ∀ s, 0 ≤ a s := by
    intro s
    simp only [ha, indicator]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (hφ0 _)
    · exact le_rfl
  refine ⟨hsum ▸ finsum_nonneg ha0, ?_⟩
  rw [hsum, finsum_eq_sum_of_support_subset a hfin.coe_toFinset.ge,
    ENNReal.ofReal_sum_of_nonneg fun s _ => ha0 s, tsum_eq_sum (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ha, indicator]
    split_ifs
    · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    · simp
  · intro s hs
    have : a s = 0 := by simpa using hs
    simp only [ha, indicator] at this ⊢
    split_ifs with h
    · rw [if_pos h] at this
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), this,
        ENNReal.ofReal_zero]
    · rfl

end Fiber

section Integrability

variable {n : ℕ}

theorem toReal_logNormSq {E : Type*} [NormedAddCommGroup E] (x : E) :
    (logNormSq x).toReal = Real.log (‖x‖ ^ 2) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [logNormSq_of_ne_zero hx, EReal.toReal_coe]

/-- **`log |g|²` is locally integrable** on `Ω` when `g` is holomorphic on `Ω` and vanishes
identically near no point of `Ω` (it is plurisubharmonic). -/
theorem locallyIntegrableOn_log_normSq {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) :
    LocallyIntegrableOn (fun x => Real.log (‖g x‖ ^ 2)) Ω volume := by
  set ψ : EuclideanSpace ℂ (Fin n) → EReal :=
    fun y => (((1 : ℚ) : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g) y with hψdef
  have hψ : PlurisubharmonicOn ψ Ω :=
    MeteredDivisorPositivity.plurisubharmonicOn_qsmul_generatorLog hΩ (by norm_num) hg
  have hnorm : ∀ y, ‖generatorVector (fun _ : Fin 1 => g) y‖ = ‖g y‖ := by
    intro y
    have h := generatorVector_norm_sq (fun _ : Fin 1 => g) y
    simp only [generatorNormSq, Finset.univ_unique, Finset.sum_singleton] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  have hval : ∀ y, (ψ y).toReal = Real.log (‖g y‖ ^ 2) := by
    intro y
    simp only [hψdef, Rat.cast_one, EReal.coe_one, one_mul, generatorLog]
    rw [toReal_logNormSq, hnorm]
  have hfun : (fun x => Real.log (‖g x‖ ^ 2)) = fun x => (ψ x).toReal := funext fun y => (hval y).symm
  rw [hfun]
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hne : ∃ a ∈ ball x r, ψ a ≠ ⊥ := by
    obtain ⟨z, hgz, hz⟩ := ((hg0 x hx).and_eventually (ball_mem_nhds x hr)).exists
    refine ⟨z, hz, ?_⟩
    simp only [hψdef, Rat.cast_one, EReal.coe_one, one_mul, generatorLog]
    rw [Ne, logNormSq_eq_bot_iff, ← norm_eq_zero, hnorm, norm_eq_zero]
    exact hgz
  obtain ⟨s, hs, hI⟩ := ((hψ.mono hball).locallyIntegrableOn_toReal volume
    (convex_ball x r).isPreconnected hne) x (mem_ball_self hr)
  refine ⟨s, ?_, hI⟩
  rw [nhdsWithin_eq_nhds.mpr (ball_mem_nhds x hr)] at hs
  exact mem_nhdsWithin_of_mem_nhds hs

end Integrability

section Key

variable {n m : ℕ} {u : EuclideanSpace ℂ (Fin n)}

/-- **The `(u, iu)`-identity for nonnegative tests, in `ℝ≥0∞`.**  For a nonnegative test function
`φ`, the integral over the transverse locus of `τ(u, iu) m φ` against the `2m`-dimensional
Hausdorff measure equals `ddᶜ log |g|²(u, iu)(φ)`. -/
theorem lintegral_transverse_eq_ofReal_ddC (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (hint : LocallyIntegrableOn (fun x => Real.log (‖g x‖ ^ 2)) Ω volume) (φ : 𝓓(Ω, ℝ))
    (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ x in transverseLocus g u ∩ Ω, ENNReal.ofReal (transverseForm g x u (Complex.I • u)) *
        ((divisorMult g x : ℝ≥0∞) * ENNReal.ofReal (φ x)) ∂(μHE[finrank ℝ (EuclideanSpace ℂ (Fin m))] :
          Measure (EuclideanSpace ℂ (Fin n))) =
      ENNReal.ofReal (LocalCurrents.ddC (regularDistribution volume
        (fun x => Real.log (‖g x‖ ^ 2)) hint) ![u, Complex.I • u] φ) ∧
    0 ≤ LocalCurrents.ddC (regularDistribution volume
        (fun x => Real.log (‖g x‖ ^ 2)) hint) ![u, Complex.I • u] φ := by
  obtain ⟨heq, hInt⟩ := ddC_apply_I_eq_integral_sliceSum hu S hg hg0 hint φ
  have hgood := ae_slice_good hu S Ω.isOpen hg hg0
  have hnn : 0 ≤ᵐ[volume] sliceSum S g Ω φ := by
    filter_upwards [hgood] with w hw
    exact (ofReal_sliceSum S Ω.isOpen hg φ.hasCompactSupport φ.tsupport_subset hφ0 hu hw).1
  have hF : Measurable fun x => ENNReal.ofReal (φ x) :=
    ENNReal.measurable_ofReal.comp φ.continuous.measurable
  refine ⟨?_, heq ▸ integral_nonneg_of_ae hnn⟩
  rw [lintegral_transverse_eq Ω.isOpen hg.continuousOn hu S hF, heq,
    ofReal_integral_eq_lintegral_ofReal hInt hnn]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with w hw
  exact (ofReal_sliceSum S Ω.isOpen hg φ.hasCompactSupport φ.tsupport_subset hφ0 hu hw).2.symm

end Key

section LineForm

open scoped ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem lineForm_add_left (ℓ : V →L[ℂ] ℂ) (v v' w : V) :
    lineForm ℓ (v + v') w = lineForm ℓ v w + lineForm ℓ v' w := by
  simp only [lineForm, map_add, add_mul, Complex.add_im, add_div]

theorem lineForm_add_right (ℓ : V →L[ℂ] ℂ) (v w w' : V) :
    lineForm ℓ v (w + w') = lineForm ℓ v w + lineForm ℓ v w' := by
  simp only [lineForm, map_add, mul_add, Complex.add_im, add_div]

theorem lineForm_smul_left (ℓ : V →L[ℂ] ℂ) (c : ℝ) (v w : V) :
    lineForm ℓ (c • v) w = c * lineForm ℓ v w := by
  simp only [lineForm, ContinuousLinearMap.map_smul_of_tower, Complex.real_smul, map_mul,
    Complex.conj_ofReal, mul_assoc, Complex.im_ofReal_mul, mul_div_assoc]

theorem lineForm_smul_right (ℓ : V →L[ℂ] ℂ) (c : ℝ) (v w : V) :
    lineForm ℓ v (c • w) = c * lineForm ℓ v w := by
  simp only [lineForm, ContinuousLinearMap.map_smul_of_tower, Complex.real_smul,
    mul_left_comm _ (c : ℂ), Complex.im_ofReal_mul, mul_div_assoc]

theorem lineForm_self (ℓ : V →L[ℂ] ℂ) (v : V) : lineForm ℓ v v = 0 := by
  simp only [lineForm]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im, zero_div]

theorem abs_lineForm_le (ℓ : V →L[ℂ] ℂ) (v w : V) : |lineForm ℓ v w| ≤ ‖v‖ * ‖w‖ := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp [lineForm]; positivity
  have hpos : 0 < ‖ℓ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hℓ) 2
  rw [lineForm, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |(conj (ℓ v) * ℓ w).im| ≤ ‖conj (ℓ v) * ℓ w‖ := Complex.abs_im_le_norm _
    _ = ‖ℓ v‖ * ‖ℓ w‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ (‖ℓ‖ * ‖v‖) * (‖ℓ‖ * ‖w‖) :=
        mul_le_mul (ℓ.le_opNorm v) (ℓ.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = ‖v‖ * ‖w‖ * ‖ℓ‖ ^ 2 := by ring

/-- **Parseval for the transverse form**: over an orthonormal basis, `Σ_j τ(e_j, i e_j) = 1`. -/
theorem sum_lineForm_basis [FiniteDimensional ℂ V] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ V) {ℓ : V →L[ℂ] ℂ} (hℓ : ℓ ≠ 0) :
    ∑ j, lineForm ℓ (b j) (Complex.I • b j) = 1 := by
  set a := (InnerProductSpace.toDual ℂ V).symm ℓ with ha
  have hℓa : ∀ y, ℓ y = ⟪a, y⟫_ℂ := fun y => (InnerProductSpace.toDual_symm_apply).symm
  have hna : ‖ℓ‖ = ‖a‖ := by rw [ha, LinearIsometryEquiv.norm_map]
  have hpos : ‖ℓ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hℓ)
  simp only [lineForm_apply_I, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hpos]
  simp only [hℓa]
  rw [b.sum_sq_norm_inner_left, hna]

end LineForm

section Density

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The density of the integration current of the divisor of `g`: `m_g(x) τ_x(v, w)` on the
regular locus, `0` elsewhere. -/
def divisorDensity (g : V → ℂ) (v w : V) (x : V) : ℝ :=
  (regularLocus g).indicator (fun x => (divisorMult g x : ℝ) * transverseForm g x v w) x

variable {g : V → ℂ}

theorem divisorDensity_add_left (v v' w x : V) :
    divisorDensity g (v + v') w x = divisorDensity g v w x + divisorDensity g v' w x := by
  simp only [divisorDensity, indicator, transverseForm, lineForm_add_left]
  split_ifs <;> ring

theorem divisorDensity_add_right (v w w' x : V) :
    divisorDensity g v (w + w') x = divisorDensity g v w x + divisorDensity g v w' x := by
  simp only [divisorDensity, indicator, transverseForm, lineForm_add_right]
  split_ifs <;> ring

theorem divisorDensity_smul_left (c : ℝ) (v w x : V) :
    divisorDensity g (c • v) w x = c * divisorDensity g v w x := by
  simp only [divisorDensity, indicator, transverseForm, lineForm_smul_left]
  split_ifs <;> ring

theorem divisorDensity_smul_right (c : ℝ) (v w x : V) :
    divisorDensity g v (c • w) x = c * divisorDensity g v w x := by
  simp only [divisorDensity, indicator, transverseForm, lineForm_smul_right]
  split_ifs <;> ring

theorem divisorDensity_self (v x : V) : divisorDensity g v v x = 0 := by
  simp only [divisorDensity, indicator, transverseForm, lineForm_self]
  split_ifs <;> ring

theorem divisorDensity_I_I (v w x : V) :
    divisorDensity g (Complex.I • v) (Complex.I • w) x = divisorDensity g v w x := by
  simp only [divisorDensity, indicator, transverseForm, lineForm_I_I]

theorem divisorDensity_apply_I_nonneg (v x : V) : 0 ≤ divisorDensity g v (Complex.I • v) x := by
  simp only [divisorDensity, indicator]
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (transverseForm_apply_I_nonneg g x v)
  · exact le_rfl

theorem abs_divisorDensity_le (v w x : V) :
    |divisorDensity g v w x| ≤
      ‖v‖ * ‖w‖ * (regularLocus g).indicator (fun x => (divisorMult g x : ℝ)) x := by
  simp only [divisorDensity, indicator]
  split_ifs
  · rw [abs_mul, Nat.abs_cast, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_lineForm_le _ v w) (Nat.cast_nonneg _)
  · simp

theorem normalFun_ne_zero {x : V} (hx : x ∈ regularLocus g) : normalFun g x ≠ 0 := by
  have hx' : Nonempty (RegularPresentation g x) := hx
  rw [normalFun, dif_pos hx']
  exact hx'.some.dh_ne x hx'.some.mem

/-- The multiplicity on the regular locus is the sum of the `(e_j, i e_j)`-densities over an
orthonormal basis. -/
theorem indicator_divisorMult_eq_sum [FiniteDimensional ℂ V] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ V) (x : V) :
    (regularLocus g).indicator (fun x => (divisorMult g x : ℝ)) x =
      ∑ j, divisorDensity g (b j) (Complex.I • b j) x := by
  simp only [divisorDensity, indicator]
  split_ifs with hx
  · rw [← Finset.mul_sum]
    simp only [transverseForm]
    rw [sum_lineForm_basis b (normalFun_ne_zero hx), mul_one]
  · simp

/-- On the transverse locus the `(u, iu)`-density is `m τ(u, iu)`; off it, it vanishes. -/
theorem divisorDensity_apply_I_eq_indicator (u x : V) :
    divisorDensity g u (Complex.I • u) x = (transverseLocus g u).indicator
      (fun x => (divisorMult g x : ℝ) * transverseForm g x u (Complex.I • u)) x := by
  simp only [divisorDensity, indicator]
  by_cases hx : x ∈ regularLocus g
  · by_cases ht : transverseForm g x u (Complex.I • u) = 0
    · simp [ht]
    · have hT : x ∈ transverseLocus g u := ⟨hx, ht⟩
      simp [hx, hT]
  · have hT : x ∉ transverseLocus g u := fun h => hx h.1
    simp [hx, hT]

end Density

section Mass

variable {n : ℕ}

theorem finrank_real_euclidean (m : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

theorem measurableSet_regularLocus_inter {g : EuclideanSpace ℂ (Fin n) → ℂ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω) (hgc : ContinuousOn g Ω) :
    MeasurableSet (regularLocus g ∩ Ω) := by
  obtain ⟨O, hOo, hO⟩ := exists_isOpen_regularLocus g
  have h0 : MeasurableSet (g ⁻¹' {0} ∩ Ω) :=
    measurableSet_inter_preimage_of_continuousOn hΩ.measurableSet hgc (measurableSet_singleton 0)
  have : regularLocus g ∩ Ω = (g ⁻¹' {0} ∩ Ω) ∩ O := by
    rw [hO]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    tauto
  rw [this]
  exact h0.inter hOo.measurableSet

theorem measurableSet_transverseLocus_inter {g : EuclideanSpace ℂ (Fin n) → ℂ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω) (hgc : ContinuousOn g Ω)
    (u : EuclideanSpace ℂ (Fin n)) : MeasurableSet (transverseLocus g u ∩ Ω) := by
  obtain ⟨O, hOo, hO⟩ := exists_isOpen_transverseLocus g u
  have h0 : MeasurableSet (g ⁻¹' {0} ∩ Ω) :=
    measurableSet_inter_preimage_of_continuousOn hΩ.measurableSet hgc (measurableSet_singleton 0)
  have : transverseLocus g u ∩ Ω = (g ⁻¹' {0} ∩ Ω) ∩ O := by
    rw [hO]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    tauto
  rw [this]
  exact h0.inter hOo.measurableSet

theorem measurable_lineForm (v w : EuclideanSpace ℂ (Fin n)) :
    Measurable fun ℓ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ => lineForm ℓ v w := by
  have hv : Continuous fun ℓ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ => ℓ v :=
    continuous_id.clm_apply continuous_const
  have hw : Continuous fun ℓ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ => ℓ w :=
    continuous_id.clm_apply continuous_const
  exact ((Complex.continuous_im.comp ((Complex.continuous_conj.comp hv).mul hw)).measurable).div
    ((continuous_norm.pow 2).measurable)

/-- The density is almost everywhere strongly measurable on `Ω` for every measure. -/
theorem aestronglyMeasurable_divisorDensity {g : EuclideanSpace ℂ (Fin n) → ℂ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω) (hgc : ContinuousOn g Ω)
    (v w : EuclideanSpace ℂ (Fin n)) (μ : Measure (EuclideanSpace ℂ (Fin n))) :
    AEStronglyMeasurable (divisorDensity g v w) (μ.restrict Ω) := by
  classical
  set Z := regularLocus g ∩ Ω with hZ
  have hZm : MeasurableSet Z := measurableSet_regularLocus_inter hΩ hgc
  have h1 : AEStronglyMeasurable (divisorDensity g v w) (μ.restrict (Ω \ Z)) := by
    refine (aestronglyMeasurable_const (b := (0 : ℝ))).congr ?_
    refine ae_restrict_of_forall_mem (hΩ.measurableSet.diff hZm) fun x hx => ?_
    have hx' : x ∉ regularLocus g := fun h => hx.2 ⟨h, hx.1⟩
    simp [divisorDensity, indicator_of_notMem hx']
  have h2 : AEStronglyMeasurable (divisorDensity g v w) (μ.restrict Z) := by
    rcases Z.eq_empty_or_nonempty with he | hne
    · rw [he, Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure _
    choose P hP using fun x (hx : x ∈ Z) => (⟨Classical.choice hx.1, trivial⟩ :
      ∃ _ : RegularPresentation g x, True)
    set f : EuclideanSpace ℂ (Fin n) → Set (EuclideanSpace ℂ (Fin n)) :=
      fun x => if hx : x ∈ Z then (P x hx).U else univ with hfdef
    have hf : ∀ x (hx : x ∈ Z), f x = (P x hx).U := fun x hx => by simp [hfdef, hx]
    obtain ⟨t, htZ, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (f := f) (s := Z)
      fun x hx => by
        rw [hf x hx]
        exact mem_nhdsWithin_of_mem_nhds ((P x hx).isOpen.mem_nhds (P x hx).mem)
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (hcov hx)
      exact ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := htc.exists_eq_range htne
    have hc : ∀ i, c i ∈ Z := fun i => htZ (mem_range_self i)
    have hsub : Z ⊆ ⋃ i, Z ∩ (P (c i) (hc i)).U := by
      intro x hx
      obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.mp (hcov hx)
      rw [hf _ (hc i)] at hxy
      exact mem_iUnion.mpr ⟨i, hx, hxy⟩
    refine AEStronglyMeasurable.mono_measure ?_ (Measure.restrict_mono hsub le_rfl)
    rw [aestronglyMeasurable_iUnion_iff]
    intro i
    set Q := P (c i) (hc i)
    have hmeas : Measurable fun x => (Q.m : ℝ) * lineForm (fderiv ℂ Q.h x) v w :=
      measurable_const.mul ((measurable_lineForm v w).comp (measurable_fderiv ℂ Q.h))
    refine hmeas.aestronglyMeasurable.congr
      (ae_restrict_of_forall_mem (hZm.inter Q.isOpen.measurableSet) fun x hx => ?_)
    have hgx : g x = 0 := eq_zero_of_mem_regularLocus hx.1.1
    simp only [divisorDensity, indicator_of_mem hx.1.1, Q.divisorMult_of_mem hx.2 hgx,
      Q.transverseForm_of_mem hx.2 hgx v w]
  have hΩZ : Ω = (Ω \ Z) ∪ Z := by
    ext x
    simp only [hZ, mem_union, Set.mem_sdiff, mem_inter_iff]
    tauto
  rw [hΩZ, aestronglyMeasurable_union_iff]
  exact ⟨h1, h2⟩

/-- **Local finiteness of the divisor mass.**  On every compact subset of `Ω`, the regular part of
the zero set, counted with multiplicity, has finite `(2n-2)`-dimensional Hausdorff measure. -/
theorem lintegral_indicator_divisorMult_lt_top
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∫⁻ x in K, ENNReal.ofReal ((regularLocus g).indicator (fun x => (divisorMult g x : ℝ)) x)
      ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) < ⊤ := by
  classical
  set b := EuclideanSpace.basisFun (Fin n) ℂ with hb
  have hint := locallyIntegrableOn_log_normSq Ω.isOpen hg hg0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hae : ∀ j, AEMeasurable (fun x => ENNReal.ofReal (divisorDensity g (b j) (Complex.I • b j) x))
      ((μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))).restrict K) := fun j =>
    ((aestronglyMeasurable_divisorDensity Ω.isOpen hg.continuousOn (b j) (Complex.I • b j)
      _).mono_measure (Measure.restrict_mono hKΩ le_rfl)).aemeasurable.ennreal_ofReal
  have hpt : ∀ x, ENNReal.ofReal ((regularLocus g).indicator (fun x => (divisorMult g x : ℝ)) x) =
      ∑ j, ENNReal.ofReal (divisorDensity g (b j) (Complex.I • b j) x) := fun x => by
    rw [indicator_divisorMult_eq_sum b x,
      ENNReal.ofReal_sum_of_nonneg fun j _ => divisorDensity_apply_I_nonneg _ _]
  simp_rw [hpt]
  rw [lintegral_finsetSum' _ fun j _ => hae j]
  refine ENNReal.sum_lt_top.mpr fun j _ => ?_
  have hu : ‖b j‖ = 1 := b.orthonormal.1 j
  obtain ⟨m, hm, ⟨S⟩⟩ := exists_splitting hu
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * n - 2 := by
    rw [finrank_real_euclidean, ← finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n), ← hm]
    omega
  obtain ⟨ψ, hψ0, hψK⟩ := exists_nonneg_testFunction_one_le_on_compact (Ω := Ω) hK hKΩ
  have hkey := (lintegral_transverse_eq_ofReal_ddC hu S hg hg0 hint ψ hψ0).1
  rw [hdim] at hkey
  refine lt_of_le_of_lt ?_ (hkey.symm ▸ ENNReal.ofReal_lt_top)
  calc ∫⁻ x in K, ENNReal.ofReal (divisorDensity g (b j) (Complex.I • b j) x)
        ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n)))
      ≤ ∫⁻ x in K, (transverseLocus g (b j) ∩ Ω).indicator (fun x =>
          ENNReal.ofReal (transverseForm g x (b j) (Complex.I • b j)) *
            ((divisorMult g x : ℝ≥0∞) * ENNReal.ofReal (ψ x))) x
        ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) := by
        refine setLIntegral_mono' hKm fun x hxK => ?_
        rw [divisorDensity_apply_I_eq_indicator]
        by_cases hT : x ∈ transverseLocus g (b j)
        · rw [indicator_of_mem hT, indicator_of_mem (show x ∈ transverseLocus g (b j) ∩ Ω from
            ⟨hT, hKΩ hxK⟩), ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            mul_comm]
          refine mul_le_mul_right ?_ _
          calc (divisorMult g x : ℝ≥0∞) = (divisorMult g x : ℝ≥0∞) * 1 := (mul_one _).symm
            _ ≤ (divisorMult g x : ℝ≥0∞) * ENNReal.ofReal (ψ x) := by
                refine mul_le_mul_right ?_ _
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (hψK x hxK)
        · rw [indicator_of_notMem hT, ENNReal.ofReal_zero]
          exact zero_le
    _ ≤ ∫⁻ x, (transverseLocus g (b j) ∩ Ω).indicator (fun x =>
          ENNReal.ofReal (transverseForm g x (b j) (Complex.I • b j)) *
            ((divisorMult g x : ℝ≥0∞) * ENNReal.ofReal (ψ x))) x
        ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_indicator_le _ _

/-- **The density of the integration current is locally integrable** on `Ω`, for the
`(2n-2)`-dimensional Hausdorff measure. -/
theorem locallyIntegrableOn_divisorDensity
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (v w : EuclideanSpace ℂ (Fin n)) :
    LocallyIntegrableOn (divisorDensity g v w) Ω
      (μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
  intro K hKΩ hK
  refine ⟨(aestronglyMeasurable_divisorDensity Ω.isOpen hg.continuousOn v w _).mono_measure
    (Measure.restrict_mono hKΩ le_rfl), ?_⟩
  have hlt := lintegral_indicator_divisorMult_lt_top hg hg0 hK hKΩ
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := ‖v‖ * ‖w‖)) hlt)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (abs_divisorDensity_le v w x)

end Mass

section TwoForms

variable {E N : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup N] [Module ℝ N]

theorem apply_add_left (A : E [⋀^Fin 2]→ₗ[ℝ] N) (x y z : E) :
    A ![x + y, z] = A ![x, z] + A ![y, z] := by
  have e : ∀ a : E, ![a, z] = Function.update ![0, z] 0 a := fun a => by
    funext i; fin_cases i <;> simp
  rw [e (x + y), e x, e y]
  exact A.map_update_add (v := ![0, z]) (i := 0) x y

theorem apply_add_right (A : E [⋀^Fin 2]→ₗ[ℝ] N) (x y z : E) :
    A ![x, y + z] = A ![x, y] + A ![x, z] := by
  have e : ∀ a : E, ![x, a] = Function.update ![x, 0] 1 a := fun a => by
    funext i; fin_cases i <;> simp
  rw [e (y + z), e y, e z]
  exact A.map_update_add (v := ![x, 0]) (i := 1) y z

theorem apply_smul_left (A : E [⋀^Fin 2]→ₗ[ℝ] N) (c : ℝ) (x z : E) :
    A ![c • x, z] = c • A ![x, z] := by
  have e : ∀ a : E, ![a, z] = Function.update ![0, z] 0 a := fun a => by
    funext i; fin_cases i <;> simp
  rw [e (c • x), e x]
  exact A.map_update_smul (v := ![0, z]) (i := 0) c x

theorem apply_smul_right (A : E [⋀^Fin 2]→ₗ[ℝ] N) (c : ℝ) (x z : E) :
    A ![x, c • z] = c • A ![x, z] := by
  have e : ∀ a : E, ![x, a] = Function.update ![x, 0] 1 a := fun a => by
    funext i; fin_cases i <;> simp
  rw [e (c • z), e z]
  exact A.map_update_smul (v := ![x, 0]) (i := 1) c z

theorem apply_self (A : E [⋀^Fin 2]→ₗ[ℝ] N) (x : E) : A ![x, x] = 0 :=
  A.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

end TwoForms

section Polarization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {Ω : TopologicalSpace.Opens E}

/-- **Polarization for `(1,1)`-forms.**  Two distribution-valued `(1,1)`-forms agreeing on all
`(z, iz)` with `z` a unit vector are equal. -/
theorem eq_of_isOneOne {A B : LocalCurrents.DistributionForm Ω 2} (hA : LocalCurrents.IsOneOne A)
    (hB : LocalCurrents.IsOneOne B)
    (h : ∀ z : E, ‖z‖ = 1 → A ![z, Complex.I • z] = B ![z, Complex.I • z]) : A = B := by
  set C := A - B with hC
  have hC11 : LocalCurrents.IsOneOne C := fun v w => by
    simp only [hC, AlternatingMap.sub_apply, hA v w, hB v w]
  have hQ1 : ∀ z : E, ‖z‖ = 1 → C ![z, Complex.I • z] = 0 := fun z hz => by
    simp only [hC, AlternatingMap.sub_apply, h z hz, sub_self]
  have hQ : ∀ z : E, C ![z, Complex.I • z] = 0 := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · rw [smul_zero]
      exact apply_self C 0
    · set c : ℝ := ‖z‖ with hcdef
      have hc : c ≠ 0 := norm_ne_zero_iff.mpr hz
      set z₁ : E := c⁻¹ • z with hz₁def
      have hz₁ : ‖z₁‖ = 1 := by
        rw [hz₁def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), ← hcdef,
          inv_mul_cancel₀ hc]
      have hzz : z = c • z₁ := by rw [hz₁def, smul_smul, mul_inv_cancel₀ hc, one_smul]
      have hcomm : Complex.I • (c • z₁) = c • (Complex.I • z₁) := smul_comm _ _ _
      rw [hzz, hcomm, apply_smul_left, apply_smul_right, hQ1 z₁ hz₁, smul_zero, smul_zero]
  have hvw : ∀ v w : E, C ![v, Complex.I • w] = 0 := by
    intro v w
    have h1 := hQ (v + w)
    rw [smul_add, apply_add_left, apply_add_right, apply_add_right, hQ v, hQ w,
      LocalCurrents.oneOne_pairing_symmetric C hC11 w v, zero_add, add_zero] at h1
    have h2 : (2 : ℝ) • C ![v, Complex.I • w] = 0 := by rw [two_smul]; exact h1
    rw [← one_smul ℝ (C ![v, Complex.I • w]), ← inv_mul_cancel₀ (two_ne_zero (α := ℝ)), mul_smul,
      h2, smul_zero]
  have hall : ∀ v w : E, C ![v, w] = 0 := by
    intro v w
    have hw : w = Complex.I • (-(Complex.I • w)) := by
      rw [smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
    rw [hw]
    exact hvw v _
  ext v : 1
  have hv : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  have := hall (v 0) (v 1)
  rw [← hv, hC, AlternatingMap.sub_apply, sub_eq_zero] at this
  exact this

end Polarization

section Current

variable {n : ℕ}

theorem integrable_testFunction_mul {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {μ : Measure (EuclideanSpace ℂ (Fin n))} {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f Ω μ) (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => φ x * f x) μ := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hint : IntegrableOn f (tsupport φ) μ := hf.integrableOn_compact_subset φ.tsupport_subset hK
  have h2 : IntegrableOn (fun x => φ x * f x) (tsupport φ) μ :=
    hint.continuousOn_mul φ.continuous.continuousOn hK
  exact h2.integrable_of_forall_notMem_eq_zero fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- **The integration current of the divisor of `g`** on `Ω ⊆ ℂⁿ`, as a distribution-valued real
two-form: `[div g](v, w)(φ) = ∫ φ m_g τ(v, w) dμHE[2n-2]`, the integral running over the regular
part of the zero set. -/
def divisorCurrent {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) : LocalCurrents.DistributionForm Ω 2 where
  toFun v := regularDistribution (μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n)))
    (divisorDensity g (v 0) (v 1)) (locallyIntegrableOn_divisorDensity hg hg0 (v 0) (v 1))
  map_update_add' := by
    intro _ v i x y
    ext φ
    rw [add_apply, regularDistribution_apply, regularDistribution_apply,
      regularDistribution_apply, ← integral_add (integrable_testFunction_mul
        (locallyIntegrableOn_divisorDensity hg hg0 _ _) φ)
        (integrable_testFunction_mul (locallyIntegrableOn_divisorDensity hg hg0 _ _) φ)]
    congr 1
    funext z
    fin_cases i
    · simp [divisorDensity_add_left, mul_add]
    · simp [divisorDensity_add_right, mul_add]
  map_update_smul' := by
    intro _ v i c x
    ext φ
    rw [smul_apply, regularDistribution_apply, regularDistribution_apply,
      smul_eq_mul, ← integral_const_mul]
    congr 1
    funext z
    fin_cases i
    · simp [divisorDensity_smul_left]; ring
    · simp [divisorDensity_smul_right]; ring
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    ext φ
    rw [regularDistribution_apply, zero_apply]
    have hv : v 0 = v 1 := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hne
      · exact hij
      · exact hij.symm
      · exact absurd rfl hne
    simp [hv, divisorDensity_self]

theorem divisorCurrent_apply {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) (v w : EuclideanSpace ℂ (Fin n)) (φ : 𝓓(Ω, ℝ)) :
    divisorCurrent hg hg0 ![v, w] φ =
      ∫ x, φ x * divisorDensity g v w x ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) :=
  regularDistribution_apply _ _ (locallyIntegrableOn_divisorDensity hg hg0 v w) φ

theorem isOneOne_divisorCurrent {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) : LocalCurrents.IsOneOne (divisorCurrent hg hg0) := by
  intro v w
  ext φ
  rw [divisorCurrent_apply, divisorCurrent_apply]
  simp only [divisorDensity_I_I]

/-- Distributions agreeing on nonnegative tests are equal. -/
theorem eq_of_forall_nonneg {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {T T' : 𝓓'(Ω, ℝ)} (h : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → T φ = T' φ) : T = T' := by
  ext φ
  obtain ⟨χ, hχ0, hχ⟩ := exists_nonneg_testFunction_abs_le (testFunctionToCompactlySupportedLM Ω φ)
  have hsum : ∀ x, 0 ≤ (φ + χ) x := by
    intro x
    change 0 ≤ φ x + χ x
    by_cases hx : x ∈ Ω
    · have := hχ ⟨x, hx⟩
      rw [testFunctionToCompactlySupportedLM_apply] at this
      linarith [neg_abs_le (φ x)]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h), zero_add]
      exact hχ0 x
  have h1 := h (φ + χ) hsum
  have h2 := h χ hχ0
  rw [map_add, map_add, h2] at h1
  exact add_right_cancel h1

end Current

section Main

variable {n : ℕ}

/-- For a nonnegative test function, the `(u, iu)`-coefficient of the divisor current is the
integral of `τ(u, iu) m φ` over the transverse locus. -/
theorem ofReal_divisorCurrent_apply_I {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) (u : EuclideanSpace ℂ (Fin n)) (φ : 𝓓(Ω, ℝ))
    (hφ0 : ∀ x, 0 ≤ φ x) :
    ENNReal.ofReal (divisorCurrent hg hg0 ![u, Complex.I • u] φ) =
      ∫⁻ x in transverseLocus g u ∩ Ω, ENNReal.ofReal (transverseForm g x u (Complex.I • u)) *
        ((divisorMult g x : ℝ≥0∞) * ENNReal.ofReal (φ x))
        ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) ∧
    0 ≤ divisorCurrent hg hg0 ![u, Complex.I • u] φ := by
  rw [divisorCurrent_apply]
  have hf0 : ∀ x, 0 ≤ φ x * divisorDensity g u (Complex.I • u) x := fun x =>
    mul_nonneg (hφ0 x) (divisorDensity_apply_I_nonneg u x)
  have hInt := integrable_testFunction_mul
    (locallyIntegrableOn_divisorDensity hg hg0 u (Complex.I • u)) φ
  refine ⟨?_, integral_nonneg hf0⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hInt.aestronglyMeasurable,
    ENNReal.ofReal_toReal hInt.lintegral_lt_top.ne,
    ← lintegral_indicator (measurableSet_transverseLocus_inter Ω.isOpen hg.continuousOn u)]
  congr 1
  funext x
  rw [divisorDensity_apply_I_eq_indicator]
  by_cases hx : x ∈ transverseLocus g u ∩ Ω
  · rw [indicator_of_mem hx.1, indicator_of_mem hx, ENNReal.ofReal_mul (hφ0 x),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    ring
  · rw [indicator_of_notMem hx]
    by_cases hT : x ∈ transverseLocus g u
    · have hxΩ : x ∉ (Ω : Set (EuclideanSpace ℂ (Fin n))) := fun h => hx ⟨hT, h⟩
      rw [image_eq_zero_of_notMem_tsupport fun h => hxΩ (φ.tsupport_subset h), zero_mul,
        ENNReal.ofReal_zero]
    · rw [indicator_of_notMem hT, mul_zero, ENNReal.ofReal_zero]

/-- **The Lelong--Poincaré equation on `ℂⁿ`.**  Let `g` be holomorphic on an open set `Ω ⊆ ℂⁿ`,
vanishing identically near no point of `Ω`.  Then `log |g|²` is locally integrable and

  `ddᶜ log |g|² = [div g]`

as distribution-valued real two-forms on `Ω`, where `[div g]` is the integration current over the
regular part of the zero set, with multiplicities (`divisorCurrent`). -/
theorem ddC_log_normSq_eq_divisorCurrent {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) :
    LocalCurrents.ddC (regularDistribution volume (fun x => Real.log (‖g x‖ ^ 2))
      (locallyIntegrableOn_log_normSq Ω.isOpen hg hg0)) = divisorCurrent hg hg0 := by
  refine eq_of_isOneOne (LocalCurrents.ddC_isOneOne _) (isOneOne_divisorCurrent hg hg0)
    fun u hu => ?_
  obtain ⟨m, hm, ⟨S⟩⟩ := exists_splitting hu
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * n - 2 := by
    rw [finrank_real_euclidean, ← finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n), ← hm]
    omega
  refine eq_of_forall_nonneg fun φ hφ0 => ?_
  obtain ⟨hk, hk0⟩ := lintegral_transverse_eq_ofReal_ddC hu S hg hg0
    (locallyIntegrableOn_log_normSq Ω.isOpen hg hg0) φ hφ0
  rw [hdim] at hk
  obtain ⟨hr, hr0⟩ := ofReal_divisorCurrent_apply_I hg hg0 u φ hφ0
  rw [← ENNReal.ofReal_eq_ofReal_iff hk0 hr0, ← hk, hr]

/-- The Lelong--Poincaré equation coefficientwise: for all real directions `v, w` and every test
function `φ`, `ddᶜ log |g|²(v, w)(φ) = ∫_{Z_reg} φ m_g τ(v, w) dμHE[2n-2]`. -/
theorem ddC_log_normSq_apply {Ω : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) (v w : EuclideanSpace ℂ (Fin n)) (φ : 𝓓(Ω, ℝ)) :
    LocalCurrents.ddC (regularDistribution volume (fun x => Real.log (‖g x‖ ^ 2))
      (locallyIntegrableOn_log_normSq Ω.isOpen hg hg0)) ![v, w] φ =
      ∫ x, φ x * divisorDensity g v w x ∂(μHE[2 * n - 2] : Measure (EuclideanSpace ℂ (Fin n))) := by
  rw [ddC_log_normSq_eq_divisorCurrent hg hg0, divisorCurrent_apply]

end Main

end SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
