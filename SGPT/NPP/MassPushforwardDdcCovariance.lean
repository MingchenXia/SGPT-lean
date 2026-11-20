import SGPT.Foundations.Analysis.Pending.DDCOverlap
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic
import SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
import SGPT.BDivisor.TestFormPullback

/-!
# Holomorphic covariance of `ddᶜ` under biholomorphisms of open sets of `ℂⁿ`

Let `τ : U → V` be a biholomorphism between open subsets of `ℂⁿ` with inverse `σ`
(`IsBiholomorphicPair U V τ σ`), and let `η` (on `U`) and `ζ` (on `V`) be test forms of the same
degree with `η = τ^* ζ`, i.e. `η_z(v) = ζ_{τ z}(Dτ_z v)`. For every function `f` on `V`,

`∫ (ddᶜ)^* η · (f ∘ τ) = ∫ (ddᶜ)^* ζ · f`,

where `(ddᶜ)^* η = DDCOverlap.ddcAdjoint B η` is the test function to which a distribution is
applied when `ddᶜ` of it is paired with `η`. In other words `ddᶜ (f ∘ τ) = τ^* (ddᶜ f)` in the
sense of distributions, for every locally integrable `f`. This is the transformation law of
`Pending.DDCOverlap` (proved there for the chart transitions of one manifold), for an arbitrary
biholomorphic pair; the proofs are the same: for smooth potentials the adjoint test function
integrates to the classical `ddᶜ`-density, which is covariant (`smoothDDC_comp`), so the two
adjoint test functions agree almost everywhere up to the Jacobian `|det Dτ|`, and the change of
variables formula concludes.

We also transport test forms: `pushTest h η` is the test form `σ^* η` on `V`
(`(σ^*η)_w = η_{σ w} ∘ Dσ_w`), and `η = τ^*(σ^* η)` (`pushTest_rel`).

These are used for the push-forward half of source `prop:nppmassinv`
(`SGPT.NPP.MassPushforwardInvariance`): over the isomorphism locus of a modification `π`,
the coordinate expression of `π` is such a biholomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.NPP.MassPushforward

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
  SGPT.Foundations.Analysis.Pending.DDCOverlap
  SGPT.Foundations.Analysis.Pending.BedfordTaylor
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor.TestFormPullback

variable {n q : ℕ}

/-! ### Biholomorphic pairs as partial homeomorphisms -/

section Pair

variable {U V : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

/-- A biholomorphic pair as an open partial homeomorphism `U → V`. -/
def pairHomeomorph (h : IsBiholomorphicPair U V τ σ) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) where
  toFun := τ
  invFun := σ
  source := U
  target := V
  map_source' := h.mapsTo
  map_target' := h.mapsTo_inv
  left_inv' := h.left_inv
  right_inv' := h.right_inv
  open_source := U.isOpen
  open_target := V.isOpen
  continuousOn_toFun := h.holo.continuousOn
  continuousOn_invFun := h.holo_inv.continuousOn

@[simp] theorem pairHomeomorph_coe (h : IsBiholomorphicPair U V τ σ) :
    ⇑(pairHomeomorph h) = τ := rfl

@[simp] theorem pairHomeomorph_symm_coe (h : IsBiholomorphicPair U V τ σ) :
    ⇑(pairHomeomorph h).symm = σ := rfl

@[simp] theorem pairHomeomorph_source (h : IsBiholomorphicPair U V τ σ) :
    (pairHomeomorph h).source = U := rfl

@[simp] theorem pairHomeomorph_target (h : IsBiholomorphicPair U V τ σ) :
    (pairHomeomorph h).target = V := rfl

/-- The inverse pair. -/
theorem pairSymm (h : IsBiholomorphicPair U V τ σ) :
    IsBiholomorphicPair V U σ τ where
  holo := h.holo_inv
  holo_inv := h.holo
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  left_inv := h.right_inv
  right_inv := h.left_inv

theorem contDiffAt_real (h : IsBiholomorphicPair U V τ σ) {x : ComplexModel n} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ τ x :=
  (h.holo.contDiffAt (U.isOpen.mem_nhds hx)).restrict_scalars ℝ

theorem hasFDerivAt_real (h : IsBiholomorphicPair U V τ σ) {x : ComplexModel n} (hx : x ∈ U) :
    HasFDerivAt τ (fderiv ℝ τ x) x :=
  ((contDiffAt_real h hx).differentiableAt (by simp)).hasFDerivAt

/-- The real Jacobian of a holomorphic map is `|det_ℂ|² ≥ 0`. -/
theorem det_fderiv_nonneg (h : IsBiholomorphicPair U V τ σ) {x : ComplexModel n} (hx : x ∈ U) :
    0 ≤ (fderiv ℝ τ x).det := by
  have hd : DifferentiableAt ℂ τ x :=
    (h.holo.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ,
    SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables.det_restrictScalars_eq_normSq]
  exact Complex.normSq_nonneg _

/-- `Dσ_{τ x} ∘ Dτ_x = id`. -/
theorem fderiv_symm_comp (h : IsBiholomorphicPair U V τ σ) {x : ComplexModel n} (hx : x ∈ U) :
    (fderiv ℝ σ (τ x)).comp (fderiv ℝ τ x) = ContinuousLinearMap.id ℝ (ComplexModel n) := by
  have hτx : τ x ∈ V := h.mapsTo hx
  have hσ : DifferentiableAt ℝ σ (τ x) :=
    ((contDiffAt_real (pairSymm h) hτx).differentiableAt (by simp))
  have hτ : DifferentiableAt ℝ τ x := (contDiffAt_real h hx).differentiableAt (by simp)
  have hσ' : DifferentiableAt ℝ σ (τ x) := hσ
  rw [← fderiv_comp x hσ' hτ]
  have hev : (σ ∘ τ) =ᶠ[𝓝 x] id := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact h.left_inv y hy
  rw [hev.fderiv_eq, fderiv_id]

end Pair

/-! ### The pointwise transformation of the `ddᶜ`-density -/

section Pointwise

/-- The scalar exterior product of two real alternating forms (as in `Pending.DDCOverlap`). -/
private def scalarWedge {r q : ℕ} (α : ComplexModel n [⋀^Fin r]→L[ℝ] ℝ)
    (β : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    ComplexModel n [⋀^(Fin r ⊕ Fin q)]→ₗ[ℝ] ℝ :=
  (LinearMap.mul' ℝ ℝ).compAlternatingMap (α.toAlternatingMap.domCoprod β.toAlternatingMap)

private theorem scalarWedge_apply {r q : ℕ} (α : ComplexModel n [⋀^Fin r]→L[ℝ] ℝ)
    (β : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) (v : Fin r ⊕ Fin q → ComplexModel n) :
    scalarWedge α β v =
      ∑ s : Equiv.Perm.ModSumCongr (Fin r) (Fin q),
        ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (α (fun i ↦ v (s.out (Sum.inl i))) * β (fun j ↦ v (s.out (Sum.inr j)))) := by
  rw [scalarWedge, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod_apply, _root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  conv_lhs => rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  rcases Int.units_eq_one_or (Equiv.Perm.sign s.out) with hs | hs
  · rw [hs]
    simp [LinearMap.mul'_apply]
  · rw [hs]
    simp [LinearMap.mul'_apply]

variable {U V : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}
  {Ω Ω' : Opens (ComplexModel n)}

/-- On `U`, the classical `ddᶜ` shuffle density of a potential that is locally `g ∘ τ` is the
density of `g` at `τ x` times the real Jacobian determinant of `τ`, for `η = τ^* ζ`. -/
theorem ddcDensity_pullback_pointwise (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (hp : IsBiholomorphicPair U V τ σ) (η : TestForm Ω q) (ζ : TestForm Ω' q)
    (hrel : ∀ z ∈ U, ∀ v : Fin q → ComplexModel n,
      η z v = ζ (τ z) (fun i => fderiv ℝ τ z (v i)))
    {g h : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g V)
    {x : ComplexModel n} (hx : x ∈ U) (hhg : h =ᶠ[𝓝 x] fun y => g (τ y)) :
    ddcDensity B h η x = (fderiv ℝ τ x).det * ddcDensity B g ζ (τ x) := by
  let D := fderiv ℝ τ x
  have hddc : smoothDDC h x = (smoothDDC g (τ x)).compContinuousLinearMap D :=
    (smoothDDC_congr hhg).trans
      (smoothDDC_comp U.isOpen V.isOpen hp.holo hg hp.mapsTo hx)
  have hdens (k : ComplexModel n → ℝ) (W : Opens (ComplexModel n)) (ξ : TestForm W q)
      (y : ComplexModel n) :
      ddcDensity B k ξ y = scalarWedge (smoothDDC k y) (ξ y) B := by
    rw [scalarWedge_apply]
    rfl
  rw [hdens, hdens]
  let W := scalarWedge (smoothDDC g (τ x)) (ζ (τ x))
  have hpull : scalarWedge (smoothDDC h x) (η x) B = W (D ∘ B) := by
    rw [scalarWedge_apply, scalarWedge_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hddc, hrel x hx]
    rfl
  rw [hpull]
  have htop := congrArg
    (fun A : ComplexModel n [⋀^(Fin 2 ⊕ Fin q)]→ₗ[ℝ] ℝ ↦ A (D ∘ B)) (W.eq_smul_basis_det B)
  have hdet : B.det (D ∘ B) = LinearMap.det D.toLinearMap := by
    change B.det (D.toLinearMap ∘ B) = LinearMap.det D.toLinearMap
    rw [B.det_comp, B.det_self, mul_one]
  calc
    W (D ∘ B) = ((W B) • B.det) (D ∘ B) := htop
    _ = W B * B.det (D ∘ B) := by simp
    _ = LinearMap.det D.toLinearMap * W B := by rw [hdet, mul_comm]

end Pointwise

/-! ### Almost-everywhere covariance of the adjoint test function -/

section Assembly

variable {U V : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}
  {μ : Measure (ComplexModel n)} [μ.IsAddHaarMeasure]

/-- The smooth test identity: pairing the adjoint test function of `η` with a smooth function
compactly supported in `U` equals pairing the adjoint of `ζ` with its transport. -/
theorem integral_ddcAdjoint_mul_pullback
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (hp : IsBiholomorphicPair U V τ σ) (η : TestForm U q) (ζ : TestForm V q)
    (hrel : ∀ z ∈ U, ∀ v : Fin q → ComplexModel n,
      η z v = ζ (τ z) (fun i => fderiv ℝ τ z (v i)))
    {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) :
    ∫ x, ddcAdjoint B η x * φ x ∂μ =
      ∫ x in (U : Set (ComplexModel n)),
        |(fderiv ℝ τ x).det| • (ddcAdjoint B ζ (τ x) * φ x) ∂μ := by
  let F := pairHomeomorph hp
  let g := transportSymm F φ
  have hg : ContDiff ℝ ∞ g :=
    contDiff_transportSymm F hφ hc hs fun y hy => contDiffAt_real (pairSymm hp) hy
  have hderiv (x : ComplexModel n) (hx : x ∈ F.source) : HasFDerivAt F (fderiv ℝ τ x) x :=
    hasFDerivAt_real hp hx
  have hdens0 (k : ComplexModel n → ℝ) (W : Opens (ComplexModel n)) (ξ : TestForm W q)
      (y : ComplexModel n) (hy : ξ y = 0) : ddcDensity B k ξ y = 0 := by
    simp [ddcDensity, hy]
  have hfullS (k : ComplexModel n → ℝ) (hk : ∀ x ∉ F.source, k x = 0) :
      ∫ x, k x ∂μ = ∫ x in F.source, k x ∂μ := by
    rw [← integral_indicator F.open_source.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ F.source
    · simp [hx]
    · simp [hx, hk x hx]
  have hfullT (k : ComplexModel n → ℝ) (hk : ∀ x ∉ F.target, k x = 0) :
      ∫ x, k x ∂μ = ∫ x in F.target, k x ∂μ := by
    rw [← integral_indicator F.open_target.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ F.target
    · simp [hx]
    · simp [hx, hk x hx]
  have hζ0 : ∀ y ∉ F.target, ddcAdjoint (⇑B) ζ y * g y = 0 := by
    intro y hy
    simp [g, transportSymm, hy]
  calc
    ∫ x, ddcAdjoint (⇑B) η x * φ x ∂μ = ∫ x, ddcDensity B φ η x ∂μ :=
      integral_ddcAdjoint_mul hφ B η
    _ = ∫ x in F.source, ddcDensity B φ η x ∂μ :=
      hfullS _ fun x hx => hdens0 φ U η x (testForm_eq_zero_of_notMem η hx)
    _ = ∫ x in F.source, |(fderiv ℝ τ x).det| • ddcDensity B g ζ (F x) ∂μ := by
      refine setIntegral_congr_fun F.open_source.measurableSet fun x hx => ?_
      rw [abs_of_nonneg (det_fderiv_nonneg hp hx), smul_eq_mul]
      exact ddcDensity_pullback_pointwise B hp η ζ hrel hg.contDiffOn hx
        (transportSymm_comp_eventuallyEq F φ hx)
    _ = ∫ y in F.target, ddcDensity B g ζ y ∂μ :=
      (integral_target_eq_integral_abs_det_fderiv_smul μ hderiv _).symm
    _ = ∫ y, ddcDensity B g ζ y ∂μ :=
      (hfullT _ fun y hy => hdens0 g V ζ y (testForm_eq_zero_of_notMem ζ hy)).symm
    _ = ∫ y, ddcAdjoint (⇑B) ζ y * g y ∂μ := (integral_ddcAdjoint_mul hg B ζ).symm
    _ = ∫ y in F.target, ddcAdjoint (⇑B) ζ y * g y ∂μ := hfullT _ hζ0
    _ = ∫ x in F.source, |(fderiv ℝ τ x).det| • (ddcAdjoint (⇑B) ζ (F x) * g (F x)) ∂μ :=
      integral_target_eq_integral_abs_det_fderiv_smul μ hderiv _
    _ = _ := by
      refine setIntegral_congr_fun F.open_source.measurableSet fun x hx => ?_
      simp only [g, transportSymm, F.map_source hx, if_true, F.left_inv hx]
      rfl

/-- The adjoint test function of `η = τ^* ζ` is, almost everywhere on `U`, the
Jacobian-weighted pull-back of the adjoint test function of `ζ`. -/
theorem ddcAdjoint_pullback_ae
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (hp : IsBiholomorphicPair U V τ σ) (η : TestForm U q) (ζ : TestForm V q)
    (hrel : ∀ z ∈ U, ∀ v : Fin q → ComplexModel n,
      η z v = ζ (τ z) (fun i => fderiv ℝ τ z (v i)))
 :
    ∀ᵐ x ∂μ, x ∈ U →
      ddcAdjoint B η x - |(fderiv ℝ τ x).det| * ddcAdjoint B ζ (τ x) = 0 := by
  let PS : ComplexModel n → ℝ := ddcAdjoint (⇑B) η
  let PR : ComplexModel n → ℝ := ddcAdjoint (⇑B) ζ
  have hτsmooth : ContDiffOn ℝ ∞ τ U := fun y hy => (contDiffAt_real hp hy).contDiffWithinAt
  have hDcont : ContinuousOn (fun x => |(fderiv ℝ τ x).det|) U :=
    (continuous_abs.comp ContinuousLinearMap.continuous_det).comp_continuousOn
      (hτsmooth.continuousOn_fderiv_of_isOpen U.isOpen (by simp))
  have hJcont : ContinuousOn (fun x => |(fderiv ℝ τ x).det| * PR (τ x)) U :=
    hDcont.mul ((ddcAdjoint (⇑B) ζ).continuous.comp_continuousOn hp.holo.continuousOn)
  have hcont : ContinuousOn (fun x => PS x - |(fderiv ℝ τ x).det| * PR (τ x)) U :=
    (ddcAdjoint (⇑B) η).continuous.continuousOn.sub hJcont
  refine U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn U.isOpen.measurableSet) fun φ hφ hc hs => ?_
  have hint1 : Integrable (fun x => PS x * φ x) μ :=
    ((ddcAdjoint (⇑B) η).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hJφcont : Continuous (fun x => (|(fderiv ℝ τ x).det| * PR (τ x)) * φ x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact ((hJcont x hx).continuousAt (U.isOpen.mem_nhds hx)).mul
        hφ.continuous.continuousAt
    · have hxt : x ∉ tsupport φ := fun h => hx (hs h)
      have hev : (fun x => (|(fderiv ℝ τ x).det| * PR (τ x)) * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxt] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact continuousAt_const.congr hev.symm
  have hint2 : Integrable (fun x => (|(fderiv ℝ τ x).det| * PR (τ x)) * φ x) μ :=
    hJφcont.integrable_of_hasCompactSupport hc.mul_left
  have hstep := integral_ddcAdjoint_mul_pullback (μ := μ) B hp η ζ hrel hφ hc hs
  have hfull : ∫ x in (U : Set (ComplexModel n)), |(fderiv ℝ τ x).det| • (PR (τ x) * φ x) ∂μ =
      ∫ x, (|(fderiv ℝ τ x).det| * PR (τ x)) * φ x ∂μ := by
    rw [← integral_indicator U.isOpen.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp [hx, smul_eq_mul, mul_assoc]
    · have hxt : x ∉ tsupport φ := fun h => hx (hs h)
      simp [hx, image_eq_zero_of_notMem_tsupport hxt]
  calc
    ∫ x, φ x • (PS x - |(fderiv ℝ τ x).det| * PR (τ x)) ∂μ =
        ∫ x, PS x * φ x ∂μ - ∫ x, (|(fderiv ℝ τ x).det| * PR (τ x)) * φ x ∂μ := by
      rw [← integral_sub hint1 hint2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    _ = 0 := by
      change ∫ x, ddcAdjoint (⇑B) η x * φ x ∂μ - _ = 0
      rw [hstep, hfull, sub_self]

/-- **Holomorphic covariance of `ddᶜ`.** For a biholomorphism `τ : U → V`, test forms
`η = τ^* ζ` and any function `f`, `∫ (ddᶜ)^*η · (f ∘ τ) = ∫ (ddᶜ)^*ζ · f`. -/
theorem integral_ddcAdjoint_mul_comp
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (hp : IsBiholomorphicPair U V τ σ) (η : TestForm U q) (ζ : TestForm V q)
    (hrel : ∀ z ∈ U, ∀ v : Fin q → ComplexModel n,
      η z v = ζ (τ z) (fun i => fderiv ℝ τ z (v i)))
    (f : ComplexModel n → ℝ) :
    ∫ x, ddcAdjoint B η x * f (τ x) ∂μ = ∫ y, ddcAdjoint B ζ y * f y ∂μ := by
  let F := pairHomeomorph hp
  have hderiv (x : ComplexModel n) (hx : x ∈ F.source) : HasFDerivAt F (fderiv ℝ τ x) x :=
    hasFDerivAt_real hp hx
  have hae := ddcAdjoint_pullback_ae (μ := μ) B hp η ζ hrel
  have hηsupp : ∀ x ∉ U, ddcAdjoint (⇑B) η x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport (ddcAdjoint (⇑B) η) := fun h =>
      hx ((ddcAdjoint (⇑B) η).tsupport_subset h)
    exact image_eq_zero_of_notMem_tsupport hxt
  have hζsupp : ∀ y ∉ V, ddcAdjoint (⇑B) ζ y = 0 := by
    intro y hy
    have hyt : y ∉ tsupport (ddcAdjoint (⇑B) ζ) := fun h =>
      hy ((ddcAdjoint (⇑B) ζ).tsupport_subset h)
    exact image_eq_zero_of_notMem_tsupport hyt
  calc
    ∫ x, ddcAdjoint (⇑B) η x * f (τ x) ∂μ =
        ∫ x in F.source, ddcAdjoint (⇑B) η x * f (F x) ∂μ := by
      rw [← integral_indicator F.open_source.measurableSet]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ F.source
      · rw [indicator_of_mem hx]
        rfl
      · simp [hx, hηsupp x hx]
    _ = ∫ x in F.source, |(fderiv ℝ τ x).det| •
        (ddcAdjoint (⇑B) ζ (F x) * f (F x)) ∂μ := by
      refine setIntegral_congr_ae F.open_source.measurableSet ?_
      filter_upwards [hae] with x hx hxS
      rw [sub_eq_zero.mp (hx hxS), smul_eq_mul, mul_assoc]
      rfl
    _ = ∫ y in F.target, ddcAdjoint (⇑B) ζ y * f y ∂μ :=
      (integral_target_eq_integral_abs_det_fderiv_smul μ hderiv
        (fun y => ddcAdjoint (⇑B) ζ y * f y)).symm
    _ = ∫ y, ddcAdjoint (⇑B) ζ y * f y ∂μ := by
      rw [← integral_indicator F.open_target.measurableSet]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ F.target
      · simp [hy]
      · simp [hy, hζsupp y hy]

end Assembly

/-! ### Transport of test forms along a biholomorphism -/

section Transport

variable {U V : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

/-- The covector pull-back field `w ↦ (Dσ_w)^*` on `q`-forms. -/
def pushField (σ : ComplexModel n → ComplexModel n) (q : ℕ) (w : ComplexModel n) :
    (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ] (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ σ w)

theorem pushField_apply (w : ComplexModel n) (A : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    pushField σ q w A = A.compContinuousLinearMap (fderiv ℝ σ w) := rfl

theorem contDiffOn_pushField (h : IsBiholomorphicPair U V τ σ) :
    ContDiffOn ℝ ∞ (pushField σ q) V := by
  let : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  let : FiniteDimensional ℝ (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :=
    Module.Finite.of_injective
      (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ))
      ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  have hG : ContDiffOn ℝ ∞ σ V := fun y hy => (contDiffAt_real (pairSymm h) hy).contDiffWithinAt
  have hD : ContDiffOn ℝ ∞ (fun w => fderiv ℝ σ w) V :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen V.isOpen).mp hG).2
  apply contDiffOn_clm_apply.mpr
  intro A
  exact SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback.contDiffOn_compContinuousLinearMap
    contDiffOn_const hD

/-- The compact `τ(supp η)` carrying the transported test form. -/
theorem isCompact_image_tsupport (h : IsBiholomorphicPair U V τ σ) (η : TestForm U q) :
    IsCompact (τ '' tsupport η) :=
  η.hasCompactSupport.isCompact.image_of_continuousOn
    (h.holo.continuousOn.mono η.tsupport_subset)

theorem image_tsupport_subset (h : IsBiholomorphicPair U V τ σ) (η : TestForm U q) :
    τ '' tsupport η ⊆ V := by
  rintro _ ⟨x, hx, rfl⟩
  exact h.mapsTo (η.tsupport_subset hx)

theorem pushField_vanish (h : IsBiholomorphicPair U V τ σ) (η : TestForm U q) :
    ∀ w ∈ (V : Set (ComplexModel n)), w ∉ τ '' tsupport η →
      pushField σ q w = 0 ∨ σ w ∉ tsupport η := by
  intro w hw hwL
  right
  intro hσ
  exact hwL ⟨σ w, hσ, h.right_inv w hw⟩

/-- **The transported test form** `σ^* η` on `V`, `w ↦ η_{σ w} ∘ (Dσ_w)^{⊗q}`. -/
def pushTest (h : IsBiholomorphicPair U V τ σ) (η : TestForm U q) : TestForm V q where
  toFun := weightedComp V σ (pushField σ q) η
  contDiff' := contDiff_weightedComp V.isOpen
    (fun y hy => (contDiffAt_real (pairSymm h) hy).contDiffWithinAt) (contDiffOn_pushField h)
    (isCompact_image_tsupport h η).isClosed (image_tsupport_subset h η) (pushField_vanish h η)
    η.contDiff (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  hasCompactSupport' := HasCompactSupport.intro (isCompact_image_tsupport h η)
    (fun w hw => weightedComp_eq_zero (pushField_vanish h η)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hw)
  tsupport_subset' := by
    refine (closure_minimal ?_ (isCompact_image_tsupport h η).isClosed).trans
      (image_tsupport_subset h η)
    intro w hw
    by_contra hwL
    exact hw (weightedComp_eq_zero (pushField_vanish h η)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hwL)

theorem pushTest_apply (h : IsBiholomorphicPair U V τ σ) (η : TestForm U q) {w : ComplexModel n}
    (hw : w ∈ V) : pushTest h η w = (η (σ w)).compContinuousLinearMap (fderiv ℝ σ w) := by
  change weightedComp V σ (pushField σ q) η w = _
  rw [weightedComp_of_mem hw, pushField_apply]

/-- `η = τ^* (σ^* η)` on `U`. -/
theorem pushTest_rel (h : IsBiholomorphicPair U V τ σ) (η : TestForm U q) :
    ∀ z ∈ U, ∀ v : Fin q → ComplexModel n,
      η z v = pushTest h η (τ z) (fun i => fderiv ℝ τ z (v i)) := by
  intro z hz v
  rw [pushTest_apply h η (h.mapsTo hz), ContinuousAlternatingMap.compContinuousLinearMap_apply,
    h.left_inv z hz]
  congr 1
  funext i
  have hc := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L (v i))
    (fderiv_symm_comp h hz)
  simpa using hc.symm

end Transport

end SGPT.NPP.MassPushforward
