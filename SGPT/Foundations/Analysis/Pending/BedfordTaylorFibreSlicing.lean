import SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCLN
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotStokes
import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure

set_option autoImplicit false

/-!
# Bedford--Taylor slicing with one slot `|τ|²`

Toward Xia, SGPT, proof of Proposition 4.3.3, Step 1 (`xia-sgpt:page-0171`, the slicing behind
(2.11) and (4.29)--(4.34)). Identify `ℂⁿ⁺¹` with `ℂⁿ × ℂ`, `q = (y, τ)`, by
`FiniteGeodesicMaximality.stripModelEquiv`, and write `ι_τ y = (y, τ)` for the inclusion of the
fibre over `τ` (`fibreMap`). For an open set `Ω ⊆ ℂⁿ⁺¹` the fibre `Ω_τ = ι_τ⁻¹ Ω` is open in `ℂⁿ`
(`fibreOpens`).

Let `u₁, …, uₙ` be locally bounded plurisubharmonic functions on `Ω`, in the Bedford--Taylor sense
of `BedfordTaylor.IsBTLimit`: they have decreasing smooth plurisubharmonic approximations on every
relatively compact open subset. Let `ν` be the Bedford--Taylor limit of `(u₁, …, uₙ, |τ|²)` on `Ω`,
i.e. `ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ∧ ddᶜ|τ|²`.

* `IsAdmissible.fibre`, `exists_isBTLimit_fibre` — the restrictions of decreasing smooth
  approximations to a fibre are decreasing smooth approximations of the restrictions (the top-left
  block of a positive semidefinite matrix is positive semidefinite), so the fibre tuples
  `(u₁(·, τ), …, uₙ(·, τ))` have Bedford--Taylor limits `μ_τ` on `Ω_τ`.
* `mixedDensity_eq_fibre_div_pi_of_contDiffOn` — the smooth slicing identity of
  `MixedDensityRankOneSlot` for functions that are smooth on an open set only.
* `measurePreserving_stripModelEquiv_symm` — `ℂⁿ × ℂ ≃ ℂⁿ⁺¹` preserves Lebesgue measure.
* `integral_mul_isBTLimit_eq_fibre` — **the slicing theorem**: for a continuous `χ` with compact
  support in `Ω` and a weight `w` with decreasing smooth plurisubharmonic approximations (for
  instance `w = 1`), `τ ↦ ∫ χ w dμ_τ` is integrable and
  \[
    \int \chi\, w\, d\nu = \frac1\pi \int_{\mathbb C} \Bigl(\int_{\mathbb C^n}
      \chi(y, \tau)\, w(y, \tau)\, d\mu_\tau(y)\Bigr) d\lambda(\tau).
  \]
  The proof passes to the limit in the smooth identity integrated by Fubini; the inner integrals
  converge for every `τ` (Bedford--Taylor convergence on the fibre, weighted), and the
  Chern--Levine--Nirenberg estimate (`BedfordTaylor.exists_cln_constant`) bounds them uniformly in
  the approximation index on finitely many boxes covering `supp χ`, so dominated convergence applies
  in `τ`.
-/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FiniteGeodesicMaximality
  MixedDensityRankOneSlot BedfordTaylor

noncomputable section

variable {n : ℕ}

/-! ### Fibres -/

/-- The inclusion `y ↦ (y, τ)` of the fibre over `τ`, read in `ℂⁿ⁺¹`. -/
def fibreMap (n : ℕ) (τ : ℂ) (y : ComplexModel n) : ComplexModel (n + 1) :=
  (stripModelEquiv n).symm (y, τ)

theorem continuous_fibreMap (τ : ℂ) : Continuous (fibreMap n τ) :=
  (stripModelEquiv n).symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem fibreMap_uncurry_eq : (fun p : ComplexModel n × ℂ => fibreMap n p.2 p.1) =
    (stripModelEquiv n).symm := by
  funext p
  simp [fibreMap]

theorem continuous_fibreMap_uncurry :
    Continuous fun p : ComplexModel n × ℂ => fibreMap n p.2 p.1 := by
  rw [fibreMap_uncurry_eq]
  exact (stripModelEquiv n).symm.continuous

theorem fibreMap_injective (τ : ℂ) : Function.Injective (fibreMap n τ) := fun y y' h => by
  have := congrArg (stripModelEquiv n) h
  simp only [fibreMap, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.injEq] at this
  exact this.1

theorem stripModelEquiv_fibreMap (τ : ℂ) (y : ComplexModel n) :
    stripModelEquiv n (fibreMap n τ y) = (y, τ) := by
  simp [fibreMap]

theorem fibreMap_stripModelEquiv (q : ComplexModel (n + 1)) :
    fibreMap n (stripModelEquiv n q).2 (stripModelEquiv n q).1 = q := by
  simp [fibreMap]

/-- Preimages of compact sets under the fibre map are compact. -/
theorem isCompact_preimage_fibreMap {K : Set (ComplexModel (n + 1))} (hK : IsCompact K) (τ : ℂ) :
    IsCompact (fibreMap n τ ⁻¹' K) := by
  have h : fibreMap n τ ⁻¹' K = Prod.fst '' (stripModelEquiv n '' K ∩ univ ×ˢ {τ}) := by
    ext y
    constructor
    · intro hy
      exact ⟨(y, τ), ⟨⟨_, hy, stripModelEquiv_fibreMap τ y⟩, mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨y', τ'⟩, ⟨⟨q, hq, hqe⟩, -, hτ'⟩, rfl⟩
      simp only [mem_singleton_iff] at hτ'
      subst hτ'
      show fibreMap n τ' y' ∈ K
      have : fibreMap n τ' y' = q := by
        rw [← fibreMap_stripModelEquiv q, hqe]
      rwa [this]
  rw [h]
  exact ((hK.image (stripModelEquiv n).continuous).inter_right
    (isClosed_univ.prod isClosed_singleton)).image continuous_fst

theorem contDiff_fibreMap (τ : ℂ) : ContDiff ℝ ∞ (fibreMap n τ) :=
  ((stripModelEquiv n).symm.contDiff.restrict_scalars ℝ).comp (contDiff_id.prodMk contDiff_const)

/-- The fibre `Ω_τ = {y | (y, τ) ∈ Ω}` of an open set, open in `ℂⁿ`. -/
def fibreOpens (Ω : Opens (ComplexModel (n + 1))) (τ : ℂ) : Opens (ComplexModel n) :=
  ⟨fibreMap n τ ⁻¹' Ω, Ω.isOpen.preimage (continuous_fibreMap τ)⟩

@[simp] theorem mem_fibreOpens {Ω : Opens (ComplexModel (n + 1))} {τ : ℂ} {y : ComplexModel n} :
    y ∈ fibreOpens Ω τ ↔ fibreMap n τ y ∈ Ω := Iff.rfl

theorem fibreOpens_mono {U Ω : Opens (ComplexModel (n + 1))} (h : U ≤ Ω) (τ : ℂ) :
    fibreOpens U τ ≤ fibreOpens Ω τ := fun _ hy => h hy

/-- Relative compactness passes to the fibres. -/
theorem relativelyCompactIn_fibreOpens {U Ω : Opens (ComplexModel (n + 1))}
    (hU : RelativelyCompactIn U Ω) (τ : ℂ) :
    RelativelyCompactIn (fibreOpens U τ) (fibreOpens Ω τ) := by
  have hcl : closure (fibreOpens U τ : Set (ComplexModel n)) ⊆
      fibreMap n τ ⁻¹' closure (U : Set (ComplexModel (n + 1))) :=
    closure_minimal (fun y hy => subset_closure hy)
      (isClosed_closure.preimage (continuous_fibreMap τ))
  exact ⟨(isCompact_preimage_fibreMap hU.1 τ).of_isClosed_subset isClosed_closure hcl,
    fun y hy => hU.2 (hcl hy)⟩

/-- The restriction of a function on `ℂⁿ⁺¹` to the fibre over `τ`. -/
def fibreRestrict (f : ComplexModel (n + 1) → ℝ) (τ : ℂ) : ComplexModel n → ℝ :=
  fun y => f (fibreMap n τ y)

/-- The fibre tuple: the first `n` slots restricted to the fibre over `τ`. -/
def fibreTuple (u : Fin (n + 1) → ComplexModel (n + 1) → ℝ) (τ : ℂ) :
    Fin n → ComplexModel n → ℝ :=
  fun i => fibreRestrict (u i.castSucc) τ

/-! ### Smooth functions on open sets: local versions of the smooth identity -/

/-- A function smooth on an open set agrees near each of its points with a globally smooth one. -/
theorem exists_contDiff_eventuallyEq {m : ℕ} {U : Set (ComplexModel m)} (hU : IsOpen U)
    {f : ComplexModel m → ℝ} (hf : ContDiffOn ℝ ∞ f U) {z : ComplexModel m} (hz : z ∈ U) :
    ∃ g : ComplexModel m → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 z] f := by
  obtain ⟨η, hη1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := ⟨U, hU⟩)
    (isCompact_singleton (x := z)) (singleton_subset_iff.2 hz)
  refine ⟨fun y => η y • f y,
    LocalPotentials.contDiff_smul_of_tsupport_subset hU η.contDiff η.tsupport_subset hf, ?_⟩
  have : ∀ᶠ y in 𝓝 z, η y = 1 := hη1.filter_mono (nhds_le_nhdsSet (mem_singleton z))
  filter_upwards [this] with y hy
  simp [hy]

theorem fibreRestrict_eventuallyEq {f g : ComplexModel (n + 1) → ℝ} {τ : ℂ} {y : ComplexModel n}
    (h : f =ᶠ[𝓝 (fibreMap n τ y)] g) : fibreRestrict f τ =ᶠ[𝓝 y] fibreRestrict g τ :=
  (continuous_fibreMap τ).continuousAt.eventually h

/-- **The complex Hessian on a fibre**, for a function smooth on an open set: the top-left block
of the complex Hessian. -/
theorem complexHessian_fibreRestrict {U : Set (ComplexModel (n + 1))} (hU : IsOpen U)
    {f : ComplexModel (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f U) {τ : ℂ} {y : ComplexModel n}
    (hy : fibreMap n τ y ∈ U) :
    complexHessian (fibreRestrict f τ) y =
      (complexHessian f (fibreMap n τ y)).submatrix Fin.castSucc Fin.castSucc := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hf hy
  rw [MixedHessian.complexHessian_congr (fibreRestrict_eventuallyEq hgf.symm),
    MixedHessian.complexHessian_congr hgf.symm]
  exact complexHessian_fibre (hg.of_le (WithTop.coe_le_coe.mpr le_top)) y τ

/-- **The smooth slicing identity** for functions smooth on an open set. -/
theorem mixedDensity_eq_fibre_div_pi_of_contDiffOn {U : Set (ComplexModel (n + 1))}
    (hU : IsOpen U) (F : Fin (n + 1) → ComplexModel (n + 1) → ℝ)
    (hF : ∀ i : Fin n, ContDiffOn ℝ ∞ (F i.castSucc) U) (hlast : F (Fin.last n) = lastNormSq n)
    {τ : ℂ} {y : ComplexModel n} (hy : fibreMap n τ y ∈ U) :
    mixedDensity F (fibreMap n τ y) = mixedDensity (fibreTuple F τ) y / Real.pi := by
  choose g hg hgF using fun i : Fin n => exists_contDiff_eventuallyEq hU (hF i) hy
  set G : Fin (n + 1) → ComplexModel (n + 1) → ℝ := Fin.lastCases (lastNormSq n) g with hG
  have hGc (i : Fin n) : G i.castSucc = g i := by simp [hG]
  have hGl : G (Fin.last n) = lastNormSq n := by simp [hG]
  have h1 : mixedDensity F (fibreMap n τ y) = mixedDensity G (fibreMap n τ y) := by
    refine mixedDensity_congr fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hlast, hGl]
    · rw [hGc]
      exact (hgF i).symm
  have h2 : mixedDensity (fibreTuple F τ) y = mixedDensity (fibreTuple G τ) y := by
    refine mixedDensity_congr fun i => ?_
    simp only [fibreTuple, hGc]
    exact fibreRestrict_eventuallyEq (hgF i).symm
  have hGs : ∀ i : Fin n, ContDiff ℝ 2 (G i.castSucc) := fun i => by
    rw [hGc i]
    exact (hg i).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [h1, h2]
  exact mixedDensity_eq_fibre_div_pi G hGs hGl y τ

/-! ### Restricting approximations to fibres -/

theorem IsSmoothPsdOn.fibre {U : Opens (ComplexModel (n + 1))} {f : ComplexModel (n + 1) → ℝ}
    (hf : IsSmoothPsdOn U f) (τ : ℂ) : IsSmoothPsdOn (fibreOpens U τ) (fibreRestrict f τ) := by
  refine ⟨hf.1.comp (contDiff_fibreMap τ).contDiffOn fun y hy => hy, fun y hy => ?_⟩
  rw [complexHessian_fibreRestrict U.isOpen hf.1 hy]
  exact (hf.2 _ hy).submatrix _

theorem IsDecApprox.fibre {U : Opens (ComplexModel (n + 1))} {w : ComplexModel (n + 1) → ℝ}
    {G : ℕ → ComplexModel (n + 1) → ℝ} (hG : IsDecApprox U w G) (τ : ℂ) :
    IsDecApprox (fibreOpens U τ) (fibreRestrict w τ) fun k => fibreRestrict (G k) τ := by
  refine ⟨fun k => IsSmoothPsdOn.fibre (hG.1 k) τ, fun y hy => hG.2.1 _ hy, fun y hy => hG.2.2.1 _ hy,
    fun K hK hKU => ?_⟩
  obtain ⟨m, hm⟩ := hG.2.2.2 (fibreMap n τ '' K) (hK.image (continuous_fibreMap τ))
    (image_subset_iff.2 hKU)
  exact ⟨m, by rintro _ ⟨y, hy, rfl⟩; exact hm ⟨fibreMap n τ y, ⟨y, hy, rfl⟩, rfl⟩⟩

theorem IsAdmissible.fibre {U : Opens (ComplexModel (n + 1))}
    {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ} {F : Fin (n + 1) → ℕ → ComplexModel (n + 1) → ℝ}
    (hF : IsAdmissible (n + 1) U u F) (τ : ℂ) :
    IsAdmissible n (fibreOpens U τ) (fibreTuple u τ)
      (fun i k => fibreRestrict (F i.castSucc k) τ) :=
  ⟨fun i => IsDecApprox.fibre (hF.1 i.castSucc) τ, fun i hi => absurd i.isLt (not_lt.2 hi)⟩

/-- Admissible approximations of the fibre tuple exist on every relatively compact open subset of
the fibre. -/
theorem exists_isAdmissible_fibre {Ω : Opens (ComplexModel (n + 1))}
    {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
    (hadm : ∀ V, RelativelyCompactIn V Ω → ∃ F, IsAdmissible (n + 1) V u F) (τ : ℂ)
    (V' : Opens (ComplexModel n)) (hV' : RelativelyCompactIn V' (fibreOpens Ω τ)) :
    ∃ F', IsAdmissible n V' (fibreTuple u τ) F' := by
  have hK : IsCompact (fibreMap n τ '' closure (V' : Set (ComplexModel n))) :=
    hV'.1.image (continuous_fibreMap τ)
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
    (image_subset_iff.2 hV'.2)
  obtain ⟨F, hF⟩ := hadm ⟨W, hWo⟩ ⟨hWc, hWΩ⟩
  refine ⟨_, (IsAdmissible.fibre hF τ).mono fun y hy => ?_⟩
  exact hKW ⟨y, subset_closure hy, rfl⟩

/-- **The fibre tuples have Bedford--Taylor limits.** -/
theorem exists_isBTLimit_fibre {Ω : Opens (ComplexModel (n + 1))}
    {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ} {ν : Measure (ComplexModel (n + 1))}
    (hν : IsBTLimit Ω u ν) (τ : ℂ) : ∃ μ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) μ :=
  exists_isBTLimit (exists_isAdmissible_fibre (fun V hV => (hν.2.2 V hV).imp fun _ h => h.1) τ)

/-! ### Lebesgue measure and Fubini -/

/-- `ℂ ≃ ℂ¹` as a real linear isometry. -/
def complexLineIsometry : ℂ ≃ₗᵢ[ℝ] ComplexModel 1 where
  toLinearEquiv := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.toLinearEquiv.restrictScalars ℝ
  norm_map' := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.norm_map

theorem complexLineIsometry_apply (z : ℂ) (i : Fin 1) : complexLineIsometry z i = z :=
  OrthonormalBasis.singleton_repr (ι := Fin 1) (𝕜 := ℂ) z i

theorem stripModelEquiv_symm_eq (p : ComplexModel n × ℂ) :
    (stripModelEquiv n).symm p =
      ProductComplexManifold.prodModelEquiv n 1 (p.1, complexLineIsometry p.2) := by
  have h : (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)).symm p.2 = complexLineIsometry p.2 := by
    ext i
    rw [complexLineIsometry_apply]
    simp [PiLp.equivOfUnique, Subsingleton.elim i default]
  simp only [stripModelEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearEquiv.symm_symm]
  rw [h]

/-- **`ℂⁿ × ℂ ≃ ℂⁿ⁺¹` preserves Lebesgue measure.** -/
theorem measurePreserving_stripModelEquiv_symm :
    MeasurePreserving (stripModelEquiv n).symm (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (id : ComplexModel n → ComplexModel n) complexLineIsometry)
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod complexLineIsometry.measurePreserving
  have h2 := (ProductMixedMeasure.measurePreserving_prodModelEquiv n 1).comp h1
  have hfun : (⇑(ProductComplexManifold.prodModelEquiv n 1) ∘
      Prod.map (id : ComplexModel n → ComplexModel n) complexLineIsometry) =
      ⇑(stripModelEquiv n).symm := by
    funext p
    rw [stripModelEquiv_symm_eq]
    rfl
  rwa [hfun] at h2

/-- **Fubini through the fibres.** -/
theorem integral_eq_integral_fibre {g : ComplexModel (n + 1) → ℝ} (hg : Integrable g) :
    ∫ q, g q = ∫ τ : ℂ, ∫ y, g (fibreMap n τ y) := by
  have hmp := measurePreserving_stripModelEquiv_symm (n := n)
  have hemb : MeasurableEmbedding (stripModelEquiv n).symm :=
    (stripModelEquiv n).symm.toHomeomorph.measurableEmbedding
  have hint : Integrable (g ∘ (stripModelEquiv n).symm) (volume.prod volume) :=
    (hmp.integrable_comp_emb hemb).2 hg
  calc ∫ q, g q = ∫ p, (g ∘ (stripModelEquiv n).symm) p ∂(volume.prod volume) :=
        (hmp.integral_comp hemb g).symm
    _ = ∫ τ : ℂ, ∫ y, (g ∘ (stripModelEquiv n).symm) (y, τ) := integral_prod_symm _ hint
    _ = ∫ τ : ℂ, ∫ y, g (fibreMap n τ y) := rfl

theorem integrable_integral_fibre {g : ComplexModel (n + 1) → ℝ} (hg : Integrable g) :
    Integrable fun τ : ℂ => ∫ y, g (fibreMap n τ y) := by
  have hmp := measurePreserving_stripModelEquiv_symm (n := n)
  have hemb : MeasurableEmbedding (stripModelEquiv n).symm :=
    (stripModelEquiv n).symm.toHomeomorph.measurableEmbedding
  have hint : Integrable (g ∘ (stripModelEquiv n).symm) (volume.prod volume) :=
    (hmp.integrable_comp_emb hemb).2 hg
  exact hint.integral_prod_right

/-! ### A covering bound -/

/-- If `|f| ≤ A·D` wherever `f ≠ 0`, every such point lies in one of finitely many balls, and `D` is
nonnegative and integrable on each ball, then `|∫ f| ≤ A Σ ∫_{ball} D`. -/
theorem abs_integral_le_sum_of_cover {m : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ComplexModel m) (r : ι → ℝ) {f D : ComplexModel m → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : Integrable f) (hD : ∀ j ∈ s, IntegrableOn D (ball (c j) (r j)))
    (hD0 : ∀ j ∈ s, ∀ y ∈ ball (c j) (r j), 0 ≤ D y)
    (hcover : ∀ y, f y ≠ 0 → (∃ j ∈ s, y ∈ ball (c j) (r j)) ∧ |f y| ≤ A * D y) :
    |∫ y, f y| ≤ A * ∑ j ∈ s, ∫ y in ball (c j) (r j), D y := by
  have hind (j : ι) (hj : j ∈ s) (y : ComplexModel m) :
      0 ≤ (ball (c j) (r j)).indicator D y := by
    by_cases hy : y ∈ ball (c j) (r j)
    · rw [indicator_of_mem hy]; exact hD0 j hj y hy
    · rw [indicator_of_notMem hy]
  have hpt (y : ComplexModel m) :
      |f y| ≤ A * ∑ j ∈ s, (ball (c j) (r j)).indicator D y := by
    by_cases hfy : f y = 0
    · rw [hfy, abs_zero]
      exact mul_nonneg hA (Finset.sum_nonneg fun j hj => hind j hj y)
    · obtain ⟨⟨j₀, hj₀, hy⟩, hle⟩ := hcover y hfy
      refine hle.trans (mul_le_mul_of_nonneg_left ?_ hA)
      rw [← indicator_of_mem hy D]
      exact Finset.single_le_sum (f := fun j => (ball (c j) (r j)).indicator D y)
        (fun j hj => hind j hj y) hj₀
  have hRint : Integrable fun y => A * ∑ j ∈ s, (ball (c j) (r j)).indicator D y :=
    (integrable_finsetSum s fun j hj =>
      (integrable_indicator_iff measurableSet_ball).2 (hD j hj)).const_mul A
  calc |∫ y, f y| ≤ ∫ y, |f y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, A * ∑ j ∈ s, (ball (c j) (r j)).indicator D y :=
        integral_mono hf.abs hRint hpt
    _ = A * ∑ j ∈ s, ∫ y in ball (c j) (r j), D y := by
        rw [integral_const_mul, integral_finsetSum s fun j hj =>
          (integrable_indicator_iff measurableSet_ball).2 (hD j hj)]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_indicator measurableSet_ball

/-! ### A uniform Chern--Levine--Nirenberg bound on the fibres -/

theorem isSmoothPsdOn_const {m : ℕ} (U : Opens (ComplexModel m)) (c : ℝ) :
    IsSmoothPsdOn U fun _ => c :=
  ⟨contDiffOn_const, fun z _ => by rw [complexHessian_const]; exact Matrix.PosSemidef.zero⟩

theorem tsupport_fibreRestrict_subset (f : ComplexModel (n + 1) → ℝ) (τ : ℂ) :
    tsupport (fibreRestrict f τ) ⊆ fibreMap n τ ⁻¹' tsupport f :=
  closure_minimal (fun _ hy => subset_tsupport f hy)
    ((isClosed_tsupport f).preimage (continuous_fibreMap τ))

/-- **Uniform mass bound on the fibres.** Let `F` be smooth plurisubharmonic slots on `U`, uniformly
bounded on compact subsets of `U`, and `K ⊆ U` compact. There is an integrable `B` on `ℂ` such that
for every index `k`, every `τ` and every integrable `f` on the fibre with `|f| ≤ A · MAₙ(F(·, τ))`
on its support and support in `K`, `|∫ f| ≤ A · B(τ)`. -/
theorem exists_integrable_fibre_bound {U : Opens (ComplexModel (n + 1))}
    {F : Fin n → ℕ → ComplexModel (n + 1) → ℝ} (hF : ∀ i k, IsSmoothPsdOn U (F i k))
    (hFb : ∀ Q : Set (ComplexModel (n + 1)), IsCompact Q → Q ⊆ U →
      ∃ C, ∀ i k, ∀ z ∈ Q, |F i k z| ≤ C)
    {K : Set (ComplexModel (n + 1))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℂ → ℝ, Integrable B ∧ ∀ (k : ℕ) (τ : ℂ) (A : ℝ), 0 ≤ A →
      ∀ f : ComplexModel n → ℝ, Integrable f →
        (∀ y, f y ≠ 0 → fibreMap n τ y ∈ K ∧
          |f y| ≤ A * mixedDensity (fun i => fibreRestrict (F i k) τ) y) →
        |∫ y, f y| ≤ A * B τ := by
  classical
  set L := stripModelEquiv n
  set K' : Set (ComplexModel n × ℂ) := L '' K
  have hK' : IsCompact K' := hK.image L.continuous
  set O : Set (ComplexModel n × ℂ) := L.symm ⁻¹' (U : Set (ComplexModel (n + 1)))
  have hO : IsOpen O := U.isOpen.preimage L.symm.continuous
  have hK'O : K' ⊆ O := by
    rintro _ ⟨q, hq, rfl⟩
    show L.symm (L q) ∈ U
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hKU hq
  -- boxes around the points of `K'`
  have hbox : ∀ p : ComplexModel n × ℂ, ∃ R : ℝ, 0 < R ∧
      (p ∈ K' → closedBall p.1 (2 * R) ×ˢ closedBall p.2 (2 * R) ⊆ O) := by
    intro p
    by_cases hp : p ∈ K'
    · obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO p (hK'O hp)
      refine ⟨ε / 4, by positivity, fun _ => ?_⟩
      rw [_root_.closedBall_prod_same]
      exact (closedBall_subset_ball (by linarith)).trans hεO
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  choose R hR hRO using hbox
  obtain ⟨t, htK', hcov⟩ := hK'.elim_nhds_subcover
    (fun p => ball p.1 (R p / 2) ×ˢ ball p.2 (R p))
    (fun p _ => prod_mem_nhds (ball_mem_nhds _ (half_pos (hR p))) (ball_mem_nhds _ (hR p)))
  -- uniform bounds of the slots on the closed boxes
  set Q : ComplexModel n × ℂ → Set (ComplexModel (n + 1)) :=
    fun p => L.symm '' (closedBall p.1 (2 * R p) ×ˢ closedBall p.2 (2 * R p))
  have hQc (p : ComplexModel n × ℂ) : IsCompact (Q p) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image L.symm.continuous
  have hQU (p : ComplexModel n × ℂ) (hp : p ∈ K') : Q p ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hRO p hp hx
  have hM : ∀ p : ComplexModel n × ℂ, ∃ M : ℝ, 0 ≤ M ∧
      (p ∈ K' → ∀ i k, ∀ z ∈ Q p, |F i k z| ≤ M) := by
    intro p
    by_cases hp : p ∈ K'
    · obtain ⟨C, hC⟩ := hFb (Q p) (hQc p) (hQU p hp)
      exact ⟨max C 0, le_max_right _ _, fun _ i k z hz => (hC i k z hz).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose M hM0 hMb using hM
  have hcln (p : ComplexModel n × ℂ) := BedfordTaylor.exists_cln_constant p.1 (hR p) (hM0 p)
  choose Ccl hCcl0 hCcl using hcln
  set c : ComplexModel n × ℂ → ℝ := fun p => Ccl p * volume.real (ball p.1 (R p))
  have hc0 (p : ComplexModel n × ℂ) : 0 ≤ c p := mul_nonneg (hCcl0 p) measureReal_nonneg
  refine ⟨fun τ => ∑ p ∈ t, (ball p.2 (R p)).indicator (fun _ => c p) τ, ?_, ?_⟩
  · exact integrable_finsetSum t fun p _ =>
      (integrable_indicator_iff measurableSet_ball).2
        (integrableOn_const (measure_ball_lt_top (x := p.2) (r := R p)).ne)
  intro k τ A hA f hf hfK
  set D : ComplexModel n → ℝ := mixedDensity fun i => fibreRestrict (F i k) τ
  have hDc : ContinuousOn D (fibreOpens U τ) :=
    continuousOn_mixedDensity fun i => (IsSmoothPsdOn.fibre (hF i k) τ).1
  -- the fibre of the closed box lies in the fibre of `U`
  have hfib (p : ComplexModel n × ℂ) (hp : p ∈ K') (hτ : τ ∈ closedBall p.2 (2 * R p)) :
      closedBall p.1 (2 * R p) ⊆ fibreOpens U τ := by
    intro y hy
    have := hRO p hp (mk_mem_prod hy hτ)
    exact this
  set s := t.filter fun p => τ ∈ ball p.2 (R p)
  have hsK' (p : ComplexModel n × ℂ) (hp : p ∈ s) : p ∈ K' := htK' p (Finset.mem_filter.1 hp).1
  have hsτ (p : ComplexModel n × ℂ) (hp : p ∈ s) : τ ∈ closedBall p.2 (2 * R p) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [hR p]))
      (Finset.mem_filter.1 hp).2
  have hsub (p : ComplexModel n × ℂ) (hp : p ∈ s) :
      closedBall p.1 (R p / 2) ⊆ fibreOpens U τ :=
    (closedBall_subset_closedBall (by linarith [hR p])).trans (hfib p (hsK' p hp) (hsτ p hp))
  have hmain := abs_integral_le_sum_of_cover s (fun p => p.1) (fun p => R p / 2) hA hf
    (fun p hp => ((hDc.mono (hsub p hp)).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall)
    (fun p hp y hy => mixedDensity_nonneg fun i =>
      (IsSmoothPsdOn.fibre (hF i k) τ).2 y (hsub p hp (ball_subset_closedBall hy)))
    (fun y hy => by
      obtain ⟨hyK, hle⟩ := hfK y hy
      refine ⟨?_, hle⟩
      have hmem : (y, τ) ∈ K' := ⟨fibreMap n τ y, hyK, stripModelEquiv_fibreMap τ y⟩
      obtain ⟨p, hpt, hpy⟩ := mem_iUnion₂.1 (hcov hmem)
      exact ⟨p, Finset.mem_filter.2 ⟨hpt, hpy.2⟩, hpy.1⟩)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hA)
  -- each ball is controlled by the Chern--Levine--Nirenberg estimate
  have hball (p : ComplexModel n × ℂ) (hp : p ∈ s) :
      ∫ y in ball p.1 (R p / 2), D y ≤ c p := by
    have h := hCcl p (fibreOpens U τ) (fun i => fibreRestrict (F i k) τ) (fun _ => 0) 1
      (hfib p (hsK' p hp) (hsτ p hp)) (fun i => IsSmoothPsdOn.fibre (hF i k) τ)
      (fun i z hz => hMb p (hsK' p hp) i k _ ⟨(z, τ), mk_mem_prod hz (hsτ p hp), rfl⟩)
      (isSmoothPsdOn_const _ 0) (fun _ _ => zero_le_one)
    simp only [sub_zero, one_mul, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] at h
    exact h
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun p hp => ?_
  by_cases hτp : τ ∈ ball p.2 (R p)
  · rw [if_pos hτp, indicator_of_mem hτp]
    exact hball p (Finset.mem_filter.2 ⟨hp, hτp⟩)
  · rw [if_neg hτp, indicator_of_notMem hτp]

/-! ### The slicing theorem -/

theorem lastUnit_posSemidef : (lastUnit n).PosSemidef := by
  classical
  have h : lastUnit n = Matrix.diagonal fun j => if j = Fin.last n then (1 : ℂ) else 0 := by
    ext j k
    by_cases hjk : j = k
    · subst hjk
      simp [lastUnit]
    · simp only [lastUnit, Matrix.diagonal_apply, hjk, if_false]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hjk (h1.trans h2.symm)
  rw [h]
  refine Matrix.PosSemidef.diagonal fun j => ?_
  by_cases hj : j = Fin.last n <;> simp [hj]

theorem isSmoothPsdOn_lastNormSq (U : Opens (ComplexModel (n + 1))) :
    IsSmoothPsdOn U (lastNormSq n) := by
  refine ⟨?_, fun q _ => by rw [complexHessian_lastNormSq]; exact lastUnit_posSemidef⟩
  have : lastNormSq n = fun q => ‖lastCoordinate n q‖ ^ 2 := rfl
  rw [this]
  exact ((contDiff_norm_sq ℝ).comp (lastCoordinate n).contDiff).contDiffOn

/-- Replacing the approximations of the last slot by the constant sequence `|τ|²`. -/
theorem isAdmissible_lastCases {U : Opens (ComplexModel (n + 1))}
    {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ} (hlast : u (Fin.last n) = lastNormSq n)
    {F : Fin (n + 1) → ℕ → ComplexModel (n + 1) → ℝ} (hF : IsAdmissible (n + 1) U u F) :
    IsAdmissible (n + 1) U u fun j => Fin.lastCases
      (motive := fun _ => ℕ → ComplexModel (n + 1) → ℝ) (fun _ => lastNormSq n)
      (fun i => F i.castSucc) j := by
  refine ⟨fun j => ?_, fun j hj => absurd j.isLt (not_lt.2 hj)⟩
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.lastCases_last]
    rw [hlast]
    exact isDecApprox_const (isSmoothPsdOn_lastNormSq U)
  · simp only [Fin.lastCases_castSucc]
    exact hF.1 i.castSucc

/-- **Bedford--Taylor slicing with one slot `|τ|²`.** Let `ν` be the Bedford--Taylor limit of
`(u₁, …, uₙ, |τ|²)` on `Ω ⊆ ℂⁿ⁺¹ = ℂⁿ × ℂ` and `μ_τ` the Bedford--Taylor limits of the fibre tuples
`(u₁(·, τ), …, uₙ(·, τ))` on the fibres `Ω_τ`. For a continuous `χ` with compact support in `Ω` and a
weight `w` having decreasing smooth plurisubharmonic approximations on every relatively compact open
subset of `Ω`, the fibre integrals are integrable in `τ` and
`∫ χ w dν = (1/π) ∫_τ ∫ χ(·, τ) w(·, τ) dμ_τ`. -/
theorem integral_mul_isBTLimit_eq_fibre {Ω : Opens (ComplexModel (n + 1))}
    {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ} (hlast : u (Fin.last n) = lastNormSq n)
    {ν : Measure (ComplexModel (n + 1))} (hν : IsBTLimit Ω u ν) {μ : ℂ → Measure (ComplexModel n)}
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    {w : ComplexModel (n + 1) → ℝ} (hw : ∀ V, RelativelyCompactIn V Ω → ∃ G, IsDecApprox V w G)
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict w τ y ∂(μ τ)) ∧
      ∫ q, χ q * w q ∂ν =
        (∫ τ : ℂ, ∫ y, fibreRestrict χ τ y * fibreRestrict w τ y ∂(μ τ)) / Real.pi := by
  classical
  set K := tsupport χ with hKdef
  have hK : IsCompact K := hχc
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hχΩ
  set UO : Opens (ComplexModel (n + 1)) := ⟨U, hUo⟩ with hUOdef
  have hUrc : RelativelyCompactIn UO Ω := ⟨hUc, hUΩ⟩
  have hUOΩ : (UO : Set (ComplexModel (n + 1))) ⊆ Ω := subset_closure.trans hUΩ
  obtain ⟨F, hF, -⟩ := hν.2.2 UO hUrc
  obtain ⟨G, hG⟩ := hw UO hUrc
  set F' : Fin (n + 1) → ℕ → ComplexModel (n + 1) → ℝ := fun j => Fin.lastCases
    (motive := fun _ => ℕ → ComplexModel (n + 1) → ℝ) (fun _ => lastNormSq n)
    (fun i => F i.castSucc) j with hF'def
  have hF' : IsAdmissible (n + 1) UO u F' := isAdmissible_lastCases hlast hF
  have hF'c (i : Fin n) : F' i.castSucc = F i.castSucc := by simp [hF'def]
  have hF'l : F' (Fin.last n) = fun _ => lastNormSq n := by simp [hF'def]
  -- the fibre densities and integrals
  set D : ℂ → ℕ → ComplexModel n → ℝ :=
    fun τ k => mixedDensity fun i => fibreRestrict (F i.castSucc k) τ with hDdef
  set I : ℕ → ℂ → ℝ := fun k τ =>
    ∫ y, fibreRestrict χ τ y * fibreRestrict (G k) τ y * D τ k y with hIdef
  set J : ℂ → ℝ := fun τ => ∫ y, fibreRestrict χ τ y * fibreRestrict w τ y ∂(μ τ) with hJdef
  have hχ0 (q : ComplexModel (n + 1)) (hq : q ∉ UO) : χ q = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hq (hKU h)
  -- (a) the smooth identity, integrated by Fubini
  set g : ℕ → ComplexModel (n + 1) → ℝ :=
    fun k q => χ q * G k q * mixedDensity (fun j => F' j k) q with hgdef
  have hgint (k : ℕ) : Integrable (g k) := by
    have h := integrable_mul_of_continuousOn (U := UO)
      (D := fun q => G k q * mixedDensity (fun j => F' j k) q)
      (((hG.1 k).1.continuousOn).mul
        (continuousOn_mixedDensity fun j => ((hF'.1 j).1 k).1)) hχ hχc hKU
    simpa only [hgdef, mul_assoc] using h
  have hgfib (k : ℕ) (τ : ℂ) : ∫ y, g k (fibreMap n τ y) = I k τ / Real.pi := by
    rw [hIdef, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hgdef, fibreRestrict]
    by_cases hy : fibreMap n τ y ∈ UO
    · rw [mixedDensity_eq_fibre_div_pi_of_contDiffOn UO.isOpen (fun j => F' j k)
        (fun i => by rw [hF'c]; exact ((hF.1 i.castSucc).1 k).1) (by rw [hF'l]) hy]
      have hft : fibreTuple (fun j => F' j k) τ = fun i => fibreRestrict (F i.castSucc k) τ := by
        funext i
        simp [fibreTuple, hF'c]
      rw [hft]
      ring
    · simp [hχ0 _ hy]
  have hsmooth (k : ℕ) : ∫ q, g k q = (∫ τ, I k τ) / Real.pi := by
    rw [integral_eq_integral_fibre (hgint k), ← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun τ => hgfib k τ)
  have hIint (k : ℕ) : Integrable (I k) := by
    have h := (integrable_integral_fibre (hgint k)).const_mul Real.pi
    refine h.congr (Eventually.of_forall fun τ => ?_)
    simp only
    rw [hgfib k τ]
    field_simp
  -- (b) convergence on `ℂⁿ⁺¹`
  have hlimν : Tendsto (fun k => ∫ q, g k q) atTop (𝓝 (∫ q, χ q * w q ∂ν)) := by
    have hc : (ν.restrict UO) (UO : Set (ComplexModel (n + 1)))ᶜ = 0 := by
      rw [Measure.restrict_apply' UO.isOpen.measurableSet]; simp
    have hf : ∀ K', IsCompact K' → K' ⊆ UO → (ν.restrict UO) K' < ⊤ := fun K' hK' hK'U =>
      (Measure.restrict_apply_le _ _).trans_lt (hν.2.1 K' hK' (hK'U.trans hUOΩ))
    have h := wClaim_of_pClaim (pClaim_all (n := n + 1)) UO u (ν.restrict UO) hc hf
      (fun F hF => hν.tendstoMixed_restrict hUrc hF) F' hF' w G hG χ hχ hχc hKU
    have hr : ∫ q, χ q * w q ∂(ν.restrict UO) = ∫ q, χ q * w q ∂ν :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq => by rw [hχ0 q hq, zero_mul]
    rw [hr] at h
    exact h
  -- (c) convergence on every fibre
  have hlimτ (τ : ℂ) : Tendsto (fun k => I k τ) atTop (𝓝 (J τ)) := by
    set Uτ := fibreOpens UO τ
    have hrc : RelativelyCompactIn Uτ (fibreOpens Ω τ) := relativelyCompactIn_fibreOpens hUrc τ
    have hUτΩ : (Uτ : Set (ComplexModel n)) ⊆ fibreOpens Ω τ := subset_closure.trans hrc.2
    have hadm : IsAdmissible n Uτ (fibreTuple u τ) fun i k => fibreRestrict (F i.castSucc k) τ :=
      IsAdmissible.fibre hF τ
    have hGτ := IsDecApprox.fibre hG τ
    have hχτ : Continuous (fibreRestrict χ τ) := hχ.comp (continuous_fibreMap τ)
    have hsupp : tsupport (fibreRestrict χ τ) ⊆ fibreMap n τ ⁻¹' K :=
      tsupport_fibreRestrict_subset χ τ
    have hχτc : HasCompactSupport (fibreRestrict χ τ) :=
      (isCompact_preimage_fibreMap hK τ).of_isClosed_subset (isClosed_tsupport _) hsupp
    have hχτU : tsupport (fibreRestrict χ τ) ⊆ Uτ := fun y hy => hKU (hsupp hy)
    have hc : ((μ τ).restrict Uτ) (Uτ : Set (ComplexModel n))ᶜ = 0 := by
      rw [Measure.restrict_apply' Uτ.isOpen.measurableSet]; simp
    have hf : ∀ K', IsCompact K' → K' ⊆ Uτ → ((μ τ).restrict Uτ) K' < ⊤ := fun K' hK' hK'U =>
      (Measure.restrict_apply_le _ _).trans_lt ((hμ τ).2.1 K' hK' (hK'U.trans hUτΩ))
    have h := wClaim_of_pClaim (pClaim_all (n := n)) Uτ (fibreTuple u τ) ((μ τ).restrict Uτ) hc hf
      (fun F hF => (hμ τ).tendstoMixed_restrict hrc hF) _ hadm _ _ hGτ _ hχτ hχτc hχτU
    have hr : ∫ y, fibreRestrict χ τ y * fibreRestrict w τ y ∂((μ τ).restrict Uτ) = J τ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hy (hχτU h), zero_mul]
    rw [hr] at h
    exact h
  -- (d) domination
  have hFb : ∀ Q : Set (ComplexModel (n + 1)), IsCompact Q → Q ⊆ UO →
      ∃ C, ∀ (i : Fin n) (k : ℕ), ∀ z ∈ Q, |F i.castSucc k z| ≤ C := by
    intro Q hQ hQU
    choose C hC using fun i : Fin n => (hF.1 i.castSucc).exists_abs_le hQ hQU
    exact ⟨∑ i, |C i|, fun i k z hz => (hC i k z hz).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))⟩
  obtain ⟨B, hBint, hB⟩ := exists_integrable_fibre_bound (F := fun i k => F i.castSucc k)
    (fun (i : Fin n) k => (hF.1 i.castSucc).1 k) hFb hK hKU
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ
  obtain ⟨MG, hMG⟩ := hG.exists_abs_le hK hKU
  set A : ℝ := max Cχ 0 * max MG 0
  have hA : 0 ≤ A := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hIB (k : ℕ) (τ : ℂ) : |I k τ| ≤ A * B τ := by
    have hDc : ContinuousOn (D τ k) (fibreOpens UO τ) :=
      continuousOn_mixedDensity fun i => (IsSmoothPsdOn.fibre ((hF.1 i.castSucc).1 k) τ).1
    have hχτ : Continuous (fibreRestrict χ τ) := hχ.comp (continuous_fibreMap τ)
    have hsupp : tsupport (fibreRestrict χ τ) ⊆ fibreMap n τ ⁻¹' K :=
      tsupport_fibreRestrict_subset χ τ
    have hχτc : HasCompactSupport (fibreRestrict χ τ) :=
      (isCompact_preimage_fibreMap hK τ).of_isClosed_subset (isClosed_tsupport _) hsupp
    have hint : Integrable fun y => fibreRestrict χ τ y * fibreRestrict (G k) τ y * D τ k y := by
      have h := integrable_mul_of_continuousOn (U := fibreOpens UO τ)
        (D := fun y => fibreRestrict (G k) τ y * D τ k y)
        ((IsSmoothPsdOn.fibre ((hG.1 k)) τ).1.continuousOn.mul hDc) hχτ hχτc
        fun y hy => hKU (hsupp hy)
      simpa only [mul_assoc] using h
    refine hB k τ A hA _ hint fun y hy => ?_
    have hyK : fibreMap n τ y ∈ K := by
      by_contra hyK
      exact hy (by simp [fibreRestrict, image_eq_zero_of_notMem_tsupport hyK])
    refine ⟨hyK, ?_⟩
    have hD0 : 0 ≤ D τ k y := mixedDensity_nonneg fun i =>
      (IsSmoothPsdOn.fibre ((hF.1 i.castSucc).1 k) τ).2 y (hKU hyK)
    rw [abs_mul, abs_mul, abs_of_nonneg hD0]
    refine mul_le_mul_of_nonneg_right ?_ hD0
    exact mul_le_mul ((Real.norm_eq_abs _ ▸ hCχ _).trans (le_max_left _ _))
      ((hMG k _ hyK).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  -- (e) dominated convergence in `τ`
  have hJmeas : AEStronglyMeasurable J :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hIint k).aestronglyMeasurable)
      (Eventually.of_forall hlimτ)
  have hJint : Integrable J := by
    refine Integrable.mono' (hBint.const_mul A) hJmeas (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs]
    exact le_of_tendsto ((continuous_abs.tendsto _).comp (hlimτ τ))
      (Eventually.of_forall fun k => hIB k τ)
  have hdct := tendsto_integral_of_dominated_convergence (fun τ => A * B τ)
    (fun k => (hIint k).aestronglyMeasurable) (hBint.const_mul A)
    (fun k => Eventually.of_forall fun τ => by rw [Real.norm_eq_abs]; exact hIB k τ)
    (Eventually.of_forall hlimτ)
  refine ⟨hJint, tendsto_nhds_unique hlimν ?_⟩
  simp only [hsmooth]
  exact hdct.div_const _

/-- **Bedford--Taylor slicing with one slot `|τ|²`, unweighted.** `∫ χ dν = (1/π) ∫_τ ∫ χ(·, τ) dμ_τ`
for a continuous `χ` with compact support in `Ω`. -/
theorem integral_isBTLimit_eq_fibre {Ω : Opens (ComplexModel (n + 1))}
    {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ} (hlast : u (Fin.last n) = lastNormSq n)
    {ν : Measure (ComplexModel (n + 1))} (hν : IsBTLimit Ω u ν) {μ : ℂ → Measure (ComplexModel n)}
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y ∂(μ τ)) ∧
      ∫ q, χ q ∂ν = (∫ τ : ℂ, ∫ y, fibreRestrict χ τ y ∂(μ τ)) / Real.pi := by
  have h := integral_mul_isBTLimit_eq_fibre (w := fun _ => 1) hlast hν hμ
    (fun V _ => ⟨fun _ _ => 1, isDecApprox_const (isSmoothPsdOn_const V 1)⟩) hχ hχc hχΩ
  simpa only [fibreRestrict, mul_one] using h

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing
