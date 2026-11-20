import SGPT.Foundations.Analysis.Pending.BedfordTaylorBorelFibreSlicing

/-!
# Fibres of `ℂⁿ⁺ᵐ = ℂⁿ × ℂᵐ` for Bedford–Taylor slicing

Source: `chapter_npp.tex`, `lma:boundedfibrefubini` (the fibre products
`M_z = dd^c_x (u₁)_z ∧ ⋯ ∧ dd^c_x (uₙ)_z`, `(u_r)_z(x) = u_r(x, z)`).

We identify `ℂⁿ × ℂᵐ` with `ℂⁿ⁺ᵐ` by `ProductComplexManifold.prodModelEquiv` (the first `n`
coordinates are `x`, the last `m` are `z`), write `ι_z x = (x, z)` (`fibreMapM`) and
`Ω_z = ι_z⁻¹ Ω` (`fibreOpensM`).  This file generalizes the fibre calculus of
`SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing` (fibre dimension one, base `ℂ`) to a
base `ℂᵐ`:

* `complexHessian_fibreRestrictM` — the complex Hessian of `x ↦ f(x, z)` is the top-left `n × n`
  block of the complex Hessian of `f`;
* `IsSmoothPsdOn.fibreM`, `IsDecApprox.fibreM`, `IsAdmissible.fibreM` — decreasing smooth
  psh approximations restrict to decreasing smooth psh approximations of the fibre functions;
* `relativelyCompactIn_fibreOpensM`, `exists_isBTLimit_fibreM` — the fibre tuples have
  Bedford–Taylor limits;
* `IsLocallyBoundedPshOn.fibreM` — restrictions of locally bounded psh functions to fibres are
  locally bounded psh;
* `fibreMapM_succ` — compatibility of the fibres over `ℂᵐ⁺¹ = ℂᵐ × ℂ` with the fibres of
  `ℂⁿ⁺ᵐ⁺¹ = ℂⁿ⁺ᵐ × ℂ` used by TN (`BedfordTaylorFibreSlicing.fibreMap`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.NPP.FibreSlicing

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {n m : ℕ}

/-! ### The fibre maps -/

/-- The inclusion `x ↦ (x, z)` of the fibre over `z ∈ ℂᵐ`, read in `ℂⁿ⁺ᵐ`. -/
def fibreMapM (n m : ℕ) (z : ComplexModel m) (x : ComplexModel n) : ComplexModel (n + m) :=
  prodModelEquiv n m (x, z)

@[simp] theorem fibreMapM_castAdd (z : ComplexModel m) (x : ComplexModel n) (j : Fin n) :
    fibreMapM n m z x (Fin.castAdd m j) = x j := by
  simp [fibreMapM, prodModelEquiv]

@[simp] theorem fibreMapM_natAdd (z : ComplexModel m) (x : ComplexModel n) (j : Fin m) :
    fibreMapM n m z x (Fin.natAdd n j) = z j := by
  simp [fibreMapM, prodModelEquiv]

theorem continuous_fibreMapM (z : ComplexModel m) : Continuous (fibreMapM n m z) :=
  (prodModelEquiv n m).continuous.comp (continuous_id.prodMk continuous_const)

theorem continuous_fibreMapM_uncurry :
    Continuous fun p : ComplexModel n × ComplexModel m => fibreMapM n m p.2 p.1 :=
  (prodModelEquiv n m).continuous

theorem fibreMapM_uncurry_eq :
    (fun p : ComplexModel n × ComplexModel m => fibreMapM n m p.2 p.1) = prodModelEquiv n m :=
  rfl

theorem contDiff_fibreMapM (z : ComplexModel m) : ContDiff ℝ ∞ (fibreMapM n m z) :=
  ((prodModelEquiv n m).contDiff.restrict_scalars ℝ).comp (contDiff_id.prodMk contDiff_const)

/-- The complex linear inclusion `x ↦ (x, 0)`. -/
def inclFstC (n m : ℕ) : ComplexModel n →L[ℂ] ComplexModel (n + m) :=
  (prodModelEquiv n m : ComplexModel n × ComplexModel m →L[ℂ] ComplexModel (n + m)).comp
    (ContinuousLinearMap.inl ℂ (ComplexModel n) (ComplexModel m))

@[simp] theorem inclFstC_apply (x : ComplexModel n) :
    inclFstC n m x = prodModelEquiv n m (x, 0) := rfl

theorem fibreMapM_eq_add (z : ComplexModel m) (x : ComplexModel n) :
    fibreMapM n m z x = fibreMapM n m z 0 + inclFstC n m x := by
  simp only [fibreMapM, inclFstC_apply, ← map_add, Prod.mk_add_mk, zero_add, add_zero]

theorem inclFstC_coordinateVector (j : Fin n) :
    inclFstC n m (coordinateVector j) = coordinateVector (Fin.castAdd m j) := by
  rw [inclFstC_apply, ← ProductMixedMeasure.prodModelEquiv_symm_coordinateVector_castAdd,
    ContinuousLinearEquiv.apply_symm_apply]

theorem fibreMapM_injective (z : ComplexModel m) : Function.Injective (fibreMapM n m z) :=
  fun x x' h => by
    have := congrArg (prodModelEquiv n m).symm h
    simp only [fibreMapM, ContinuousLinearEquiv.symm_apply_apply, Prod.mk.injEq] at this
    exact this.1

/-- Preimages of compact sets under the fibre maps are compact. -/
theorem isCompact_preimage_fibreMapM {K : Set (ComplexModel (n + m))} (hK : IsCompact K)
    (z : ComplexModel m) : IsCompact (fibreMapM n m z ⁻¹' K) := by
  have h : fibreMapM n m z ⁻¹' K =
      Prod.fst '' ((prodModelEquiv n m).symm '' K ∩ univ ×ˢ {z}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, z), ⟨⟨_, hx, by simp [fibreMapM]⟩, mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨x', z'⟩, ⟨⟨q, hq, hqe⟩, -, hz'⟩, rfl⟩
      simp only [mem_singleton_iff] at hz'
      subst hz'
      show fibreMapM n m z' x' ∈ K
      have : fibreMapM n m z' x' = q := by
        rw [fibreMapM, ← hqe, ContinuousLinearEquiv.apply_symm_apply]
      rwa [this]
  rw [h]
  exact ((hK.image (prodModelEquiv n m).symm.continuous).inter_right
    (isClosed_univ.prod isClosed_singleton)).image continuous_fst

/-- The fibre `Ω_z = {x | (x, z) ∈ Ω}` of an open set, open in `ℂⁿ`. -/
def fibreOpensM (Ω : Opens (ComplexModel (n + m))) (z : ComplexModel m) : Opens (ComplexModel n) :=
  ⟨fibreMapM n m z ⁻¹' Ω, Ω.isOpen.preimage (continuous_fibreMapM z)⟩

@[simp] theorem mem_fibreOpensM {Ω : Opens (ComplexModel (n + m))} {z : ComplexModel m}
    {x : ComplexModel n} : x ∈ fibreOpensM Ω z ↔ fibreMapM n m z x ∈ Ω := Iff.rfl

theorem fibreOpensM_mono {U Ω : Opens (ComplexModel (n + m))} (h : U ≤ Ω) (z : ComplexModel m) :
    fibreOpensM U z ≤ fibreOpensM Ω z := fun _ hx => h hx

/-- Relative compactness passes to the fibres. -/
theorem relativelyCompactIn_fibreOpensM {U Ω : Opens (ComplexModel (n + m))}
    (hU : RelativelyCompactIn U Ω) (z : ComplexModel m) :
    RelativelyCompactIn (fibreOpensM U z) (fibreOpensM Ω z) := by
  have hcl : closure (fibreOpensM U z : Set (ComplexModel n)) ⊆
      fibreMapM n m z ⁻¹' closure (U : Set (ComplexModel (n + m))) :=
    closure_minimal (fun x hx => subset_closure hx)
      (isClosed_closure.preimage (continuous_fibreMapM z))
  exact ⟨(isCompact_preimage_fibreMapM hU.1 z).of_isClosed_subset isClosed_closure hcl,
    fun x hx => hU.2 (hcl hx)⟩

/-- The restriction of a function on `ℂⁿ⁺ᵐ` to the fibre over `z`. -/
def fibreRestrictM (f : ComplexModel (n + m) → ℝ) (z : ComplexModel m) : ComplexModel n → ℝ :=
  fun x => f (fibreMapM n m z x)

/-- The fibre tuple: the first `n` slots restricted to the fibre over `z`. -/
def fibreTupleM (u : Fin (n + m) → ComplexModel (n + m) → ℝ) (z : ComplexModel m) :
    Fin n → ComplexModel n → ℝ :=
  fun i => fibreRestrictM (u (Fin.castAdd m i)) z

theorem tsupport_fibreRestrictM_subset (f : ComplexModel (n + m) → ℝ) (z : ComplexModel m) :
    tsupport (fibreRestrictM f z) ⊆ fibreMapM n m z ⁻¹' tsupport f :=
  closure_minimal (fun _ hx => subset_tsupport f hx)
    ((isClosed_tsupport f).preimage (continuous_fibreMapM z))

theorem hasCompactSupport_fibreRestrictM {f : ComplexModel (n + m) → ℝ} (hf : HasCompactSupport f)
    (z : ComplexModel m) : HasCompactSupport (fibreRestrictM f z) :=
  (isCompact_preimage_fibreMapM hf z).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_fibreRestrictM_subset f z)

/-! ### The complex Hessian on a fibre -/

/-- **The complex Hessian of the restriction to a fibre** is the top-left block of the complex
Hessian. -/
theorem complexHessian_fibreM {F : ComplexModel (n + m) → ℝ} (hF : ContDiff ℝ 2 F)
    (z : ComplexModel m) (x : ComplexModel n) :
    complexHessian (fibreRestrictM F z) x =
      (complexHessian F (fibreMapM n m z x)).submatrix (Fin.castAdd m) (Fin.castAdd m) := by
  set L : ComplexModel n →L[ℝ] ComplexModel (n + m) := (inclFstC n m).restrictScalars ℝ
  have hfun : fibreRestrictM F z = fun x' => F (fibreMapM n m z 0 + L x') := by
    funext x'
    simp only [fibreRestrictM, L, ContinuousLinearMap.coe_restrictScalars']
    rw [fibreMapM_eq_add]
  have hR : ∀ a b : ComplexModel n,
      realHessian (fibreRestrictM F z) x a b = realHessian F (fibreMapM n m z x) (L a) (L b) := by
    intro a b
    rw [hfun, realHessian_comp_affine hF]
    congr 1
    simp only [L, ContinuousLinearMap.coe_restrictScalars']
    rw [← fibreMapM_eq_add]
  have hv : ∀ j : Fin n, L (coordinateVector j) = coordinateVector (Fin.castAdd m j) :=
    fun j => inclFstC_coordinateVector j
  have hIv : ∀ j : Fin n, L (Complex.I • coordinateVector j) =
      Complex.I • coordinateVector (Fin.castAdd m j) := fun j => by
    simp only [L, ContinuousLinearMap.coe_restrictScalars', map_smul]
    rw [inclFstC_coordinateVector]
  ext j k
  simp only [complexHessian, Matrix.submatrix_apply, hR, hv, hIv]

theorem fibreRestrictM_eventuallyEq {f g : ComplexModel (n + m) → ℝ} {z : ComplexModel m}
    {x : ComplexModel n} (h : f =ᶠ[𝓝 (fibreMapM n m z x)] g) :
    fibreRestrictM f z =ᶠ[𝓝 x] fibreRestrictM g z :=
  (continuous_fibreMapM z).continuousAt.eventually h

/-- **The complex Hessian on a fibre**, for a function smooth on an open set. -/
theorem complexHessian_fibreRestrictM {U : Set (ComplexModel (n + m))} (hU : IsOpen U)
    {f : ComplexModel (n + m) → ℝ} (hf : ContDiffOn ℝ ∞ f U) {z : ComplexModel m}
    {x : ComplexModel n} (hx : fibreMapM n m z x ∈ U) :
    complexHessian (fibreRestrictM f z) x =
      (complexHessian f (fibreMapM n m z x)).submatrix (Fin.castAdd m) (Fin.castAdd m) := by
  obtain ⟨g, hg, hgf⟩ := BedfordTaylorFibreSlicing.exists_contDiff_eventuallyEq hU hf hx
  rw [MixedHessian.complexHessian_congr (fibreRestrictM_eventuallyEq hgf.symm),
    MixedHessian.complexHessian_congr hgf.symm]
  exact complexHessian_fibreM (hg.of_le (WithTop.coe_le_coe.mpr le_top)) z x

/-! ### Restricting approximations to fibres -/

theorem IsSmoothPsdOn.fibreM {U : Opens (ComplexModel (n + m))} {f : ComplexModel (n + m) → ℝ}
    (hf : IsSmoothPsdOn U f) (z : ComplexModel m) :
    IsSmoothPsdOn (fibreOpensM U z) (fibreRestrictM f z) := by
  refine ⟨hf.1.comp (contDiff_fibreMapM z).contDiffOn fun x hx => hx, fun x hx => ?_⟩
  rw [complexHessian_fibreRestrictM U.isOpen hf.1 hx]
  exact (hf.2 _ hx).submatrix _

theorem IsDecApprox.fibreM {U : Opens (ComplexModel (n + m))} {w : ComplexModel (n + m) → ℝ}
    {G : ℕ → ComplexModel (n + m) → ℝ} (hG : IsDecApprox U w G) (z : ComplexModel m) :
    IsDecApprox (fibreOpensM U z) (fibreRestrictM w z) fun k => fibreRestrictM (G k) z := by
  refine ⟨fun k => IsSmoothPsdOn.fibreM (hG.1 k) z, fun x hx => hG.2.1 _ hx,
    fun x hx => hG.2.2.1 _ hx, fun K hK hKU => ?_⟩
  obtain ⟨b, hb⟩ := hG.2.2.2 (fibreMapM n m z '' K) (hK.image (continuous_fibreMapM z))
    (image_subset_iff.2 hKU)
  exact ⟨b, by rintro _ ⟨x, hx, rfl⟩; exact hb ⟨fibreMapM n m z x, ⟨x, hx, rfl⟩, rfl⟩⟩

theorem IsAdmissible.fibreM {U : Opens (ComplexModel (n + m))}
    {u : Fin (n + m) → ComplexModel (n + m) → ℝ} {F : Fin (n + m) → ℕ → ComplexModel (n + m) → ℝ}
    (hF : IsAdmissible (n + m) U u F) (z : ComplexModel m) :
    IsAdmissible n (fibreOpensM U z) (fibreTupleM u z)
      (fun i k => fibreRestrictM (F (Fin.castAdd m i) k) z) :=
  ⟨fun i => IsDecApprox.fibreM (hF.1 (Fin.castAdd m i)) z,
    fun i hi => absurd i.isLt (not_lt.2 hi)⟩

/-- Admissible approximations of the fibre tuple exist on every relatively compact open subset of
the fibre. -/
theorem exists_isAdmissible_fibreM {Ω : Opens (ComplexModel (n + m))}
    {u : Fin (n + m) → ComplexModel (n + m) → ℝ}
    (hadm : ∀ V, RelativelyCompactIn V Ω → ∃ F, IsAdmissible (n + m) V u F) (z : ComplexModel m)
    (V' : Opens (ComplexModel n)) (hV' : RelativelyCompactIn V' (fibreOpensM Ω z)) :
    ∃ F', IsAdmissible n V' (fibreTupleM u z) F' := by
  have hK : IsCompact (fibreMapM n m z '' closure (V' : Set (ComplexModel n))) :=
    hV'.1.image (continuous_fibreMapM z)
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
    (image_subset_iff.2 hV'.2)
  obtain ⟨F, hF⟩ := hadm ⟨W, hWo⟩ ⟨hWc, hWΩ⟩
  refine ⟨_, (IsAdmissible.fibreM hF z).mono fun x hx => ?_⟩
  exact hKW ⟨x, subset_closure hx, rfl⟩

/-- **The fibre tuples have Bedford–Taylor limits.** -/
theorem exists_isBTLimit_fibreM {Ω : Opens (ComplexModel (n + m))}
    {u : Fin (n + m) → ComplexModel (n + m) → ℝ} {ν : Measure (ComplexModel (n + m))}
    (hν : IsBTLimit Ω u ν) (z : ComplexModel m) :
    ∃ μ, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) μ :=
  exists_isBTLimit (exists_isAdmissible_fibreM (fun V hV => (hν.2.2 V hV).imp fun _ h => h.1) z)

/-! ### Locally bounded psh functions on fibres -/

/-- **Restrictions of locally bounded psh functions to fibres are locally bounded psh.** -/
theorem IsLocallyBoundedPshOn.fibreM {Ω : Opens (ComplexModel (n + m))}
    {f : ComplexModel (n + m) → ℝ} (hf : IsLocallyBoundedPshOn Ω f) (z : ComplexModel m) :
    IsLocallyBoundedPshOn (fibreOpensM Ω z) (fibreRestrictM f z) := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h := hf.1.comp_affine (inclFstC n m) (fibreMapM n m z 0)
    have e : ∀ y, fibreMapM n m z 0 + inclFstC n m y = fibreMapM n m z y := fun y =>
      (fibreMapM_eq_add z y).symm
    simp only [e] at h
    exact h
  · obtain ⟨V, hxV, hVΩ, C, hC⟩ := hf.2 _ hx
    exact ⟨fibreOpensM V z, hxV, fibreOpensM_mono hVΩ z, C, fun y hy => hC _ hy⟩

/-! ### Compatibility with the fibres of `ℂⁿ⁺ᵐ⁺¹ = ℂⁿ⁺ᵐ × ℂ` -/

open FiniteGeodesicMaximality BedfordTaylorFibreSlicing MixedDensityRankOneSlot in
/-- The fibre of `ℂⁿ⁺⁽ᵐ⁺¹⁾` over `(z, τ) ∈ ℂᵐ × ℂ = ℂᵐ⁺¹` is the fibre over `z` of the fibre of
`ℂⁿ⁺ᵐ⁺¹ = ℂⁿ⁺ᵐ × ℂ` over `τ`. -/
theorem fibreMapM_succ (z : ComplexModel m) (τ : ℂ) (x : ComplexModel n) :
    fibreMapM n (m + 1) ((stripModelEquiv m).symm (z, τ)) x =
      fibreMap (n + m) τ (fibreMapM n m z x) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · rw [fibreMapM_castAdd]
    have e : (Fin.castAdd (m + 1) j : Fin (n + (m + 1))) = (Fin.castAdd m j).castSucc :=
      Fin.ext rfl
    rw [e, fibreMap, stripModelEquiv_symm_apply_castSucc, fibreMapM_castAdd]
  · rw [fibreMapM_natAdd]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · have e : (Fin.natAdd n (Fin.last m) : Fin (n + (m + 1))) = Fin.last (n + m) := Fin.ext rfl
      rw [e, fibreMap, stripModelEquiv_symm_apply_last, stripModelEquiv_symm_apply_last]
    · have e : (Fin.natAdd n k'.castSucc : Fin (n + (m + 1))) = (Fin.natAdd n k').castSucc :=
        Fin.ext rfl
      rw [e, fibreMap, stripModelEquiv_symm_apply_castSucc, stripModelEquiv_symm_apply_castSucc,
        fibreMapM_natAdd]

end SGPT.NPP.FibreSlicing
