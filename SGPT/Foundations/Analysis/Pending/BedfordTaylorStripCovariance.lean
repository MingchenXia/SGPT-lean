import SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing
import SGPT.Foundations.Analysis.Pending.BedfordTaylorDefectPairing

set_option autoImplicit false

/-!
# Strips `A × S ⊆ ℂⁿ × ℂ`: transitions `(z, τ) ↦ (t(z), τ)` and functions of `z` alone

On `ℂⁿ⁺¹ = ℂⁿ × ℂ` (`FiniteGeodesicMaximality.stripModelEquiv`), write `P(q) = z` for the first
factor (`stripFst`), `stripLift A S` for the open set `A × S` and `stripMap t` for
`(z, τ) ↦ (t(z), τ)`.

* `isBiholomorphicPair_stripLift` — a biholomorphism `t : A → B` lifts to `A × S → B × S`.
* `complexHessian_comp_stripFst` — the complex Hessian of `f ∘ P` is `Bᴴ H B`, with `H` the complex
  Hessian of `f` and `B` the matrix of `P`; hence `f ∘ P` is smooth plurisubharmonic, respectively
  smooth pluriharmonic, when `f` is (`isSmoothPsdOn_comp_stripFst`,
  `isSmoothPluriharmonicOn_comp_stripFst`).
* `isBTLimit_comp_stripFst_eq_zero` — **functions of `z` alone have no top-degree mass on
  `ℂⁿ⁺¹`**: if `u₁, …, uₙ₊₁` are locally bounded plurisubharmonic on `A`, the Bedford--Taylor limit of
  `(u₁ ∘ P, …, uₙ₊₁ ∘ P)` on `A × S` is `0` (every complex Hessian has a zero last row).

These are the chart transitions of `X × (strip)` (Xia, SGPT, proof of Proposition 4.3.3,
`xia-sgpt:page-0171`): the potentials pulled back from `X` change by pluriharmonic functions of
`z`, and `(ddᶜ (φ ∘ P))ⁿ⁺¹ = 0`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorStripCovariance

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FiniteGeodesicMaximality
  MixedDensityRankOneSlot BedfordTaylorFibreSlicing BedfordTaylor

noncomputable section

variable {n : ℕ}

/-! ### The first factor -/

/-- `q = (z, τ) ↦ z`, as a complex linear map. -/
def stripFst (n : ℕ) : ComplexModel (n + 1) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ).comp
    (stripModelEquiv n : ComplexModel (n + 1) →L[ℂ] ComplexModel n × ℂ)

theorem stripFst_apply (q : ComplexModel (n + 1)) : stripFst n q = (stripModelEquiv n q).1 := rfl

theorem stripFst_fibreMap (τ : ℂ) (y : ComplexModel n) : stripFst n (fibreMap n τ y) = y := by
  simp [stripFst_apply, fibreMap]

theorem stripFst_coordinateVector_castSucc (j : Fin n) :
    stripFst n (coordinateVector j.castSucc) = coordinateVector j := by
  rw [stripFst_apply, ← stripModelEquiv_symm_coordinateVector, ContinuousLinearEquiv.apply_symm_apply]

theorem stripFst_coordinateVector_last : stripFst n (coordinateVector (Fin.last n)) = 0 := by
  ext i
  rw [stripFst_apply]
  have h := stripModelEquiv_symm_apply_castSucc (stripModelEquiv n (coordinateVector (Fin.last n))).1
    (stripModelEquiv n (coordinateVector (Fin.last n))).2 i
  rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at h
  rw [← h]
  simp [coordinateVector, Fin.castSucc_ne_last]

/-- The matrix of `P`: `B j k = 1` if `k = j.castSucc`, else `0`. -/
def fstMatrix (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℂ :=
  fun j k => if k = j.castSucc then 1 else 0

/-- **The complex Hessian of a function of `z` alone.** -/
theorem complexHessian_comp_stripFst {A : Set (ComplexModel n)} (hA : IsOpen A)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f A) {q : ComplexModel (n + 1)}
    (hq : stripFst n q ∈ A) :
    complexHessian (fun q' => f (stripFst n q')) q =
      (fstMatrix n)ᴴ * complexHessian f (stripFst n q) * fstMatrix n := by
  classical
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hA hf hq
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hev : (fun q' => g (stripFst n q')) =ᶠ[𝓝 q] fun q' => f (stripFst n q') :=
    ((stripFst n).continuous.continuousAt.eventually hgf)
  rw [← MixedHessian.complexHessian_congr hev, ← MixedHessian.complexHessian_congr hgf]
  have hR (a b : ComplexModel (n + 1)) :
      realHessian (fun q' => g (stripFst n q')) q a b =
        realHessian g (stripFst n q) (stripFst n a) (stripFst n b) := by
    have h := realHessian_comp_affine (hg.of_le h2) ((stripFst n).restrictScalars ℝ) 0 q a b
    simpa using h
  have hI (v : ComplexModel (n + 1)) : stripFst n (Complex.I • v) = Complex.I • stripFst n v :=
    (stripFst n).map_smul _ _
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fstMatrix]
  have hl (x : Fin n) : (Fin.last n = x.castSucc) = False := eq_false (Fin.castSucc_ne_last x).symm
  refine Fin.lastCases ?_ (fun j' => ?_) j <;> refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp [complexHessian, hR, hI, stripFst_coordinateVector_last, hl]
  · simp [complexHessian, hR, hI, stripFst_coordinateVector_last, hl]
  · simp [complexHessian, hR, hI, stripFst_coordinateVector_last, hl]
  · simp only [complexHessian, hR, hI, stripFst_coordinateVector_castSucc]
    rw [Finset.sum_eq_single k']
    · rw [Finset.sum_eq_single j']
      · simp
      · intro b _ hb
        simp [Ne.symm hb, Fin.castSucc_inj]
      · simp
    · intro b _ hb
      simp [Ne.symm hb, Fin.castSucc_inj]
    · simp

theorem isSmoothPsdOn_comp_stripFst {A : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : IsSmoothPsdOn A f) {S : Opens (ComplexModel (n + 1))}
    (hS : ∀ q ∈ S, stripFst n q ∈ A) : IsSmoothPsdOn S fun q => f (stripFst n q) := by
  refine ⟨hf.1.comp ((stripFst n).contDiff.restrict_scalars ℝ).contDiffOn
    (fun q hq => hS q hq), fun q hq => ?_⟩
  rw [complexHessian_comp_stripFst A.isOpen hf.1 (hS q hq)]
  exact (hf.2 _ (hS q hq)).conjTranspose_mul_mul_same _

theorem isSmoothPluriharmonicOn_comp_stripFst {A : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : IsSmoothPluriharmonicOn A f) {S : Opens (ComplexModel (n + 1))}
    (hS : ∀ q ∈ S, stripFst n q ∈ A) : IsSmoothPluriharmonicOn S fun q => f (stripFst n q) := by
  refine ⟨hf.1.comp ((stripFst n).contDiff.restrict_scalars ℝ).contDiffOn
    (fun q hq => hS q hq), fun q hq => ?_⟩
  rw [complexHessian_comp_stripFst A.isOpen hf.1 (hS q hq), hf.2 _ (hS q hq)]
  simp

/-- The last row of the complex Hessian of a function of `z` alone vanishes. -/
theorem complexHessian_comp_stripFst_last {A : Set (ComplexModel n)} (hA : IsOpen A)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f A) {q : ComplexModel (n + 1)}
    (hq : stripFst n q ∈ A) (k : Fin (n + 1)) :
    complexHessian (fun q' => f (stripFst n q')) q (Fin.last n) k = 0 := by
  rw [complexHessian_comp_stripFst hA hf hq, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hl (x : Fin n) : (Fin.last n = x.castSucc) = False := eq_false (Fin.castSucc_ne_last x).symm
  rw [Matrix.mul_apply]
  simp [fstMatrix, Matrix.conjTranspose_apply, hl]

/-- **The mixed density of functions of `z` alone vanishes on `ℂⁿ⁺¹`.** -/
theorem mixedDensity_comp_stripFst_eq_zero {A : Set (ComplexModel n)} (hA : IsOpen A)
    {f : Fin (n + 1) → ComplexModel n → ℝ} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) A)
    {q : ComplexModel (n + 1)} (hq : stripFst n q ∈ A) :
    mixedDensity (fun i q' => f i (stripFst n q')) q = 0 := by
  unfold mixedDensity mixedCoefficient
  rw [Finset.sum_eq_zero fun σ _ => ?_, Complex.zero_re, zero_div]
  exact Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) fun k =>
    complexHessian_comp_stripFst_last hA (hf (σ (Fin.last n))) hq k

/-! ### Strips and strip maps -/

/-- The open set `A × S`, read in `ℂⁿ⁺¹`. -/
def stripLift (A : Opens (ComplexModel n)) (S : Set ℂ) (hS : IsOpen S) :
    Opens (ComplexModel (n + 1)) :=
  ⟨stripModelEquiv n ⁻¹' ((A : Set (ComplexModel n)) ×ˢ S),
    (A.isOpen.prod hS).preimage (stripModelEquiv n).continuous⟩

theorem mem_stripLift {A : Opens (ComplexModel n)} {S : Set ℂ} {hS : IsOpen S}
    {q : ComplexModel (n + 1)} :
    q ∈ stripLift A S hS ↔ stripFst n q ∈ A ∧ (stripModelEquiv n q).2 ∈ S := Iff.rfl

theorem stripLift_mono {A B : Opens (ComplexModel n)} (hAB : A ≤ B) (S : Set ℂ) (hS : IsOpen S) :
    stripLift A S hS ≤ stripLift B S hS := fun _ hq => ⟨hAB hq.1, hq.2⟩

/-- `(z, τ) ↦ (t(z), τ)`. -/
def stripMap (t : ComplexModel n → ComplexModel n) (q : ComplexModel (n + 1)) :
    ComplexModel (n + 1) :=
  (stripModelEquiv n).symm (t (stripModelEquiv n q).1, (stripModelEquiv n q).2)

@[simp] theorem stripModelEquiv_stripMap (t : ComplexModel n → ComplexModel n)
    (q : ComplexModel (n + 1)) :
    stripModelEquiv n (stripMap t q) = (t (stripModelEquiv n q).1, (stripModelEquiv n q).2) := by
  simp [stripMap]

theorem stripFst_stripMap (t : ComplexModel n → ComplexModel n) (q : ComplexModel (n + 1)) :
    stripFst n (stripMap t q) = t (stripFst n q) := by
  simp [stripFst_apply]

/-- **A biholomorphism lifts to strips.** -/
theorem isBiholomorphicPair_stripLift {A B : Opens (ComplexModel n)}
    {t s : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B t s) (S : Set ℂ)
    (hS : IsOpen S) :
    IsBiholomorphicPair (stripLift A S hS) (stripLift B S hS) (stripMap t) (stripMap s) := by
  have hlift (u : ComplexModel n → ComplexModel n) (U V : Opens (ComplexModel n))
      (hu : ContDiffOn ℂ ∞ u U) (huV : MapsTo u U V) :
      ContDiffOn ℂ ∞ (stripMap u) (stripLift U S hS) := by
    have h1 : ContDiffOn ℂ ∞ (fun p : ComplexModel n × ℂ => (u p.1, p.2))
        ((U : Set (ComplexModel n)) ×ˢ S) :=
      (hu.comp contDiffOn_fst fun p hp => hp.1).prodMk contDiffOn_snd
    exact (stripModelEquiv n).symm.contDiff.comp_contDiffOn
      (h1.comp (stripModelEquiv n).contDiff.contDiffOn fun q hq => hq)
  refine ⟨hlift t A B h.holo h.mapsTo, hlift s B A h.holo_inv h.mapsTo_inv, fun q hq => ?_,
    fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [stripModelEquiv_stripMap]; exact h.mapsTo hq.1
    · simpa using hq.2
  · refine ⟨?_, ?_⟩
    · rw [stripModelEquiv_stripMap]; exact h.mapsTo_inv hq.1
    · simpa using hq.2
  · apply (stripModelEquiv n).injective
    simp only [stripModelEquiv_stripMap]
    rw [h.left_inv _ hq.1]
  · apply (stripModelEquiv n).injective
    simp only [stripModelEquiv_stripMap]
    rw [h.right_inv _ hq.1]

/-! ### Functions of `z` alone have no top-degree mass -/

theorem exists_isDecApprox_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Ω w) (V : Opens (ComplexModel n))
    (hV : RelativelyCompactIn V Ω) : ∃ G, IsDecApprox V w G := by
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hw hV
  exact ⟨f, isDecApprox_of_isDecreasingApproximation hw (subset_closure.trans hV.2) hf⟩

/-- **`(ddᶜ(u ∘ P))ⁿ⁺¹ = 0`.** For locally bounded plurisubharmonic `u₁, …, uₙ₊₁` on `A`, the
Bedford--Taylor limit of `(u₁ ∘ P, …, uₙ₊₁ ∘ P)` on the strip `A × S` is zero. -/
theorem isBTLimit_comp_stripFst_eq_zero {A : Opens (ComplexModel n)} {S : Set ℂ} (hS : IsOpen S)
    {u : Fin (n + 1) → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn A (u i)) :
    IsBTLimit (stripLift A S hS) (fun i q => u i (stripFst n q)) 0 := by
  refine ⟨by simp, fun _ _ _ => by simp, fun V hV => ?_⟩
  -- the projection of `closure V` is a compact subset of `A`
  have hK : IsCompact (stripFst n '' closure (V : Set (ComplexModel (n + 1)))) :=
    hV.1.image (stripFst n).continuous
  have hKA : stripFst n '' closure (V : Set (ComplexModel (n + 1))) ⊆ A := by
    rintro _ ⟨q, hq, rfl⟩; exact (hV.2 hq).1
  obtain ⟨W, hWo, hKW, hWA, hWc⟩ := exists_open_between_and_isCompact_closure hK A.isOpen hKA
  set WO : Opens (ComplexModel n) := ⟨W, hWo⟩
  have hWrc : RelativelyCompactIn WO A := ⟨hWc, hWA⟩
  choose G hG using fun i => exists_isDecApprox_of_isLocallyBoundedPshOn (hu i) WO hWrc
  have hVW : ∀ q ∈ V, stripFst n q ∈ WO := fun q hq => hKW ⟨q, subset_closure hq, rfl⟩
  refine ⟨fun i k q => G i k (stripFst n q), ⟨fun i => ⟨fun k => ?_, fun q hq => (hG i).2.1 _
    (hVW q hq), fun q hq => (hG i).2.2.1 _ (hVW q hq), fun K hK' hKV => ?_⟩,
    fun i hi => absurd i.isLt (not_lt.2 hi)⟩, fun φ _ _ hφV => ?_⟩
  · exact isSmoothPsdOn_comp_stripFst ((hG i).1 k) hVW
  · obtain ⟨m, hm⟩ := (hG i).2.2.2 (stripFst n '' K) (hK'.image (stripFst n).continuous)
      (by rintro _ ⟨q, hq, rfl⟩; exact hVW q (hKV hq))
    exact ⟨m, by rintro _ ⟨q, hq, rfl⟩; exact hm ⟨stripFst n q, ⟨q, hq, rfl⟩, rfl⟩⟩
  · refine tendsto_const_nhds.congr fun k => ?_
    simp only [integral_zero_measure]
    symm
    refine integral_eq_zero_of_ae (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ V
    · simp only [Pi.zero_apply]
      rw [mixedDensity_comp_stripFst_eq_zero WO.isOpen (fun i => ((hG i).1 k).1) (hVW q hq),
        mul_zero]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hq (hφV h)]

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorStripCovariance
