import SGPT.Trace.TwistedL2DProj

/-!
# Complete cut-offs and finite partitions of unity into frame domains

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:cutoff`).  For a twisted datum `T` on `ℂⁿ`:

* `exists_cutoffs`: the complete cut-offs `χ_k` of `HasCompactSupport`, read on `ℂⁿ`;
* `norm_mv_Bi_dbarV_sq_le`: `|∂̄χ|²_σ ≤ c²/2` when `|dχ(v)|² ≤ c² σ(v)` (dual norm);
* `exists_localization`: for a compactly supported smooth real `χ` with support in `U`, finitely
  many frames `e_i` and smooth real `ζ_i`, compactly supported in the frame domains, with
  `∑_i ζ_i = χ`, each with an open relatively compact neighbourhood `D_i` of `tsupport ζ_i`
  whose closure lies in the frame domain;
* `norm_wedge_sq_le`: `½ ‖x yᵀ - y xᵀ‖² ≤ ‖x‖² ‖y‖²`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold InnerProductSpace ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### The wedge bound -/

/-- The matrix `x yᵀ - y xᵀ` (the coefficient matrix of `x ∧ y` for covectors). -/
def wedgeM (x y : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => x j * y k - y j * x k

theorem norm_flat2_outer (x y : ComplexModel n) :
    ‖flat2 (Matrix.of fun j k => x j * y k)‖ = ‖x‖ * ‖y‖ := by
  have h : ‖flat2 (Matrix.of fun j k => x j * y k)‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    rw [norm_flat2_sq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul_sum]
    simp only [of_apply, norm_mul, mul_pow]
  have h1 : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  nlinarith [norm_nonneg (flat2 (Matrix.of fun j k => x j * y k)),
    sq_nonneg (‖flat2 (Matrix.of fun j k => x j * y k)‖ - ‖x‖ * ‖y‖),
    sq_nonneg (‖flat2 (Matrix.of fun j k => x j * y k)‖ + ‖x‖ * ‖y‖)]

theorem norm_flat2_wedge_le (x y : ComplexModel n) :
    ‖flat2 (wedgeM x y)‖ ≤ 2 * (‖x‖ * ‖y‖) := by
  have h : flat2 (wedgeM x y) = flat2 (Matrix.of fun j k => x j * y k) -
      flat2 (Matrix.of fun j k => y j * x k) := by
    ext p; simp [flat2, wedgeM]
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_flat2_outer, norm_flat2_outer]
  linarith [mul_comm ‖x‖ ‖y‖]

theorem mul_wedgeM_mul_transpose (B : Matrix (Fin n) (Fin n) ℂ) (x y : ComplexModel n) :
    B * wedgeM x y * Bᵀ = wedgeM (mv B x) (mv B y) := by
  ext j k
  simp only [wedgeM, mul_apply, of_apply, transpose_apply, mv_apply, Finset.sum_mul,
    Finset.mul_sum, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-! ### Real cut-off functions -/

theorem fderiv_ofReal_apply {χ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hχ : DifferentiableAt ℝ χ z) (w : ComplexModel n) :
    fderiv ℝ (fun y => (χ y : ℂ)) z w = (fderiv ℝ χ z w : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z hχ.hasFDerivAt).fderiv
  exact congrArg (fun L : ComplexModel n →L[ℝ] ℂ => L w) h

theorem norm_dbarDir_ofReal_sq {χ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hχ : DifferentiableAt ℝ χ z) (v : ComplexModel n) :
    ‖dbarDir v (fun y => (χ y : ℂ)) z‖ ^ 2 =
      (fderiv ℝ χ z v ^ 2 + fderiv ℝ χ z (Complex.I • v) ^ 2) / 4 := by
  simp only [dbarDir, fderiv_ofReal_apply hχ]
  rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq]
  have h2 : ‖(2 : ℂ)‖ ^ 2 = 4 := by norm_num
  rw [h2, mul_comm Complex.I, Complex.normSq_add_mul_I]

theorem dDir_ofReal_eq_conj {χ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hχ : DifferentiableAt ℝ χ z) (v : ComplexModel n) :
    dDir v (fun y => (χ y : ℂ)) z = conj (dbarDir v (fun y => (χ y : ℂ)) z) := by
  have h := dbarDir_conj (v := v) (differentiableAt_ofReal_comp hχ)
  simp only [Complex.conj_ofReal] at h
  rw [h, Complex.conj_conj]

theorem inner_dbarV_eq_dbarDir (f : ComplexModel n → ℂ) (z v : ComplexModel n) :
    ⟪v, TwistedDatum.dbarV f z⟫_ℂ = dbarDir v f z := by
  rw [TwistedDatum.inner_dbarV]
  have hu : (∑ j : Fin n, v j • coordVec j : ComplexModel n) = v := by
    ext i
    simp [coordVec, euclid_sum_apply]
  have := dbarDir_sum_dir Finset.univ (fun j => v j) (fun j => (coordVec j : ComplexModel n)) f z
  rw [hu] at this
  rw [this, dbarPairing]

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)}

/-- **The complete cut-offs on `ℂⁿ`.** -/
theorem exists_cutoffs (T : TwistedDatum n (ComplexModel n)) :
    ∃ (χ : ℕ → ComplexModel n → ℝ) (C : ℝ), (∀ k, ContDiff ℝ ∞ (χ k)) ∧
      (∀ k, HasCompactSupport (χ k)) ∧ (∀ k, tsupport (χ k) ⊆ T.U) ∧
      (∀ k z, 0 ≤ χ k z ∧ χ k z ≤ 1) ∧ (∀ z ∈ T.U, Tendsto (fun k => χ k z) atTop (𝓝 1)) ∧
      ∀ k, ∀ z ∈ T.U, ∀ v, fderiv ℝ (χ k) z v ^ 2 ≤
        (C / ((k : ℝ) + 1)) ^ 2 * sigmaQ T.omega T.r z v := by
  obtain ⟨χ, C, h1, h2, h3, h4, h5, h6⟩ := T.complete
  refine ⟨χ, C, fun k => ?_, h2, h3, h4, h5, fun k z hz v => ?_⟩
  · have := h1 k chart0
    simp only [chart0_target, chart0_symm_apply] at this
    exact contDiffOn_univ.mp this
  · have := h6 k chart0 z (by simp) (by simpa using hz) v
    simpa [sigmaQ] using this

/-- **The dual bound for `∂̄χ`**: `‖Bi ∂̄χ‖² ≤ c²/2` if `|dχ(v)|² ≤ c² σ(v)`. -/
theorem norm_mv_Bi_dbarV_sq_le {χ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hχ : DifferentiableAt ℝ χ z) (hz : z ∈ T.U) {c : ℝ}
    (hc : ∀ v, fderiv ℝ χ z v ^ 2 ≤ c ^ 2 * sigmaQ T.omega T.r z v) :
    ‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ ^ 2 ≤ c ^ 2 / 2 := by
  refine norm_mv_Bi_sq_le T.isOpen_U T.kahler hz (by positivity) fun v => ?_
  rw [inner_dbarV_eq_dbarDir, norm_dbarDir_ofReal_sq hχ]
  have h1 := hc v
  have h2 := hc (Complex.I • v)
  have hI : sigmaQ T.omega T.r z (Complex.I • v) = sigmaQ T.omega T.r z v := by
    rw [sigmaQ_eq_norm_sq T.isOpen_U T.kahler hz, sigmaQ_eq_norm_sq T.isOpen_U T.kahler hz,
      mv_smul, norm_smul, Complex.norm_I, one_mul]
  rw [hI] at h2
  linarith

/-- **Localization of a cut-off into frame domains.** -/
theorem exists_localization {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ T.U) :
    ∃ (N : ℕ) (e : Fin N → AtlasFrame T.L) (ζ : Fin N → ComplexModel n → ℝ)
      (D : Fin N → Set (ComplexModel n)),
      (∀ i, ContDiff ℝ ∞ (ζ i)) ∧ (∀ i, HasCompactSupport (ζ i)) ∧ (∀ i, IsOpen (D i)) ∧
      (∀ i, tsupport (ζ i) ⊆ D i) ∧
      (∀ i, ∃ K, IsCompact K ∧ D i ⊆ K ∧ K ⊆ T.dom (e i)) ∧ ∀ z, ∑ i, ζ i z = χ z := by
  set K := tsupport χ
  have hK : IsCompact K := hχc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => T.dom (atlasFrameAt T.L (z : ComplexModel n)))
    (fun z => T.isOpen_dom _) fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, frameAt_mem_dom (hχU hz)⟩
  set N := t.card
  let f : Fin N ≃ t := t.equivFin.symm
  set e : Fin N → AtlasFrame T.L := fun i => atlasFrameAt T.L ((f i : K) : ComplexModel n)
  have hcov : K ⊆ ⋃ i, T.dom (e i) := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion.mpr ⟨f.symm ⟨y, hy⟩, by simpa [e] using hzy⟩
  obtain ⟨θ, hθ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ComplexModel n)
    (isClosed_tsupport χ) (fun i => T.dom (e i)) (fun i => T.isOpen_dom _) hcov
  set ζ : Fin N → ComplexModel n → ℝ := fun i z => θ i z * χ z
  have hζc : ∀ i, HasCompactSupport (ζ i) := fun i => hχc.mul_left
  have hζd : ∀ i, tsupport (ζ i) ⊆ T.dom (e i) := fun i =>
    (tsupport_mul_subset_left (f := fun z => θ i z)).trans (hθ i)
  have hδ : ∀ i, ∃ δ, 0 < δ ∧ cthickening δ (tsupport (ζ i)) ⊆ T.dom (e i) := fun i =>
    (hζc i).exists_cthickening_subset_open (T.isOpen_dom _) (hζd i)
  choose δ hδpos hδsub using hδ
  refine ⟨N, e, ζ, fun i => thickening (δ i) (tsupport (ζ i)), fun i => ?_, hζc,
    fun i => isOpen_thickening, fun i => self_subset_thickening (hδpos i) _,
    fun i => ⟨cthickening (δ i) (tsupport (ζ i)), (hζc i).cthickening,
      thickening_subset_cthickening _ _, hδsub i⟩, fun z => ?_⟩
  · exact (contMDiff_iff_contDiff.mp (θ i).contMDiff).mul hχ
  · simp only [ζ, ← Finset.sum_mul]
    by_cases hz : z ∈ K
    · rw [← finsum_eq_sum_of_fintype, θ.sum_eq_one hz, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end TwistedDatum

end SGPT.Trace.TwistedL2
