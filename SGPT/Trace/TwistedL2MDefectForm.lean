import SGPT.Trace.TwistedL2MDefect

/-!
# The `∂̄`-defect of a family is bounded by its `S`-energy

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:defect`).  The form
`FS e u w z = ⟨∂̄σ^♭u, ∂̄σ^♭w⟩_σ e^{-p_e}` is a gauge form; its diagonal integral over a family is the
`S`-energy `‖∂̄(σ^♭ W_τ)‖²_{H₃}` (with the weight `e^{-φ}`).  `FrameFamily.defect_le`:
`Q(τ) ≤ sup_U a · ‖∂̄(σ^♭ W_τ)‖²`.  Consequently graph density follows from the textbook form of the
density lemma, in which the approximating families have small `S`-energy
(`TwistedDatum.SigmaGraphDensity`, `graphDensity_of_sigmaGraphDensity`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### Algebra of the `σ`-pairing -/

theorem zeroTwoPair_smul (N β γ : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    zeroTwoPair N (c • β) (c • γ) = (c * conj c) * zeroTwoPair N β γ := by
  simp only [zeroTwoPair, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
    smul_eq_mul, RCLike.star_def]
  ring

theorem zeroTwoPair_sum (N β : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι)
    (γ : ι → Matrix (Fin n) (Fin n) ℂ) :
    zeroTwoPair N β (∑ i ∈ s, γ i) = ∑ i ∈ s, zeroTwoPair N β (γ i) := by
  simp only [zeroTwoPair, Matrix.sum_mul, trace_sum, Finset.mul_sum]

theorem zeroTwoPair_zero (N β : Matrix (Fin n) (Fin n) ℂ) : zeroTwoPair N β 0 = 0 := by
  simp [zeroTwoPair]

theorem continuous_zeroTwoPair :
    Continuous fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ ×
      Matrix (Fin n) (Fin n) ℂ => zeroTwoPair x.1 x.2.1 x.2.2 := by
  unfold zeroTwoPair
  have h1 : Continuous fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ ×
      Matrix (Fin n) (Fin n) ℂ => x.1 := continuous_fst
  have h2 : Continuous fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ ×
      Matrix (Fin n) (Fin n) ℂ => x.2.1 := continuous_fst.comp continuous_snd
  have h3 : Continuous fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ ×
      Matrix (Fin n) (Fin n) ℂ => x.2.2 := continuous_snd.comp continuous_snd
  exact continuous_const.mul ((((h2.matrix_conjTranspose.matrix_mul h1).matrix_mul h3).matrix_mul
    h1.matrix_transpose).matrix_trace)

theorem continuousOn_zeroTwoPair {D : Set (ComplexModel n)}
    {N β γ : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} (h1 : ContinuousOn N D)
    (h2 : ContinuousOn β D) (h3 : ContinuousOn γ D) :
    ContinuousOn (fun z => zeroTwoPair (N z) (β z) (γ z)) D := by
  have := continuous_zeroTwoPair.comp_continuousOn (h1.prodMk (h2.prodMk h3))
  exact this

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}

theorem dom_subset_U (e : AtlasFrame T.L) : T.dom e ⊆ T.U := fun _ hz => ((T.mem_dom).mp hz).2

variable (T ρ) in
/-- The `S`-form `⟨∂̄σ^♭u, ∂̄σ^♭w⟩_σ e^{-p}`. -/
def FS (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  zeroTwoPair (sigmaInv T.omega T.r z) (sigmaDbar T.omega T.r u z) (sigmaDbar T.omega T.r w z) *
    cweight (T.pW ρ e) z

theorem lowerSigma_congr {u u' : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hu : u =ᶠ[𝓝 z] u') (k : Fin n) :
    (fun y => lowerSigma T.omega T.r u y k) =ᶠ[𝓝 z] fun y => lowerSigma T.omega T.r u' y k :=
  hu.mono fun y hy => by simp [lowerSigma, hy]

theorem sigmaDbar_congr {u u' : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hu : u =ᶠ[𝓝 z] u') : sigmaDbar T.omega T.r u z = sigmaDbar T.omega T.r u' z := by
  ext j k
  simp only [sigmaDbar, of_apply, dbarDir_congr_of_eventuallyEq (lowerSigma_congr hu _)]

theorem sigmaDbar_zero {u : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hu : u =ᶠ[𝓝 z] 0) : sigmaDbar T.omega T.r u z = 0 := by
  rw [sigmaDbar_congr hu]
  ext j k
  have h0 : ∀ k : Fin n, (fun y => lowerSigma T.omega T.r (0 : ComplexModel n → ComplexModel n) y k) =
      fun _ => 0 := fun k => by funext y; simp [lowerSigma]
  simp only [sigmaDbar, of_apply, h0, dbarDir_const, sub_self, Matrix.zero_apply]

theorem differentiableAt_lowerSigma {u : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hz : z ∈ T.U) (hu : ContDiffAt ℝ ∞ u z) (k : Fin n) :
    DifferentiableAt ℝ (fun y => lowerSigma T.omega T.r u y k) z := by
  unfold lowerSigma
  refine DifferentiableAt.fun_sum fun l _ => ?_
  have hσ := ((contDiffOn_sigmaMat T.isOpen_U T.kahler l k).contDiffAt
    (T.isOpen_U.mem_nhds hz)).differentiableAt (by simp)
  exact hσ.mul (differentiableAt_coord (hu.differentiableAt (by simp)) l)

theorem sigmaDbar_sum {ι : Type} (s : Finset ι) {w : ι → ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∈ T.U) (hw : ∀ i ∈ s, ContDiffAt ℝ ∞ (w i) z) :
    sigmaDbar T.omega T.r (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, sigmaDbar T.omega T.r (w i) z := by
  have hl : ∀ k, (fun y => lowerSigma T.omega T.r (fun y => ∑ i ∈ s, w i y) y k) =
      fun y => ∑ i ∈ s, lowerSigma T.omega T.r (w i) y k := by
    intro k; funext y
    simp only [lowerSigma, euclid_sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  ext j k
  simp only [sigmaDbar, of_apply, hl, Matrix.sum_apply]
  rw [dbarDir_finset_sum_fun s fun i hi => differentiableAt_lowerSigma hz (hw i hi) k,
    dbarDir_finset_sum_fun s fun i hi => differentiableAt_lowerSigma hz (hw i hi) j,
    ← Finset.sum_sub_distrib]

theorem sigmaDbar_smul {t : ComplexModel n → ℂ} {u : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∈ T.U) (ht : DifferentiableAt ℂ t z) (hu : ContDiffAt ℝ ∞ u z) :
    sigmaDbar T.omega T.r (fun y => t y • u y) z = t z • sigmaDbar T.omega T.r u z := by
  have hl : ∀ k, (fun y => lowerSigma T.omega T.r (fun y => t y • u y) y k) =
      fun y => t y * lowerSigma T.omega T.r u y k := by
    intro k; funext y
    simp only [lowerSigma, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  ext j k
  simp only [sigmaDbar, of_apply, hl, Matrix.smul_apply, smul_eq_mul]
  rw [dbarDir_holo_mul ht (differentiableAt_lowerSigma hz hu k),
    dbarDir_holo_mul ht (differentiableAt_lowerSigma hz hu j)]
  ring

theorem continuousOn_sigmaInv : ContinuousOn (sigmaInv T.omega T.r) T.U := by
  intro z hz
  have hσ : ContinuousOn (fun y => (sigmaMat T.omega T.r y)ᵀ) T.U := by
    refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
    exact (contDiffOn_sigmaMat T.isOpen_U T.kahler l k).continuousOn
  have hdet : (sigmaMat T.omega T.r z)ᵀ.det ≠ 0 :=
    (posDef_sigmaMat_transpose T.isOpen_U T.kahler hz).det_pos.ne'
  have hinv : ContinuousAt Ring.inverse (sigmaMat T.omega T.r z)ᵀ.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact (ContinuousAt.comp (f := fun y => (sigmaMat T.omega T.r y)ᵀ)
    (continuousAt_matrix_inv _ hinv) (hσ.continuousAt (T.isOpen_U.mem_nhds hz))).continuousWithinAt

theorem continuousOn_sigmaDbar {D : Set (ComplexModel n)} (hD : IsOpen D) (hDU : D ⊆ T.U)
    {u : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u D) :
    ContinuousOn (sigmaDbar T.omega T.r u) D := by
  refine continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => ?_
  simp only [sigmaDbar, of_apply]
  exact (contDiffOn_dbarDir hD (contDiffOn_lowerSigma T.isOpen_U T.kahler hDU hu k) _).continuousOn.sub
    (contDiffOn_dbarDir hD (contDiffOn_lowerSigma T.isOpen_U T.kahler hDU hu j) _).continuousOn

theorem continuousOn_FS (hρ : IsChartDensity T.μ chart0 ρ) (e : AtlasFrame T.L)
    {u w : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u (T.dom e))
    (hw : ContDiffOn ℝ ∞ w (T.dom e)) : ContinuousOn (T.FS ρ e u w) (T.dom e) := by
  have hO := T.isOpen_dom e
  have h1 : ContinuousOn (sigmaInv T.omega T.r) (T.dom e) :=
    continuousOn_sigmaInv.mono (dom_subset_U e)
  have h2 : ContinuousOn (sigmaDbar T.omega T.r u) (T.dom e) :=
    continuousOn_sigmaDbar hO (dom_subset_U e) hu
  have h3 : ContinuousOn (sigmaDbar T.omega T.r w) (T.dom e) :=
    continuousOn_sigmaDbar hO (dom_subset_U e) hw
  have hc : ContinuousOn (fun z => zeroTwoPair (sigmaInv T.omega T.r z)
      (sigmaDbar T.omega T.r u z) (sigmaDbar T.omega T.r w z)) (T.dom e) :=
    continuousOn_zeroTwoPair h1 h2 h3
  have hw' : ContinuousOn (cweight (T.pW ρ e)) (T.dom e) :=
    continuousOn_cweight (T.contDiffOn_pW hρ e)
  unfold FS
  exact hc.mul hw'

theorem FS_gauge (e e' : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) (hz : z ∈ T.dom e) (hz' : z ∈ T.dom e') (hu : ContDiffAt ℝ ∞ u z)
    (hw : ContDiffAt ℝ ∞ w z) :
    T.FS ρ e' (fun y => frameTrans T.L e e' y • u y) (fun y => frameTrans T.L e e' y • w y) z =
      T.FS ρ e u w z := by
  have g := T.gaugeData_pW (ρ := ρ) e e'
  have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
  have hzU := dom_subset_U e hz
  unfold FS
  rw [sigmaDbar_smul hzU (g.differentiableAt hzS) hu, sigmaDbar_smul hzU (g.differentiableAt hzS) hw,
    zeroTwoPair_smul, ← g.cweight_mul hzS]
  ring

theorem isGaugeForm_S (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.FS ρ) where
  congr e u u' w w' z hu hw := by
    unfold FS
    rw [sigmaDbar_congr hu, sigmaDbar_congr hw]
  zero e u w z hw := by
    unfold FS
    rw [sigmaDbar_zero hw, zeroTwoPair_zero, zero_mul]
  add e u ι s w z hz _ hw := by
    unfold FS
    rw [sigmaDbar_sum s (dom_subset_U e hz) hw, zeroTwoPair_sum, Finset.sum_mul]
  gauge e e' u w z hz hz' hu hw := FS_gauge e e' u w z hz hz' hu hw
  contOn e u w hu hw := continuousOn_FS hρ e hu hw

end TwistedDatum

end SGPT.Trace.TwistedL2
