import SGPT.Trace.TwistedL2MSigma
import SGPT.Trace.TwistedL2KahlerLowering
import SGPT.Trace.TwistedL2Pointwise

/-!
# The `∂̄`-defect is controlled by `|∂̄(σ^♭ W)|²_σ`

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:defect`).  For a vector field `W` near a point of
`U` (where `σ = ω + ddᶜr` is Kähler), with `σ^♭W` its `σ`-lowering (a `(0,1)`-form) and
`sigmaDbar W` the coefficient matrix of `∂̄(σ^♭ W)`:

`-Re tr(A_W Ā_W) ≤ |∂̄(σ^♭ W)|²_σ`        (`neg_re_trS_le`),

the pointwise Kähler identity (`claude-twisted-l2:kahler-antisym`) combined with Kähler lowering
(`claude-twisted-l2:kahler-lowering`) for a local potential of `σ`.  The form
`FS e u w = ⟨∂̄σ^♭u, ∂̄σ^♭w⟩_σ e^{-p_e}` is a gauge form, and for every finite family of pieces the
`∂̄`-defect `Q(τ)` is at most `sup a · ‖∂̄(σ^♭ W_τ)‖²` (`FrameFamily.defect_le`).
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

variable (omega : KahlerBackground n (ComplexModel n)) (r : ComplexModel n → ℝ)

/-- The `σ`-lowering `(σ^♭ W)_k = ∑_l σ_{lk} W_l`. -/
def lowerSigma (W : ComplexModel n → ComplexModel n) (y : ComplexModel n) (k : Fin n) : ℂ :=
  ∑ l, sigmaMat omega r y l k * W y l

/-- The coefficient matrix `∂_{j̄}(σ^♭W)_k - ∂_{k̄}(σ^♭W)_j` of `∂̄(σ^♭ W)`. -/
def sigmaDbar (W : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => dbarDir (coordVec j) (fun y => lowerSigma omega r W y k) z -
    dbarDir (coordVec k) (fun y => lowerSigma omega r W y j) z

/-- The `σ`-pairing `½ tr(βᴴ N γ Nᵀ)` of `(0,2)`-coefficient matrices (`N = g⁻¹`). -/
def zeroTwoPair (N β γ : Matrix (Fin n) (Fin n) ℂ) : ℂ := (1 / 2 : ℂ) * trace (βᴴ * N * γ * Nᵀ)

/-- The inverse `σ`-matrix `((σ_{lk})ᵀ)⁻¹`. -/
def sigmaInv (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ := ((sigmaMat omega r z)ᵀ)⁻¹

variable {omega r} {U : Set (ComplexModel n)}

theorem zeroTwoPair_re (N β : Matrix (Fin n) (Fin n) ℂ) :
    (zeroTwoPair N β β).re = zeroTwoNormSq N β := by
  simp [zeroTwoPair, zeroTwoNormSq, Complex.mul_re]

theorem zeroTwoNormSq_nonneg {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.PosDef)
    (β : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ zeroTwoNormSq g⁻¹ β := by
  unfold zeroTwoNormSq
  have hN : (g⁻¹).PosDef := hg.inv
  have h1 : (βᴴ * g⁻¹ * β).PosSemidef := hN.posSemidef.conjTranspose_mul_mul_same β
  have h2 := re_trace_mul_nonneg_of_posSemidef h1 hN.transpose.posSemidef
  have : βᴴ * g⁻¹ * β * (g⁻¹)ᵀ = (βᴴ * g⁻¹ * β) * (g⁻¹)ᵀ := rfl
  rw [this]
  positivity

/-- `σ` is smooth on `U`. -/
theorem contDiffOn_sigmaMat (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U) (l k : Fin n) :
    ContDiffOn ℝ ∞ (fun y => sigmaMat omega r y l k) U := by
  intro z hz
  obtain ⟨V, R, hV, hzV, hVU, hR, hσ⟩ := exists_sigma_potential hU hr hz
  have hRc : ContDiffOn ℝ ∞ (fun y => (R y : ℂ)) V := contDiffOn_ofReal' hR
  have h : ContDiffOn ℝ ∞ (dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ))) V :=
    contDiffOn_dbarDir hV (contDiffOn_dDir hV hRc _) _
  have hev : (fun y => sigmaMat omega r y l k) =ᶠ[𝓝 z]
      dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ)) := by
    filter_upwards [hV.mem_nhds hzV] with y hy
    exact sigmaMat_eq_hessian hV hR hσ hy l k
  exact ((h.contDiffAt (hV.mem_nhds hzV)).congr_of_eventuallyEq hev).contDiffWithinAt

theorem contDiffOn_lowerSigma (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {D : Set (ComplexModel n)} (hDU : D ⊆ U) {W : ComplexModel n → ComplexModel n}
    (hW : ContDiffOn ℝ ∞ W D) (k : Fin n) :
    ContDiffOn ℝ ∞ (fun y => lowerSigma omega r W y k) D := by
  unfold lowerSigma
  exact ContDiffOn.sum fun l _ =>
    ((contDiffOn_sigmaMat hU hr l k).mono hDU).mul (contDiffOn_coord hW l)

/-- **The pointwise defect bound** `-Re tr(A_W Ā_W) ≤ |∂̄(σ^♭W)|²_σ`. -/
theorem neg_re_trS_le (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {D : Set (ComplexModel n)} (hD : IsOpen D) (hDU : D ⊆ U) {W : ComplexModel n → ComplexModel n}
    (hW : ContDiffOn ℝ ∞ W D) {z : ComplexModel n} (hz : z ∈ D) :
    -(trS W W z).re ≤ zeroTwoNormSq (sigmaInv omega r z) (sigmaDbar omega r W z) := by
  obtain ⟨V, R, hV, hzV, hVU, hR, hσ⟩ := exists_sigma_potential hU hr (hDU hz)
  set g : Matrix (Fin n) (Fin n) ℂ := (sigmaMat omega r z)ᵀ with hgdef
  have hg : g.PosDef := posDef_sigmaMat_transpose hU hr (hDU hz)
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j k => dbarDir (coordVec k) (fun y => W y j) z
  have hT : trS W W z = traceMulConj A := by
    simp only [trS, traceMulConj, trace, diag_apply, mul_apply, A, of_apply, transpose_apply,
      conjTranspose_apply, RCLike.star_def]
  have hO : IsOpen (V ∩ D) := hV.inter hD
  have hzO : z ∈ V ∩ D := ⟨hzV, hz⟩
  have hlow : KahlerLoweringStatement n := kahlerLoweringStatement
  have hWl : ∀ l, ContDiffOn ℝ ∞ (fun y => W y l) (V ∩ D) := fun l =>
    contDiffOn_coord (hW.mono inter_subset_right) l
  have hK := hlow (V ∩ D) hO R (hR.mono inter_subset_left) (fun l y => W y l) hWl z hzO
  have hev : ∀ k, (fun y => lowerSigma omega r W y k) =ᶠ[𝓝 z]
      lowerVector R (fun l y => W y l) k := by
    intro k
    filter_upwards [hV.mem_nhds hzV] with y hy
    simp only [lowerSigma, lowerVector, sigmaMat_eq_hessian hV hR hσ hy]
  have hβ : sigmaDbar omega r W z = kahlerAntisym g A := by
    ext j k
    simp only [sigmaDbar, of_apply, dbarDir_congr_of_eventuallyEq (hev _)]
    rw [hK j k, kahlerAntisym, Matrix.sub_apply, transpose_apply, mul_apply, mul_apply,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hgdef, transpose_apply, A, of_apply, sigmaMat_eq_hessian hV hR hσ hzV]
  rw [hT, hβ, sigmaInv]
  exact neg_re_traceMulConj_le hg A

end SGPT.Trace.TwistedL2
