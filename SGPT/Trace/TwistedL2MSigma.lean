import SGPT.Trace.TwistedL2MReduction
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# The Kähler form `σ = ω + ddᶜr` on `ℂⁿ` as a Hermitian matrix with local potentials

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:sigma`).  On an open `U ⊆ ℂⁿ` where
`σ = ω + ddᶜ r` is Kähler (`IsKahlerModificationOn`):

* `exists_sigma_potential`: near every point of `U`, `σ(v) = Levi(R)(v)` for a smooth real `R`
  (`R = (ρ_ω + r)/π` with a local `ddᶜ`-potential `ρ_ω` of `ω`, TN
  `closedRealOneOne_hasLocalPotentials`);
* `sigmaMat z`: the Hermitian matrix of `σ` at `z`, defined by polarization of the quadratic form
  `modifiedKahlerQuad`; near each point it is the complex Hessian `∂_l ∂_{k̄} R` of a local
  potential (`sigmaMat_eq_hessian`), and `(sigmaMat z)ᵀ` is positive definite on `U`
  (`posDef_sigmaMat_transpose`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate ComplexOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ}

/-! ### Sesquilinearity of `leviS` -/

section Sesqui

variable (p : ComplexModel n → ℝ) (z : ComplexModel n)

theorem leviS_add_left (u v w : ComplexModel n) :
    leviS p z (u + v) w = leviS p z u w + leviS p z v w := by
  simp only [leviS, PiLp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem leviS_add_right (u v w : ComplexModel n) :
    leviS p z u (v + w) = leviS p z u v + leviS p z u w := by
  simp only [leviS, PiLp.add_apply, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem leviS_smul_left (c : ℂ) (u w : ComplexModel n) :
    leviS p z (c • u) w = c * leviS p z u w := by
  simp only [leviS, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem leviS_smul_right (c : ℂ) (u w : ComplexModel n) :
    leviS p z u (c • w) = conj c * leviS p z u w := by
  simp only [leviS, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem leviS_neg_left (u w : ComplexModel n) : leviS p z (-u) w = -leviS p z u w := by
  have := leviS_smul_left p z (-1) u w
  simpa using this

theorem leviS_neg_right (u w : ComplexModel n) : leviS p z u (-w) = -leviS p z u w := by
  have := leviS_smul_right p z (-1) u w
  simpa using this

/-- **Polarization** of the sesquilinear Levi form. -/
theorem leviS_polar (u w : ComplexModel n) :
    leviS p z u w = (leviS p z (u + w) (u + w) - leviS p z (u - w) (u - w) +
      Complex.I * leviS p z (u + Complex.I • w) (u + Complex.I • w) -
      Complex.I * leviS p z (u - Complex.I • w) (u - Complex.I • w)) / 4 := by
  simp only [sub_eq_add_neg, leviS_add_left, leviS_add_right, leviS_neg_left, leviS_neg_right,
    leviS_smul_left, leviS_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

end Sesqui

/-! ### The σ-quadratic form and its matrix -/

/-- The quadratic form of `σ = ω + ddᶜ r` on `ℂⁿ`. -/
def sigmaQ (omega : KahlerBackground n (ComplexModel n)) (r : ComplexModel n → ℝ)
    (z v : ComplexModel n) : ℝ :=
  modifiedKahlerQuad omega r chart0 z v

/-- The polarized sesquilinear form of `σ`. -/
def sigmaS (omega : KahlerBackground n (ComplexModel n)) (r : ComplexModel n → ℝ)
    (z u w : ComplexModel n) : ℂ :=
  ((sigmaQ omega r z (u + w) : ℂ) - sigmaQ omega r z (u - w) +
    Complex.I * sigmaQ omega r z (u + Complex.I • w) -
    Complex.I * sigmaQ omega r z (u - Complex.I • w)) / 4

/-- The Hermitian matrix `σ_{lk}` of `σ` (`σ(v) = ∑_{l,k} σ_{lk} v_l conj v_k`). -/
def sigmaMat (omega : KahlerBackground n (ComplexModel n)) (r : ComplexModel n → ℝ)
    (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun l k => sigmaS omega r z (coordVec l) (coordVec k)

variable {omega : KahlerBackground n (ComplexModel n)} {r : ComplexModel n → ℝ}
  {U : Set (ComplexModel n)}

/-- **Local potentials of `σ`.** -/
theorem exists_sigma_potential (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ V : Set (ComplexModel n), ∃ R : ComplexModel n → ℝ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ R V ∧ ∀ y ∈ V, ∀ v, sigmaQ omega r y v = leviForm R y v := by
  obtain ⟨W, ρω, hzW, hW, -, hρ, heq⟩ :=
    SGPT.Foundations.Analysis.Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials
      omega.form chart0 z (by simp)
  have hrU : ContDiffOn ℝ ∞ r U := by
    have h := hr.1 chart0
    simp only [chart0_target, chart0_symm_apply] at h
    exact h.mono fun y hy => ⟨mem_univ y, hy⟩
  refine ⟨W ∩ U, (1 / Real.pi) • (ρω + r), hW.inter hU, ⟨hzW, hz⟩, inter_subset_right,
    ((hρ.mono inter_subset_left).add (hrU.mono inter_subset_right)).const_smul (1 / Real.pi), ?_⟩
  intro y hy v
  have hO : IsOpen (W ∩ U) := hW.inter hU
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hρy : ContDiffAt ℝ 2 ρω y := ((hρ.contDiffAt (hW.mem_nhds hy.1))).of_le h2
  have hry : ContDiffAt ℝ 2 r y := ((hrU.contDiffAt (hU.mem_nhds hy.2))).of_le h2
  have hsum : ContDiffAt ℝ 2 (ρω + r) y := hρy.add hry
  rw [leviForm_smul hsum, leviForm_add hρy hry]
  simp only [sigmaQ, modifiedKahlerQuad, kahlerQuad, chart0_symm_apply]
  rw [← heq hy.1, smoothDDC_complexDiagonal_eq_leviForm hρy]
  ring

/-- Near a point of `U`, the sesquilinear form of `σ` is the Levi form of a local potential. -/
theorem sigmaS_eq_leviS {V : Set (ComplexModel n)} {R : ComplexModel n → ℝ} (hV : IsOpen V)
    (hR : ContDiffOn ℝ ∞ R V) (hσ : ∀ y ∈ V, ∀ v, sigmaQ omega r y v = leviForm R y v)
    {y : ComplexModel n} (hy : y ∈ V) (u w : ComplexModel n) :
    sigmaS omega r y u w = leviS R y u w := by
  have hRy : ContDiffAt ℝ 2 R y :=
    (hR.contDiffAt (hV.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [leviS_polar R y u w, sigmaS]
  simp only [hσ y hy, leviS_self hRy]

theorem sigmaMat_eq_hessian {V : Set (ComplexModel n)} {R : ComplexModel n → ℝ} (hV : IsOpen V)
    (hR : ContDiffOn ℝ ∞ R V) (hσ : ∀ y ∈ V, ∀ v, sigmaQ omega r y v = leviForm R y v)
    {y : ComplexModel n} (hy : y ∈ V) (l k : Fin n) :
    sigmaMat omega r y l k = dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ)) y := by
  rw [sigmaMat, of_apply, sigmaS_eq_leviS hV hR hσ hy, leviS]
  simp [coordVec, Finset.sum_ite_eq']

/-- `∑_{l,k} σ_{lk} u_l conj w_k = σ(u, w)`. -/
theorem sum_sigmaMat_mul {V : Set (ComplexModel n)} {R : ComplexModel n → ℝ} (hV : IsOpen V)
    (hR : ContDiffOn ℝ ∞ R V) (hσ : ∀ y ∈ V, ∀ v, sigmaQ omega r y v = leviForm R y v)
    {y : ComplexModel n} (hy : y ∈ V) (u w : ComplexModel n) :
    ∑ l, ∑ k, sigmaMat omega r y l k * u l * conj (w k) = leviS R y u w := by
  simp only [sigmaMat_eq_hessian hV hR hσ hy, leviS]

theorem conj_leviS_symm {p : ComplexModel n → ℝ} {z : ComplexModel n} (hp : ContDiffAt ℝ 2 p z)
    (u w : ComplexModel n) : conj (leviS p z u w) = leviS p z w u := by
  have hpc : ContDiffAt ℝ 2 (fun y => (p y : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp z hp
  have hD : ∀ j k : Fin n, conj (dbarDir (coordVec k) (dDir (coordVec j) fun y => (p y : ℂ)) z) =
      dbarDir (coordVec j) (dDir (coordVec k) fun y => (p y : ℂ)) z := by
    intro j k
    have hd : DifferentiableAt ℝ (dDir (coordVec j) fun y => (p y : ℂ)) z :=
      differentiableAt_dDir hpc
    rw [← dDir_conj hd]
    have hev : (fun y => conj (dDir (coordVec j) (fun y => (p y : ℂ)) y)) =ᶠ[𝓝 z]
        dbarDir (coordVec j) fun y => (p y : ℂ) := by
      filter_upwards [hp.eventually (by simp)] with y hy
      have hy1 : DifferentiableAt ℝ (fun y => (p y : ℂ)) y :=
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp y hy).differentiableAt (by norm_num)
      rw [← dbarDir_conj hy1]
      simp
    rw [dDir_congr_of_eventuallyEq hev, ← dbarDir_dDir_comm hpc]
  simp only [leviS, map_sum, map_mul, Complex.conj_conj, hD]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **`σᵀ` is positive definite on `U`** (Mathlib's convention `star x ⬝ᵥ (M *ᵥ x) > 0`). -/
theorem posDef_sigmaMat_transpose (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {z : ComplexModel n} (hz : z ∈ U) : (sigmaMat omega r z)ᵀ.PosDef := by
  obtain ⟨V, R, hV, hzV, hVU, hR, hσ⟩ := exists_sigma_potential hU hr hz
  have hRz : ContDiffAt ℝ 2 R z :=
    (hR.contDiffAt (hV.mem_nhds hzV)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hquad : ∀ x : Fin n → ℂ, star x ⬝ᵥ ((sigmaMat omega r z)ᵀ *ᵥ x) =
      leviS R z (WithLp.toLp 2 x) (WithLp.toLp 2 x) := by
    intro x
    rw [← sum_sigmaMat_mul hV hR hσ hzV]
    simp only [dotProduct, mulVec, transpose_apply, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]
    ring
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext l k
    simp only [conjTranspose_apply, transpose_apply, RCLike.star_def]
    rw [sigmaMat_eq_hessian hV hR hσ hzV, sigmaMat_eq_hessian hV hR hσ hzV]
    have := conj_leviS_symm hRz (coordVec l) (coordVec k)
    simp only [leviS] at this
    simp [coordVec, Finset.sum_ite_eq'] at this
    exact this
  · rw [hquad, leviS_self hRz, ← hσ z hzV]
    have hv : (WithLp.toLp 2 x : ComplexModel n) ≠ 0 := by
      intro h0
      exact hx (by simpa using congrArg WithLp.ofLp h0)
    exact_mod_cast hr.2 chart0 z (by simp) (by simpa using hz) _ hv

end SGPT.Trace.TwistedL2
