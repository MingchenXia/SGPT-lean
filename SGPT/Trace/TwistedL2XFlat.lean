import SGPT.Trace.TwistedL2MSigmaDensity
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp

/-!
# Holomorphic changes of coordinates: the flat calculus

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:flat`).  On a complex manifold the
local pieces of a twisted test form live in different charts.  A change of chart is a holomorphic
map `ψ` between open subsets of `ℂⁿ`; together with a change of frame `t` of `L` it acts on
coefficient vector fields by

`w' ∘ ψ = t · Dψ w`                                       (near a point `z`).

This file proves the transformation rules of the pointwise integrands of the twisted
Bochner--Kodaira--Nakano argument under such a change (only the germs at `z` matter):

* `dDir_comp_holo`, `dbarDir_comp_holo`: the chain rule `∂_v (f ∘ ψ) = ∂_{Dψ v} f`;
* `Amat_transport`: the matrix `A_w = (∂_{k̄} w_j)` of `∂̄w` satisfies `A_{w'} \overline{Dψ} = t Dψ A_w`;
* `trS_transport`: `tr(A_{u'} Ā_{w'}) = |t|² tr(A_u Ā_w)`;
* `dbarPairing_transport`: `⟨∂̄G', t Dψ v⟩ = |t|² ⟨∂̄G, v⟩` when `G' ∘ ψ = t G`;
* `leviS_comp_holo`: `Levi(q)(ψ z)(Dψ a, Dψ b) = Levi(q ∘ ψ)(z)(a, b)` (TN `leviForm_comp`,
  polarized).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander

variable {n : ℕ}

/-! ### Chain rules -/

theorem fderiv_comp_holo_apply {ψ : ComplexModel n → ComplexModel n} {f : ComplexModel n → ℂ}
    {z : ComplexModel n} (hψ : DifferentiableAt ℂ ψ z) (hf : DifferentiableAt ℝ f (ψ z))
    (v : ComplexModel n) :
    fderiv ℝ (fun y => f (ψ y)) z v = fderiv ℝ f (ψ z) (fderiv ℂ ψ z v) := by
  have hψR : DifferentiableAt ℝ ψ z := hψ.restrictScalars ℝ
  rw [show (fun y => f (ψ y)) = f ∘ ψ from rfl, fderiv_comp z hf hψR,
    hψ.fderiv_restrictScalars ℝ]
  rfl

/-- The chain rule for `∂_v` under a holomorphic map. -/
theorem dDir_comp_holo {ψ : ComplexModel n → ComplexModel n} {f : ComplexModel n → ℂ}
    {z : ComplexModel n} (hψ : DifferentiableAt ℂ ψ z) (hf : DifferentiableAt ℝ f (ψ z))
    (v : ComplexModel n) :
    dDir v (fun y => f (ψ y)) z = dDir (fderiv ℂ ψ z v) f (ψ z) := by
  simp only [dDir, fderiv_comp_holo_apply hψ hf, map_smul]

/-- The chain rule for `∂_{v̄}` under a holomorphic map. -/
theorem dbarDir_comp_holo {ψ : ComplexModel n → ComplexModel n} {f : ComplexModel n → ℂ}
    {z : ComplexModel n} (hψ : DifferentiableAt ℂ ψ z) (hf : DifferentiableAt ℝ f (ψ z))
    (v : ComplexModel n) :
    dbarDir v (fun y => f (ψ y)) z = dbarDir (fderiv ℂ ψ z v) f (ψ z) := by
  simp only [dbarDir, fderiv_comp_holo_apply hψ hf, map_smul]

/-! ### Matrices of linear maps -/

/-- The matrix `M_{jk} = (A e_k)_j` of a `ℂ`-linear map of `ℂⁿ`. -/
def linMat (A : ComplexModel n →L[ℂ] ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => A (coordVec k) j

theorem eq_sum_coordVec (u : ComplexModel n) : (∑ k, u k • coordVec k : ComplexModel n) = u := by
  ext i
  simp [coordVec, euclid_sum_apply]

theorem linMat_apply_eq (A : ComplexModel n →L[ℂ] ComplexModel n) (u : ComplexModel n) (j : Fin n) :
    A u j = ∑ k, linMat A j k * u k := by
  conv_lhs => rw [← eq_sum_coordVec u]
  rw [map_sum, euclid_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, PiLp.smul_apply, smul_eq_mul, linMat, of_apply, mul_comm]

theorem apply_coordVec_eq_sum (A : ComplexModel n →L[ℂ] ComplexModel n) (k : Fin n) :
    A (coordVec k) = ∑ l, linMat A l k • coordVec l := by
  conv_lhs => rw [← eq_sum_coordVec (A (coordVec k))]
  rfl

theorem linMat_comp (A B : ComplexModel n →L[ℂ] ComplexModel n) :
    linMat (A.comp B) = linMat A * linMat B := by
  ext j k
  simp only [linMat, of_apply, ContinuousLinearMap.comp_apply, mul_apply]
  rw [linMat_apply_eq A (B (coordVec k)) j]
  simp [linMat]

theorem linMat_id : linMat (ContinuousLinearMap.id ℂ (ComplexModel n)) = 1 := by
  ext j k
  simp only [linMat, of_apply, ContinuousLinearMap.id_apply, coordVec, one_apply]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

/-! ### The matrix of `∂̄ w` -/

/-- The coefficient matrix `A_{jk} = ∂_{k̄} w_j` of `∂̄ w`. -/
def Amat (w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => dbarDir (coordVec k) (fun y => w y j) z

theorem trS_eq_trace (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    trS u w z = trace (Amat u z * (Amat w z).map conj) := by
  simp only [trS, trace, diag_apply, mul_apply, Amat, of_apply, map_apply]

/-! ### Holomorphic factors -/

theorem differentiableAt_fderiv_holo_coord {ψ : ComplexModel n → ComplexModel n}
    {S : Set (ComplexModel n)} (hS : IsOpen S) (hψ : DifferentiableOn ℂ ψ S) {z : ComplexModel n}
    (hz : z ∈ S) (v : ComplexModel n) (j : Fin n) :
    DifferentiableAt ℂ (fun y => fderiv ℂ ψ y v j) z := by
  have h : DifferentiableAt ℂ (fun y => fderiv ℂ ψ y v) z :=
    (differentiableOn_fderiv_apply_of_isOpen hψ hS v).differentiableAt (hS.mem_nhds hz)
  exact (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiableAt.comp z h

theorem fderiv_holo_coord_eq_sum (ψ : ComplexModel n → ComplexModel n) (y u : ComplexModel n)
    (j : Fin n) : fderiv ℂ ψ y u j = ∑ m, fderiv ℂ ψ y (coordVec m) j * u m := by
  rw [linMat_apply_eq]
  rfl

/-- **The transformation of `∂̄ w`.**  If `w' ∘ ψ = t · Dψ w` near `z`, with `ψ` and `t`
holomorphic on an open `S ∋ z`, then `A_{w'}(ψ z) \overline{Dψ(z)} = t(z) Dψ(z) A_w(z)`. -/
theorem Amat_transport {S : Set (ComplexModel n)} (hS : IsOpen S)
    {ψ : ComplexModel n → ComplexModel n} (hψ : DifferentiableOn ℂ ψ S)
    {t : ComplexModel n → ℂ} (ht : DifferentiableOn ℂ t S) {z : ComplexModel n} (hz : z ∈ S)
    {w w' : ComplexModel n → ComplexModel n} (hw : DifferentiableAt ℝ w z)
    (hw' : DifferentiableAt ℝ w' (ψ z))
    (hrel : (fun y => w' (ψ y)) =ᶠ[𝓝 z] fun y => t y • fderiv ℂ ψ y (w y)) :
    Amat w' (ψ z) * (linMat (fderiv ℂ ψ z)).map conj =
      t z • (linMat (fderiv ℂ ψ z) * Amat w z) := by
  have hψz : DifferentiableAt ℂ ψ z := hψ.differentiableAt (hS.mem_nhds hz)
  have htz : DifferentiableAt ℂ t z := ht.differentiableAt (hS.mem_nhds hz)
  ext j k
  simp only [mul_apply, map_apply, Amat, of_apply, Matrix.smul_apply, smul_eq_mul]
  -- left side: a directional derivative along `Dψ e_k`
  have hL : ∑ l, dbarDir (coordVec l) (fun y => w' y j) (ψ z) * conj (linMat (fderiv ℂ ψ z) l k) =
      dbarDir (fderiv ℂ ψ z (coordVec k)) (fun y => w' y j) (ψ z) := by
    rw [apply_coordVec_eq_sum, dbarDir_sum_dir]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [hL, ← dbarDir_comp_holo hψz (differentiableAt_coord hw' j)]
  have hev : (fun y => w' (ψ y) j) =ᶠ[𝓝 z]
      fun y => ∑ m, (t y * fderiv ℂ ψ y (coordVec m) j) * w y m := by
    filter_upwards [hrel] with y hy
    rw [hy, PiLp.smul_apply, smul_eq_mul, fderiv_holo_coord_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [dbarDir_congr hev]
  have hhol : ∀ m, DifferentiableAt ℂ (fun y => t y * fderiv ℂ ψ y (coordVec m) j) z := fun m =>
    htz.mul (differentiableAt_fderiv_holo_coord hS hψ hz _ j)
  have hdiff : ∀ m ∈ Finset.univ, DifferentiableAt ℝ
      (fun y => (t y * fderiv ℂ ψ y (coordVec m) j) * w y m) z := fun m _ =>
    ((hhol m).restrictScalars ℝ).mul (differentiableAt_coord hw m)
  rw [dbarDir_finset_sum_fun Finset.univ hdiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dbarDir_holo_mul (hhol m) (differentiableAt_coord hw m)]
  simp only [linMat, of_apply]
  ring

theorem map_conj_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (c • A).map conj = conj c • A.map conj := by
  ext j k
  simp [map_mul]

theorem map_conj_map_conj (A : Matrix (Fin n) (Fin n) ℂ) : (A.map conj).map conj = A := by
  ext j k
  simp

/-- **Invariance of `tr(A Ā)`**: `tr(A_{u'} Ā_{w'})(ψ z) = |t(z)|² tr(A_u Ā_w)(z)`, for an
invertible `Dψ(z)`. -/
theorem trS_transport {S : Set (ComplexModel n)} (hS : IsOpen S)
    {ψ : ComplexModel n → ComplexModel n} (hψ : DifferentiableOn ℂ ψ S)
    {t : ComplexModel n → ℂ} (ht : DifferentiableOn ℂ t S) {z : ComplexModel n} (hz : z ∈ S)
    (hinv : IsUnit (linMat (fderiv ℂ ψ z)))
    {u u' w w' : ComplexModel n → ComplexModel n} (hu : DifferentiableAt ℝ u z)
    (hu' : DifferentiableAt ℝ u' (ψ z)) (hw : DifferentiableAt ℝ w z)
    (hw' : DifferentiableAt ℝ w' (ψ z))
    (hru : (fun y => u' (ψ y)) =ᶠ[𝓝 z] fun y => t y • fderiv ℂ ψ y (u y))
    (hrw : (fun y => w' (ψ y)) =ᶠ[𝓝 z] fun y => t y • fderiv ℂ ψ y (w y)) :
    trS u' w' (ψ z) = (t z * conj (t z)) * trS u w z := by
  set M := linMat (fderiv ℂ ψ z) with hM
  have hU := Amat_transport hS hψ ht hz hu hu' hru
  have hW := Amat_transport hS hψ ht hz hw hw' hrw
  rw [← hM] at hU hW
  have hdet : IsUnit M.det := (isUnit_iff_isUnit_det M).mp hinv
  have hMN : M * M⁻¹ = 1 := mul_nonsing_inv M hdet
  -- conjugate the second relation
  have hW' : (Amat w' (ψ z)).map conj * M = conj (t z) • (M.map conj * (Amat w z).map conj) := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.map conj) hW
    simp only [Matrix.map_mul, map_conj_smul, map_conj_map_conj] at this
    exact this
  have key : Amat u' (ψ z) * (Amat w' (ψ z)).map conj * M =
      (t z * conj (t z)) • (M * (Amat u z * (Amat w z).map conj)) := by
    rw [Matrix.mul_assoc, hW', Matrix.mul_smul, ← Matrix.mul_assoc, hU, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, mul_comm (conj (t z))]
  have key' : Amat u' (ψ z) * (Amat w' (ψ z)).map conj =
      (t z * conj (t z)) • (M * (Amat u z * (Amat w z).map conj) * M⁻¹) := by
    have := congrArg (fun A => A * M⁻¹) key
    simp only [Matrix.mul_assoc, hMN, Matrix.mul_one, Matrix.smul_mul] at this
    rw [this, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [trS_eq_trace, trS_eq_trace, key', trace_smul, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc, nonsing_inv_mul M hdet, Matrix.mul_one, smul_eq_mul]

/-! ### The data pairing -/

theorem dbarPairing_eq_dbarDir (f : ComplexModel n → ℂ) (z v : ComplexModel n) :
    dbarPairing f z v = dbarDir v f z := by
  conv_rhs => rw [← eq_sum_coordVec v]
  rw [dbarDir_sum_dir]
  rfl

/-- **Invariance of the data pairing**: if `G' ∘ ψ = t G` near `z`, then
`⟨∂̄G'(ψ z), t Dψ v⟩ = |t|² ⟨∂̄G(z), v⟩`. -/
theorem dbarPairing_transport {S : Set (ComplexModel n)} (hS : IsOpen S)
    {ψ : ComplexModel n → ComplexModel n} (hψ : DifferentiableOn ℂ ψ S)
    {t : ComplexModel n → ℂ} (ht : DifferentiableOn ℂ t S) {z : ComplexModel n} (hz : z ∈ S)
    {G G' : ComplexModel n → ℂ} (hG : DifferentiableAt ℝ G z)
    (hG' : DifferentiableAt ℝ G' (ψ z))
    (hrel : (fun y => G' (ψ y)) =ᶠ[𝓝 z] fun y => t y * G y) (v : ComplexModel n) :
    dbarPairing G' (ψ z) (t z • fderiv ℂ ψ z v) = (t z * conj (t z)) * dbarPairing G z v := by
  have hψz : DifferentiableAt ℂ ψ z := hψ.differentiableAt (hS.mem_nhds hz)
  have htz : DifferentiableAt ℂ t z := ht.differentiableAt (hS.mem_nhds hz)
  rw [dbarPairing_eq_dbarDir, dbarPairing_eq_dbarDir, dbarDir_smul_dir,
    ← dbarDir_comp_holo hψz hG', dbarDir_congr hrel, dbarDir_holo_mul htz hG]
  ring

/-! ### The Levi form -/

/-- **Naturality of the sesquilinear Levi form** under a holomorphic map (TN `leviForm_comp`,
polarized). -/
theorem leviS_comp_holo {S V : Set (ComplexModel n)} (hS : IsOpen S) (hV : IsOpen V)
    {ψ : ComplexModel n → ComplexModel n} (hψ : DifferentiableOn ℂ ψ S)
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q V) (hψV : MapsTo ψ S V)
    {z : ComplexModel n} (hz : z ∈ S) (a b : ComplexModel n) :
    leviS q (ψ z) (fderiv ℂ ψ z a) (fderiv ℂ ψ z b) = leviS (fun y => q (ψ y)) z a b := by
  have hψc : ContDiffOn ℂ ∞ ψ S := contDiffOn_of_differentiableOn_complex hψ hS
  have hψz : DifferentiableAt ℂ ψ z := hψ.differentiableAt (hS.mem_nhds hz)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hq2 : ContDiffAt ℝ 2 q (ψ z) :=
    (hq.contDiffAt (hV.mem_nhds (hψV hz))).of_le h2
  have hqψ : ContDiffAt ℝ 2 (fun y => q (ψ y)) z :=
    ((hq.comp (hψc.restrict_scalars ℝ) hψV).contDiffAt (hS.mem_nhds hz)).of_le h2
  have hdiag : ∀ v : ComplexModel n, leviS q (ψ z) (fderiv ℂ ψ z v) (fderiv ℂ ψ z v) =
      leviS (fun y => q (ψ y)) z v v := by
    intro v
    rw [leviS_self hq2, leviS_self hqψ,
      SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp.leviForm_comp hS hV hψc hq hψV hz v,
      hψz.fderiv_restrictScalars ℝ]
    rfl
  rw [leviS_polar q (ψ z), leviS_polar (fun y => q (ψ y)) z]
  simp only [← map_add, ← map_sub, ← map_smul, hdiag]

end SGPT.Trace.TwistedL2
