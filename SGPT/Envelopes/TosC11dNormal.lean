import SGPT.Envelopes.TosC11dTransfer
import SGPT.Analysis.KahlerNormalUniform
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Kähler normal coordinates diagonalizing the complex Hessian, with uniform bounds

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:normal-frame`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 2 ("choose normal coordinates for `κ` at
`x₀` in which `G(x₀)` is diagonal … followed by a unitary change of coordinates that diagonalizes
`G(x₀)`, there are such coordinates in which the derivatives of `k` of every fixed order at `x₀` are
bounded independently of `x₀`") and `lem:kahler-normal-coordinates-uniform`, for SGPT `thm:Tos_C11`
(Tosatti, Chu–Zhou).

* `exists_unitary_diag` — a Hermitian matrix `M` is diagonalized as `Pᵀ M P̄` by the matrix `P` of a
  unitary map (an orthonormal eigenbasis of `Mᵀ`).
* `exists_normal_frame` — for a chart `e`, a compact `K ⊆ target(e)` and a Kähler form `A`: there are
  constants such that for every `z₀ ∈ K` and every Hermitian `M₀` there are normal coordinates
  `Φ(w) = z₀ + A₂(w - ½ c(w, w))` (`A₂` a normalizing map composed with a unitary map) with
  `Φ^*A = ω₀` at `0`, vanishing first derivative, bounded second and third derivatives on the real
  frame, bounded `DΦ(0)` and `D²Φ(0)`, invertible `DΦ` near `0`, and `Jᵀ M₀ J̄` diagonal for the Jacobian
  matrix `J` of `Φ` at `0`.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Analysis.KahlerNormal

variable {N : ℕ}

/-- The matrix of a `ℂ`-linear map in the standard basis. -/
def lmat (L : ComplexModel N →L[ℂ] ComplexModel N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a j => L (coordinateVector j) a

theorem lmat_comp (L Q : ComplexModel N →L[ℂ] ComplexModel N) :
    lmat (L.comp Q) = lmat L * lmat Q := by
  ext a j
  simp only [lmat, Matrix.of_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply]
  conv_lhs => rw [← BlockiLocalEstimate.coordinateVector_sum (Q (coordinateVector j))]
  simp [map_sum, map_smul, mul_comm]

/-- **Unitary diagonalization** `Pᵀ M P̄ = diag(r)` of a Hermitian matrix. -/
theorem exists_unitary_diag {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian) :
    ∃ (Q : ComplexModel N ≃ₗᵢ[ℂ] ComplexModel N) (r : Fin N → ℝ),
      (lmat (Q.toContinuousLinearEquiv : ComplexModel N →L[ℂ] ComplexModel N)).transpose * M *
        (lmat (Q.toContinuousLinearEquiv : ComplexModel N →L[ℂ] ComplexModel N)).map
          (starRingEnd ℂ) = Matrix.diagonal fun i => (r i : ℂ) := by
  have hT : M.transpose.IsHermitian := hM.transpose
  set b := hT.eigenvectorBasis with hbdef
  refine ⟨b.repr.symm, hT.eigenvalues, ?_⟩
  have hcol : ∀ j a, lmat (b.repr.symm.toContinuousLinearEquiv :
      ComplexModel N →L[ℂ] ComplexModel N) a j = b j a := fun j a => by
    simp only [lmat, Matrix.of_apply, coordinateVector]
    rw [show (b.repr.symm.toContinuousLinearEquiv : ComplexModel N →L[ℂ] ComplexModel N)
      (EuclideanSpace.single j 1) = b.repr.symm (EuclideanSpace.single j 1) from rfl,
      b.repr_symm_single]
  have heig : ∀ k c, ∑ a, M a c * b k a = hT.eigenvalues k * b k c := fun k c => by
    have := congrFun (hT.mulVec_eigenvectorBasis k) c
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.smul_apply,
      Complex.real_smul] at this
    rw [← this]
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hcol,
    Matrix.diagonal_apply]
  have e1 : ∑ c, (∑ a, b k a * M a c) * (starRingEnd ℂ) (b l c) =
      hT.eigenvalues k * ∑ c, (starRingEnd ℂ) (b l c) * b k c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show ∑ a, b k a * M a c = ∑ a, M a c * b k a from
      Finset.sum_congr rfl fun a _ => mul_comm _ _, heig]
    ring
  rw [e1]
  have horth := b.orthonormal
  have hinner : ∑ c, (starRingEnd ℂ) (b l c) * b k c = inner ℂ (b l) (b k) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [mul_comm]
  rw [hinner]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, horth.1 k]
    simp
  · rw [if_neg hkl, horth.2 (Ne.symm hkl), mul_zero]

/-- The real frame `eⱼ, i eⱼ` of `ℂⁿ` as a finite family. -/
def frameV (p : Fin N × Bool) : ComplexModel N :=
  if p.2 then Complex.I • TosC11c.stdVec p.1 else TosC11c.stdVec p.1

theorem contDiff_normalCoord (z₀ : ComplexModel N) (A : ComplexModel N →L[ℂ] ComplexModel N)
    (c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N) :
    ContDiff ℂ ∞ (normalCoord z₀ A c) := by
  unfold normalCoord
  have hq : ContDiff ℂ ∞ (fun w : ComplexModel N => c w w) :=
    c.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  exact contDiff_const.add (A.contDiff.comp (contDiff_id.sub (hq.const_smul _)))

/-- **Diagonalizing Kähler normal coordinates with uniform bounds.** -/
theorem exists_normal_frame {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] (A : KahlerBackground N Y) (e : ComplexChart N Y)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ CA C2 C3 : ℝ, 0 ≤ CA ∧ ∀ z₀ ∈ K, ∀ M₀ : Matrix (Fin N) (Fin N) ℂ, M₀.IsHermitian →
      ∃ (Φ : ComplexModel N → ComplexModel N) (r : Fin N → ℝ),
        ContDiff ℂ ∞ Φ ∧ Φ 0 = z₀ ∧ (∀ᶠ x in 𝓝 0, Function.Bijective (fderiv ℝ Φ x)) ∧
        pullbackField Φ (A.form.val.coeff e) 0 = flatForm N ∧
        HasFDerivAt (pullbackField Φ (A.form.val.coeff e))
          (0 : ComplexModel N →L[ℝ] CoordinateRealTwoForm N) 0 ∧
        (∀ p q, ‖iteratedFDeriv ℝ 2
          (fun w => pullbackField Φ (A.form.val.coeff e) w ![frameV p, frameV q]) 0‖ ≤ C2) ∧
        (∀ p q, ‖iteratedFDeriv ℝ 3
          (fun w => pullbackField Φ (A.form.val.coeff e) w ![frameV p, frameV q]) 0‖ ≤ C3) ∧
        ‖fderiv ℝ Φ 0‖ ≤ CA ∧ (∀ v, ‖fderiv ℝ (fderiv ℝ Φ) 0 v v‖ ≤ CA * CA * ‖v‖ ^ 2) ∧
        (HolomorphicMixedDensity.jacobianMatrix Φ 0).transpose * M₀ *
          (HolomorphicMixedDensity.jacobianMatrix Φ 0).map (starRingEnd ℂ) =
            Matrix.diagonal fun i => (r i : ℂ) := by
  have hκ := A.isKahler
  obtain ⟨⟨CA, hCA0, hb⟩, hder⟩ := kahlerNormal_uniform_of_isKahler hκ e hK hKt
  choose C2f hC2f using fun p q : Fin N × Bool => hder 2 (frameV p) (frameV q)
  choose C3f hC3f using fun p q : Fin N × Bool => hder 3 (frameV p) (frameV q)
  refine ⟨CA, ∑ p, ∑ q, |C2f p q|, ∑ p, ∑ q, |C3f p q|, hCA0, fun z₀ hz₀ M₀ hM₀ => ?_⟩
  set α := A.form.val.coeff e with hαdef
  have hz₀t := hKt hz₀
  have hU := e.val.open_target
  have h11 : ∀ z ∈ e.val.target, IsOneOne (α z) := fun z hz => (hκ.1 e z hz).1
  obtain ⟨A₁, hA₁⟩ := exists_normalizing_linear (h11 z₀ hz₀t) (hκ.1 e z₀ hz₀t).2
  set M : Matrix (Fin N) (Fin N) ℂ := (lmat (A₁ : ComplexModel N →L[ℂ] ComplexModel N)).transpose *
    M₀ * (lmat (A₁ : ComplexModel N →L[ℂ] ComplexModel N)).map (starRingEnd ℂ) with hMdef
  have hMh : M.IsHermitian := by
    rw [hMdef, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM₀.eq,
      Matrix.mul_assoc]
    congr 1
    ext a b; simp [Matrix.conjTranspose_apply]
  obtain ⟨Q, r, hQr⟩ := exists_unitary_diag hMh
  set A₂ : ComplexModel N ≃L[ℂ] ComplexModel N := Q.toContinuousLinearEquiv.trans A₁ with hA₂def
  have hA₂ : ∀ u v, α z₀ ![A₂ u, A₂ v] = flatForm N ![u, v] := fun u v => by
    rw [hA₂def, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, hA₁]
    exact flatForm_unitary Q.toLinearIsometry u v
  have hα : ContDiffOn ℝ ∞ α e.val.target := A.form.val.smooth e
  have ha0 : DifferentiableAt ℝ α z₀ := (hα.contDiffAt (hU.mem_nhds hz₀t)).differentiableAt (by simp)
  have h11ev : ∀ᶠ z in 𝓝 z₀, IsOneOne (α z) :=
    Filter.mem_of_superset (hU.mem_nhds hz₀t) fun z hz => h11 z hz
  have hβ11 := normalizedDeriv_isOneOne ha0 h11ev (A₂ : ComplexModel N →L[ℂ] ComplexModel N)
  set c := normalQuad (normalizedDeriv α z₀ (A₂ : ComplexModel N →L[ℂ] ComplexModel N)) hβ11
    with hcdef
  have hc : ∀ p u v, inner ℂ v (c p u) = (Real.pi : ℂ) *
      dHol (normalizedDeriv α z₀ (A₂ : ComplexModel N →L[ℂ] ComplexModel N)) p u v :=
    fun p u v => inner_quadFun _ p u v
  obtain ⟨hsymm, h0, hd⟩ := kahlerNormal_of_normalizing z₀
    (A₂ : ComplexModel N →L[ℂ] ComplexModel N) c ha0 h11ev (hκ.2 e z₀ hz₀t) hA₂ hc
  set Φ := normalCoord z₀ (A₂ : ComplexModel N →L[ℂ] ComplexModel N) c with hΦdef
  obtain ⟨hAn, hcb⟩ := hb z₀ hz₀ (A₂ : ComplexModel N →L[ℂ] ComplexModel N) hA₂
  obtain ⟨hcpx, -⟩ := hcb c hc
  have hD : ∀ x, fderiv ℝ Φ x =
      ((A₂ : ComplexModel N →L[ℂ] ComplexModel N) ∘L
        (ContinuousLinearMap.id ℂ _ - c x)).restrictScalars ℝ := fun x =>
    fderiv_normalCoord z₀ _ c hsymm x
  refine ⟨Φ, r, contDiff_normalCoord _ _ _, normalCoord_zero _ _ _, ?_, h0, hd, ?_, ?_, ?_, ?_, ?_⟩
  · -- invertibility of `DΦ` near `0`
    set Dc : ComplexModel N → (ComplexModel N →L[ℂ] ComplexModel N) :=
      fun w => (A₂ : ComplexModel N →L[ℂ] ComplexModel N) ∘L (ContinuousLinearMap.id ℂ _ - c w)
    have hDc : Continuous Dc := continuous_const.clm_comp (continuous_const.sub c.continuous)
    have hopen : IsOpen (Dc ⁻¹' range ((↑) : (ComplexModel N ≃L[ℂ] ComplexModel N) → _)) :=
      ContinuousLinearEquiv.isOpen.preimage hDc
    have h0m : (0 : ComplexModel N) ∈ Dc ⁻¹' range ((↑) : (ComplexModel N ≃L[ℂ] ComplexModel N) → _) :=
      ⟨A₂, by ext u; simp [Dc]⟩
    filter_upwards [hopen.mem_nhds h0m] with x hx
    obtain ⟨E', hE'⟩ := hx
    rw [hD x]
    have : ((A₂ : ComplexModel N →L[ℂ] ComplexModel N) ∘L
        (ContinuousLinearMap.id ℂ _ - c x)) = (E' : ComplexModel N →L[ℂ] ComplexModel N) := hE'.symm
    rw [this]
    exact E'.bijective
  · intro p q
    exact (hC2f p q z₀ hz₀ _ hA₂ c hc).trans ((le_abs_self _).trans
      ((Finset.single_le_sum (f := fun q => |C2f p q|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ q)).trans (Finset.single_le_sum
          (f := fun p => ∑ q, |C2f p q|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ p))))
  · intro p q
    exact (hC3f p q z₀ hz₀ _ hA₂ c hc).trans ((le_abs_self _).trans
      ((Finset.single_le_sum (f := fun q => |C3f p q|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ q)).trans (Finset.single_le_sum
          (f := fun p => ∑ q, |C3f p q|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ p))))
  · rw [hD 0]
    refine ContinuousLinearMap.opNorm_le_bound _ hCA0 fun v => ?_
    simp only [map_zero, sub_zero, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact ((A₂ : ComplexModel N →L[ℂ] ComplexModel N).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
  · intro v
    rw [(hasFDerivAt_fderiv_normalCoord z₀ _ c hsymm 0).fderiv]
    simp only [neg_apply, normalCoordSecond_apply, norm_neg]
    calc ‖(A₂ : ComplexModel N →L[ℂ] ComplexModel N) (c v v)‖ ≤ CA * ‖c v v‖ :=
          ((A₂ : ComplexModel N →L[ℂ] ComplexModel N).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
      _ ≤ CA * (CA * ‖v‖ * ‖v‖) := mul_le_mul_of_nonneg_left (hcpx v v) hCA0
      _ = CA * CA * ‖v‖ ^ 2 := by ring
  · -- the Jacobian matrix
    have hJ : HolomorphicMixedDensity.jacobianMatrix Φ 0 =
        lmat (A₁ : ComplexModel N →L[ℂ] ComplexModel N) *
          lmat (Q.toContinuousLinearEquiv : ComplexModel N →L[ℂ] ComplexModel N) := by
      rw [← lmat_comp]
      ext a j
      simp only [HolomorphicMixedDensity.jacobianMatrix, lmat, Matrix.of_apply, hD 0, map_zero,
        sub_zero, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply]
      rfl
    rw [hJ, Matrix.transpose_mul, Matrix.map_mul, ← hQr, hMdef]
    simp only [Matrix.mul_assoc]

end SGPT.Envelopes.TosC11d
