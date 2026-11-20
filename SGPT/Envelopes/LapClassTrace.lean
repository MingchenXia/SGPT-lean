import SGPT.Envelopes.LapClassFlat
import SGPT.Analysis.KahlerNormalUniform
import SGPT.Okounkov.TranscendentalWNRegBeta
import SGPT.Foundations.Analysis.Pending.AubinYauEstimate
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
import SGPT.Foundations.Analysis.Pending.SkodaElMirHolomorphic
import SGPT.Foundations.Analysis.Pending.KahlerPotentialNormalization

/-!
# The trace form of Berman's Laplacian estimate for the penalized equations

Lane LAP-CLASS (`claude-lap-class`, nodes `lap-class:normal-barrier`, `lap-class:trace-estimate`).
Source: Xia, *Foundations of pluripotential theory*, `lem:kahler-trace-laplacian` and
`lem:penalized-equation-trace` (chapter q10), in the case where the background of the envelope is
the Kähler form `ω` that also measures the Laplacian (SGPT `prop:DR16_C11bar`).

Let `Y` be a compact connected complex manifold of dimension `N` with a Kähler background `A`, and
let `Δ = Δ_A` be its Laplacian (TN `KahlerLaplacianChart.laplacian`,
`Δu = Re tr(H⁻¹ (∂∂̄u))`, `H` the coefficient matrix of `A`).  For a β-solution `u` of
`(A + ddᶜu)^N = e^{β(u - F)} A^N` the trace `tr_A(A + ddᶜu) = N + Δu` is controlled by an *upper
bound of `ΔF` alone*:

* `betaSolution_trace_le`: there are `a ≥ 0`, `β₀ > 0` depending only on `(Y, A)` such that for
  `β ≥ β₀`, every chart-smooth `F` with `ΔF ≤ S`, every β-solution `u` and every `m ≤ u`,
  `N + Δu ≤ 2(N + S) e^{a(u - m)}`.

This is the estimate needed for obstacles with bounded metric Laplacian, whose complex Hessian is
not bounded (FPT `ex:metric-laplacian-unbounded-hessian`); the library's Berman estimate
(`betaSolution_line_le`) uses a one-sided bound for the whole complex Hessian of `F`.

## Proof

At a maximum point `y₀` of `log(N + Δu) - a u` we use Kähler normal coordinates for `A`
(`Φ(w) = z₀ + L(w - ½c(w,w))`, lane TOS-C11), in which the coefficient matrix `h̃` of `A` is `1` at
`0` with vanishing first derivatives and second derivatives bounded uniformly in `y₀`.  By
Taylor's formula `h̃(w) ≤ (1 + K‖w‖²)·1` near `0` (`exists_normal_barrier`), hence
`N + Δu ≥ (1 - K‖w‖²) tr G̃` (`one_sub_mul_re_trace_le`), `G̃` the complex Hessian of a local
potential of `A + ddᶜu` in the coordinates `w`.  So `log tr G̃ - 2K‖w‖² - a u` has a local maximum
at `0`, and the flat maximum principle step (`levTr_le_of_isLocalMax`) applies; the determinant
term `∑ₚ(log det G̃)_{pp̄}(0)` is bounded below using the equation, the plurisubharmonicity of
`log|det DΦ|²` and the uniform bounds of `log det` of the local potential of `A`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Analysis.KahlerNormal

/-! ### Normal coordinates with a quadratic barrier -/

section Barrier

variable {N : ℕ}

/-- The evaluation of a field of two-forms at two fixed vectors has vanishing derivative where
the field does. -/
theorem fderiv_apply_eq_zero {a : ComplexModel N → CoordinateRealTwoForm N} {x : ComplexModel N}
    (ha : HasFDerivAt a (0 : ComplexModel N →L[ℝ] CoordinateRealTwoForm N) x)
    (u v : ComplexModel N) : fderiv ℝ (fun w => a w ![u, v]) x = 0 := by
  have h := (ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ ![u, v]).hasFDerivAt.comp x ha
  rw [ContinuousLinearMap.comp_zero] at h
  exact h.fderiv

/-- **Normal coordinates with a quadratic barrier** (FPT `lem:kahler-normal-coordinates-uniform`
and Taylor's formula).  For a Kähler form `κ`, a chart `e` and a compact `K ⊆ e(target)` there are
`C_A, K_b ≥ 0` such that every `z₀ ∈ K` is the centre of normal coordinates
`Φ = normalCoord z₀ L c` (`c` symmetric) with `‖L‖ ≤ C_A`, coefficient matrix `1` at `0`, and
`h̃(w) ≤ (1 + K_b‖w‖²)·1` for `w` near `0`. -/
theorem exists_normal_barrier {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
    [IsComplexManifold N M] {κ : SmoothRealForm N M 2} (hκ : κ.IsKahler) (e : ComplexChart N M)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ CA Kb : ℝ, 0 ≤ CA ∧ 0 ≤ Kb ∧ ∀ z₀ ∈ K, ∃ (L : ComplexModel N ≃L[ℂ] ComplexModel N)
      (c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N),
      (∀ p u, c p u = c u p) ∧ (∀ x, ‖L x‖ ≤ CA * ‖x‖) ∧
      normalizedHermitianMatrix
        (pullbackField (normalCoord z₀ (L : ComplexModel N →L[ℂ] ComplexModel N) c)
          (κ.coeff e) 0) = 1 ∧
      ∀ᶠ w in 𝓝 (0 : ComplexModel N), ∀ v : Fin N → ℂ,
        (star v ⬝ᵥ (normalizedHermitianMatrix
          (pullbackField (normalCoord z₀ (L : ComplexModel N →L[ℂ] ComplexModel N) c)
            (κ.coeff e) w) *ᵥ v)).re ≤ (1 + Kb * ‖w‖ ^ 2) * (star v ⬝ᵥ v).re := by
  classical
  obtain ⟨⟨C0, hC0, hb⟩, hder⟩ := kahlerNormal_uniform_of_isKahler hκ e hK hKt
  -- the vector pairs giving the entries of the coefficient matrix
  set vec : Fin N → Fin N → Fin 2 → ComplexModel N × ComplexModel N := fun j k t =>
    if t = 0 then (coordinateVector j, Complex.I • coordinateVector k)
    else (coordinateVector j, coordinateVector k) with hvec
  choose C₂ hC₂ using fun (jkt : Fin N × Fin N × Fin 2) =>
    hder 2 (vec jkt.1 jkt.2.1 jkt.2.2).1 (vec jkt.1 jkt.2.1 jkt.2.2).2
  set Ct : ℝ := ∑ jkt, |C₂ jkt| with hCt
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₂le : ∀ jkt, C₂ jkt ≤ Ct := fun jkt =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun jkt => |C₂ jkt|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ jkt))
  refine ⟨C0, 2 * Real.pi * N * (Ct + 1), hC0, by positivity, fun z₀ hz₀ => ?_⟩
  have hz₀t : z₀ ∈ e.val.target := hKt hz₀
  set a := κ.coeff e with hadef
  obtain ⟨L, hL⟩ := exists_normalizing_linear (hκ.1 e z₀ hz₀t).1 (hκ.1 e z₀ hz₀t).2
  set L' := (L : ComplexModel N →L[ℂ] ComplexModel N) with hL'def
  have ha0 : DifferentiableAt ℝ a z₀ :=
    ((κ.smooth e).contDiffAt (e.val.open_target.mem_nhds hz₀t)).differentiableAt (by simp)
  have h11ev : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z) :=
    Filter.mem_of_superset (e.val.open_target.mem_nhds hz₀t) fun z hz => (hκ.1 e z hz).1
  set β := normalizedDeriv a z₀ L'
  have hβ11 := normalizedDeriv_isOneOne ha0 h11ev L'
  set c := normalQuad β hβ11 with hcdef
  have hc : ∀ p u v, inner ℂ v (c p u) = (Real.pi : ℂ) * dHol β p u v := fun p u v =>
    inner_quadFun β p u v
  obtain ⟨hsymm, h0, hd⟩ := kahlerNormal_of_normalizing z₀ L' c ha0 h11ev (hκ.2 e z₀ hz₀t) hL hc
  refine ⟨L, c, hsymm, fun x => ?_, by rw [h0, normalizedHermitianMatrix_flatForm], ?_⟩
  · exact (L'.le_opNorm x).trans (mul_le_mul_of_nonneg_right ((hb z₀ hz₀ L' hL).1)
      (norm_nonneg x))
  -- the scalar coefficients `g_{uv}(w) = (Φ^*a)(w)(u, v)`
  set Φ := normalCoord z₀ L' c with hΦdef
  obtain ⟨cR, hcR⟩ : ∃ cR : ComplexModel N →L[ℝ] ComplexModel N →L[ℝ] ComplexModel N,
      ∀ p x, cR p x = c p x :=
    ⟨ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel N) (ComplexModel N) ℝ ℝ ∘L
      c.restrictScalars ℝ, fun p x => rfl⟩
  set x₀ : NormalData N := (z₀, L'.restrictScalars ℝ, cR) with hx₀
  have hfun : ∀ u v : ComplexModel N, (fun w => pullbackField Φ a w ![u, v]) =
      fun w => normalCoeffFun a u v (x₀, w) := by
    intro u v
    funext w
    have hhalf : ((1 / 2 : ℂ)) • c w w = (1 / 2 : ℝ) • c w w := by
      rw [← Complex.coe_smul]; norm_num
    rw [pullbackField, fderiv_normalCoord z₀ L' c hsymm, compContinuousLinearMap_apply_two]
    simp only [normalCoeffFun, normalPoint, hΦdef, normalCoord, hcR, hx₀,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      _root_.sub_apply, ContinuousLinearMap.id_apply, hhalf]
  have hO : IsOpen {y : NormalData N × ComplexModel N | normalPoint y.1 y.2 ∈ e.val.target} :=
    e.val.open_target.preimage contDiff_normalPoint.continuous
  have hcd : ∀ u v : ComplexModel N, ContDiffAt ℝ 2 (fun w => pullbackField Φ a w ![u, v]) 0 := by
    intro u v
    rw [hfun u v]
    have hmem : ((x₀, (0 : ComplexModel N)) : NormalData N × ComplexModel N) ∈
        {y : NormalData N × ComplexModel N | normalPoint y.1 y.2 ∈ e.val.target} := by
      simpa [normalPoint, hx₀] using hz₀t
    have h1 : ContDiffAt ℝ ∞ (normalCoeffFun a u v) (x₀, 0) :=
      (contDiffOn_normalCoeffFun (κ.smooth e) u v).contDiffAt (hO.mem_nhds hmem)
    have h2 : ContDiffAt ℝ ∞ (fun w : ComplexModel N => (x₀, w)) 0 :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (h1.comp (0 : ComplexModel N) h2).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  -- Taylor's formula for each entry
  have htaylor : ∀ jkt : Fin N × Fin N × Fin 2, ∀ᶠ w in 𝓝 (0 : ComplexModel N),
      |pullbackField Φ a w ![(vec jkt.1 jkt.2.1 jkt.2.2).1, (vec jkt.1 jkt.2.1 jkt.2.2).2] -
        pullbackField Φ a 0 ![(vec jkt.1 jkt.2.1 jkt.2.2).1, (vec jkt.1 jkt.2.1 jkt.2.2).2]| ≤
          (Ct + 1) * ‖w‖ ^ 2 := by
    intro jkt
    set u := (vec jkt.1 jkt.2.1 jkt.2.2).1
    set v := (vec jkt.1 jkt.2.1 jkt.2.2).2
    have hD : fderiv ℝ (fun w => pullbackField Φ a w ![u, v]) 0 = 0 :=
      fderiv_apply_eq_zero hd u v
    have hD2 : ‖fderiv ℝ (fderiv ℝ (fun w => pullbackField Φ a w ![u, v])) 0‖ ≤ Ct := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact (hC₂ jkt z₀ hz₀ L' hL c hc).trans (hC₂le jkt)
    have h := norm_sub_le_of_fderiv_eq_zero (hcd u v) hD hD2
    filter_upwards [h] with w hw
    rw [sub_zero, Real.norm_eq_abs] at hw
    exact hw
  have hall := Filter.eventually_all.mpr htaylor
  filter_upwards [hall] with w hw v
  -- the entries of `h̃(w) - 1`
  set Hw := normalizedHermitianMatrix (pullbackField Φ a w) with hHw
  have h0' : normalizedHermitianMatrix (pullbackField Φ a 0) = 1 := by
    rw [h0, normalizedHermitianMatrix_flatForm]
  have hentry : ∀ j k, ‖Hw j k - (1 : Matrix (Fin N) (Fin N) ℂ) j k‖ ≤
      2 * Real.pi * (Ct + 1) * ‖w‖ ^ 2 := by
    intro j k
    rw [← h0']
    have e1 := hw (j, k, 0)
    have e2 := hw (j, k, 1)
    simp only [hvec, if_pos rfl, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at e1 e2
    simp only [hHw, normalizedHermitianMatrix]
    have : (Real.pi : ℂ) * ((pullbackField Φ a w ![coordinateVector j,
        Complex.I • coordinateVector k] : ℂ) - Complex.I * (pullbackField Φ a w
          ![coordinateVector j, coordinateVector k] : ℂ)) -
        (Real.pi : ℂ) * ((pullbackField Φ a 0 ![coordinateVector j,
        Complex.I • coordinateVector k] : ℂ) - Complex.I * (pullbackField Φ a 0
          ![coordinateVector j, coordinateVector k] : ℂ)) =
        (Real.pi : ℂ) * (((pullbackField Φ a w ![coordinateVector j,
          Complex.I • coordinateVector k] - pullbackField Φ a 0 ![coordinateVector j,
          Complex.I • coordinateVector k] : ℝ) : ℂ) - Complex.I *
          ((pullbackField Φ a w ![coordinateVector j, coordinateVector k] -
            pullbackField Φ a 0 ![coordinateVector j, coordinateVector k] : ℝ) : ℂ)) := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hsub : ‖((pullbackField Φ a w ![coordinateVector j,
          Complex.I • coordinateVector k] - pullbackField Φ a 0 ![coordinateVector j,
          Complex.I • coordinateVector k] : ℝ) : ℂ) - Complex.I *
          ((pullbackField Φ a w ![coordinateVector j, coordinateVector k] -
            pullbackField Φ a 0 ![coordinateVector j, coordinateVector k] : ℝ) : ℂ)‖ ≤
        2 * ((Ct + 1) * ‖w‖ ^ 2) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      linarith
    calc Real.pi * ‖_‖ ≤ Real.pi * (2 * ((Ct + 1) * ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsub Real.pi_pos.le
      _ = 2 * Real.pi * (Ct + 1) * ‖w‖ ^ 2 := by ring
  -- the quadratic form
  set ε := 2 * Real.pi * (Ct + 1) * ‖w‖ ^ 2 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hdiff : star v ⬝ᵥ (Hw *ᵥ v) = star v ⬝ᵥ v +
      ∑ j, ∑ k, star (v j) * ((Hw j k - (1 : Matrix (Fin N) (Fin N) ℂ) j k) * v k) := by
    have hsplit : Hw = 1 + (Hw - 1) := by abel
    conv_lhs => rw [hsplit]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    congr 1
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Matrix.sub_apply]
  have hbound : (∑ j, ∑ k, star (v j) * ((Hw j k - (1 : Matrix (Fin N) (Fin N) ℂ) j k) *
      v k)).re ≤ ε * N * (star v ⬝ᵥ v).re := by
    have hre : (star v ⬝ᵥ v).re = ∑ j, ‖v j‖ ^ 2 := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
    have h1 : (∑ j, ∑ k, star (v j) * ((Hw j k - (1 : Matrix (Fin N) (Fin N) ℂ) j k) *
        v k)).re ≤ ∑ j, ∑ k, ε * (‖v j‖ * ‖v k‖) := by
      refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ => ?_)))
      rw [norm_mul, norm_mul, norm_star]
      have := hentry j k
      have h0 : 0 ≤ ‖v j‖ := norm_nonneg _
      have h0' : 0 ≤ ‖v k‖ := norm_nonneg _
      nlinarith [mul_nonneg h0 h0']
    have h2 : ∑ j, ∑ k, ε * (‖v j‖ * ‖v k‖) = ε * (∑ j, ‖v j‖) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    have h3 : (∑ j, ‖v j‖) ^ 2 ≤ N * ∑ j, ‖v j‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
        (f := fun j => ‖v j‖)
      simpa using this
    rw [hre]
    calc _ ≤ ∑ j, ∑ k, ε * (‖v j‖ * ‖v k‖) := h1
      _ = ε * (∑ j, ‖v j‖) ^ 2 := h2
      _ ≤ ε * (N * ∑ j, ‖v j‖ ^ 2) := mul_le_mul_of_nonneg_left h3 hε0
      _ = ε * N * ∑ j, ‖v j‖ ^ 2 := by ring
  have hfinal : (star v ⬝ᵥ (Hw *ᵥ v)).re ≤ (1 + ε * N) * (star v ⬝ᵥ v).re := by
    rw [hdiff, Complex.add_re]
    linarith
  calc (star v ⬝ᵥ (Hw *ᵥ v)).re ≤ (1 + ε * N) * (star v ⬝ᵥ v).re := hfinal
    _ = (1 + 2 * Real.pi * N * (Ct + 1) * ‖w‖ ^ 2) * (star v ⬝ᵥ v).re := by
      rw [hε]; ring

end Barrier

/-! ### Computations in normal coordinates -/

section Coordinates

variable {N : ℕ}

open HolomorphicMixedDensity

theorem contDiff_normalCoord (z₀ : ComplexModel N) (L : ComplexModel N →L[ℂ] ComplexModel N)
    (c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N) :
    ContDiff ℂ ∞ (normalCoord z₀ L c) := by
  unfold normalCoord
  have h1 : ContDiff ℂ ∞ (fun w : ComplexModel N => c w w) := c.contDiff.clm_apply contDiff_id
  exact contDiff_const.add (L.contDiff.comp (contDiff_id.sub (h1.const_smul (1 / 2 : ℂ))))

/-- The derivative of the normal coordinate map at `w`, as a `ℂ`-linear map. -/
def normalLinear (L : ComplexModel N →L[ℂ] ComplexModel N)
    (c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N) (w : ComplexModel N) :
    ComplexModel N →ₗ[ℂ] ComplexModel N :=
  ((L ∘L (ContinuousLinearMap.id ℂ (ComplexModel N) - c w) :
    ComplexModel N →L[ℂ] ComplexModel N) : ComplexModel N →ₗ[ℂ] ComplexModel N)

theorem normalLinear_apply (L : ComplexModel N →L[ℂ] ComplexModel N)
    (c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N) (w x : ComplexModel N) :
    normalLinear L c w x = L (x - c w x) := rfl

variable (z₀ : ComplexModel N) (L : ComplexModel N →L[ℂ] ComplexModel N)
  {c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N}

theorem fderiv_normalCoord_apply (hc : ∀ p u, c p u = c u p) (w x : ComplexModel N) :
    fderiv ℝ (normalCoord z₀ L c) w x = normalLinear L c w x := by
  rw [fderiv_normalCoord z₀ L c hc w]
  rfl

theorem pullbackField_eq_compLinearMap (hc : ∀ p u, c p u = c u p)
    (a : ComplexModel N → CoordinateRealTwoForm N) (w : ComplexModel N) :
    pullbackField (normalCoord z₀ L c) a w =
      compLinearMap (a (normalCoord z₀ L c w)) (normalLinear L c w) := by
  rw [pullbackField]
  congr 1
  refine ContinuousLinearMap.ext fun x => ?_
  exact fderiv_normalCoord_apply z₀ L hc w x

theorem standardMatrix_normalLinear (hc : ∀ p u, c p u = c u p) (w : ComplexModel N) :
    standardMatrix (normalLinear L c w) = jacobianMatrix (normalCoord z₀ L c) w := by
  ext p j
  rw [standardMatrix_apply, jacobianMatrix, Matrix.of_apply, fderiv_normalCoord_apply z₀ L hc]

theorem contDiff_det_jacobianMatrix (hc : ∀ p u, c p u = c u p) :
    ContDiff ℂ ∞ (fun w => (jacobianMatrix (normalCoord z₀ L c) w).det) := by
  have hentry : ∀ a j : Fin N,
      ContDiff ℂ ∞ (fun w => jacobianMatrix (normalCoord z₀ L c) w a j) := by
    intro a j
    have hfun : (fun w => jacobianMatrix (normalCoord z₀ L c) w a j) = fun w =>
        (EuclideanSpace.proj a : ComplexModel N →L[ℂ] ℂ)
          (L (coordinateVector j - (c.flip (coordinateVector j)) w)) := by
      funext w
      rw [jacobianMatrix, Matrix.of_apply, fderiv_normalCoord_apply z₀ L hc, normalLinear_apply]
      rfl
    rw [hfun]
    exact (EuclideanSpace.proj a : ComplexModel N →L[ℂ] ℂ).contDiff.comp
      (L.contDiff.comp (contDiff_const.sub (c.flip (coordinateVector j)).contDiff))
  simp_rw [WirtingerLogDet.det_eq_sum]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hentry _ _)

theorem isUnit_det_jacobianMatrix_zero (hc : ∀ p u, c p u = c u p)
    (Le : ComplexModel N ≃L[ℂ] ComplexModel N) (hL : (Le : ComplexModel N →L[ℂ] ComplexModel N) = L) :
    IsUnit (jacobianMatrix (normalCoord z₀ L c) 0).det := by
  rw [← standardMatrix_normalLinear z₀ L hc, det_standardMatrix]
  have h : normalLinear L c 0 = (Le.toLinearEquiv : ComplexModel N →ₗ[ℂ] ComplexModel N) := by
    ext x
    rw [normalLinear_apply, map_zero, _root_.zero_apply, sub_zero, ← hL]
    rfl
  rw [h]
  exact LinearEquiv.isUnit_det' _

/-- The complex Hessian along the normal coordinate map. -/
theorem complexHessian_comp_normalCoord {p : ComplexModel N → ℝ} {V : Set (ComplexModel N)}
    (hV : IsOpen V) (hp : ContDiffOn ℝ 2 p V) {w : ComplexModel N}
    (hw : normalCoord z₀ L c w ∈ V) :
    complexHessian (fun x => p (normalCoord z₀ L c x)) w =
      (jacobianMatrix (normalCoord z₀ L c) w)ᵀ * complexHessian p (normalCoord z₀ L c w) *
        (jacobianMatrix (normalCoord z₀ L c) w).map (starRingEnd ℂ) :=
  HolomorphicHessianTwo.complexHessian_comp_holomorphic_two
    (hV.preimage (contDiff_normalCoord z₀ L c).continuous) hV
    (contDiff_normalCoord z₀ L c).contDiffOn hp (fun _ hx => hx) hw

end Coordinates

/-! ### Matrix facts -/

section Matrices

variable {N : ℕ}

theorem posDef_transpose_mul_mul_conj {H J : Matrix (Fin N) (Fin N) ℂ} (hH : H.PosDef)
    (hJ : IsUnit J.det) : (Jᵀ * H * J.map (starRingEnd ℂ)).PosDef := by
  have hconj : (J.map (starRingEnd ℂ))ᴴ = Jᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hinj : Function.Injective (J.map (starRingEnd ℂ)).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  have h := hH.conjTranspose_mul_mul_same hinj
  rwa [hconj] at h

theorem re_det_transpose_mul_mul_conj {H J : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    (Jᵀ * H * J.map (starRingEnd ℂ)).det.re = ‖J.det‖ ^ 2 * H.det.re := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← WirtingerLogDet.ofReal_re_det_of_isHermitian hH]
  rw [mul_comm J.det, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast
  ring

/-- `Re tr(P K) > 0` for positive definite `P`, `K` of positive size. -/
theorem re_trace_mul_pos {P K : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) (hP : P.PosDef)
    (hK : K.PosDef) : 0 < (P * K).trace.re := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hK.posSemidef
  have hterm : ∀ i, 0 ≤ (P * vecMulVec (v i) (star (v i))).trace.re := fun i => by
    rw [AubinYauLocalStep.trace_mul_vecMulVec]
    exact hP.posSemidef.re_dotProduct_nonneg _
  rw [hv, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  by_contra hle
  push Not at hle
  have hzero : ∀ i, (P * vecMulVec (v i) (star (v i))).trace.re = 0 := fun i =>
    le_antisymm ((Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)).trans hle)
      (hterm i)
  have hvi : ∀ i, v i = 0 := by
    intro i
    have h := hzero i
    rw [AubinYauLocalStep.trace_mul_vecMulVec] at h
    by_contra hne
    exact (hP.re_dotProduct_pos hne).ne' h
  have hK0 : K = 0 := by
    rw [hv]
    simp [hvi]
  have hne : (Pi.single (⟨0, hN⟩ : Fin N) (1 : ℂ) : Fin N → ℂ) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hN⟩
    simp at this
  have h := hK.re_dotProduct_pos hne
  rw [hK0] at h
  simp at h

end Matrices

/-! ### The trace estimate -/

section Estimate

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

open KahlerLaplacianChart HolomorphicMixedDensity SGPT.Okounkov.TranscendentalWNReg
open AubinYauEstimate AubinYauUniformConstants ManifoldTubePositivity

theorem chartSmooth_two {u : Y → ℝ} (hu : ChartSmooth (n := N) u) :
    ∀ e : ComplexChart N Y, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target :=
  fun e => (hu e).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The coefficient matrix of `A + ddᶜu` is that of `A` plus the complex Hessian of `u`. -/
theorem normalizedHermitianMatrix_add_ddc (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) :
    normalizedHermitianMatrix ((A.form + ddcClosedForm u hu).val.coeff e z) =
      normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun w => u (e.val.symm w)) z := by
  rw [ClosedRealOneOneForm.coeff_add, normalizedHermitianMatrix_add, ddcClosedForm_coeff,
    normalizedHermitianMatrix_smoothDDC
      (contDiffAt_two_of_contDiffOn e.val.open_target (hu e) hz)]

/-- `tr_A(A + ddᶜu) = N + Δu` is positive when `A + ddᶜu` is Kähler. -/
theorem add_laplacian_pos (hN : 0 < N) (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (hK : (A.form + ddcClosedForm u hu).val.IsKahler) (y : Y) :
    0 < (N : ℝ) + laplacian A.form.val u y := by
  set e := complexChartAt (n := N) y
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  rw [laplacian_eq A.isKahler.1 (chartSmooth_two hu) hy, chartLaplacian]
  have hH := posDef_coeff A.isKahler.1 hz
  have hK' := posDef_coeff hK.1 hz
  rw [normalizedHermitianMatrix_add_ddc A hu hz] at hK'
  have h := re_trace_mul_pos hN hH.inv hK'
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.trace_one] at h
  simpa using h

theorem levTr_sub {f g : ComplexModel N → ℝ} {x : ComplexModel N} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) : levTr (fun y => f y - g y) x = levTr f x - levTr g x := by
  simp only [levTr, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hf hg _

theorem log_one_sub_ge {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    -(2 * δ) ≤ Real.log (1 - δ) := by
  have hpos : 0 < 1 - δ := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : -(2 * δ) ≤ 1 - (1 - δ)⁻¹ := by
    rw [show 1 - (1 - δ)⁻¹ = -(δ / (1 - δ)) by field_simp; ring, neg_le_neg_iff,
      div_le_iff₀ hpos]
    nlinarith
  linarith

/-! #### The complex Hessian and the Laplacian in normal coordinates -/

/-- The complex Hessian of a local potential of `κ` in normal coordinates is the coefficient matrix
of the pulled-back form. -/
theorem complexHessian_comp_potential (z₀ : ComplexModel N)
    (L : ComplexModel N →L[ℂ] ComplexModel N)
    {c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N}
    {κ : SmoothRealForm N Y 2} (hκ : κ.IsKahler) {E : ComplexChart N Y}
    {V : Set (ComplexModel N)} (hVo : IsOpen V) (hVt : V ⊆ E.val.target)
    {ρ' : ComplexModel N → ℝ} (hρ' : ContDiffOn ℝ 2 ρ' V)
    (hρV : ∀ z ∈ V, complexHessian ρ' z = normalizedHermitianMatrix (κ.coeff E z))
    (hc : ∀ p u, c p u = c u p) {w : ComplexModel N} (hw : normalCoord z₀ L c w ∈ V) :
    complexHessian (fun x => ρ' (normalCoord z₀ L c x)) w =
      normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (κ.coeff E) w) := by
  rw [complexHessian_comp_normalCoord z₀ L hVo hρ' hw, hρV _ hw,
    pullbackField_eq_compLinearMap z₀ L hc,
    normalizedHermitianMatrix_compLinearMap (hκ.1 E _ (hVt hw)).1,
    standardMatrix_normalLinear z₀ L hc]

/-- **The Laplacian in normal coordinates**: `Δ_g v = Re tr(h̃⁻¹ Hess_ℂ(v ∘ Φ))`, `h̃` the complex
Hessian of a local potential of `g` in the coordinates `w`. -/
theorem laplacian_normalCoord (z₀ : ComplexModel N) (L : ComplexModel N →L[ℂ] ComplexModel N)
    {c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N}
    {g : SmoothRealForm N Y 2} (hg : g.IsHermitian) {E : ComplexChart N Y}
    {V : Set (ComplexModel N)} (hVo : IsOpen V) (hVt : V ⊆ E.val.target)
    {ρ' : ComplexModel N → ℝ} (hρ' : ContDiffOn ℝ 2 ρ' V)
    (hρV : ∀ z ∈ V, complexHessian ρ' z = normalizedHermitianMatrix (g.coeff E z))
    {v : Y → ℝ} (hv : ChartSmooth (n := N) v) {w : ComplexModel N}
    (hw : normalCoord z₀ L c w ∈ V)
    (hJ : IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det) :
    laplacian g v (E.val.symm (normalCoord z₀ L c w)) =
      ((complexHessian (fun x => ρ' (normalCoord z₀ L c x)) w)⁻¹ *
        complexHessian (fun x => v (E.val.symm (normalCoord z₀ L c x))) w).trace.re := by
  have hzt := hVt hw
  rw [laplacian_eq hg (chartSmooth_two hv) (E.val.map_target hzt), E.val.right_inv hzt,
    chartLaplacian, complexHessian_comp_normalCoord z₀ L hVo hρ' hw, hρV _ hw,
    complexHessian_comp_normalCoord z₀ L E.val.open_target (chartSmooth_two hv E) hzt,
    trace_inv_mul_congr hJ]

/-- The pullback of the constants `-K₁ ‖ζ‖² ≤ (log det ρ')_{ζζ̄}` along a linear map of norm
`≤ C_A`. -/
theorem neg_le_leviForm_of_norm_le {f : ComplexModel N → ℝ} {z : ComplexModel N} {K₁ CA : ℝ}
    (hK₁ : 0 ≤ K₁) (hf : ∀ ζ : ComplexModel N, ‖ζ‖ ≤ 1 → -K₁ ≤ leviForm f z ζ)
    {ζ : ComplexModel N} (hζ : ‖ζ‖ ≤ CA) : -(K₁ * CA ^ 2) ≤ leviForm f z ζ := by
  rcases eq_or_ne ζ 0 with h0 | h0
  · rw [h0, leviForm_zero]
    have : 0 ≤ K₁ * CA ^ 2 := by positivity
    linarith
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr h0
  have hunit : ‖‖ζ‖⁻¹ • ζ‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hb := hf (‖ζ‖⁻¹ • ζ) hunit
  have hscale : ζ = ‖ζ‖ • (‖ζ‖⁻¹ • ζ) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hscale, KahlerPotentialNormalization.leviForm_smul_right]
  have hsq : ‖ζ‖ ^ 2 ≤ CA ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  nlinarith [sq_nonneg ‖ζ‖]

/-- `log |det J|²` of a holomorphic Jacobian determinant is plurisubharmonic. -/
theorem levTr_log_normSq_nonneg {d : ComplexModel N → ℂ} (hd : ContDiff ℂ ∞ d)
    (hd0 : d 0 ≠ 0) : 0 ≤ levTr (fun w => Real.log (‖d w‖ ^ 2)) 0 := by
  set e₀ : ComplexModel 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℂ) with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  have hYd : ∀ᶠ y in 𝓝 (0 : ComplexModel N), DifferentiableAt ℂ (fun w => d w • e₀) y :=
    Filter.Eventually.of_forall fun y => ((hd.differentiable (by simp)) y).smul_const e₀
  have hY0 : d 0 • e₀ ≠ 0 :=
    smul_ne_zero hd0 (by rw [← norm_ne_zero_iff, he₀n]; exact one_ne_zero)
  have hfun : (fun y => Real.log (‖d y • e₀‖ ^ 2)) = fun w => Real.log (‖d w‖ ^ 2) := by
    funext y
    rw [norm_smul, he₀n, mul_one]
  refine Finset.sum_nonneg fun q _ => ?_
  have h := SkodaElMirHolomorphic.leviForm_log_normSq_nonneg_of_holo (fun w => d w • e₀) hYd hY0
    (coordinateVector q)
  rwa [hfun] at h

/-! #### The bound at a maximum point -/

/-- **The trace bound at the maximum point** of `log(N + Δu) - a u`, in normal coordinates centred
there (FPT `lem:penalized-equation-trace`, Steps 2–3). -/
theorem trace_le_of_isMax (hN : 0 < N) (A : KahlerBackground N Y) {β : ℝ} {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) (U : BetaSolution A β F) {E : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val E W ρ) {ρ' u' : ComplexModel N → ℝ}
    (hρ' : ContDiff ℝ ∞ ρ') (hu' : ContDiff ℝ ∞ u') {V : Set (ComplexModel N)}
    (hVo : IsOpen V) (hVW : V ⊆ W) (hρ'eq : EqOn ρ' ρ V)
    (hu'eq : EqOn u' (fun w => ρ w + U.u (E.val.symm w)) V) {z₀ : ComplexModel N}
    (hz₀ : z₀ ∈ V) {K₁ CA Kb a S : ℝ} (hK₁ : 0 ≤ K₁) (hKb : 0 ≤ Kb)
    (hlog : ∀ ζ : ComplexModel N, ‖ζ‖ ≤ 1 →
      -K₁ ≤ leviForm (fun y => Real.log (complexHessian ρ' y).det.re) z₀ ζ)
    (L : ComplexModel N →L[ℂ] ComplexModel N)
    {c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N}
    (hsymm : ∀ p u, c p u = c u p) (hLbd : ∀ x, ‖L x‖ ≤ CA * ‖x‖)
    (hJ0 : IsUnit (jacobianMatrix (normalCoord z₀ L c) 0).det)
    (h0 : normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (A.form.val.coeff E) 0) = 1)
    (hbar : ∀ᶠ w in 𝓝 (0 : ComplexModel N), ∀ v : Fin N → ℂ,
      (star v ⬝ᵥ (normalizedHermitianMatrix
        (pullbackField (normalCoord z₀ L c) (A.form.val.coeff E) w) *ᵥ v)).re ≤
          (1 + Kb * ‖w‖ ^ 2) * (star v ⬝ᵥ v).re)
    (hFS : ∀ y, laplacian A.form.val F y ≤ S) (ha : 2 * Kb + K₁ * N * CA ^ 2 ≤ a)
    (hβ : 2 * a * N < β)
    (hmax : ∀ y, Real.log (N + laplacian A.form.val U.u y) - a * U.u y ≤
      Real.log (N + laplacian A.form.val U.u (E.val.symm z₀)) - a * U.u (E.val.symm z₀)) :
    (N : ℝ) + laplacian A.form.val U.u (E.val.symm z₀) ≤ 2 * (N + S) := by
  classical
  have hg : A.form.val.IsHermitian := A.isKahler.1
  have hVt : V ⊆ E.val.target := hVW.trans hpot.2.1
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  -- Hessians of the local potentials
  have hρ2 : ∀ z ∈ V, ContDiffAt ℝ 2 ρ z := fun z hz =>
    contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 (hVW hz)
  have hHρ0 : ∀ z ∈ V, complexHessian ρ z = normalizedHermitianMatrix (A.form.val.coeff E z) := by
    intro z hz
    rw [← normalizedHermitianMatrix_smoothDDC (hρ2 z hz), hpot.2.2.2 (hVW hz)]
  have hHρ : ∀ z ∈ V, complexHessian ρ' z = normalizedHermitianMatrix (A.form.val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρ'eq), hHρ0 z hz]
  have hHu : ∀ z ∈ V, complexHessian u' z =
      normalizedHermitianMatrix ((A.form + ddcClosedForm U.u U.smooth).val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hu'eq),
      normalizedHermitianMatrix_add_ddc A U.smooth (hVt hz), ← hHρ0 z hz]
    exact AubinYauLocalStep.complexHessian_fun_add (hρ2 z hz)
      (contDiffAt_two_of_contDiffOn E.val.open_target (U.smooth E) (hVt hz))
  have hρ'V : ContDiffOn ℝ 2 ρ' V := hρ'.contDiffOn.of_le h2
  have hu'V : ContDiffOn ℝ 2 u' V := hu'.contDiffOn.of_le h2
  -- the normal coordinate map
  have hΦ0 : normalCoord z₀ L c 0 = z₀ := normalCoord_zero z₀ L c
  have hΦc : ContDiff ℂ ∞ (normalCoord z₀ L c) := contDiff_normalCoord z₀ L c
  have hΦcR : ContDiff ℝ ∞ (normalCoord z₀ L c) := hΦc.restrict_scalars ℝ
  have hU₀ : IsOpen (normalCoord z₀ L c ⁻¹' V) := hVo.preimage hΦcR.continuous
  have h0U₀ : (0 : ComplexModel N) ∈ normalCoord z₀ L c ⁻¹' V := by
    show normalCoord z₀ L c 0 ∈ V
    rw [hΦ0]; exact hz₀
  have hdetJc : ContDiff ℂ ∞ (fun w => (jacobianMatrix (normalCoord z₀ L c) w).det) :=
    contDiff_det_jacobianMatrix z₀ L hsymm
  have hevJ : ∀ᶠ w in 𝓝 (0 : ComplexModel N),
      IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det := by
    filter_upwards [hdetJc.continuous.continuousAt.eventually_ne hJ0.ne_zero] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  -- the functions in the coordinates `w`
  obtain ⟨σt, hσt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => ρ' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ψt, hψt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => u' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ut, hut⟩ : ∃ f : ComplexModel N → ℝ,
      f = fun x => U.u (E.val.symm (normalCoord z₀ L c x)) := ⟨_, rfl⟩
  obtain ⟨Ft, hFt⟩ : ∃ f : ComplexModel N → ℝ,
      f = fun x => F (E.val.symm (normalCoord z₀ L c x)) := ⟨_, rfl⟩
  have hσs : ContDiff ℝ ∞ σt := by rw [hσt]; exact hρ'.comp hΦcR
  have hψs : ContDiff ℝ ∞ ψt := by rw [hψt]; exact hu'.comp hΦcR
  have hcomp2 : ∀ {v : Y → ℝ}, ChartSmooth (n := N) v → ∀ w,
      normalCoord z₀ L c w ∈ V →
      ContDiffAt ℝ 2 (fun x => v (E.val.symm (normalCoord z₀ L c x))) w := by
    intro v hv w hw
    exact ContDiffAt.comp (g := fun z => v (E.val.symm z)) w
      (contDiffAt_two_of_contDiffOn E.val.open_target (hv E) (hVt hw))
      (hΦcR.contDiffAt.of_le h2)
  have hut2 : ContDiffAt ℝ 2 ut 0 := by rw [hut]; exact hcomp2 U.smooth 0 h0U₀
  have hFt2 : ContDiffAt ℝ 2 Ft 0 := by rw [hFt]; exact hcomp2 hF 0 h0U₀
  -- Hessians in the coordinates `w`
  have hHσJ : ∀ w, normalCoord z₀ L c w ∈ V → complexHessian σt w =
      (jacobianMatrix (normalCoord z₀ L c) w)ᵀ *
        normalizedHermitianMatrix (A.form.val.coeff E (normalCoord z₀ L c w)) *
          (jacobianMatrix (normalCoord z₀ L c) w).map (starRingEnd ℂ) := by
    intro w hw
    rw [hσt, complexHessian_comp_normalCoord z₀ L hVo hρ'V hw, hHρ _ hw]
  have hHσpb : ∀ w, normalCoord z₀ L c w ∈ V → complexHessian σt w =
      normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (A.form.val.coeff E) w) := by
    intro w hw
    rw [hσt]
    exact complexHessian_comp_potential z₀ L A.isKahler hVo hVt hρ'V hHρ hsymm hw
  have hσ0 : complexHessian σt 0 = 1 := by rw [hHσpb 0 h0U₀, h0]
  have hHψJ : ∀ w, normalCoord z₀ L c w ∈ V → complexHessian ψt w =
      (jacobianMatrix (normalCoord z₀ L c) w)ᵀ * complexHessian u' (normalCoord z₀ L c w) *
        (jacobianMatrix (normalCoord z₀ L c) w).map (starRingEnd ℂ) := by
    intro w hw
    rw [hψt]
    exact complexHessian_comp_normalCoord z₀ L hVo hu'V hw
  have hHσpd : ∀ w, normalCoord z₀ L c w ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det → (complexHessian σt w).PosDef := by
    intro w hw hJ
    rw [hHσJ w hw]
    exact posDef_transpose_mul_mul_conj (posDef_coeff hg (hVt hw)) hJ
  have hHψpd : ∀ w, normalCoord z₀ L c w ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det → (complexHessian ψt w).PosDef := by
    intro w hw hJ
    rw [hHψJ w hw, hHu _ hw]
    exact posDef_transpose_mul_mul_conj (posDef_coeff U.isKahler.1 (hVt hw)) hJ
  -- `ψ̃ = σ̃ + ũ` near `0`
  have hψeq : ∀ w, normalCoord z₀ L c w ∈ V → ψt w = σt w + ut w := fun w hw => by
    rw [hψt, hσt, hut]
    simp only
    rw [hu'eq hw, hρ'eq hw]
  have hHψsplit : ∀ w, normalCoord z₀ L c w ∈ V →
      complexHessian ψt w = complexHessian σt w + complexHessian ut w := by
    intro w hw
    have hgerm : ψt =ᶠ[𝓝 w] fun x => σt x + ut x :=
      Filter.eventuallyEq_of_mem (hU₀.mem_nhds hw) hψeq
    rw [complexHessian_congr hgerm]
    have hut2w : ContDiffAt ℝ 2 ut w := by rw [hut]; exact hcomp2 U.smooth w hw
    exact AubinYauLocalStep.complexHessian_fun_add (AubinYauLocalStep.contDiffAt_two hσs w) hut2w
  -- the trace of `A + ddᶜu` in the coordinates `w`
  have hlapσ : ∀ (v : Y → ℝ) (hv : ChartSmooth (n := N) v) (w : ComplexModel N),
      normalCoord z₀ L c w ∈ V → IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det →
      laplacian A.form.val v (E.val.symm (normalCoord z₀ L c w)) =
        ((complexHessian σt w)⁻¹ *
          complexHessian (fun x => v (E.val.symm (normalCoord z₀ L c x))) w).trace.re := by
    intro v hv w hw hJ
    rw [hσt]
    exact laplacian_normalCoord z₀ L hg hVo hVt hρ'V hHρ hv hw hJ
  have hNtr : ∀ w, normalCoord z₀ L c w ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det →
      (N : ℝ) + laplacian A.form.val U.u (E.val.symm (normalCoord z₀ L c w)) =
        ((complexHessian σt w)⁻¹ * complexHessian ψt w).trace.re := by
    intro w hw hJ
    rw [hlapσ U.u U.smooth w hw hJ, ← hut, hHψsplit w hw, Matrix.mul_add, Matrix.trace_add,
      Complex.add_re, Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.mpr (hHσpd w hw hJ).det_pos.ne'), Matrix.trace_one]
    simp
  have hy0 : E.val.symm (normalCoord z₀ L c 0) = E.val.symm z₀ := by rw [hΦ0]
  have hℓ0 : levTr ψt 0 = (N : ℝ) + laplacian A.form.val U.u (E.val.symm z₀) := by
    rw [← hy0, hNtr 0 h0U₀ hJ0, hσ0, inv_one, Matrix.one_mul,
      re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hψs 0)]
  have hℓpos0 : 0 < levTr ψt 0 := hℓ0 ▸ add_laplacian_pos hN A U.smooth U.isKahler _
  -- the local maximum
  have hLs : ContDiff ℝ ∞ (levTr ψt) := by
    have : levTr ψt = fun y => ∑ q, leviForm ψt y (coordinateVector q) := rfl
    rw [this]
    exact ContDiff.sum fun q _ => BlockiLocalEstimate.contDiff_leviForm hψs _
  have hmaxw : IsLocalMax
      (fun w => Real.log (levTr ψt w) - 2 * Kb * ‖w‖ ^ 2 - a * (ψt w - σt w)) 0 := by
    have hevℓ : ∀ᶠ w in 𝓝 (0 : ComplexModel N), 0 < levTr ψt w :=
      continuousAt_const.eventually_lt hLs.continuous.continuousAt hℓpos0
    have hsmall : ∀ᶠ w in 𝓝 (0 : ComplexModel N), Kb * ‖w‖ ^ 2 < 1 / 2 := by
      have hc : Continuous fun w : ComplexModel N => Kb * ‖w‖ ^ 2 := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [hbar, hevJ, hU₀.mem_nhds h0U₀, hevℓ, hsmall] with w hb hJ hwU hℓw hsm
    have hb' : ∀ v : Fin N → ℂ, (star v ⬝ᵥ (complexHessian σt w *ᵥ v)).re ≤
        (1 + Kb * ‖w‖ ^ 2) * (star v ⬝ᵥ v).re := by
      rw [hHσpb w hwU]; exact hb
    have hb1 := one_sub_mul_re_trace_le (hHσpd w hwU hJ) (hHψpd w hwU hJ).posSemidef hb'
    rw [re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hψs w),
      ← hNtr w hwU hJ] at hb1
    have hδ0 : 0 ≤ Kb * ‖w‖ ^ 2 := by positivity
    have hlog1 : Real.log (levTr ψt w) - 2 * (Kb * ‖w‖ ^ 2) ≤
        Real.log ((1 - Kb * ‖w‖ ^ 2) * levTr ψt w) := by
      rw [Real.log_mul (by linarith) hℓw.ne']
      linarith [log_one_sub_ge hδ0 hsm.le]
    have hlog2 : Real.log ((1 - Kb * ‖w‖ ^ 2) * levTr ψt w) ≤
        Real.log ((N : ℝ) + laplacian A.form.val U.u (E.val.symm (normalCoord z₀ L c w))) :=
      Real.log_le_log (mul_pos (by linarith) hℓw) hb1
    have hu_w : U.u (E.val.symm (normalCoord z₀ L c w)) = ψt w - σt w := by
      rw [hψeq w hwU, hut]; ring
    have hu_0 : U.u (E.val.symm z₀) = ψt 0 - σt 0 := by
      rw [hψeq 0 h0U₀, hut]; simp only [hΦ0]; ring
    have hQw := hmax (E.val.symm (normalCoord z₀ L c w))
    show Real.log (levTr ψt w) - 2 * Kb * ‖w‖ ^ 2 - a * (ψt w - σt w) ≤
      Real.log (levTr ψt 0) - 2 * Kb * ‖(0 : ComplexModel N)‖ ^ 2 - a * (ψt 0 - σt 0)
    rw [hℓ0, norm_zero, ← hu_0, ← hu_w]
    nlinarith
  -- the determinant term
  have hdetu' : ∀ z ∈ V, (complexHessian u' z).det.re =
      Real.exp (β * (U.u (E.val.symm z) - F (E.val.symm z))) *
        (complexHessian ρ' z).det.re := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hu'eq),
      complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρ'eq)]
    exact re_det_complexHessian_eq_exp (G := fun y => β * (U.u y - F y)) A U.smooth
      U.density hpot (hVW hz)
  have hdetρpos : ∀ z ∈ V, 0 < (complexHessian ρ' z).det.re := fun z hz => by
    rw [hHρ z hz]
    exact (Complex.pos_iff.mp (posDef_coeff hg (hVt hz)).det_pos).1
  have hdetdecomp : (fun w => Real.log (complexHessian ψt w).det.re) =ᶠ[𝓝 0]
      fun w => Real.log (‖(jacobianMatrix (normalCoord z₀ L c) w).det‖ ^ 2) +
        (β * (ut w - Ft w) +
          Real.log (complexHessian ρ' (normalCoord z₀ L c w)).det.re) := by
    filter_upwards [hevJ, hU₀.mem_nhds h0U₀] with w hJ hwU
    have hherm : (complexHessian u' (normalCoord z₀ L c w)).IsHermitian :=
      complexHessian_isHermitian (AubinYauLocalStep.contDiffAt_two hu' _)
    have hJn : ‖(jacobianMatrix (normalCoord z₀ L c) w).det‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hJ.ne_zero)
    rw [hHψJ w hwU, re_det_transpose_mul_mul_conj hherm, hdetu' _ hwU,
      Real.log_mul hJn (mul_pos (Real.exp_pos _) (hdetρpos _ hwU)).ne',
      Real.log_mul (Real.exp_pos _).ne' (hdetρpos _ hwU).ne', Real.log_exp, hut, hFt]
  have hdetρc : ContDiff ℝ ∞ (fun z => (complexHessian ρ' z).det.re) :=
    Complex.reCLM.contDiff.comp (WirtingerLogDet.contDiff_det_complexHessian hρ')
  have hLρV : ContDiffOn ℝ ∞ (fun z => Real.log (complexHessian ρ' z).det.re) V :=
    hdetρc.contDiffOn.log fun z hz => (hdetρpos z hz).ne'
  have hLρΦ2 : ContDiffAt ℝ 2
      (fun w => Real.log (complexHessian ρ' (normalCoord z₀ L c w)).det.re) 0 := by
    have h1 : ContDiffAt ℝ ∞ (fun z => Real.log (complexHessian ρ' z).det.re)
        (normalCoord z₀ L c 0) := hLρV.contDiffAt (hVo.mem_nhds h0U₀)
    exact (h1.comp (0 : ComplexModel N) hΦcR.contDiffAt).of_le h2
  have hlnJ2 : ContDiffAt ℝ 2
      (fun w => Real.log (‖(jacobianMatrix (normalCoord z₀ L c) w).det‖ ^ 2)) 0 := by
    have h1 : ContDiff ℝ ∞ (fun w => ‖(jacobianMatrix (normalCoord z₀ L c) w).det‖ ^ 2) :=
      (hdetJc.restrict_scalars ℝ).norm_sq ℝ
    exact (h1.contDiffAt.of_le h2).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hJ0.ne_zero))
  have hlnJ0 := levTr_log_normSq_nonneg hdetJc hJ0.ne_zero
  have hLρbound : -(K₁ * N * CA ^ 2) ≤
      levTr (fun w => Real.log (complexHessian ρ' (normalCoord z₀ L c w)).det.re) 0 := by
    have hterm : ∀ q : Fin N, -(K₁ * CA ^ 2) ≤ leviForm
        (fun w => Real.log (complexHessian ρ' (normalCoord z₀ L c w)).det.re) 0
        (coordinateVector q) := by
      intro q
      rw [LeviFormHolomorphicComp.leviForm_comp hU₀ hVo hΦc.contDiffOn hLρV
        (fun _ hx => hx) h0U₀, fderiv_normalCoord_apply z₀ L hsymm, normalLinear_apply,
        map_zero, _root_.zero_apply, sub_zero, hΦ0]
      refine neg_le_leviForm_of_norm_le hK₁ hlog ?_
      have := hLbd (coordinateVector q)
      rwa [show ‖(coordinateVector q : ComplexModel N)‖ = 1 by simp [coordinateVector],
        mul_one] at this
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hterm q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    unfold levTr
    linarith
  have hutr : levTr ut 0 = levTr ψt 0 - N := by
    have h1 : levTr ψt 0 = levTr σt 0 + levTr ut 0 := by
      rw [levTr_congr (Filter.eventuallyEq_of_mem (hU₀.mem_nhds h0U₀) hψeq),
        levTr_add (AubinYauLocalStep.contDiffAt_two hσs 0) hut2]
    have h3 : levTr σt 0 = N := by
      rw [← re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hσs 0), hσ0,
        Matrix.trace_one]
      simp
    linarith
  have hdetlow : β * (levTr ψt 0 - N - levTr Ft 0) - K₁ * N * CA ^ 2 ≤
      levTr (fun w => Real.log (complexHessian ψt w).det.re) 0 := by
    rw [levTr_congr hdetdecomp,
      levTr_add hlnJ2 ((contDiffAt_const.mul (hut2.sub hFt2)).add hLρΦ2),
      levTr_add (contDiffAt_const.mul (hut2.sub hFt2)) hLρΦ2,
      levTr_const_mul (hut2.sub hFt2), levTr_sub hut2 hFt2, hutr]
    linarith
  have hFS0 : levTr Ft 0 ≤ S := by
    rw [← re_trace_complexHessian hFt2]
    have h := hlapσ F hF 0 h0U₀ hJ0
    rw [hσ0, inv_one, Matrix.one_mul, hy0, ← hFt] at h
    rw [← h]
    exact hFS _
  have hfinal := levTr_le_of_isLocalMax hN hψs hσs (hHψpd 0 h0U₀ hJ0) hσ0 hKb
    (by positivity) ha hβ hdetlow hFS0 hmaxw
  rw [← hℓ0]
  exact hfinal

/-- **The trace form of Berman's Laplacian estimate** (FPT `lem:penalized-equation-trace`, the
uniform bound, for the background `κ = ω = A`).  On a compact connected complex manifold `Y` with a
Kähler background `A` there are `a ≥ 0` and `β₀ > 0` such that for every `β ≥ β₀`, every
chart-smooth `F` with `Δ_A F ≤ S`, every β-solution `u` of `(A + ddᶜu)^N = e^{β(u - F)} A^N` and
every lower bound `m ≤ u`: `N + Δ_A u ≤ 2(N + S) e^{a(u - m)}` on `Y`. -/
theorem betaSolution_trace_le [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y) :
    ∃ a β₀ : ℝ, 0 ≤ a ∧ 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ (F : Y → ℝ),
      ChartSmooth (n := N) F → ∀ (S : ℝ), (∀ y, laplacian A.form.val F y ≤ S) →
      ∀ (U : BetaSolution A β F) (m : ℝ), (∀ y, m ≤ U.u y) →
      ∀ y, (N : ℝ) + laplacian A.form.val U.u y ≤ 2 * (N + S) * Real.exp (a * (U.u y - m)) := by
  classical
  have hg : A.form.val.IsHermitian := A.isKahler.1
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨0, 1, le_rfl, one_pos, fun β _ F hF S _ U m _ y => (hY.false y).elim⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨0, 1, le_rfl, one_pos, fun β _ F hF S hFS U m _ y => ?_⟩
    subst hN
    have h0 : ∀ (v : Y → ℝ) x, laplacian A.form.val v x = 0 := fun v x => by
      simp [laplacian, chartLaplacian, Matrix.trace]
    have hS : 0 ≤ S := by have := hFS y; rwa [h0] at this
    rw [h0]
    simp only [Nat.cast_zero, zero_add]
    positivity
  -- the finite atlas of pieces
  choose W ρ ρ' R hR hpot hWball hρ' hρ'eq c₀ C₀ M₀ K₁ hc₀ hC₀ hM₀ hK₁ hbd using
    exists_piece hN A
  have hKt : ∀ p, closedBall ((complexChartAt (n := N) p).val p) (R p) ⊆
      (complexChartAt (n := N) p).val.target := fun p =>
    ((closedBall_subset_closedBall (by linarith [hR p])).trans (hWball p)).trans (hpot p).2.1
  choose CA Kb hCA hKb hnb using fun p =>
    exists_normal_barrier A.isKahler (complexChartAt (n := N) p)
      (isCompact_closedBall ((complexChartAt (n := N) p).val p) (R p)) (hKt p)
  obtain ⟨O, hOdef⟩ : ∃ O : Y → Set Y, O = fun p => (complexChartAt (n := N) p).val.source ∩
      (complexChartAt (n := N) p).val ⁻¹' ball ((complexChartAt (n := N) p).val p) (R p) :=
    ⟨_, rfl⟩
  have hO : ∀ p, IsOpen (O p) := fun p => by
    rw [hOdef]; exact (complexChartAt (n := N) p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p => by
    rw [hOdef]; exact ⟨mem_complexChartAt_source p, mem_ball_self (hR p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = ∑ p ∈ t, (2 * Kb p + K₁ p * N * CA p ^ 2) := ⟨_, rfl⟩
  have hterm0 : ∀ p, 0 ≤ 2 * Kb p + K₁ p * N * CA p ^ 2 := fun p => by
    have := hKb p; have := hK₁ p; positivity
  have ha0 : 0 ≤ a := by rw [hadef]; exact Finset.sum_nonneg fun p _ => hterm0 p
  have hale : ∀ p ∈ t, 2 * Kb p + K₁ p * N * CA p ^ 2 ≤ a := fun p hp => by
    rw [hadef]; exact Finset.single_le_sum (f := fun p => 2 * Kb p + K₁ p * N * CA p ^ 2)
      (fun q _ => hterm0 q) hp
  refine ⟨a, 2 * a * N + 1, ha0, by positivity, ?_⟩
  intro β hβ F hF S hFS U m hm
  have hβ' : 2 * a * N < β := by linarith
  have htrpos : ∀ y, 0 < (N : ℝ) + laplacian A.form.val U.u y :=
    add_laplacian_pos hN A U.smooth U.isKahler
  -- the maximum of `log(N + Δu) - a u`
  have hQc : Continuous fun y => Real.log (N + laplacian A.form.val U.u y) - a * U.u y :=
    ((continuous_const.add (KahlerLaplacianStokes.continuous_laplacian hg
      (chartSmooth_two U.smooth))).log fun y => (htrpos y).ne').sub
      (continuous_const.mul (YauUniformEstimate.continuous_of_chartSmooth U.smooth))
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hQc.continuousOn
  have hQmax : ∀ y, Real.log (N + laplacian A.form.val U.u y) - a * U.u y ≤
      Real.log (N + laplacian A.form.val U.u y₀) - a * U.u y₀ := fun y => hy₀ (mem_univ y)
  -- the bound at the maximum point
  have hkey : (N : ℝ) + laplacian A.form.val U.u y₀ ≤ 2 * (N + S) := by
    obtain ⟨p, hpt, hyp⟩ : ∃ p ∈ t, y₀ ∈ O p := by
      have := ht (mem_univ y₀)
      rw [mem_iUnion₂] at this
      obtain ⟨p, hp, h⟩ := this
      exact ⟨p, hp, h⟩
    rw [hOdef] at hyp
    have hz₀B : (complexChartAt (n := N) p).val y₀ ∈
        ball ((complexChartAt (n := N) p).val p) (R p) := hyp.2
    have hz₀K := ball_subset_closedBall hz₀B
    have hz₀V : (complexChartAt (n := N) p).val y₀ ∈
        ball ((complexChartAt (n := N) p).val p) (2 * R p) :=
      ball_subset_ball (by linarith [hR p]) hz₀B
    have hVW : ball ((complexChartAt (n := N) p).val p) (2 * R p) ⊆ W p :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [hR p]))).trans
        (hWball p)
    have hu_on : ContDiffOn ℝ ∞
        (fun w => ρ p w + U.u ((complexChartAt (n := N) p).val.symm w)) (W p) :=
      (hpot p).2.2.1.add ((U.smooth _).mono (hpot p).2.1)
    obtain ⟨u', hu', hu'eq⟩ := exists_contDiff_eqOn_ball (hpot p).1 hu_on
      (by linarith [hR p] : 0 < 2 * R p) (by linarith [hR p] : 2 * R p < 4 * R p) (hWball p)
    obtain ⟨Le, cc, hsymm, hLbd, h0, hbar⟩ := hnb p _ hz₀K
    have hy₀eq : (complexChartAt (n := N) p).val.symm ((complexChartAt (n := N) p).val y₀) = y₀ :=
      (complexChartAt (n := N) p).val.left_inv hyp.1
    have h := trace_le_of_isMax hN A hF U (hpot p) (hρ' p) hu' isOpen_ball hVW (hρ'eq p) hu'eq
      hz₀V (hK₁ p) (hKb p) ((hbd p _ hz₀K).2.2.2) (Le : ComplexModel N →L[ℂ] ComplexModel N)
      hsymm hLbd (isUnit_det_jacobianMatrix_zero _ _ hsymm Le rfl) h0 hbar hFS
      ((hale p hpt)) hβ' (by rw [hy₀eq]; exact hQmax)
    rwa [hy₀eq] at h
  -- conclusion
  intro y
  have h1 := hQmax y
  have hpos0 := htrpos y₀
  have hS2 : 0 < 2 * (N + S) := hpos0.trans_le hkey
  have h3 : Real.log (N + laplacian A.form.val U.u y₀) ≤ Real.log (2 * (N + S)) :=
    Real.log_le_log hpos0 hkey
  have h4 : a * m ≤ a * U.u y₀ := mul_le_mul_of_nonneg_left (hm y₀) ha0
  have h2 : Real.log (N + laplacian A.form.val U.u y) ≤
      Real.log (2 * (N + S)) + a * (U.u y - m) := by
    nlinarith
  have := Real.exp_le_exp.mpr h2
  rw [Real.exp_log (htrpos y), Real.exp_add, Real.exp_log hS2] at this
  exact this

end Estimate

end SGPT.Envelopes.LapClass
