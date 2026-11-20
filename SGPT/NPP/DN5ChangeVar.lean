import SGPT.NPP.DN5Defs
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Change of variables for means along a local fibre map

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1, lines 222–224: "For `w ≠ 0`, the
change of variables `y = F(x, wζ)` in the fiber, whose inverse depends smoothly on `(x, w, y)` by
the inverse function theorem, writes `Ψ_u(x, w)`, in a chart around `x`, as the integral of `u`
against a smooth nonnegative kernel supported in a ball of radius `C|w|` about `x`.
Differentiation under the integral sign shows that `Ψ_u` is smooth for `w ≠ 0` even when `u` has
poles.").

Everything here is chart-level analysis on `ℂⁿ`.  For a local fibre map `Φ`
(`SGPT.NPP.DN5.IsLocalFibreMap`) the joint map `(z, v) ↦ (z, Φ(z, v))` has derivative
`(a, b) ↦ (a, a + b)` along the zero section, so it is a local diffeomorphism there
(`exists_jointInverse`).  Writing `v = V(z, y)` for its inverse, a mean
`∫ f(Φ(z, t ξ)) k(z, ξ) dξ` with a weight `k` of uniformly bounded support becomes
`∫ f(y) K(z, t, y) dy` with `K = χ(y) k(z, V(z, y)/t) |t|^{-2n} |det ∂_y V(z, y)|`, smooth in
`(z, t, y)` for `t ≠ 0` and supported in a fixed compact set (`exists_transportKernel`).
Consequently such means of a locally integrable `f` are smooth in `(z, t)`
(`contDiffOn_mean_of_locallyIntegrableOn`).  (Adapted from the specialised Codex modules
`SGPT.NPP.MetricJetJointInverse`, `SGPT.NPP.MetricJetInverseJacobian`,
`SGPT.NPP.PolynomialSourceSmooth`, which treat the quadratic metric jet only.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Convolution

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {N : ℕ}

/-! ### Partial derivatives and determinants -/

section Partial

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The partial derivative in the second (fibre) variable. -/
def fibrePartial (F : E × E → G) (q : E × E) : E →L[ℝ] G :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ E E)

theorem hasFDerivAt_fibre_slice {F : E × E → G} {z v : E}
    (hF : DifferentiableAt ℝ F (z, v)) :
    HasFDerivAt (fun a => F (z, a)) (fibrePartial F (z, v)) v :=
  hF.hasFDerivAt.comp v ((hasFDerivAt_const z v).prodMk (hasFDerivAt_id v))

theorem hasFDerivAt_base_slice {F : E × E → G} {z v : E}
    (hF : DifferentiableAt ℝ F (z, v)) :
    HasFDerivAt (fun a => F (a, v)) ((fderiv ℝ F (z, v)).comp (ContinuousLinearMap.inl ℝ E E)) z :=
  hF.hasFDerivAt.comp z ((hasFDerivAt_id z).prodMk (hasFDerivAt_const v z))

theorem contDiffOn_fibrePartial {F : E × E → G} {W : Set (E × E)} (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) : ContDiffOn ℝ ∞ (fibrePartial F) W := by
  have H : ContDiffOn ℝ ∞ (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  exact H.clm_comp contDiffOn_const

/-- The determinant is a smooth function of the linear map. -/
theorem contDiff_det' [FiniteDimensional ℝ E] : ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A.det) := by
  classical
  let b := Module.finBasis ℝ E
  have h : (fun A : E →L[ℝ] E => A.det) = fun A =>
      ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) * ∏ i, b.coord (σ i) (A (b i)) := by
    funext A
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [h]
  have hc : ∀ i j, ContDiff ℝ ∞ (fun A : E →L[ℝ] E => b.coord i (A (b j))) := fun i j =>
    ((LinearMap.toContinuousLinearMap (b.coord i)).comp
      (ContinuousLinearMap.apply ℝ E (b j))).contDiff
  fun_prop

end Partial

/-! ### The joint map and its inverse -/

/-- The joint map `(z, v) ↦ (z, Φ(z, v))`. -/
def jointMap (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (q : ComplexModel N × ComplexModel N) : ComplexModel N × ComplexModel N :=
  (q.1, Φ q.1 q.2)

/-- The shear `(a, b) ↦ (a, a + b)`, the derivative of the joint map along the zero section. -/
def shearEquiv (N : ℕ) :
    (ComplexModel N × ComplexModel N) ≃L[ℝ] (ComplexModel N × ComplexModel N) :=
  { toLinearEquiv :=
      { toFun := fun q => (q.1, q.1 + q.2)
        invFun := fun q => (q.1, q.2 - q.1)
        left_inv := fun q => by ext <;> simp
        right_inv := fun q => by ext <;> simp
        map_add' := fun p q => by ext <;> simp [add_left_comm, add_comm]
        map_smul' := fun a q => by ext <;> simp [smul_add] }
    continuous_toFun := continuous_fst.prodMk (continuous_fst.add continuous_snd)
    continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst) }

variable {Φ : ComplexModel N → ComplexModel N → ComplexModel N}
  {O : Set (ComplexModel N × ComplexModel N)}

theorem contDiffOn_jointMap (hΦ : IsLocalFibreMap Φ O) : ContDiffOn ℝ ∞ (jointMap Φ) O :=
  contDiffOn_fst.prodMk hΦ.contDiffOn

theorem hasFDerivAt_jointMap_zero (hΦ : IsLocalFibreMap Φ O) {z : ComplexModel N}
    (hz : (z, (0 : ComplexModel N)) ∈ O) :
    HasFDerivAt (jointMap Φ) ((shearEquiv N : _ ≃L[ℝ] _) : _ →L[ℝ] _) (z, 0) := by
  let J := fun q : ComplexModel N × ComplexModel N => Φ q.1 q.2
  have hJ : DifferentiableAt ℝ J (z, 0) :=
    (hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds hz)).differentiableAt (by simp)
  -- base slice
  have hbase_ev : (fun a => J (a, 0)) =ᶠ[𝓝 z] id := by
    have hc : Continuous fun a : ComplexModel N => (a, (0 : ComplexModel N)) :=
      continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hΦ.isOpen.mem_nhds hz)] with a ha
    exact hΦ.map_zero a ha
  have hbase : (fderiv ℝ J (z, 0)).comp (ContinuousLinearMap.inl ℝ _ _) =
      ContinuousLinearMap.id ℝ _ :=
    (hasFDerivAt_base_slice hJ).unique ((hasFDerivAt_id z).congr_of_eventuallyEq hbase_ev)
  have hfibre : fibrePartial J (z, 0) = ContinuousLinearMap.id ℝ _ := by
    have h1 := hasFDerivAt_fibre_slice hJ
    have h2 : HasFDerivAt (Φ z) (ContinuousLinearMap.id ℝ _) 0 := by
      have hd : DifferentiableAt ℝ (Φ z) 0 := h1.differentiableAt
      have := hd.hasFDerivAt
      rwa [hΦ.fderiv_zero z hz] at this
    exact h1.unique h2
  have hDJ : fderiv ℝ J (z, 0) =
      ContinuousLinearMap.fst ℝ (ComplexModel N) (ComplexModel N) +
        ContinuousLinearMap.snd ℝ (ComplexModel N) (ComplexModel N) := by
    apply ContinuousLinearMap.ext
    intro q
    have hdecomp : q = ContinuousLinearMap.inl ℝ _ _ q.1 + ContinuousLinearMap.inr ℝ _ _ q.2 := by
      ext <;> simp
    rw [hdecomp, map_add]
    have e1 := congrArg (fun T : ComplexModel N →L[ℝ] ComplexModel N => T q.1) hbase
    have e2 := congrArg (fun T : ComplexModel N →L[ℝ] ComplexModel N => T q.2) hfibre
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e1
    simp only [fibrePartial, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e2
    rw [e1, e2]
    simp
  have H := (hasFDerivAt_fst (𝕜 := ℝ) (p := (z, (0 : ComplexModel N)))).prodMk hJ.hasFDerivAt
  change HasFDerivAt (jointMap Φ) _ (z, 0) at H
  apply H.congr_fderiv
  rw [hDJ]
  apply ContinuousLinearMap.ext
  intro q
  rfl

/-- **The joint inverse** (inverse function theorem): a local diffeomorphism `Ψ` with
`Ψ = jointMap Φ`, source in `O` containing `(z₀, 0)`, smooth inverse preserving the base point. -/
theorem exists_jointInverse (hΦ : IsLocalFibreMap Φ O) {z₀ : ComplexModel N}
    (hz₀ : (z₀, (0 : ComplexModel N)) ∈ O) :
    ∃ Ψ : OpenPartialHomeomorph (ComplexModel N × ComplexModel N) (ComplexModel N × ComplexModel N),
      ⇑Ψ = jointMap Φ ∧ (z₀, (0 : ComplexModel N)) ∈ Ψ.source ∧ Ψ.source ⊆ O ∧
      (∀ q ∈ Ψ.target, ContDiffAt ℝ ∞ Ψ.symm q) ∧
      ∀ q ∈ Ψ.target, (Ψ.symm q).1 = q.1 ∧ Φ q.1 (Ψ.symm q).2 = q.2 := by
  have hF := contDiffOn_jointMap hΦ
  have hF0 : ContDiffAt ℝ ∞ (jointMap Φ) (z₀, (0 : ComplexModel N)) :=
    hF.contDiffAt (hΦ.isOpen.mem_nhds hz₀)
  have hd0 := hasFDerivAt_jointMap_zero hΦ hz₀
  let Ψ₀ := hF0.toOpenPartialHomeomorph (jointMap Φ) hd0 (by simp)
  have hDFcont : ContinuousAt (fderiv ℝ (jointMap Φ)) (z₀, (0 : ComplexModel N)) :=
    (hF0.fderiv_right (m := ∞) (by simp)).continuousAt
  let Inv : Set ((ComplexModel N × ComplexModel N) →L[ℝ] (ComplexModel N × ComplexModel N)) :=
    range ((↑) : ((ComplexModel N × ComplexModel N) ≃L[ℝ] (ComplexModel N × ComplexModel N)) → _)
  have hInv : Inv ∈ 𝓝 (fderiv ℝ (jointMap Φ) (z₀, 0)) :=
    ContinuousLinearEquiv.isOpen.mem_nhds ⟨shearEquiv N, hd0.fderiv.symm⟩
  have hgood : O ∩ (fderiv ℝ (jointMap Φ)) ⁻¹' Inv ∈ 𝓝 (z₀, (0 : ComplexModel N)) :=
    inter_mem (hΦ.isOpen.mem_nhds hz₀) (hDFcont.preimage_mem_nhds hInv)
  obtain ⟨O', hOsub, hO', h0O⟩ := _root_.mem_nhds_iff.mp hgood
  let Ψ := Ψ₀.restrOpen O' hO'
  have hcoe : ⇑Ψ = jointMap Φ := by
    rw [OpenPartialHomeomorph.coe_restrOpen]
    exact ContDiffAt.toOpenPartialHomeomorph_coe hF0 hd0 (by simp)
  have hsrc : Ψ.source ⊆ O' := by
    intro q hq
    rw [OpenPartialHomeomorph.restrOpen_source] at hq
    exact hq.2
  have h0source : (z₀, (0 : ComplexModel N)) ∈ Ψ.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source hF0 hd0 (by simp), h0O⟩
  refine ⟨Ψ, hcoe, h0source, fun q hq => (hOsub (hsrc hq)).1, ?_, ?_⟩
  · intro q hqt
    have hqs := Ψ.map_target hqt
    have hqgood := hOsub (hsrc hqs)
    obtain ⟨L, hL⟩ := hqgood.2
    have hFat : ContDiffAt ℝ ∞ (jointMap Φ) (Ψ.symm q) :=
      hF.contDiffAt (hΦ.isOpen.mem_nhds hqgood.1)
    have hd : HasFDerivAt Ψ L.toContinuousLinearMap (Ψ.symm q) := by
      rw [hcoe, hL]
      exact (hFat.differentiableAt (by simp)).hasFDerivAt
    apply Ψ.contDiffAt_symm hqt hd
    rw [hcoe]
    exact hFat
  · intro q hqt
    have H := Ψ.right_inv hqt
    rw [hcoe] at H
    have hfirst := congrArg Prod.fst H
    have hsecond := congrArg Prod.snd H
    change (Ψ.symm q).1 = q.1 at hfirst
    change Φ (Ψ.symm q).1 (Ψ.symm q).2 = q.2 at hsecond
    exact ⟨hfirst, by rwa [hfirst] at hsecond⟩

/-! ### The transport kernel -/

/-- The fibre component `V(z, y)` of the joint inverse. -/
def invTangent (Ψ : OpenPartialHomeomorph (ComplexModel N × ComplexModel N)
    (ComplexModel N × ComplexModel N)) (q : ComplexModel N × ComplexModel N) : ComplexModel N :=
  (Ψ.symm q).2

/-- The Jacobian `|det ∂_y V(z, y)|`. -/
def invJacobian (Ψ : OpenPartialHomeomorph (ComplexModel N × ComplexModel N)
    (ComplexModel N × ComplexModel N)) (q : ComplexModel N × ComplexModel N) : ℝ :=
  |(fibrePartial (invTangent Ψ) q).det|

/-- The transported kernel `k(z, V(z, y)/t) |t^{-d}| |det ∂_y V(z, y)|` (`d = dim_ℝ`). -/
def transportKernel (k : ComplexModel N → ComplexModel N → ℝ)
    (Ψ : OpenPartialHomeomorph (ComplexModel N × ComplexModel N) (ComplexModel N × ComplexModel N))
    (t : ℝ) (q : ComplexModel N × ComplexModel N) : ℝ :=
  k q.1 (t⁻¹ • invTangent Ψ q) * |(t ^ Module.finrank ℝ (ComplexModel N))⁻¹| * invJacobian Ψ q

section Kernel

variable {Ψ : OpenPartialHomeomorph (ComplexModel N × ComplexModel N)
    (ComplexModel N × ComplexModel N)}

theorem contDiffOn_invTangent (hΨ : ∀ q ∈ Ψ.target, ContDiffAt ℝ ∞ Ψ.symm q) :
    ContDiffOn ℝ ∞ (invTangent Ψ) Ψ.target := fun q hq =>
  (contDiffAt_snd.comp q (hΨ q hq)).contDiffWithinAt

theorem contDiffOn_invJacobian (hΨ : ∀ q ∈ Ψ.target, ContDiffAt ℝ ∞ Ψ.symm q)
    (hΦV : ∀ q ∈ Ψ.target, Φ q.1 (invTangent Ψ q) = q.2) (hΦ : IsLocalFibreMap Φ O)
    (hsrc : Ψ.source ⊆ O) (hident : ∀ q ∈ Ψ.target, (Ψ.symm q).1 = q.1) :
    ContDiffOn ℝ ∞ (invJacobian Ψ) Ψ.target := by
  have hV := contDiffOn_invTangent hΨ
  have hDV := contDiffOn_fibrePartial Ψ.open_target hV
  have hdet : ContDiffOn ℝ ∞ (fun q => (fibrePartial (invTangent Ψ) q).det) Ψ.target :=
    contDiff_det'.comp_contDiffOn hDV
  refine hdet.abs ?_
  intro q hq
  -- the fibre derivative of `V` is invertible: `∂_v Φ ∘ ∂_y V = id`
  let V := invTangent Ψ
  have hVd : DifferentiableAt ℝ V q :=
    (hV.contDiffAt (Ψ.open_target.mem_nhds hq)).differentiableAt (by simp)
  have hVq : DifferentiableAt ℝ V (q.1, q.2) := by simpa only [Prod.mk.eta] using hVd
  have hVs := hasFDerivAt_fibre_slice hVq
  have hsrcq : (q.1, V q) ∈ O := by
    have h1 := hsrc (Ψ.map_target hq)
    have h2 : Ψ.symm q = (q.1, V q) := Prod.ext (hident q hq) rfl
    rwa [h2] at h1
  have hΦd : DifferentiableAt ℝ (Φ q.1) (V q) := by
    have hJ : DifferentiableAt ℝ (fun p : ComplexModel N × ComplexModel N => Φ p.1 p.2) (q.1, V q) :=
      (hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds hsrcq)).differentiableAt (by simp)
    exact hJ.comp (V q) ((differentiableAt_const q.1).prodMk differentiableAt_id)
  have htarget : ∀ᶠ y in 𝓝 q.2, (q.1, y) ∈ Ψ.target :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using Ψ.open_target.mem_nhds hq)
  have hidentity : (fun y => Φ q.1 (V (q.1, y))) =ᶠ[𝓝 q.2] id := by
    filter_upwards [htarget] with y hy
    exact hΦV (q.1, y) hy
  have hVs' : HasFDerivAt (fun y => V (q.1, y)) (fibrePartial V q) q.2 := by
    simpa only [Prod.mk.eta] using hVs
  have hcomp : (fderiv ℝ (Φ q.1) (V q)).comp (fibrePartial V q) = ContinuousLinearMap.id ℝ _ := by
    have h := (hΦd.hasFDerivAt.comp q.2 hVs')
    exact (h.congr_of_eventuallyEq hidentity.symm).unique (hasFDerivAt_id q.2)
  have hinj : Function.Injective (fibrePartial V q) := by
    apply Function.LeftInverse.injective (g := fderiv ℝ (Φ q.1) (V q))
    intro a
    exact congrArg (fun T => T a) hcomp
  have hbij : Function.Bijective (fibrePartial V q).toLinearMap :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact (LinearEquiv.ofBijective (fibrePartial V q).toLinearMap hbij).isUnit_det'.ne_zero

/-- Change of variables `v = V(z, y)` on the fibre of the target over `z`. -/
theorem integral_image_invTangent (hΨ : ∀ q ∈ Ψ.target, ContDiffAt ℝ ∞ Ψ.symm q)
    (hΦV : ∀ q ∈ Ψ.target, Φ q.1 (invTangent Ψ q) = q.2) (z : ComplexModel N)
    (h : ComplexModel N → ℝ) :
    (∫ v in (fun y => invTangent Ψ (z, y)) '' {y | (z, y) ∈ Ψ.target}, h v) =
      ∫ y in {y | (z, y) ∈ Ψ.target}, invJacobian Ψ (z, y) * h (invTangent Ψ (z, y)) := by
  let S : Set (ComplexModel N) := {y | (z, y) ∈ Ψ.target}
  let V := fun y => invTangent Ψ (z, y)
  have hS : IsOpen S := Ψ.open_target.preimage (continuous_const.prodMk continuous_id)
  have hder : ∀ y ∈ S, HasFDerivWithinAt V (fibrePartial (invTangent Ψ) (z, y)) S y := by
    intro y hy
    have hV : DifferentiableAt ℝ (invTangent Ψ) (z, y) :=
      ((contDiffOn_invTangent hΨ).contDiffAt (Ψ.open_target.mem_nhds hy)).differentiableAt
        (by simp)
    exact (hasFDerivAt_fibre_slice hV).hasFDerivWithinAt
  have hinj : InjOn V S := by
    intro y hy t ht hyt
    have H := congrArg (Φ z) hyt
    simpa only [V, hΦV (z, y) hy, hΦV (z, t) ht] using H
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS.measurableSet hder hinj]
  rfl

theorem invTangent_image_eq_source (hcoe : ⇑Ψ = jointMap Φ)
    (hident : ∀ q ∈ Ψ.target, (Ψ.symm q).1 = q.1) (z : ComplexModel N) :
    (fun y => invTangent Ψ (z, y)) '' {y | (z, y) ∈ Ψ.target} = {v | (z, v) ∈ Ψ.source} := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    have H := Ψ.map_target hy
    have hp : (z, invTangent Ψ (z, y)) = Ψ.symm (z, y) := Prod.ext (hident (z, y) hy).symm rfl
    change (z, invTangent Ψ (z, y)) ∈ Ψ.source
    rw [hp]
    exact H
  · intro hv
    have hy := Ψ.map_source hv
    rw [hcoe] at hy
    refine ⟨Φ z v, hy, ?_⟩
    have H := congrArg Prod.snd (Ψ.left_inv hv)
    rw [hcoe] at H
    exact H

end Kernel

/-- **The transport kernel.**  For a local fibre map `Φ` near `(z₀, 0)` and a smooth weight `k`
with uniformly bounded support near `z₀`, there are `ε, δ > 0`, a compact `C` inside any given
neighbourhood of `z₀`, and a kernel `K` smooth in `((z, t), y)` on `(B(z₀, ε) × (0, δ)) × ℂⁿ`,
vanishing for `y ∉ C`, nonnegative if `k` is, with
`∫ f(Φ(z, t ξ)) k(z, ξ) dξ = ∫ f(y) K((z, t), y) dy` for every `f`. -/
theorem exists_transportKernel (hΦ : IsLocalFibreMap Φ O)
    {k : ComplexModel N → ComplexModel N → ℝ} {U : Set (ComplexModel N)} (hU : IsOpen U)
    (hk : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => k q.1 q.2)
      (U ×ˢ univ))
    {R : ℝ} (hkR : ∀ z ∈ U, ∀ ξ, k z ξ ≠ 0 → ‖ξ‖ ≤ R)
    {z₀ : ComplexModel N} (hz₀U : z₀ ∈ U) (hz₀O : (z₀, (0 : ComplexModel N)) ∈ O)
    {W : Set (ComplexModel N)} (hW : W ∈ 𝓝 z₀) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ C : Set (ComplexModel N), IsCompact C ∧ C ⊆ W ∧
      ∃ K : ComplexModel N × ℝ → ComplexModel N → ℝ,
        ContDiffOn ℝ ∞ (fun q : (ComplexModel N × ℝ) × ComplexModel N => K q.1 q.2)
          ((ball z₀ ε ×ˢ Ioo 0 δ) ×ˢ univ) ∧
        (∀ p y, y ∉ C → K p y = 0) ∧
        ((∀ z ξ, 0 ≤ k z ξ) → ∀ p y, 0 ≤ K p y) ∧
        ball z₀ ε ⊆ U ∧
        (∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ ξ, k z ξ ≠ 0 → (z, t • ξ) ∈ O) ∧
        ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ f : ComplexModel N → ℝ,
          (∫ ξ, f (Φ z (t • ξ)) * k z ξ) = ∫ y, f y * K (z, t) y := by
  classical
  obtain ⟨Ψ, hcoe, hsource, hsrcO, hΨ, hident⟩ := exists_jointInverse hΦ hz₀O
  have hΦV : ∀ q ∈ Ψ.target, Φ q.1 (invTangent Ψ q) = q.2 := fun q hq => (hident q hq).2
  have hbase : ∀ q ∈ Ψ.target, (Ψ.symm q).1 = q.1 := fun q hq => (hident q hq).1
  -- a product neighbourhood of `(z₀, z₀)` in the target
  have hz₀T : (z₀, z₀) ∈ Ψ.target := by
    have H := Ψ.map_source hsource
    rw [hcoe] at H
    have : jointMap Φ (z₀, 0) = (z₀, z₀) := by
      simp only [jointMap, hΦ.map_zero z₀ hz₀O]
    rwa [this] at H
  obtain ⟨ρW, hρW, hρWsub⟩ := Metric.mem_nhds_iff.mp hW
  have hD : IsOpen (Ψ.target ∩ (U ×ˢ (univ : Set (ComplexModel N)))) :=
    Ψ.open_target.inter (hU.prod isOpen_univ)
  obtain ⟨ε₀, hε₀, hε₀D⟩ := Metric.isOpen_iff.mp hD (z₀, z₀) ⟨hz₀T, hz₀U, mem_univ _⟩
  set ε₁ := min ε₀ ρW with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε₀ hρW
  -- the cutoff in `y`
  let χ : ContDiffBump z₀ := ⟨ε₁ / 4, ε₁ / 2, by positivity, by linarith⟩
  have hχt : tsupport χ = closedBall z₀ (ε₁ / 2) := χ.tsupport_eq
  set A := ball z₀ (ε₁ / 2)
  have hbuffer : ∀ a ∈ A, ∀ y ∈ closedBall z₀ (ε₁ / 2), (a, y) ∈ Ψ.target ∧ a ∈ U := by
    intro a ha y hy
    have H := hε₀D (show (a, y) ∈ ball (z₀, z₀) ε₀ from by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      have h1 : ε₁ ≤ ε₀ := min_le_left _ _
      exact ⟨(mem_ball.mp ha).trans (by linarith), (mem_closedBall.mp hy).trans_lt (by linarith)⟩)
    exact ⟨H.1, H.2.1⟩
  have hCW : closedBall z₀ (ε₁ / 2) ⊆ W := fun y hy => hρWsub (by
    rw [mem_ball]
    have h1 : ε₁ ≤ ρW := min_le_right _ _
    exact (mem_closedBall.mp hy).trans_lt (by linarith))
  -- sample points stay where `χ = 1`, and in the source
  have hcontΦ : ContinuousAt (fun q : ComplexModel N × ComplexModel N => Φ q.1 q.2)
      (z₀, (0 : ComplexModel N)) :=
    (hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds hz₀O)).continuousAt
  have hnb : {q : ComplexModel N × ComplexModel N | Φ q.1 q.2 ∈ ball z₀ (ε₁ / 4)} ∩ Ψ.source ∈
      𝓝 (z₀, (0 : ComplexModel N)) := by
    refine inter_mem (hcontΦ.preimage_mem_nhds ?_) (Ψ.open_source.mem_nhds hsource)
    have hΦ0 : Φ z₀ 0 = z₀ := hΦ.map_zero z₀ hz₀O
    have hb : ball z₀ (ε₁ / 4) ∈ 𝓝 (Φ z₀ 0) := by
      rw [hΦ0]; exact ball_mem_nhds _ (by positivity)
    exact hb
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hnb
  set ε := min (η / 2) (ε₁ / 2) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  set δ := (η / 2) / (|R| + 1) with hδdef
  have hδ : 0 < δ := div_pos (by positivity) (by positivity)
  have hsample : ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ ξ, k z ξ ≠ 0 →
      Φ z (t • ξ) ∈ ball z₀ (ε₁ / 4) ∧ (z, t • ξ) ∈ Ψ.source := by
    intro z hz t ht ξ hξ
    have hzU : z ∈ U := (hbuffer z (ball_subset_ball (min_le_right _ _) hz) z₀
      (mem_closedBall_self (by positivity))).2
    have hξR := hkR z hzU ξ hξ
    have htξ : ‖t • ξ‖ < η / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      have h1 : t * (|R| + 1) < η / 2 := (lt_div_iff₀ (by positivity)).mp ht.2
      have h2 : ‖ξ‖ ≤ |R| := hξR.trans (le_abs_self R)
      nlinarith [norm_nonneg ξ, ht.1]
    have hmem : (z, t • ξ) ∈ ball (z₀, (0 : ComplexModel N)) η := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right]
      exact ⟨(mem_ball.mp hz).trans_le ((min_le_left _ _).trans (by linarith)),
        htξ.trans (by linarith)⟩
    exact ⟨(hηsub hmem).1, (hηsub hmem).2⟩
  -- the kernel
  let K : ComplexModel N × ℝ → ComplexModel N → ℝ := fun p y =>
    χ y * transportKernel k Ψ p.2 (p.1, y)
  refine ⟨ε, δ, hε, hδ, closedBall z₀ (ε₁ / 2), isCompact_closedBall _ _, hCW, K, ?_, ?_, ?_,
    fun z hz => (hbuffer z (ball_subset_ball (min_le_right _ _) hz) z₀
      (mem_closedBall_self (by positivity))).2,
    fun z hz t ht ξ hξ => hsrcO (hsample z hz t ht ξ hξ).2, ?_⟩
  · -- smoothness
    intro q hq
    have hzA : q.1.1 ∈ A := ball_subset_ball (min_le_right _ _) hq.1.1
    have ht0 : q.1.2 ≠ 0 := (hq.1.2.1).ne'
    by_cases hy : q.2 ∈ tsupport χ
    · have hyb : q.2 ∈ closedBall z₀ (ε₁ / 2) := hχt ▸ hy
      have hT : (q.1.1, q.2) ∈ Ψ.target := (hbuffer _ hzA _ hyb).1
      have hUq : q.1.1 ∈ U := (hbuffer _ hzA _ hyb).2
      -- smoothness of the transported kernel near `q`
      have hpair : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N => (p.1.1, p.2)) q :=
        (contDiffAt_fst.comp q contDiffAt_fst).prodMk contDiffAt_snd
      have hV0 : ContDiffAt ℝ ∞ (invTangent Ψ) (q.1.1, q.2) :=
        (contDiffOn_invTangent hΨ).contDiffAt (Ψ.open_target.mem_nhds hT)
      have hJ0 : ContDiffAt ℝ ∞ (invJacobian Ψ) (q.1.1, q.2) :=
        (contDiffOn_invJacobian hΨ hΦV hΦ hsrcO hbase).contDiffAt (Ψ.open_target.mem_nhds hT)
      have hVq : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N =>
          invTangent Ψ (p.1.1, p.2)) q :=
        ContDiffAt.comp (g := invTangent Ψ)
          (f := fun p : (ComplexModel N × ℝ) × ComplexModel N => (p.1.1, p.2)) q hV0 hpair
      have hJq : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N =>
          invJacobian Ψ (p.1.1, p.2)) q :=
        ContDiffAt.comp (g := invJacobian Ψ)
          (f := fun p : (ComplexModel N × ℝ) × ComplexModel N => (p.1.1, p.2)) q hJ0 hpair
      have htq : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N => p.1.2) q :=
        contDiffAt_snd.comp q contDiffAt_fst
      have hinv : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N => p.1.2⁻¹) q :=
        htq.inv ht0
      have hpow : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N =>
          |(p.1.2 ^ Module.finrank ℝ (ComplexModel N))⁻¹|) q := by
        have hne : (q.1.2 ^ Module.finrank ℝ (ComplexModel N))⁻¹ ≠ 0 :=
          inv_ne_zero (pow_ne_zero _ ht0)
        exact ((htq.pow _).inv (pow_ne_zero _ ht0)).abs hne
      have hkq : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N =>
          k p.1.1 (p.1.2⁻¹ • invTangent Ψ (p.1.1, p.2))) q := by
        have hin : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N =>
            (p.1.1, p.1.2⁻¹ • invTangent Ψ (p.1.1, p.2))) q :=
          (contDiffAt_fst.comp q contDiffAt_fst).prodMk (hinv.smul hVq)
        exact (hk.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hUq, mem_univ _⟩)).comp q hin
      have hχq : ContDiffAt ℝ ∞ (fun p : (ComplexModel N × ℝ) × ComplexModel N => χ p.2) q :=
        χ.contDiff.contDiffAt.comp q contDiffAt_snd
      exact (hχq.mul ((hkq.mul hpow).mul hJq)).contDiffWithinAt
    · have hzero : (fun p : (ComplexModel N × ℝ) × ComplexModel N => K p.1 p.2) =ᶠ[𝓝 q]
          fun _ => 0 := by
        have H := (continuous_snd.continuousAt (x := q)).preimage_mem_nhds
          (notMem_tsupport_iff_eventuallyEq.mp hy)
        filter_upwards [H] with p hp
        have hp0 : χ p.2 = 0 := hp
        change χ p.2 * _ = 0
        rw [hp0, zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt
  · -- support
    intro p y hy
    have hχ0 : χ y = 0 := image_eq_zero_of_notMem_tsupport (by rw [hχt]; exact hy)
    change χ y * _ = 0
    rw [hχ0, zero_mul]
  · -- nonnegativity
    intro hk0 p y
    exact mul_nonneg χ.nonneg (mul_nonneg (mul_nonneg (hk0 _ _) (abs_nonneg _)) (abs_nonneg _))
  · -- the change of variables
    intro z hz t ht f
    have ht0 : t ≠ 0 := ht.1.ne'
    have hzA : z ∈ A := ball_subset_ball (min_le_right _ _) hz
    -- substitution `v = t ξ`
    have hscale : (∫ ξ, f (Φ z (t • ξ)) * k z ξ) =
        |(t ^ Module.finrank ℝ (ComplexModel N))⁻¹| * ∫ v, f (Φ z v) * k z (t⁻¹ • v) := by
      have H := Measure.integral_comp_smul (μ := (volume : Measure (ComplexModel N)))
        (fun v => f (Φ z v) * k z (t⁻¹ • v)) t
      simp only [smul_smul, inv_mul_cancel₀ ht0, one_smul, smul_eq_mul] at H
      exact H
    -- restriction to the source fibre
    have hsupp : (∫ v, f (Φ z v) * k z (t⁻¹ • v)) =
        ∫ v in {v | (z, v) ∈ Ψ.source}, f (Φ z v) * k z (t⁻¹ • v) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro v hv
      by_cases hkv : k z (t⁻¹ • v) = 0
      · rw [hkv, mul_zero]
      · exfalso
        have H := (hsample z hz t ht (t⁻¹ • v) hkv).2
        rw [smul_smul, mul_inv_cancel₀ ht0, one_smul] at H
        exact hv H
    rw [hscale, hsupp, ← invTangent_image_eq_source hcoe hbase z,
      integral_image_invTangent hΨ hΦV z]
    -- back to the whole space with the cutoff
    rw [← integral_const_mul]
    have hmeas : MeasurableSet {y | (z, y) ∈ Ψ.target} :=
      (Ψ.open_target.preimage (continuous_const.prodMk continuous_id)).measurableSet
    have hfull : (∫ y, f y * K (z, t) y) = ∫ y in {y | (z, y) ∈ Ψ.target}, f y * K (z, t) y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hχ0 : χ y = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hyχ
        exact hy (hbuffer z hzA y (hχt ▸ hyχ)).1
      change f y * (χ y * _) = 0
      rw [hχ0, zero_mul, mul_zero]
    rw [hfull]
    · apply setIntegral_congr_fun hmeas
      intro y hy
      have hy' : Φ z (invTangent Ψ (z, y)) = y := hΦV (z, y) hy
      change _ = f y * (χ y * (k z (t⁻¹ • invTangent Ψ (z, y)) *
        |(t ^ Module.finrank ℝ (ComplexModel N))⁻¹| * invJacobian Ψ (z, y)))
      beta_reduce
      rw [hy']
      by_cases hkv : k z (t⁻¹ • invTangent Ψ (z, y)) = 0
      · rw [hkv]; ring
      · have H := (hsample z hz t ht _ hkv).1
        rw [smul_smul, mul_inv_cancel₀ ht0, one_smul, hy'] at H
        have hχ1 : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall H)
        rw [hχ1]; ring

/-- **Differentiation under the integral sign against a smooth compactly supported kernel**:
`p ↦ ∫ f(y) K(p, y) dy` is smooth when `K` is smooth in `(p, y)`, vanishes off a fixed compact `C`,
and `f` is integrable on `C`. -/
theorem contDiffOn_integral_mul_kernel {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {S : Set P} (hS : IsOpen S) {K : P → ComplexModel N → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun q : P × ComplexModel N => K q.1 q.2) (S ×ˢ univ))
    {C : Set (ComplexModel N)} (hC : IsCompact C) (hKC : ∀ p y, y ∉ C → K p y = 0)
    {f : ComplexModel N → ℝ} (hf : IntegrableOn f C) :
    ContDiffOn ℝ ∞ (fun p => ∫ y, f y * K p y) S := by
  let F := C.indicator f
  have hIF : Integrable F := hf.integrable_indicator hC.isClosed.measurableSet
  let kk : P → ComplexModel N → ℝ := fun p x => K p (-x)
  have hkk : ContDiffOn ℝ ∞ (Function.uncurry kk) (S ×ˢ univ) :=
    hK.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hzero (p : P) (x : ComplexModel N) (_ : p ∈ S) (hx : x ∉ -C) : kk p x = 0 := by
    have hx' : -x ∉ C := by simpa only [Set.mem_neg, neg_neg] using hx
    exact hKC p (-x) hx'
  have H := contDiffOn_convolution_right_with_param_comp (ContinuousLinearMap.mul ℝ ℝ)
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P => (0 : ComplexModel N)) _)
    hS hC.neg hzero hIF.locallyIntegrable hkk
  refine H.congr fun p _ => ?_
  simp only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub, kk, neg_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change f y * K p y = F y * K p y
  by_cases hy : y ∈ C
  · simp only [F, indicator_of_mem hy]
  · rw [hKC p y hy, mul_zero, mul_zero]

/-- **Smoothness of means of locally integrable functions along a local fibre map.** -/
theorem contDiffOn_mean_of_locallyIntegrableOn (hΦ : IsLocalFibreMap Φ O)
    {k : ComplexModel N → ComplexModel N → ℝ} {U : Set (ComplexModel N)} (hU : IsOpen U)
    (hk : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => k q.1 q.2)
      (U ×ˢ univ))
    {R : ℝ} (hkR : ∀ z ∈ U, ∀ ξ, k z ξ ≠ 0 → ‖ξ‖ ≤ R)
    {z₀ : ComplexModel N} (hz₀U : z₀ ∈ U) (hz₀O : (z₀, (0 : ComplexModel N)) ∈ O)
    {W : Set (ComplexModel N)} (hW : IsOpen W) (hz₀W : z₀ ∈ W)
    {f : ComplexModel N → ℝ} (hf : LocallyIntegrableOn f W) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => ∫ ξ, f (Φ p.1 (p.2 • ξ)) * k p.1 ξ)
        (ball z₀ ε ×ˢ Ioo 0 δ) := by
  obtain ⟨ε, δ, hε, hδ, C, hC, hCW, K, hK, hKC, -, -, -, hrep⟩ :=
    exists_transportKernel hΦ hU hk hkR hz₀U hz₀O (hW.mem_nhds hz₀W)
  have hs : IsOpen (ball z₀ ε ×ˢ Ioo (0 : ℝ) δ) := isOpen_ball.prod isOpen_Ioo
  refine ⟨ε, δ, hε, hδ, ?_⟩
  refine (contDiffOn_integral_mul_kernel hs hK hC hKC
    ((hf.mono_set hCW).integrableOn_isCompact hC)).congr fun p hp => ?_
  exact hrep p.1 hp.1 p.2 hp.2 f

end SGPT.NPP.DN5
