import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The adjoint of a fibrewise substitution

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 7, proof of
`eq:chern-smoothing-generator`): "For fixed `ζ` near `0` the map `Φ_ζ(x) = F(x, ζ)` is a
diffeomorphism near `Supp φ`, with `Φ_0` the identity, and its inverse depends smoothly on `(ζ, y)`,
by the inverse function theorem.  By Fubini's theorem and the change of variables `y = Φ_{rζ}(x)`,
the adjoint kernel is …"

Let `G : E × E → E` be smooth with `G(z, 0) = z` (`E` a finite-dimensional real space with an
additive Haar measure).  The **graph map** `Θ(z, η) = (G(z, η), η)` has derivative
`(a, b) ↦ (D_zG a + D_ηG b, b)`, invertible where `det D_zG ≠ 0`, in particular at `(z₀, 0)`.  By
the inverse function theorem `Θ` is an open partial homeomorphism `P` near `(z₀, 0)` with smooth
inverse (`exists_graphChart`).  For a function `ψ` supported near `z₀`, the **adjoint density**
`Ã(y, η) = ψ(z) / |det D_zG(z, η)|`, `(z, η) = Θ⁻¹(y, η)`, satisfies
`∫ F(G(z, η)) ψ(z) dz = ∫ F(y) Ã(y, η) dy` for **every** `F` (`integral_comp_mul_eq`).

The main result `exists_adjointDensity` packages a smooth, compactly supported version of `Ã`
with `Ã(y, 0) = ψ(y)`, valid for `‖η‖ < t₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN6

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedSectionVars false

/-! ### The determinant is smooth -/

/-- The determinant is a smooth function of the linear map (a polynomial in the matrix entries). -/
theorem contDiff_clm_det : ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A.det) := by
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

/-! ### Partial derivatives and the graph map -/

/-- The partial derivative `D_zG(z, η)`. -/
def dFst (G : E × E → E) (q : E × E) : E →L[ℝ] E :=
  (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E E)

/-- The partial derivative `D_ηG(z, η)`. -/
def dSnd (G : E × E → E) (q : E × E) : E →L[ℝ] E :=
  (fderiv ℝ G q).comp (ContinuousLinearMap.inr ℝ E E)

/-- The Jacobian `|det D_zG(z, η)|` of the fibre map `z ↦ G(z, η)`. -/
def jacFst (G : E × E → E) (q : E × E) : ℝ := |(dFst G q).det|

/-- The graph map `Θ(z, η) = (G(z, η), η)`. -/
def graphMap (G : E × E → E) (q : E × E) : E × E := (G q, q.2)

theorem fderiv_apply_eq (G : E × E → E) (q : E × E) (a b : E) :
    fderiv ℝ G q (a, b) = dFst G q a + dSnd G q b := by
  have h : ((a, b) : E × E) = (a, 0) + (0, b) := by simp
  rw [h, map_add]
  rfl

theorem hasFDerivAt_fst {G : E × E → E} (hG : Differentiable ℝ G) (q : E × E) :
    HasFDerivAt (fun z => G (z, q.2)) (dFst G q) q.1 :=
  (hG q).hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)

theorem hasFDerivAt_graphMap {G : E × E → E} (hG : Differentiable ℝ G) (q : E × E) :
    HasFDerivAt (graphMap G) ((fderiv ℝ G q).prod (ContinuousLinearMap.snd ℝ E E)) q :=
  (hG q).hasFDerivAt.prodMk hasFDerivAt_snd

theorem contDiff_graphMap {G : E × E → E} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (graphMap G) :=
  hG.prodMk contDiff_snd

theorem contDiff_dFst {G : E × E → E} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dFst G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem contDiff_det_dFst {G : E × E → E} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q => (dFst G q).det) :=
  contDiff_clm_det.comp (contDiff_dFst hG)

/-- Along `η = 0`, where `G(z, 0) = z`, the partial derivative `D_zG` is the identity. -/
theorem dFst_zero {G : E × E → E} (hG : Differentiable ℝ G) (hG0 : ∀ z, G (z, 0) = z) (z : E) :
    dFst G (z, 0) = ContinuousLinearMap.id ℝ E := by
  have h1 := hasFDerivAt_fst hG (z, 0)
  have h2 : HasFDerivAt (fun z : E => G (z, 0)) (ContinuousLinearMap.id ℝ E) z := by
    have : (fun z : E => G (z, 0)) = id := funext hG0
    rw [this]
    exact hasFDerivAt_id z
  exact h1.unique h2

theorem jacFst_zero {G : E × E → E} (hG : Differentiable ℝ G) (hG0 : ∀ z, G (z, 0) = z) (z : E) :
    jacFst G (z, 0) = 1 := by
  rw [jacFst, dFst_zero hG hG0, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
    LinearMap.det_id, abs_one]

/-- The inverse of the derivative of the graph map. -/
def graphDerivInv (G : E × E → E) (q : E × E) (hq : (dFst G q).det ≠ 0) : E × E →L[ℝ] E × E :=
  ((((dFst G q).toContinuousLinearEquivOfDetNeZero hq).symm : E →L[ℝ] E).comp
      (ContinuousLinearMap.fst ℝ E E - (dSnd G q).comp (ContinuousLinearMap.snd ℝ E E))).prod
    (ContinuousLinearMap.snd ℝ E E)

/-- The derivative of the graph map, as a linear equivalence where `det D_zG ≠ 0`. -/
def graphDerivEquiv (G : E × E → E) (q : E × E) (hq : (dFst G q).det ≠ 0) :
    (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse
    ((fderiv ℝ G q).prod (ContinuousLinearMap.snd ℝ E E)) (graphDerivInv G q hq)
    (fun p => by
      obtain ⟨a, b⟩ := p
      have h := ((dFst G q).toContinuousLinearEquivOfDetNeZero hq).symm_apply_apply a
      simp only [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] at h
      simp [graphDerivInv, fderiv_apply_eq, h])
    (fun p => by
      obtain ⟨c, b⟩ := p
      have h1 := ((dFst G q).toContinuousLinearEquivOfDetNeZero hq).apply_symm_apply c
      have h2 := ((dFst G q).toContinuousLinearEquivOfDetNeZero hq).apply_symm_apply
        (dSnd G q b)
      simp only [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] at h1 h2
      simp [graphDerivInv, fderiv_apply_eq, h1, h2])

theorem coe_graphDerivEquiv (G : E × E → E) (q : E × E) (hq : (dFst G q).det ≠ 0) :
    ((graphDerivEquiv G q hq : (E × E) ≃L[ℝ] (E × E)) : E × E →L[ℝ] E × E) =
      (fderiv ℝ G q).prod (ContinuousLinearMap.snd ℝ E E) := by
  ext p <;> simp [graphDerivEquiv]

/-- **The inverse function theorem for the graph map.** -/
theorem exists_graphChart {G : E × E → E} (hG : ContDiff ℝ ∞ G) (hG0 : ∀ z, G (z, 0) = z)
    (z₀ : E) :
    ∃ P : OpenPartialHomeomorph (E × E) (E × E), (⇑P = graphMap G) ∧ (z₀, 0) ∈ P.source ∧
      (∀ q ∈ P.source, (dFst G q).det ≠ 0) ∧ ∀ p ∈ P.target, ContDiffAt ℝ ∞ P.symm p := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by simp)
  have hgm := contDiff_graphMap hG
  have hdet0 : (dFst G (z₀, 0)).det ≠ 0 := by
    rw [dFst_zero hG1 hG0, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_ne_zero
  set U : Set (E × E) := {q | (dFst G q).det ≠ 0} with hUdef
  have hU : IsOpen U := isOpen_ne_fun (contDiff_det_dFst hG).continuous continuous_const
  have hder : HasFDerivAt (graphMap G)
      ((graphDerivEquiv G (z₀, 0) hdet0 : (E × E) ≃L[ℝ] (E × E)) : E × E →L[ℝ] E × E) (z₀, 0) := by
    rw [coe_graphDerivEquiv]; exact hasFDerivAt_graphMap hG1 _
  let P₀ := (hgm.contDiffAt (x := (z₀, 0))).toOpenPartialHomeomorph (graphMap G) hder (by simp)
  refine ⟨P₀.restrOpen U hU, rfl, ⟨?_, hdet0⟩, fun q hq => hq.2, fun p hp => ?_⟩
  · exact (hgm.contDiffAt).mem_toOpenPartialHomeomorph_source hder (by simp)
  · set P := P₀.restrOpen U hU
    have hq : P.symm p ∈ P.source := P.map_target hp
    have hdet : (dFst G (P.symm p)).det ≠ 0 := hq.2
    refine P.contDiffAt_symm hp (f₀' := graphDerivEquiv G (P.symm p) hdet) ?_ hgm.contDiffAt
    rw [coe_graphDerivEquiv]
    exact hasFDerivAt_graphMap hG1 _

/-! ### The adjoint density -/

section Density

variable {P : OpenPartialHomeomorph (E × E) (E × E)} {G : E × E → E}

/-- The adjoint density `Ã(y, η) = ψ(z) / |det D_zG(z, η)|`, where `(z, η) = P⁻¹(y, η)`. -/
def adjDensity (P : OpenPartialHomeomorph (E × E) (E × E)) (G : E × E → E) (ψ : E → ℝ) :
    E × E → ℝ :=
  P.target.indicator fun p => ψ (P.symm p).1 * (jacFst G (P.symm p))⁻¹

theorem graphMap_symm (hPG : ⇑P = graphMap G) {p : E × E} (hp : p ∈ P.target) :
    G (P.symm p) = p.1 ∧ (P.symm p).2 = p.2 := by
  have h := P.right_inv hp
  rw [hPG, graphMap] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact ⟨h1, h2⟩

theorem adjDensity_graphMap (hPG : ⇑P = graphMap G) (ψ : E → ℝ) {q : E × E}
    (hq : q ∈ P.source) : adjDensity P G ψ (graphMap G q) = ψ q.1 * (jacFst G q)⁻¹ := by
  have h1 : graphMap G q ∈ P.target := by rw [← hPG]; exact P.map_source hq
  have h2 : P.symm (graphMap G q) = q := by rw [← hPG]; exact P.left_inv hq
  rw [adjDensity, indicator_of_mem h1, h2]

/-- Where the adjoint density does not vanish, the point is the image of a point of the support. -/
theorem mem_of_adjDensity_ne_zero (hPG : ⇑P = graphMap G) {ψ : E → ℝ} {p : E × E}
    (hp : adjDensity P G ψ p ≠ 0) :
    p ∈ P.target ∧ (P.symm p).1 ∈ Function.support ψ ∧ P.symm p = ((P.symm p).1, p.2) ∧
      G ((P.symm p).1, p.2) = p.1 := by
  have ht : p ∈ P.target := by
    by_contra h
    exact hp (indicator_of_notMem h _)
  rw [adjDensity, indicator_of_mem ht] at hp
  have hψ : ψ (P.symm p).1 ≠ 0 := left_ne_zero_of_mul hp
  obtain ⟨hG1, hG2⟩ := graphMap_symm hPG ht
  have he : P.symm p = ((P.symm p).1, p.2) := Prod.ext rfl hG2
  refine ⟨ht, hψ, he, ?_⟩
  rw [← he]
  exact hG1

theorem adjDensity_abs (ψ : E → ℝ) (p : E × E) :
    adjDensity P G (fun z => |ψ z|) p = |adjDensity P G ψ p| := by
  by_cases hp : p ∈ P.target
  · rw [adjDensity, adjDensity, indicator_of_mem hp, indicator_of_mem hp, abs_mul, abs_inv,
      jacFst, abs_abs]
  · rw [adjDensity, adjDensity, indicator_of_notMem hp, indicator_of_notMem hp, abs_zero]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem injOn_fibre (hPG : ⇑P = graphMap G) {s : Set E} {η : E}
    (hK : ∀ z ∈ s, (z, η) ∈ P.source) : InjOn (fun z => G (z, η)) s := by
  intro z hz z' hz' h
  have hP : P (z, η) = P (z', η) := by
    rw [hPG]
    simp only [graphMap] at h ⊢
    rw [h]
  exact (Prod.ext_iff.mp (P.injOn (hK z hz) (hK z' hz') hP)).1

/-- **The change of variables `y = G(z, η)`**, for every function `F`. -/
theorem integral_comp_mul_eq (hPG : ⇑P = graphMap G) (hG : Differentiable ℝ G)
    (hdet : ∀ q ∈ P.source, (dFst G q).det ≠ 0) {ψ : E → ℝ} {η : E}
    (hK : ∀ z ∈ tsupport ψ, (z, η) ∈ P.source) (F : E → ℝ) :
    ∫ z, F (G (z, η)) * ψ z ∂μ = ∫ y, F y * adjDensity P G ψ (y, η) ∂μ := by
  set s := tsupport ψ with hsdef
  have hs : MeasurableSet s := (isClosed_tsupport ψ).measurableSet
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ hs
    (fun z _ => (hasFDerivAt_fst hG (z, η)).hasFDerivWithinAt) (injOn_fibre hPG hK)
    (fun y => F y * adjDensity P G ψ (y, η))
  -- the left side
  have hL : ∫ y in (fun z => G (z, η)) '' s, F y * adjDensity P G ψ (y, η) ∂μ =
      ∫ y, F y * adjDensity P G ψ (y, η) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    by_contra hne
    have hA : adjDensity P G ψ (y, η) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨-, hsupp, -, hGy⟩ := mem_of_adjDensity_ne_zero hPG hA
    exact hy ⟨_, subset_tsupport ψ hsupp, hGy⟩
  -- the right side
  have hR : ∫ z in s, |(dFst G (z, η)).det| • (F (G (z, η)) * adjDensity P G ψ (G (z, η), η)) ∂μ =
      ∫ z, F (G (z, η)) * ψ z ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := s)
      (f := fun z => F (G (z, η)) * ψ z) fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]]
    refine setIntegral_congr_fun hs fun z hz => ?_
    have h := adjDensity_graphMap hPG ψ (hK z hz)
    simp only [graphMap] at h
    have hne : jacFst G (z, η) ≠ 0 := abs_ne_zero.mpr (hdet _ (hK z hz))
    rw [h, smul_eq_mul]
    change jacFst G (z, η) * _ = _
    field_simp
  rw [← hL, hcv, hR]

/-- **Integrability after the change of variables.** -/
theorem integrable_comp_mul (hPG : ⇑P = graphMap G) (hG : Differentiable ℝ G)
    (hdet : ∀ q ∈ P.source, (dFst G q).det ≠ 0) {ψ : E → ℝ} {η : E}
    (hK : ∀ z ∈ tsupport ψ, (z, η) ∈ P.source) {F : E → ℝ} {C : Set E}
    (hC : ∀ z ∈ tsupport ψ, G (z, η) ∈ C) (hF : IntegrableOn F C μ)
    (hA : AEStronglyMeasurable (fun y => adjDensity P G ψ (y, η)) μ) {M : ℝ}
    (hM : ∀ y, |adjDensity P G ψ (y, η)| ≤ M) :
    Integrable (fun z => F (G (z, η)) * ψ z) μ := by
  set s := tsupport ψ with hsdef
  have hs : MeasurableSet s := (isClosed_tsupport ψ).measurableSet
  have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs
    (fun z _ => (hasFDerivAt_fst hG (z, η)).hasFDerivWithinAt) (injOn_fibre hPG hK)
    (fun y => F y * adjDensity P G ψ (y, η))
  have himg : (fun z => G (z, η)) '' s ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩; exact hC z hz
  have h1 : Integrable (fun y => F y * adjDensity P G ψ (y, η))
      (μ.restrict ((fun z => G (z, η)) '' s)) := by
    have h := (hF.mono_set himg).bdd_mul (c := M) hA.restrict
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
    simpa only [mul_comm] using h
  have h2 := hiff.mp h1
  have h3 : IntegrableOn (fun z => F (G (z, η)) * ψ z) s μ := by
    refine h2.congr_fun (fun z hz => ?_) hs
    have h := adjDensity_graphMap hPG ψ (hK z hz)
    simp only [graphMap] at h
    have hne : jacFst G (z, η) ≠ 0 := abs_ne_zero.mpr (hdet _ (hK z hz))
    show |(dFst G (z, η)).det| • (F (G (z, η)) * adjDensity P G ψ (G (z, η), η)) = _
    rw [h, smul_eq_mul]
    change jacFst G (z, η) * _ = _
    field_simp
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h3
  intro z hz
  by_contra hzs
  exact hz (by simp [image_eq_zero_of_notMem_tsupport hzs])

/-- **Integrability after the change of variables**, from the integrability of `F Ã(·, η)`. -/
theorem integrable_comp_mul' (hPG : ⇑P = graphMap G) (hG : Differentiable ℝ G)
    (hdet : ∀ q ∈ P.source, (dFst G q).det ≠ 0) {ψ : E → ℝ} {η : E}
    (hK : ∀ z ∈ tsupport ψ, (z, η) ∈ P.source) {F : E → ℝ}
    (hFA : Integrable (fun y => F y * adjDensity P G ψ (y, η)) μ) :
    Integrable (fun z => F (G (z, η)) * ψ z) μ := by
  set s := tsupport ψ with hsdef
  have hs : MeasurableSet s := (isClosed_tsupport ψ).measurableSet
  have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs
    (fun z _ => (hasFDerivAt_fst hG (z, η)).hasFDerivWithinAt) (injOn_fibre hPG hK)
    (fun y => F y * adjDensity P G ψ (y, η))
  have h2 := hiff.mp hFA.integrableOn
  have h3 : IntegrableOn (fun z => F (G (z, η)) * ψ z) s μ := by
    refine h2.congr_fun (fun z hz => ?_) hs
    have h := adjDensity_graphMap hPG ψ (hK z hz)
    simp only [graphMap] at h
    have hne : jacFst G (z, η) ≠ 0 := abs_ne_zero.mpr (hdet _ (hK z hz))
    show |(dFst G (z, η)).det| • (F (G (z, η)) * adjDensity P G ψ (G (z, η), η)) = _
    rw [h, smul_eq_mul]
    change jacFst G (z, η) * _ = _
    field_simp
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h3
  intro z hz
  by_contra hzs
  exact hz (by simp [image_eq_zero_of_notMem_tsupport hzs])

end Density

/-! ### Smoothness of the adjoint density and the package -/

section Package

variable {P : OpenPartialHomeomorph (E × E) (E × E)} {G : E × E → E}

theorem contDiffAt_jacFst_inv {G : E × E → E} (hG : ContDiff ℝ ∞ G) {q : E × E}
    (hq : (dFst G q).det ≠ 0) : ContDiffAt ℝ ∞ (fun q => (jacFst G q)⁻¹) q :=
  ((contDiffAt_abs hq).comp q (contDiff_det_dFst hG).contDiffAt).inv (abs_ne_zero.mpr hq)

/-- Where the adjoint density does not vanish, the point lies in the image of the support. -/
theorem mem_image_of_adjDensity_ne_zero (hPG : ⇑P = graphMap G) {ψ : E → ℝ} {r : ℝ}
    {p : E × E} (hp : adjDensity P G ψ p ≠ 0) (hr : ‖p.2‖ ≤ r) :
    p ∈ P '' (tsupport ψ ×ˢ closedBall (0 : E) r) := by
  obtain ⟨ht, hsupp, he, -⟩ := mem_of_adjDensity_ne_zero hPG hp
  refine ⟨P.symm p, ?_, P.right_inv ht⟩
  rw [he]
  exact ⟨subset_tsupport ψ hsupp, by simpa using hr⟩

/-- **The adjoint density is smooth on the slab `‖η‖ < r`.** -/
theorem contDiffAt_adjDensity (hPG : ⇑P = graphMap G) (hG : ContDiff ℝ ∞ G)
    (hdet : ∀ q ∈ P.source, (dFst G q).det ≠ 0)
    (hsymm : ∀ p ∈ P.target, ContDiffAt ℝ ∞ P.symm p) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {r : ℝ} (hK : tsupport ψ ×ˢ closedBall (0 : E) r ⊆ P.source)
    {p : E × E} (hp : ‖p.2‖ < r) : ContDiffAt ℝ ∞ (adjDensity P G ψ) p := by
  by_cases ht : p ∈ P.target
  · have hev : adjDensity P G ψ =ᶠ[𝓝 p]
        fun p => ψ (P.symm p).1 * (jacFst G (P.symm p))⁻¹ := by
      filter_upwards [P.open_target.mem_nhds ht] with p' hp'
      rw [adjDensity, indicator_of_mem hp']
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hs := hsymm p ht
    have hq : P.symm p ∈ P.source := P.map_target ht
    exact (hψ.contDiffAt.comp p (contDiffAt_fst.comp p hs)).mul
      ((contDiffAt_jacFst_inv hG (hdet _ hq)).comp p hs)
  · set Kc := P '' (tsupport ψ ×ˢ closedBall (0 : E) r) with hKcdef
    have hKc : IsCompact Kc :=
      (hψc.prod (isCompact_closedBall 0 r)).image_of_continuousOn (P.continuousOn.mono hK)
    have hpK : p ∉ Kc := by
      rintro ⟨q, hq, rfl⟩
      exact ht (P.map_source (hK hq))
    have hev : adjDensity P G ψ =ᶠ[𝓝 p] fun _ => 0 := by
      have hr : IsOpen {p' : E × E | ‖p'.2‖ < r} :=
        isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hpK, hr.mem_nhds hp] with p' hp' hr'
      by_contra hne
      exact hp' (mem_image_of_adjDensity_ne_zero hPG hne (le_of_lt hr'))
    exact contDiffAt_const.congr_of_eventuallyEq hev

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The output of the change of variables**: a smooth compactly supported density `A` with
`A(y, 0) = ψ(y)`, vanishing for `y ∉ C`, which represents the adjoint of `ψ ↦ ψ(G(·, η))` for
`‖η‖ < t₀`. -/
structure IsAdjointDensity (G : E × E → E) (ψ : E → ℝ) (t₀ : ℝ) (C : Set E)
    (A : E × E → ℝ) : Prop where
  pos : 0 < t₀
  contDiff : ContDiff ℝ ∞ A
  hasCompactSupport : HasCompactSupport A
  eq_zero : ∀ y, A (y, 0) = ψ y
  isCompact : IsCompact C
  vanish : ∀ p : E × E, p.1 ∉ C → A p = 0
  integral_eq : ∀ η : E, ‖η‖ < t₀ → ∀ F : E → ℝ,
    ∫ z, F (G (z, η)) * ψ z ∂μ = ∫ y, F y * A (y, η) ∂μ
  integral_abs_eq : ∀ η : E, ‖η‖ < t₀ → ∀ F : E → ℝ,
    ∫ z, F (G (z, η)) * |ψ z| ∂μ = ∫ y, F y * |A (y, η)| ∂μ
  integrable : ∀ η : E, ‖η‖ < t₀ → ∀ F : E → ℝ, IntegrableOn F C μ →
    Integrable (fun z => F (G (z, η)) * ψ z) μ
  mapsTo : ∀ z ∈ tsupport ψ, ∀ η : E, ‖η‖ < t₀ → G (z, η) ∈ C

/-- The inverse of the fibre map attached to an adjoint density: `inv(G(z, η), η) = z`, smooth
near the support of `A`. -/
structure IsAdjointInverse (G : E × E → E) (ψ : E → ℝ) (t₀ : ℝ) (A : E × E → ℝ)
    (inv : E × E → E) : Prop where
  smooth : ∃ T : Set (E × E), IsOpen T ∧ tsupport A ⊆ T ∧ ContDiffOn ℝ ∞ inv T
  apply : ∀ z ∈ tsupport ψ, ∀ η : E, ‖η‖ < t₀ → inv (G (z, η), η) = z
  zero : ∀ y : E, A (y, 0) ≠ 0 → inv (y, 0) = y
  integrable : ∀ η : E, ‖η‖ < t₀ → ∀ F : E → ℝ, Integrable (fun y => F y * A (y, η)) μ →
    Integrable (fun z => F (G (z, η)) * ψ z) μ

/-- **Existence of the adjoint density** (FPT `lem:chern-joint-smoothing`, Step 7): for smooth
`G` with `G(z, 0) = z` and every point `z₀` there is `ε > 0` such that every smooth `ψ` supported
in `B(z₀, ε)` has an adjoint density. -/
theorem exists_adjointDensity {G : E × E → E} (hG : ContDiff ℝ ∞ G) (hG0 : ∀ z, G (z, 0) = z)
    (z₀ : E) {W : Set E} (hW : IsOpen W) (hz₀W : z₀ ∈ W) :
    ∃ ε > 0, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ ball z₀ ε →
      ∃ (t₀ : ℝ) (C : Set E) (A : E × E → ℝ) (inv : E × E → E),
        IsAdjointDensity μ G ψ t₀ C A ∧ C ⊆ W ∧ IsAdjointInverse μ G ψ t₀ A inv := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by simp)
  obtain ⟨P, hPG, hz₀, hdet, hsymm⟩ := exists_graphChart hG hG0 z₀
  obtain ⟨ε, hε, hball2⟩ := Metric.isOpen_iff.mp (P.open_source.inter (hW.preimage hG.continuous))
    _ (⟨hz₀, by simpa [hG0] using hz₀W⟩ : ((z₀, 0) : E × E) ∈ P.source ∩ G ⁻¹' W)
  have hball : ball ((z₀, 0) : E × E) ε ⊆ P.source := fun p hp => (hball2 hp).1
  have hballW : ∀ p ∈ ball ((z₀, 0) : E × E) ε, G p ∈ W := fun p hp => (hball2 hp).2
  refine ⟨ε, hε, fun ψ hψ hψs => ?_⟩
  set r := ε / 2 with hrdef
  have hr : 0 < r := by positivity
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall z₀ ε).of_isClosed_subset (isClosed_tsupport ψ)
      (hψs.trans ball_subset_closedBall)
  have hKb : tsupport ψ ×ˢ closedBall (0 : E) r ⊆ ball ((z₀, 0) : E × E) ε := by
    rintro ⟨z, η⟩ ⟨hz, hη⟩
    rw [← ball_prod_same]
    refine ⟨hψs hz, ?_⟩
    simp only [mem_closedBall, dist_zero_right] at hη
    simp only [mem_ball, dist_zero_right]
    linarith
  have hK : tsupport ψ ×ˢ closedBall (0 : E) r ⊆ P.source := hKb.trans hball
  -- the cut-off in `η`
  let β : ContDiffBump (0 : E) := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  set A : E × E → ℝ := fun p => β p.2 * adjDensity P G ψ p with hAdef
  set Kc := P '' (tsupport ψ ×ˢ closedBall (0 : E) r) with hKcdef
  have hKc : IsCompact Kc :=
    (hψc.prod (isCompact_closedBall 0 r)).image_of_continuousOn (P.continuousOn.mono hK)
  have hβ1 : ∀ η : E, ‖η‖ < r / 2 → β η = 1 := fun η hη =>
    β.one_of_mem_closedBall (by simpa using hη.le)
  have hAsupp : ∀ p, A p ≠ 0 → p ∈ Kc := by
    intro p hp
    have hβ : β p.2 ≠ 0 := left_ne_zero_of_mul hp
    have hadj : adjDensity P G ψ p ≠ 0 := right_ne_zero_of_mul hp
    have hmem : p.2 ∈ Function.support β := hβ
    rw [β.support_eq] at hmem
    have h34 : ‖p.2‖ < 3 * r / 4 := by simpa using hmem
    exact mem_image_of_adjDensity_ne_zero hPG hadj (by linarith)
  have hAeq : ∀ y η, ‖η‖ < r / 2 → A (y, η) = adjDensity P G ψ (y, η) := by
    intro y η hη
    simp only [hAdef]
    rw [hβ1 η hη, one_mul]
  -- smoothness
  have hAc : ContDiff ℝ ∞ A := by
    refine contDiff_iff_contDiffAt.mpr fun p => ?_
    by_cases hp : ‖p.2‖ < r
    · exact (β.contDiff.comp contDiff_snd).contDiffAt.mul
        (contDiffAt_adjDensity hPG hG hdet hsymm hψ hψc hK hp)
    · have hnot : p.2 ∉ tsupport β := by
        have hro : β.rOut = 3 * r / 4 := rfl
        rw [β.tsupport_eq, hro]
        simp only [mem_closedBall, dist_zero_right, not_le]
        linarith [not_lt.mp hp]
      have hev0 := (notMem_tsupport_iff_eventuallyEq).mp hnot
      have hev : A =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [(continuous_snd.tendsto p).eventually hev0] with p' hp'
        simp only [hAdef]
        rw [hp']
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hAcs : HasCompactSupport A :=
    HasCompactSupport.intro hKc fun p hp => by
      by_contra hne
      exact hp (hAsupp p hne)
  obtain ⟨M, hM⟩ := hAc.continuous.bounded_above_of_compact_support hAcs
  -- the facts for `‖η‖ < r / 2`
  have hKη : ∀ η : E, ‖η‖ < r / 2 → ∀ z ∈ tsupport ψ, (z, η) ∈ P.source := by
    intro η hη z hz
    exact hK ⟨hz, by simp only [mem_closedBall, dist_zero_right]; linarith⟩
  have hsuppabs : tsupport (fun z => |ψ z|) = tsupport ψ := by
    have : Function.support (fun z => |ψ z|) = Function.support ψ := by ext z; simp
    rw [tsupport, this, tsupport]
  have hmaps : ∀ z ∈ tsupport ψ, ∀ η : E, ‖η‖ < r / 2 → G (z, η) ∈ Prod.fst '' Kc := by
    intro z hz η hη
    refine ⟨P (z, η), ⟨(z, η), ⟨hz, ?_⟩, rfl⟩, ?_⟩
    · simp only [mem_closedBall, dist_zero_right]; linarith
    · rw [hPG]; rfl
  have hCW : Prod.fst '' Kc ⊆ W := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [hPG]
    exact hballW q (hKb hq)
  have hKcT : Kc ⊆ P.target := by
    rintro _ ⟨q, hq, rfl⟩; exact P.map_source (hK hq)
  have hAts : tsupport A ⊆ Kc :=
    closure_minimal (fun p hp => hAsupp p hp) hKc.isClosed
  have hinv : IsAdjointInverse μ G ψ (r / 2) A (fun p => (P.symm p).1) := by
    refine ⟨⟨P.target, P.open_target, hAts.trans hKcT, fun p hp =>
      (contDiffAt_fst.comp p (hsymm p hp)).contDiffWithinAt⟩, ?_, ?_, ?_⟩
    · intro z hz η hη
      have hq := hKη η hη z hz
      have h1 : P.symm (P (z, η)) = (z, η) := P.left_inv hq
      have h2 : P (z, η) = (G (z, η), η) := by rw [hPG]; rfl
      rw [h2] at h1
      simp only [h1]
    · intro y hy
      have hadj : adjDensity P G ψ (y, 0) ≠ 0 := by
        rwa [← hAeq y 0 (by simpa using half_pos hr)]
      obtain ⟨-, -, -, hGy⟩ := mem_of_adjDensity_ne_zero hPG hadj
      simp only [hG0] at hGy
      exact hGy
    · intro η hη F hF
      have hF' : Integrable (fun y => F y * adjDensity P G ψ (y, η)) μ := by
        refine hF.congr (Eventually.of_forall fun y => ?_)
        simp only
        rw [hAeq y η hη]
      exact integrable_comp_mul' μ hPG hG1 hdet (hKη η hη) hF'
  refine ⟨r / 2, Prod.fst '' Kc, A, fun p => (P.symm p).1,
    ⟨by positivity, hAc, hAcs, ?_, hKc.image continuous_fst, ?_, ?_, ?_, ?_, hmaps⟩, hCW, hinv⟩
  · -- `A(y, 0) = ψ(y)`
    intro y
    rw [hAeq y 0 (by simpa using half_pos hr)]
    by_cases hy : ψ y = 0
    · rw [hy]
      by_contra hne
      obtain ⟨-, hsupp, -, hGy⟩ := mem_of_adjDensity_ne_zero hPG hne
      rw [hG0] at hGy
      exact hsupp (by rw [hGy]; exact hy)
    · have hq : ((y, 0) : E × E) ∈ P.source :=
        hK ⟨subset_tsupport ψ hy, by simp [hr.le]⟩
      have h := adjDensity_graphMap hPG ψ hq
      simp only [graphMap, hG0] at h
      rw [h, jacFst_zero hG1 hG0, inv_one, mul_one]
  · -- vanishing off `C`
    intro p hp
    by_contra hne
    exact hp ⟨p, hAsupp p hne, rfl⟩
  · -- the change of variables
    intro η hη F
    rw [integral_comp_mul_eq μ hPG hG1 hdet (hKη η hη) F]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hAeq y η hη]
  · intro η hη F
    have hK' : ∀ z ∈ tsupport (fun z => |ψ z|), (z, η) ∈ P.source := by
      rw [hsuppabs]; exact hKη η hη
    rw [integral_comp_mul_eq μ hPG hG1 hdet hK' F]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hAeq y η hη, adjDensity_abs]
  · intro η hη F hF
    have hC : ∀ z ∈ tsupport ψ, G (z, η) ∈ Prod.fst '' Kc := fun z hz => hmaps z hz η hη
    have hcont : Continuous fun y => adjDensity P G ψ (y, η) := by
      have h : (fun y => adjDensity P G ψ (y, η)) = fun y => A (y, η) := by
        funext y; rw [hAeq y η hη]
      rw [h]
      exact hAc.continuous.comp (continuous_id.prodMk continuous_const)
    refine integrable_comp_mul μ hPG hG1 hdet (hKη η hη) hC hF hcont.aestronglyMeasurable
      (M := M) fun y => ?_
    rw [← hAeq y η hη, ← Real.norm_eq_abs]
    exact hM _

end Package

end SGPT.NPP.DN6
