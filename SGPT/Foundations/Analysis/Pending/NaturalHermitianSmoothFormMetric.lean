import SGPT.Foundations.Analysis.Pending.NaturalHermitianOriginalFormMetric
import Mathlib.Analysis.Matrix.Normed

/-! # Actual full-norm smooth and compatible metrics on all original form coefficients -/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianSmoothFormMetric

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients
  NaturalHermitianDualMetric NaturalHermitianExteriorCovectorMetric NaturalHermitianOriginalFormMetric

variable {n : ℕ}

/-- The actual finite exterior-coordinate index, empty in excessive degree. -/
abbrev FormIndex (n q : ℕ) := Set.powersetCard (Fin (n * 2)) q

/-- The original continuous alternating coefficient fiber, with its original operator norm. -/
abbrev FormCoefficients (n q : ℕ) := (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ

local instance matrixNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (Matrix (FormIndex n q) (FormIndex n q) ℝ) := Matrix.normedAddCommGroup

local instance matrixNormedSpace (q : ℕ) :
    NormedSpace ℝ (Matrix (FormIndex n q) (FormIndex n q) ℝ) := Matrix.normedSpace

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formBilinearNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formBilinearNormedSpace (q : ℕ) :
    NormedSpace ℝ (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance dualNormedAddCommGroup : NormedAddCommGroup (ComplexModel n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance dualNormedSpace : NormedSpace ℝ (ComplexModel n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance bidualNormedAddCommGroup : NormedAddCommGroup ((ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bidualNormedSpace : NormedSpace ℝ ((ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Pointwise readback of the genuine algebraic-to-continuous equivalence. -/
theorem algebraicContinuousEquiv_apply (q : ℕ)
    (A : (ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) (v : Fin q → ComplexModel n) :
    algebraicContinuousEquiv q A v = A v := by
  exact congrArg (fun F : (ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ => F v)
    ((algebraicContinuousEquiv q).symm_apply_apply A)

/-- Fixed determinant basis of the original form fiber, independent of any Hermitian metric. -/
def originalFormBasis (q : ℕ) : Module.Basis (FormIndex n q) ℝ (FormCoefficients n q) :=
  ((coordinateRealBasis n).exteriorPower q).dualBasis.map
    ((exteriorPower.alternatingMapLinearEquiv :
      ((ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) ≃ₗ[ℝ]
        Module.Dual ℝ (⋀[ℝ]^q (ComplexModel n))).symm.trans (algebraicContinuousEquiv q))

/-- Literal original continuous coordinate covectors occurring in a determinant basis element. -/
def formBasisCovectors (q : ℕ) (s : FormIndex n q) (j : Fin q) : ComplexModel n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((coordinateRealBasis n).coord (Set.powersetCard.ofFinEmbEquiv.symm s j))

/-- Entire original vector-tuple determinant readback of the fixed form basis. -/
theorem originalFormBasis_apply (q : ℕ) (s : FormIndex n q) (v : Fin q → ComplexModel n) :
    originalFormBasis q s v = Matrix.det (Matrix.of fun i j => formBasisCovectors q s j (v i)) := by
  change algebraicContinuousEquiv q
    (exteriorPower.alternatingMapLinearEquiv.symm
      (((coordinateRealBasis n).exteriorPower q).dualBasis s)) v = _
  rw [algebraicContinuousEquiv_apply, exteriorPower.alternatingMapLinearEquiv_symm_apply]
  change ((coordinateRealBasis n).exteriorPower q).dualBasis s (exteriorPower.ιMulti ℝ q v) = _
  rw [Module.Basis.coe_dualBasis, exteriorPower.basis_coord,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

/-- Actual continuous coefficient functionals in the unchanged original fiber norm. -/
def formCoordCLM (q : ℕ) (s : FormIndex n q) : FormCoefficients n q →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((originalFormBasis q).coord s)

/-- Actual finite-matrix linear reconstruction of an entire continuous bilinear operator. -/
def bilinearReconstructionLinear (q : ℕ) : Matrix (FormIndex n q) (FormIndex n q) ℝ →ₗ[ℝ]
    FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ where
  toFun A := ∑ s, ∑ t, A s t • (formCoordCLM q s).smulRight (formCoordCLM q t)
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r A := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul,
      Finset.smul_sum]

/-- Genuine continuity of the finite-dimensional matrix reconstruction in the full operator norm. -/
def bilinearReconstructionCLM (q : ℕ) : Matrix (FormIndex n q) (FormIndex n q) ℝ →L[ℝ]
    FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ :=
  (bilinearReconstructionLinear q).toContinuousLinearMap

/-- Literal whole-operator finite coordinate formula, on arbitrary original form tensors. -/
theorem bilinearReconstructionCLM_apply (q : ℕ)
    (A : Matrix (FormIndex n q) (FormIndex n q) ℝ) (η θ : FormCoefficients n q) :
    bilinearReconstructionCLM q A η θ =
      ∑ s, ∑ t, A s t * (originalFormBasis q).coord s η * (originalFormBasis q).coord t θ := by
  simp [bilinearReconstructionCLM, bilinearReconstructionLinear, formCoordCLM,
    sum_apply, mul_assoc]

/-- The actual reconstructed operator reads back every original matrix entry on the fixed basis. -/
theorem bilinearReconstructionCLM_basis (q : ℕ)
    (A : Matrix (FormIndex n q) (FormIndex n q) ℝ) (s t : FormIndex n q) :
    bilinearReconstructionCLM q A (originalFormBasis q s) (originalFormBasis q t) = A s t := by
  rw [bilinearReconstructionCLM_apply]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

/-- The fixed basis is the actual dictionary image of its original coordinate covectors. -/
theorem originalFormBasis_eq_dictionary (q : ℕ) (s : FormIndex n q)
    (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hJ : IsOneOne a)
    (hp : IsStrictlyPositive a) :
    originalFormBasis q s = originalFormDictionary a hJ hp q
      (exteriorCovectorDecomposable a hJ hp q (formBasisCovectors q s)) := by
  ext v
  rw [originalFormBasis_apply, originalFormDictionary_decomposable_apply]

/-- Equality on fixed basis pairs determines the entire original bilinear operator. -/
theorem bilinear_ext_basis (q : ℕ)
    {G H : FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ}
    (h : ∀ s t : FormIndex n q, G (originalFormBasis q s) (originalFormBasis q t) =
      H (originalFormBasis q s) (originalFormBasis q t)) : G = H := by
  have hlin : G.toLinearMap = H.toLinearMap := by
    apply (originalFormBasis q).ext
    intro s
    have hlin' : (G (originalFormBasis q s)).toLinearMap =
        (H (originalFormBasis q s)).toLinearMap := (originalFormBasis q).ext (h s)
    exact ContinuousLinearMap.ext (fun θ => DFunLike.congr_fun hlin' θ)
  exact ContinuousLinearMap.ext (fun η => DFunLike.congr_fun hlin η)

/-- Actual finite signed-product determinant smoothness over the reals, including size zero. -/
theorem determinant_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {s : Set E} {F : E → Matrix (Fin q) (Fin q) ℝ}
    (hF : ∀ i j, ContDiffOn ℝ ∞ (fun x => F x i j) s) :
    ContDiffOn ℝ ∞ (fun x => Matrix.det (F x)) s := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ =>
    contDiffOn_const.mul (contDiffOn_prod fun i _ => hF (σ i) i)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Literal finite inverse-metric Gram matrix in the fixed original determinant coordinates. -/
def formGramMatrix (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) : Matrix (FormIndex n q) (FormIndex n q) ℝ :=
  fun s t => Matrix.det (Matrix.of fun i j =>
    dualMetricCoefficients w e z (formBasisCovectors q s j) (formBasisCovectors q t i))

/-- Actual all-degree coefficient field in the original full bilinear operator norm. -/
def formMetricCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) :
    FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ :=
  bilinearReconstructionCLM q (formGramMatrix w e z q)

/-- Full norm smoothness of the whole finite original Gram-matrix field. -/
theorem formGramMatrix_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (fun z => formGramMatrix w e z q) e.val.target := by
  apply contDiffOn_pi'
  intro s
  apply contDiffOn_pi'
  intro t
  apply determinant_contDiffOn
  intro i j
  change ContDiffOn ℝ ∞ (fun z => dualMetricCoefficients w e z
    (formBasisCovectors q s j) (formBasisCovectors q t i)) e.val.target
  exact ((dualMetricCoefficients_smooth w hw e).clm_apply
    (show ContDiffOn ℝ ∞ (fun _ : ComplexModel n => formBasisCovectors q s j)
      e.val.target from contDiffOn_const)).clm_apply
        (show ContDiffOn ℝ ∞ (fun _ : ComplexModel n => formBasisCovectors q t i)
          e.val.target from contDiffOn_const)

/-- Actual smoothness in the full unchanged original bilinear operator norm in every degree. -/
theorem formMetricCoefficients_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (fun z => formMetricCoefficients w e z q) e.val.target := by
  apply ContDiff.comp_contDiffOn ?_ (formGramMatrix_smooth w hw e q)
  exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := Matrix (FormIndex n q) (FormIndex n q) ℝ)
    (F := FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ)
    (by exact bilinearReconstructionCLM q)

/-- The smooth field equals the genuine exterior metric as an entire original bilinear operator. -/
theorem formMetricCoefficients_eq_original (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    formMetricCoefficients w e z q =
      originalFormMetric (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q := by
  apply bilinear_ext_basis q
  intro s t
  change bilinearReconstructionCLM q (formGramMatrix w e z q)
    (originalFormBasis q s) (originalFormBasis q t) = _
  rw [bilinearReconstructionCLM_basis,
    originalFormBasis_eq_dictionary q s (w.coeff e z) (hw e z hz).1 (hw e z hz).2,
    originalFormBasis_eq_dictionary q t (w.coeff e z) (hw e z hz).1 (hw e z hz).2,
    originalFormMetric_decomposable]
  rfl

/-- Actual symmetry and strict positivity on the entire original coefficient fiber. -/
theorem formMetricCoefficients_positive (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    (∀ η θ : FormCoefficients n q,
      formMetricCoefficients w e z q η θ = formMetricCoefficients w e z q θ η) ∧
    ∀ η : FormCoefficients n q, η ≠ 0 → 0 < formMetricCoefficients w e z q η η := by
  rw [formMetricCoefficients_eq_original w hw e z hz q]
  exact originalFormMetric_symm_positive (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q

/-- Actual original alternating pullback carries determinant forms to composed covectors. -/
theorem dictionary_decomposable_pullback (q : ℕ)
    (a b : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (haJ : IsOneOne a) (hap : IsStrictlyPositive a)
    (hbJ : IsOneOne b) (hbp : IsStrictlyPositive b)
    (C : ComplexModel n →L[ℝ] ComplexModel n)
    (α : Fin q → (ComplexModel n →L[ℝ] ℝ)) :
    (originalFormDictionary b hbJ hbp q (exteriorCovectorDecomposable b hbJ hbp q α)).compContinuousLinearMap C =
      originalFormDictionary a haJ hap q
        (exteriorCovectorDecomposable a haJ hap q (fun j => (α j).comp C)) := by
  ext v
  change originalFormDictionary b hbJ hbp q (exteriorCovectorDecomposable b hbJ hbp q α)
    (fun i => C (v i)) = _
  rw [originalFormDictionary_decomposable_apply, originalFormDictionary_decomposable_apply]
  rfl

/-- Literal inverse-metric Gram readback of the full smooth operator on any determinant forms. -/
theorem formMetricCoefficients_dictionary_gram (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ)
    (α β : Fin q → (ComplexModel n →L[ℝ] ℝ)) :
    formMetricCoefficients w e z q
      (originalFormDictionary (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q
        (exteriorCovectorDecomposable (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q α))
      (originalFormDictionary (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q
        (exteriorCovectorDecomposable (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q β)) =
      Matrix.det (Matrix.of fun i j => dualMetricCoefficients w e z (α j) (β i)) := by
  rw [formMetricCoefficients_eq_original w hw e z hz q, originalFormMetric_decomposable]
  rfl

/-- Actual entrywise covector transport gives the whole inverse-metric Gram determinant transport. -/
theorem gramDet_transport (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source)
    (q : ℕ) (α β : Fin q → (ComplexModel n →L[ℝ] ℝ)) :
    Matrix.det (Matrix.of fun i j => dualMetricCoefficients w e z
      ((α j).comp (chartTransitionDerivative e f z))
      ((β i).comp (chartTransitionDerivative e f z))) =
      Matrix.det (Matrix.of fun i j => dualMetricCoefficients w f (chartTransition e f z)
        (α j) (β i)) := by
  congr 1
  ext i j
  exact dualMetricCoefficients_transport w hw e f z hz (α j) (β i)

/-- Genuine full form metric transport first on arbitrary determinant forms. -/
theorem formMetricCoefficients_decomposable_transport (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) (q : ℕ)
    (α β : Fin q → (ComplexModel n →L[ℝ] ℝ))
    (hzf : chartTransition e f z ∈ f.val.target) :
    let A := originalFormDictionary (w.coeff f (chartTransition e f z))
      (hw f (chartTransition e f z) hzf).1 (hw f (chartTransition e f z) hzf).2 q
    let αf := exteriorCovectorDecomposable (w.coeff f (chartTransition e f z))
      (hw f (chartTransition e f z) hzf).1 (hw f (chartTransition e f z) hzf).2 q α
    let βf := exteriorCovectorDecomposable (w.coeff f (chartTransition e f z))
      (hw f (chartTransition e f z) hzf).1 (hw f (chartTransition e f z) hzf).2 q β
    formMetricCoefficients w e z q
      ((A αf).compContinuousLinearMap (chartTransitionDerivative e f z))
      ((A βf).compContinuousLinearMap (chartTransitionDerivative e f z)) =
      formMetricCoefficients w f (chartTransition e f z) q (A αf) (A βf) := by
  dsimp only
  rw [dictionary_decomposable_pullback q (w.coeff e z) (w.coeff f (chartTransition e f z))
    (hw e z hz.1).1 (hw e z hz.1).2 (hw f (chartTransition e f z) hzf).1
    (hw f (chartTransition e f z) hzf).2]
  rw [dictionary_decomposable_pullback q (w.coeff e z) (w.coeff f (chartTransition e f z))
    (hw e z hz.1).1 (hw e z hz.1).2 (hw f (chartTransition e f z) hzf).1
    (hw f (chartTransition e f z) hzf).2]
  rw [formMetricCoefficients_dictionary_gram w hw e z hz.1 q,
    formMetricCoefficients_dictionary_gram w hw f (chartTransition e f z) hzf q]
  exact gramDet_transport w hw e f z hz q α β

/-- Whole original tensor chart transport, derived internally from the actual inverse metric law. -/
theorem formMetricCoefficients_transport (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source)
    (q : ℕ) (η θ : FormCoefficients n q) :
    formMetricCoefficients w e z q
        (η.compContinuousLinearMap (chartTransitionDerivative e f z))
        (θ.compContinuousLinearMap (chartTransitionDerivative e f z)) =
      formMetricCoefficients w f (chartTransition e f z) q η θ := by
  let C := chartTransitionDerivative e f z
  let P : FormCoefficients n q →L[ℝ] FormCoefficients n q :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM C
  let G := formMetricCoefficients w e z q
  let H := formMetricCoefficients w f (chartTransition e f z) q
  let GP : FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ (FormCoefficients n q) (FormCoefficients n q) ℝ).flip P).comp
      (G.comp P)
  have hzf : chartTransition e f z ∈ f.val.target := f.val.map_source hz.2
  have hGP : GP = H := by
    apply bilinear_ext_basis q
    intro s t
    change G ((originalFormBasis q s).compContinuousLinearMap C)
      ((originalFormBasis q t).compContinuousLinearMap C) = H (originalFormBasis q s)
        (originalFormBasis q t)
    dsimp [G, H]
    rw [originalFormBasis_eq_dictionary q s (w.coeff f (chartTransition e f z))
        (hw f (chartTransition e f z) hzf).1 (hw f (chartTransition e f z) hzf).2,
      originalFormBasis_eq_dictionary q t (w.coeff f (chartTransition e f z))
        (hw f (chartTransition e f z) hzf).1 (hw f (chartTransition e f z) hzf).2]
    exact formMetricCoefficients_decomposable_transport w hw e f z hz q
      (formBasisCovectors q s) (formBasisCovectors q t) hzf
  exact congrArg (fun B : FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ => B η θ) hGP

/-- The same original Hermitian form internally supplies all smooth, positive, compatible degrees. -/
theorem exists_original_smooth_compatible_form_metrics (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) :
    ∃ G : ∀ q : ℕ, ComplexChart n M → ComplexModel n →
        FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ,
      (∀ q e, ContDiffOn ℝ ∞ (G q e) e.val.target) ∧
      (∀ q e z, z ∈ e.val.target →
        (∀ η θ : FormCoefficients n q, G q e z η θ = G q e z θ η) ∧
        ∀ η : FormCoefficients n q, η ≠ 0 → 0 < G q e z η η) ∧
      (∀ q e z (hz : z ∈ e.val.target), G q e z =
        originalFormMetric (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q) ∧
      ∀ q e f z, z ∈ (chartTransition e f).source → ∀ η θ : FormCoefficients n q,
        G q e z (η.compContinuousLinearMap (chartTransitionDerivative e f z))
          (θ.compContinuousLinearMap (chartTransitionDerivative e f z)) =
            G q f (chartTransition e f z) η θ := by
  refine ⟨fun q e z => formMetricCoefficients w e z q, ?_, ?_, ?_, ?_⟩
  · intro q e
    exact formMetricCoefficients_smooth w hw e q
  · intro q e z hz
    exact formMetricCoefficients_positive w hw e z hz q
  · intro q e z hz
    exact formMetricCoefficients_eq_original w hw e z hz q
  · intro q e f z hz η θ
    exact formMetricCoefficients_transport w hw e f z hz q η θ

end SGPT.Foundations.Analysis.Pending.NaturalHermitianSmoothFormMetric
