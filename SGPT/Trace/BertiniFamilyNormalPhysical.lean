import SGPT.Trace.BertiniFamilyNormalIntegral

/-! Actual native normal top-form values and physical density, no atlas shortcut. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

private def actualTupleEvaluation {n : ℕ} {C V : Type*}
    [AddCommGroup C] [Module ℂ C] [AddCommGroup V] [Module ℂ V]
    (F : C ≃ₗ[ℂ] (V [⋀^Fin n]→ₗ[ℂ] ℂ)) (v : Fin n → V) : C →ₗ[ℂ] ℂ where
  toFun α := F α v
  map_add' α β := by rw [map_add, AlternatingMap.add_apply]
  map_smul' a α := by rw [map_smul, AlternatingMap.smul_apply]; rfl

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

omit [CompactSpace X] in
theorem familyFlatInverse_chart_derivative :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target) (u : ComplexModel (d + 1)),
      nativeOriginalChartTangentEquiv F.amb (finv F z) (finv_mem F hz).1
        (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z u) =
      fderiv ℂ F.flat.symm z u := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F z hz u
  have hA := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (d + 1))) F.amb.property (finv_mem F hz).1
  have hI := mdifferentiableAt_finv F hz
  have hcomp := mfderiv_comp z hA hI
  have heq : (F.amb.val ∘ finv F) =ᶠ[𝓝 z] F.flat.symm := by
    filter_upwards [F.flat.open_target.mem_nhds hz] with y hy
    change F.amb.val (F.amb.val.symm (F.flat.symm y)) = F.flat.symm y
    exact F.amb.val.right_inv (F.flat_source_subset (F.flat.map_target hy))
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
  exact (DFunLike.congr_fun hcomp u).symm

def familyNormalPhysicalValue :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      (familyNativePhysicalModel p i a v U hsm L).Fiber (finv F z) →ₗ[ℂ] L.Fiber (finv F z).val.2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F z hz
  let tuple := fun j => mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z
    ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis j)
  exact (TensorProduct.lid ℂ (L.Fiber (finv F z).val.2)).toLinearMap.comp (TensorProduct.map
    (actualTupleEvaluation (familyNativeCanonicalFiberEquiv p i a v U hsm (finv F z)) tuple) LinearMap.id)

theorem familyNormalPhysicalValue_tmul :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target)
      (α : (familyNativeCanonicalModel p i a v U hsm).Fiber (finv F z)) (l : L.Fiber (finv F z).val.2),
      familyNormalPhysicalValue p i a v U hsm L F z hz (α ⊗ₜ[ℂ] l) =
        familyNativeCanonicalFiberEquiv p i a v U hsm (finv F z) α
          (fun j => mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z
            ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis j)) • l := by
  intros
  rfl

theorem familyNormalPhysicalValue_eq_det :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target)
      (s : (familyNativePhysicalModel p i a v U hsm L).Fiber (finv F z)),
      familyNormalPhysicalValue p i a v U hsm L F z hz s =
        (fderiv ℂ F.flat.symm z).det •
          familyPhysicalCoordinateEquiv p i a v U hsm L F.amb (finv F z) (finv_mem F hz).1 s := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F z hz s
  let q := finv F z
  let A := nativeOriginalChartTangentEquiv F.amb q (finv_mem F hz).1
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let D := (fderiv ℂ F.flat.symm z).toLinearMap
  have htuple : (fun j => A.symm (D (b j))) =
      fun j => mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z (b j) := by
    funext j
    apply A.injective
    rw [A.apply_symm_apply]
    exact (familyFlatInverse_chart_derivative p i a v U hsm F z hz (b j)).symm
  have hmaps : familyNormalPhysicalValue p i a v U hsm L F z hz =
      (fderiv ℂ F.flat.symm z).det •
        (familyPhysicalCoordinateEquiv p i a v U hsm L F.amb q (finv_mem F hz).1).toLinearMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro l
    change familyNormalPhysicalValue p i a v U hsm L F z hz (α ⊗ₜ[ℂ] l) =
      (fderiv ℂ F.flat.symm z).det •
        familyPhysicalCoordinateEquiv p i a v U hsm L F.amb q (finv_mem F hz).1 (α ⊗ₜ[ℂ] l)
    rw [familyNormalPhysicalValue_tmul, familyPhysicalCoordinateEquiv_tmul]
    change familyNativeCanonicalFiberEquiv p i a v U hsm q α
      (fun j => mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z (b j)) • l =
      (fderiv ℂ F.flat.symm z).det •
        (familyCanonicalCoordinateValue p i a v U hsm F.amb q (finv_mem F hz).1 α • l)
    let beta := (AlternatingMap.domLCongr ℂ ℂ (Fin (d + 1)) ℂ A)
      (familyNativeCanonicalFiberEquiv p i a v U hsm q α)
    have h := congrArg (fun (t : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) => t (D ∘ b))
      (beta.eq_smul_basis_det b)
    change familyNativeCanonicalFiberEquiv p i a v U hsm q α
      (fun j => A.symm (D (b j))) = beta b * b.det (D ∘ b) at h
    rw [htuple, Module.Basis.det_comp, Module.Basis.det_self, mul_one] at h
    rw [h, smul_smul, mul_comm]
    rfl
  exact LinearMap.congr_fun hmaps s

theorem familyNormalPhysicalDensity_eq_value :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (w : familyIncidence p i a v U → ℝ≥0∞) (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target),
      familyNormalPhysicalDensity p i a v U hsm L F S w z =
        ENNReal.ofReal (‖familyNormalPhysicalValue p i a v U hsm L F z hz (S (finv F z))‖ ^ 2) *
          w (finv F z) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S w z hz
  have hD : DifferentiableAt ℂ F.flat.symm z :=
    F.differentiableOn_flat_symm.differentiableAt (F.flat.open_target.mem_nhds hz)
  have hJ : |(fderiv ℝ F.flat.symm z).det| = ‖(fderiv ℂ F.flat.symm z).det‖ ^ 2 := by
    rw [hD.fderiv_restrictScalars ℝ]
    change |LinearMap.det (((fderiv ℂ F.flat.symm z).toLinearMap).restrictScalars ℝ)| = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  unfold familyNormalPhysicalDensity familyPhysicalCoordinateDensity
  rw [dif_pos (F.flat_source_subset (F.flat.map_target hz)), hJ,
    familyNormalPhysicalValue_eq_det p i a v U hsm L F z hz,
    norm_smul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
  rfl

end SGPT.Trace.BertiniFamilyCanonical
