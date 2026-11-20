import SGPT.Trace.BertiniFamilyNormalOpenCoordinates
import SGPT.Trace.NativeCanonicalPhysicalHodgeIntegral

/-! Actual open-domain derivatives and physical top density without native-atlas claims. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.BertiniFamilyCanonical

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

section Basis
variable [CompactSpace X] (L : HermitianHolomorphicLineBundle n X)

theorem nativeCanonicalPhysicalValue_basis_change (e : ComplexChart n X) (x : X)
    (hx : x ∈ e.val.source) (A : ComplexModel n →ₗ[ℂ] TangentSpace 𝓘(ℂ, ComplexModel n) x)
    (T : (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) :
    nativeCanonicalPhysicalValue L x (fun j => A ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) T =
      LinearMap.det ((nativeOriginalChartTangentEquiv e x hx).toLinearMap.comp A) •
        nativeCanonicalPhysicalChartValue L e x hx T := by
  let C := nativeOriginalChartTangentEquiv e x hx
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let M := C.toLinearMap.comp A
  have hmaps : nativeCanonicalPhysicalValue L x (fun j => A (b j)) =
      (LinearMap.det M) • nativeCanonicalPhysicalChartValue L e x hx := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro l
    change nativeCanonicalFiberEquiv (n := n) x α (fun j => A (b j)) • l =
      LinearMap.det M • (nativeCanonicalFiberEquiv (n := n) x α (fun j => C.symm (b j)) • l)
    let β := nativeCanonicalFiberInChart e x hx α
    have htuple : (fun j => C.symm (M (b j))) = fun j => A (b j) := by
      funext j
      exact C.symm_apply_apply (A (b j))
    have hβ := congrArg (fun (t : (ComplexModel n) [⋀^Fin n]→ₗ[ℂ] ℂ) => t (M ∘ b))
      (β.eq_smul_basis_det b)
    change nativeCanonicalFiberEquiv (n := n) x α (fun j => C.symm (M (b j))) =
      β b * b.det (M ∘ b) at hβ
    rw [htuple, Module.Basis.det_comp, Module.Basis.det_self, mul_one] at hβ
    rw [hβ]
    change (β b * LinearMap.det M) • l = LinearMap.det M • ((β b) • l)
    rw [smul_smul, mul_comm]
  exact LinearMap.congr_fun hmaps T
end Basis

variable (D : TopologicalSpace.Opens (ComplexModel n))
  (g : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) D X ∞)

def nativeOpenCoordinateMap (e : ComplexChart n X) (z : ComplexModel n) : ComplexModel n := by
  classical
  exact if hz : z ∈ D then e.val (g ⟨z,hz⟩) else 0

omit [IsComplexManifold n X] in
theorem nativeOpenCoordinateMap_apply (e : ComplexChart n X) (u : D) :
    nativeOpenCoordinateMap D g e u.val = e.val (g u) := by
  classical
  exact dif_pos u.property

theorem nativeOpenCoordinateMap_contDiffAt (e : ComplexChart n X) (u : D)
    (hu : g u ∈ e.val.source) : ContDiffAt ℂ ∞ (nativeOpenCoordinateMap D g e) u.val := by
  have he : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.val (g u) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hu
  have hcomp : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (e.val ∘ g) u :=
    ContMDiffAt.comp (f := g) (g := e.val) u he g.contMDiff.contMDiffAt
  have heq : (fun z : D => nativeOpenCoordinateMap D g e z.val) = e.val ∘ g := by
    funext z
    exact nativeOpenCoordinateMap_apply D g e z
  have hr : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : D => nativeOpenCoordinateMap D g e z.val) u := by
    rw [heq]
    exact hcomp
  exact (contMDiffAt_subtype_iff.mp hr).contDiffAt

theorem nativeOpenCoordinateMap_fderiv (e : ComplexChart n X) (u : D) (hu : g u ∈ e.val.source) :
    (fderiv ℂ (nativeOpenCoordinateMap D g e) u.val).toLinearMap =
      (nativeOriginalChartTangentEquiv e (g u) hu).toLinearMap.comp
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g u).toLinearMap := by
  have hF := (nativeOpenCoordinateMap_contDiffAt D g e u hu).differentiableAt (by simp)
  have hv : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (Subtype.val : D → ComplexModel n) u :=
    (contMDiff_subtype_val (n := ∞)).contMDiffAt.mdifferentiableAt (by simp)
  have hleft := mfderiv_comp u hF.mdifferentiableAt hv
  have hright := mfderiv_comp u (mdifferentiableAt_atlas e.property hu)
    (g.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have heq : (nativeOpenCoordinateMap D g e ∘ (Subtype.val : D → ComplexModel n)) = e.val ∘ g := by
    funext z
    exact nativeOpenCoordinateMap_apply D g e z
  rw [heq, mfderiv_eq_fderiv, mfderiv_openComplexModel_val] at hleft
  apply LinearMap.ext
  intro v
  have hl := DFunLike.congr_fun hleft v
  have hr := DFunLike.congr_fun hright v
  change mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (e.val ∘ g) u v =
    fderiv ℂ (nativeOpenCoordinateMap D g e) u.val v at hl
  exact hl.symm.trans hr

theorem nativeOpenCoordinateMap_realJacobian (e : ComplexChart n X) (u : D) (hu : g u ∈ e.val.source) :
    |(fderiv ℝ (nativeOpenCoordinateMap D g e) u.val).det| =
      ‖LinearMap.det ((nativeOriginalChartTangentEquiv e (g u) hu).toLinearMap.comp
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g u).toLinearMap)‖ ^ 2 := by
  have hF := (nativeOpenCoordinateMap_contDiffAt D g e u hu).differentiableAt (by simp)
  rw [hF.fderiv_restrictScalars ℝ]
  change |LinearMap.det (((fderiv ℂ (nativeOpenCoordinateMap D g e) u.val).toLinearMap).restrictScalars ℝ)| = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
    nativeOpenCoordinateMap_fderiv D g e u hu]

variable [CompactSpace X] (L : HermitianHolomorphicLineBundle n X)
  (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : X → ℝ≥0∞)

def nativeCanonicalPhysicalOpenDensity (z : ComplexModel n) : ℝ≥0∞ := by
  classical
  exact if hz : z ∈ D then
    ENNReal.ofReal (‖nativeCanonicalPhysicalValue L (g ⟨z,hz⟩)
      (fun j => mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g ⟨z,hz⟩
        ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) (S (g ⟨z,hz⟩))‖ ^ 2) * w (g ⟨z,hz⟩)
    else 0

private theorem actualOpenPhysicalDensity_point_eq (e : ComplexChart n X)
    (a b : X) (ha : a ∈ e.val.source) (hb : b ∈ e.val.source) (hab : a = b) :
    nativeCanonicalPhysicalChartDensity L e a ha (S a) (w a) =
      nativeCanonicalPhysicalChartDensity L e b hb (S b) (w b) := by
  subst b
  rfl

theorem nativeCanonicalPhysicalOpenDensity_change (e : ComplexChart n X) (u : D)
    (hu : g u ∈ e.val.source) :
    nativeCanonicalPhysicalOpenDensity D g L S w u.val =
      ENNReal.ofReal |(fderiv ℝ (nativeOpenCoordinateMap D g e) u.val).det| *
        nativeCanonicalPhysicalCoordinateDensity L S w e (nativeOpenCoordinateMap D g e u.val) := by
  classical
  have ht : e.val (g u) ∈ e.val.target := e.val.map_source hu
  unfold nativeCanonicalPhysicalOpenDensity
  rw [dif_pos u.property, nativeOpenCoordinateMap_apply]
  unfold nativeCanonicalPhysicalCoordinateDensity
  rw [dif_pos ht]
  have hd := actualOpenPhysicalDensity_point_eq L S w e
    (e.val.symm (e.val (g u))) (g u) (e.val.map_target ht) hu (e.val.left_inv hu)
  rw [hd]
  change ENNReal.ofReal (‖nativeCanonicalPhysicalValue L (g u)
    (fun j => (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g u).toLinearMap
      ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) (S (g u))‖ ^ 2) * w (g u) = _
  let A : ComplexModel n →ₗ[ℂ] TangentSpace 𝓘(ℂ, ComplexModel n) (g u) :=
    (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g u).toLinearMap
  let M := (nativeOriginalChartTangentEquiv e (g u) hu).toLinearMap.comp A
  have hval := nativeCanonicalPhysicalValue_basis_change L e (g u) hu A (S (g u))
  have hnorm := congrArg (fun l : L.Fiber (g u) => ENNReal.ofReal (‖l‖ ^ 2) * w (g u)) hval
  apply hnorm.trans
  change ENNReal.ofReal (‖LinearMap.det M • nativeCanonicalPhysicalChartValue L e (g u) hu (S (g u))‖ ^ 2) * w (g u) = _
  unfold nativeCanonicalPhysicalChartDensity
  rw [norm_smul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc,
    nativeOpenCoordinateMap_realJacobian D g e u hu]

end SGPT.Trace.Bertini
