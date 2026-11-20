import SGPT.Trace.BertiniFamilyNormalIntegral

/-! Produced actual full normal tangent equivalence and exact dTau projection. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyNormalChartTangentEquiv :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      ComplexModel (d + 1) ≃ₗ[ℂ] TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (finv F z) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F z hz
  let q := finv F z
  let D := mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z
  let E := mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (fcoord F) q
  have hfc := mdifferentiableAt_fcoord F (finv_mem F hz)
  have hfi := mdifferentiableAt_finv F hz
  have hcod : fcoord F q = z := fcoord_finv F hz
  have heq₁ : (fcoord F ∘ finv F) =ᶠ[𝓝 z] id := by
    filter_upwards [F.flat.open_target.mem_nhds hz] with y hy
    exact fcoord_finv F hy
  have h₁ := mfderiv_comp z hfc hfi
  rw [heq₁.mfderiv_eq, mfderiv_id] at h₁
  have heq₂ : (finv F ∘ fcoord F) =ᶠ[𝓝 q] id := by
    filter_upwards [F.isOpen_ambSource.mem_nhds (finv_mem F hz)] with y hy
    exact finv_fcoord F hy
  have hfiq : MDifferentiableAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) (fcoord F q) := by
    rw [hcod]
    exact hfi
  have h₂ := mfderiv_comp q hfiq hfc
  rw [heq₂.mfderiv_eq, mfderiv_id, hcod] at h₂
  exact {
    toLinearMap := D.toLinearMap
    invFun := E
    left_inv := fun u => (DFunLike.congr_fun h₁ u).symm
    right_inv := fun u => (DFunLike.congr_fun h₂ u).symm }

theorem familyNormalChartTangentEquiv_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target) (u : ComplexModel (d + 1)),
      familyNormalChartTangentEquiv p i a v U hsm F z hz u =
        mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) z u := by
  intros
  rfl

theorem familyParameter_flatInverse_derivative :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target) (u : ComplexModel (d + 1)),
      mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) (finv F z)
        (familyNormalChartTangentEquiv p i a v U hsm F z hz u) = u (Fin.last d) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz u
  have hτ : MDifferentiableAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ)
      (scalarParameter p i a v U) (finv F z) :=
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm).contMDiffAt.mdifferentiableAt (by simp)
  have hfi := mdifferentiableAt_finv F hz
  have heq : (scalarParameter p i a v U ∘ finv F) =ᶠ[𝓝 z]
      (fun y : ComplexModel (d + 1) => y (Fin.last d)) := by
    filter_upwards [F.flat.open_target.mem_nhds hz] with y hy
    exact SGPT.Trace.BertiniExactNormalCoordinates.exact_normal_inverse hF hy
  have h := DFunLike.congr_fun (mfderiv_comp z hτ hfi) u
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at h
  have hproj : fderiv ℂ (fun y : ComplexModel (d + 1) => y (Fin.last d)) z =
      (EuclideanSpace.proj (Fin.last d) : ComplexModel (d + 1) →L[ℂ] ℂ) :=
    (EuclideanSpace.proj (Fin.last d) : ComplexModel (d + 1) →L[ℂ] ℂ).hasFDerivAt.fderiv
  rw [hproj] at h
  exact h.symm

theorem exists_actual_parameter_normal_tangent_coordinates :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (q : familyIncidence p i a v U), scalarParameter p i a v U q = 0 →
      ∃ F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0},
        q ∈ F.ambSource ∧ fcoord F q = 0 ∧
        (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) ∧
        ∀ (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target) (u : ComplexModel (d + 1)),
          mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) (finv F z)
            (familyNormalChartTangentEquiv p i a v U hsm F z hz u) = u (Fin.last d) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro q hq
  obtain ⟨F, hsrc, hzero, hF, _hinv⟩ := exists_actual_parameter_normal_flatData p i a v U hsm q hq
  exact ⟨F, hsrc, hzero, hF, familyParameter_flatInverse_derivative p i a v U hsm F hF⟩

end SGPT.Trace.BertiniFamilyCanonical
