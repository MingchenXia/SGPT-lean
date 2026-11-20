import SGPT.Trace.BertiniPencilFamily

/-!
# The literal holomorphic normal parameter on native pencil incidence

Native differential surjectivity and actual central-fibre regularity are
produced from original pencil geometry. No normal-function or regular-divisor
certificate is an input.
Blueprint: work/sgpt-resume-20261114/bert-e2-normal/blueprint/bert-e2-normal.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniPencilNormal
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Trace.BertiniPencilFamily

/-- Actual scalar manifold differentials are the literal derivative in the
original preferred source chart and the standard scalar target chart. -/
theorem mfderiv_scalar_eq_chart {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] {f : Y → ℂ} {y : Y}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f y) :
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f y =
      fderiv ℂ (f ∘ (complexChartAt (n := n) y).val.symm)
        ((complexChartAt (n := n) y).val y) := by
  simp [mfderiv, hf, writtenInExtChartAt, complexChartAt,
    mfld_simps, fderivWithin_univ, Function.comp_def, chartAt_self_eq]
  rfl

/-- The literal complex coordinate on the original open parameter domain. -/
def parameterCoordinate (U : TopologicalSpace.Opens (ComplexModel 1)) (t : U) : ℂ := t.val 0

theorem contMDiff_parameterCoordinate (U : TopologicalSpace.Opens (ComplexModel 1)) :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞ (parameterCoordinate U) :=
  (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.contMDiff.comp
    contMDiff_subtype_val

/-- The derivative of the original open-domain coordinate is exactly the
canonical coordinate projection, proved by the native chart inverse germ. -/
theorem mfderiv_parameterCoordinate (U : TopologicalSpace.Opens (ComplexModel 1)) (t : U) :
    mfderiv 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) (parameterCoordinate U) t =
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ) := by
  let e := complexChartAt (n := 1) t
  have ht : t ∈ e.val.source := mem_complexChartAt_source t
  have heq : (parameterCoordinate U ∘ e.val.symm) =ᶠ[𝓝 (e.val t)]
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ) := by
    filter_upwards [e.val.open_target.mem_nhds (e.val.map_source ht)] with z hz
    exact congrArg (fun y : ComplexModel 1 => y 0) (e.val.right_inv hz)
  rw [mfderiv_scalar_eq_chart
    ((contMDiff_parameterCoordinate U).contMDiffAt.mdifferentiableAt (by simp))]
  change fderiv ℂ (parameterCoordinate U ∘ e.val.symm) (e.val t) = _
  rw [heq.fderiv_eq]
  exact (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).hasFDerivAt.fderiv

variable {n N : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)
  (U : TopologicalSpace.Opens (ComplexModel 1))

/-- The literal scalar normal parameter on the original full incidence. -/
def scalarParameter (q : familyIncidence p i a v U) : ℂ := q.val.1.val 0

theorem contMDiff_scalarParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U hp hsm
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (scalarParameter p i a v U) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  exact (contMDiff_parameterCoordinate U).comp (contMDiff_familyProjection p i a v U hp hsm)

theorem holomorphicAt_scalarParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    HolomorphicAt n (scalarParameter p i a v U) q := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  exact Eventually.of_forall fun _ =>
    (contMDiff_scalarParameter p i a v U hp hsm).contMDiffAt.mdifferentiableAt (by simp)

/-- The original scalar normal parameter has surjective native differential;
this is produced from the actual projection submersion. -/
theorem surjective_mfderiv_scalarParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U hp hsm
    Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (scalarParameter p i a v U) q) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  have hd : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q =
      (mfderiv 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) (parameterCoordinate U) q.val.1).comp
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) (familyProjection p i a v U) q) :=
    mfderiv_comp q ((contMDiff_parameterCoordinate U).contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_familyProjection p i a v U hp hsm).contMDiffAt.mdifferentiableAt (by simp))
  rw [hd, mfderiv_parameterCoordinate]
  intro c
  change ℂ at c
  obtain ⟨w, hw⟩ := surjective_mfderiv_familyProjection p i a v U hp hsm q
    (EuclideanSpace.single (0 : Fin 1) c)
  refine ⟨w, ?_⟩
  change (EuclideanSpace.proj (0 : Fin 1))
    (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) (familyProjection p i a v U) q w) = c
  rw [hw]
  simp

theorem exists_chartDeriv_scalarParameter_eq_one
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∃ w : ComplexModel n,
      chartDeriv (complexChartAt (n := n) q) w (scalarParameter p i a v U) q = 1 := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  obtain ⟨w, hw⟩ := surjective_mfderiv_scalarParameter p i a v U hp hsm q (1 : ℂ)
  rw [mfderiv_scalar_eq_chart
    ((contMDiff_scalarParameter p i a v U hp hsm).contMDiffAt.mdifferentiableAt (by simp))] at hw
  exact ⟨w, hw⟩

/-- The original central zero fibre is a genuine regular divisor in the
actual native incidence manifold, retaining every common base-locus point. -/
theorem regularAtDim_zero_scalarParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    {q : familyIncidence p i a v U} (hq : scalarParameter p i a v U q = 0) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    RegularAtDim (n := n) {y | scalarParameter p i a v U y = 0} q (n - 1) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  have hr := LocalGiraudTransform.regularAtDim_zeroSet isOpen_univ
    (fun y _ => holomorphicAt_scalarParameter p i a v U hp hsm y)
    (fun y _ _ => by
      obtain ⟨w, hw⟩ := exists_chartDeriv_scalarParameter_eq_one p i a v U hp hsm y
      exact ⟨complexChartAt (n := n) y, w, mem_complexChartAt_source y, by rw [hw]; exact one_ne_zero⟩)
    (mem_univ q) hq
  simpa only [inter_univ] using hr

omit [TopologicalSpace X] in
/-- Scalar zero is exactly the original projection fibre at the zero
parameter, not a replacement of that fibre. -/
theorem scalarParameter_zero_iff_projection (h₀ : (0 : ComplexModel 1) ∈ U)
    (q : familyIncidence p i a v U) :
    scalarParameter p i a v U q = 0 ↔ familyProjection p i a v U q = ⟨0, h₀⟩ := by
  constructor
  · intro hq
    apply Subtype.ext
    ext k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    simpa only [scalarParameter, familyProjection, PiLp.zero_apply] using hq
  · intro hq
    have h := congrArg (fun t : U => t.val 0) hq
    simpa only [familyProjection, scalarParameter, PiLp.zero_apply] using h

/-- The actual scalar zero fibre is canonically homeomorphic to the same
original central hyperplane member, with its original subspace topology. -/
def centralFibreHomeomorph (h₀ : (0 : ComplexModel 1) ∈ U) :
    {q : familyIncidence p i a v U | scalarParameter p i a v U q = 0} ≃ₜ
      member p (affinePoint i a) :=
  let t₀ : U := ⟨0, h₀⟩
  let hf : {q : familyIncidence p i a v U | scalarParameter p i a v U q = 0} =
      {q : familyIncidence p i a v U | familyProjection p i a v U q = t₀} :=
    Set.ext fun q => scalarParameter_zero_iff_projection p i a v U h₀ q
  let hm : member p (pencilParameter i a v t₀.val) = member p (affinePoint i a) := by
    simp only [t₀, pencilParameter, PiLp.zero_apply, zero_smul, sub_zero]
  (Homeomorph.setCongr hf).trans
    ((familyFibreHomeomorphMember p i a v U t₀).trans (Homeomorph.setCongr hm))

/-- The fibre identification sends an incident point to its exact original
X point; it introduces neither a chosen member nor a new parametrization. -/
theorem centralFibreHomeomorph_apply (h₀ : (0 : ComplexModel 1) ∈ U)
    (q : {q : familyIncidence p i a v U | scalarParameter p i a v U q = 0}) :
    ((centralFibreHomeomorph p i a v U h₀ q : member p (affinePoint i a)) : X) = q.val.val.2 := rfl


end SGPT.Trace.BertiniPencilNormal
