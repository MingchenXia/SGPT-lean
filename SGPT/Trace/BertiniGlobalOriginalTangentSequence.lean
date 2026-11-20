import SGPT.Trace.BertiniGlobalOriginalNormal

/-! Actual all-point original native tangent-normal sequence.
Every geometric input is produced from the original smooth member;
no incoming tangent/kernel/inclusion-rank/conormal-surjectivity certificate. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

theorem nativeBertiniMemberRegularity
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)) :
    ∀ x ∈ member p (affinePoint i ζ), RegularAtDim (n := d + 1) (member p (affinePoint i ζ)) x d := by
  intro x hx
  simpa using regularAtDim_member p p.contMDiff hsm hx

@[instance_reducible] def nativeBertiniMemberChartedSpace
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)) :
    ChartedSpace (ComplexModel d) (member p (affinePoint i ζ)) :=
  SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) (nativeBertiniMemberRegularity p i ζ hsm)

theorem nativeBertiniMemberComplex
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    IsComplexManifold d (member p (affinePoint i ζ)) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) (nativeBertiniMemberRegularity p i ζ hsm)

/-- At EVERY original member point, actual original native tangent equals
the kernel of actual original intrinsic conormal; underlying map is native
mfderiv of the literal original subtype inclusion. -/
def nativeBertiniMemberTangentKernelEquiv
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    TangentSpace 𝓘(ℂ, ComplexModel d) y ≃ₗ[ℂ]
      LinearMap.ker (nativeBertiniIntrinsicConormal p i ζ y.val y.property) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let inc := (Subtype.val : member p (affinePoint i ζ) → X)
  let D : TangentSpace 𝓘(ℂ, ComplexModel d) y →L[ℂ] TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val :=
    mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) inc y
  let δ := nativeBertiniIntrinsicConormal p i ζ y.val y.property
  let j := chartIndex (p y.val)
  have hj : p y.val ∈ (affineChart j).source := mem_affineChart_chartIndex (p y.val)
  let g := nativeBertiniLocalEquation p i ζ j
  have hg := nativeBertiniLocalEquation_mdifferentiableAt p i ζ j y.val hj
  have hinc := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d) (nativeBertiniMemberRegularity p i ζ hsm)
  have hi := hinc.mdifferentiable (by simp) y
  have hzero : (g ∘ inc) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    have hF : ContinuousAt (fun z : member p (affinePoint i ζ) => p z.val) y :=
      p.contMDiff.continuous.continuousAt.comp continuous_subtype_val.continuousAt
    filter_upwards [hF.eventually ((affineChart j).open_source.mem_nhds hj)] with z hz
    exact nativeBertiniLocalEquation_zero p i ζ j z.val hz z.property
  have hcomp := mfderiv_comp y hg hi
  have hδD (v : TangentSpace 𝓘(ℂ, ComplexModel d) y) : δ (D v) = 0 := by
    have hv := DFunLike.congr_fun hcomp v
    rw [hzero.mfderiv_eq, mfderiv_const] at hv
    change (0 : ℂ) = nativeScalarDifferential g y.val (D v) at hv
    change nativeBertiniIntrinsicConormal p i ζ y.val y.property (D v) = 0
    unfold nativeBertiniIntrinsicConormal
    rw [nativeBertiniSectionDifferentialAtZero p i ζ j y.val hj y.property (D v), ← hv, zero_smul]
  let e := complexChartAt (n := d) y
  let a := complexChartAt (n := d + 1) y.val
  have hey : y ∈ e.val.source := mem_complexChartAt_source y
  have hay : y.val ∈ a.val.source := mem_complexChartAt_source y.val
  have hz : e.val y ∈ coordinateDomain inc e a := mem_coordinateDomain hey hay
  have hcoord := injective_nativeSubmanifoldCoordinateDerivative (Nat.le_succ d)
    (nativeBertiniMemberRegularity p i ζ hsm) e a (e.val y) hz
  have hD : Function.Injective D := by
    intro u v huv
    apply hcoord
    have hu := coordinateMap_fderiv_preferred_source_apply ⟨inc, hinc⟩ y a hay u
    have hv := coordinateMap_fderiv_preferred_source_apply ⟨inc, hinc⟩ y a hay v
    change fderiv ℂ (coordinateMap inc e a) (e.val y) u = _ at hu
    change fderiv ℂ (coordinateMap inc e a) (e.val y) v = _ at hv
    rw [hu, hv]
    exact congrArg (nativeOriginalChartTangentEquiv a y.val hay) huv
  let R : TangentSpace 𝓘(ℂ, ComplexModel d) y →ₗ[ℂ] LinearMap.ker δ :=
    D.toLinearMap.codRestrict (LinearMap.ker δ) hδD
  have hR : Function.Injective R := by
    intro u v huv
    exact hD (congrArg Subtype.val huv)
  let A := nativeOriginalChartTangentEquiv a y.val hay
  let B := nativeOriginalChartTangentEquiv e y hey
  let C := nativeBertiniCoordinateFiberEquiv p j y.val hj
  let : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) := A.symm.finiteDimensional
  let : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ, ComplexModel d) y) := B.symm.finiteDimensional
  let : FiniteDimensional ℂ ((nativeBertiniHyperplaneBundle p).Fiber y.val) := C.symm.finiteDimensional
  have hX : Module.finrank ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) = d + 1 := by
    simpa using A.finrank_eq
  have hH : Module.finrank ℂ (TangentSpace 𝓘(ℂ, ComplexModel d) y) = d := by
    simpa using B.finrank_eq
  have hP : Module.finrank ℂ ((nativeBertiniHyperplaneBundle p).Fiber y.val) = 1 := by
    simpa using C.finrank_eq
  have hs : Function.Surjective δ := nativeBertiniIntrinsicConormal_surjective p i ζ y.val y.property hsm
  have hdim := δ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at hdim
  have hdim1 : Module.finrank ℂ ((nativeBertiniHyperplaneBundle p).Fiber y.val) +
      Module.finrank ℂ (LinearMap.ker δ) =
      Module.finrank ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) := by simpa using hdim
  rw [hP, hX] at hdim1
  have hdim' : Module.finrank ℂ (TangentSpace 𝓘(ℂ, ComplexModel d) y) = Module.finrank ℂ (LinearMap.ker δ) := by
    rw [hH]
    omega
  exact LinearEquiv.ofBijective R
    ⟨hR, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hR⟩

theorem nativeBertiniMemberTangentKernelEquiv_apply
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    ∀ v : TangentSpace 𝓘(ℂ, ComplexModel d) y,
      (nativeBertiniMemberTangentKernelEquiv p i ζ hsm y v).val =
        mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
          (Subtype.val : member p (affinePoint i ζ) → X) y v := by
  intros
  rfl

theorem nativeBertiniMemberInclusion_injective
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
      (Subtype.val : member p (affinePoint i ζ) → X) y) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  intro u v huv
  apply (nativeBertiniMemberTangentKernelEquiv p i ζ hsm y).injective
  apply Subtype.ext
  simpa only [nativeBertiniMemberTangentKernelEquiv_apply] using huv

theorem nativeBertiniMemberInclusion_range
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    LinearMap.range (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
      (Subtype.val : member p (affinePoint i ζ) → X) y).toLinearMap =
      LinearMap.ker (nativeBertiniIntrinsicConormal p i ζ y.val y.property) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let E := nativeBertiniMemberTangentKernelEquiv p i ζ hsm y
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    have h : (nativeBertiniMemberTangentKernelEquiv p i ζ hsm y u).val ∈
        LinearMap.ker (nativeBertiniIntrinsicConormal p i ζ y.val y.property) := (E u).property
    rw [nativeBertiniMemberTangentKernelEquiv_apply] at h
    exact h
  · intro hw
    refine ⟨E.symm ⟨w, hw⟩, ?_⟩
    have h := congrArg Subtype.val (E.apply_symm_apply ⟨w, hw⟩)
    change (nativeBertiniMemberTangentKernelEquiv p i ζ hsm y (E.symm ⟨w, hw⟩)).val = w at h
    rw [nativeBertiniMemberTangentKernelEquiv_apply] at h
    exact h

end SGPT.Trace.Bertini
