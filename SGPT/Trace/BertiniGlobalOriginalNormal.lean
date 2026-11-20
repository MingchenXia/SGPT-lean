import SGPT.Trace.BertiniOriginalNativeParametrizationPatch

/-! Actual intrinsic original normal-line right inverses at EVERY original
smooth member point, without selecting an auxiliary SliceChart. Choices
are pointwise; global holomorphic adjunction gluing remains downstream. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
private theorem scalarDifferential_preferred {g : X → ℂ} {x : X}
    (hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x) :
    nativeScalarDifferential (n := n) g x =
      fderiv ℂ (g ∘ (complexChartAt (n := n) x).val.symm)
        ((complexChartAt (n := n) x).val x) := by
  unfold nativeScalarDifferential
  simp [mfderiv, hg, writtenInExtChartAt, complexChartAt,
    mfld_simps, fderivWithin_univ, Function.comp_def]

variable
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

/-- Actual original affine defining-section differential, at ANY point
of the literal same original member and in the original physical P line. -/
def nativeBertiniIntrinsicConormal (x : X) (hx : x ∈ member p (affinePoint i ζ)) :
    TangentSpace 𝓘(ℂ, ComplexModel n) x →ₗ[ℂ] (nativeBertiniHyperplaneBundle p).Fiber x :=
  nativeSectionDifferentialAtZero (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ)
    x ((nativeBertiniAffineSection_zero_iff p i ζ x).mpr hx)

/-- The actual local scalar coefficient has a produced normalized native
normal at EVERY original smooth member point, without a SliceChart input. -/
theorem exists_nativeBertiniScalarNormal (x : X) (hx : x ∈ member p (affinePoint i ζ))
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    ∃ v : TangentSpace 𝓘(ℂ, ComplexModel n) x,
      nativeScalarDifferential (nativeBertiniLocalEquation p i ζ (chartIndex (p x))) x v = 1 := by
  let j := chartIndex (p x)
  have hj : p x ∈ (affineChart j).source := mem_affineChart_chartIndex (p x)
  let g := nativeBertiniLocalEquation p i ζ j
  have hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x :=
    nativeBertiniLocalEquation_mdifferentiableAt p i ζ j x hj
  have hnonzero : ∃ v : TangentSpace 𝓘(ℂ, ComplexModel n) x, nativeScalarDifferential g x v ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨a, ha, hrep⟩ := rep_smul (affinePoint i ζ) (affineLift_ne_zero i ζ) rfl
    let e := complexChartAt (n := n) x
    have hex : x ∈ e.val.source := mem_complexChartAt_source x
    have hrel : memberEquation p (affinePoint i ζ) j ∘ e.val.symm =
        fun z => a * (g ∘ e.val.symm) z := by
      funext z
      change pairing (affinePoint i ζ).rep (affineLift j (affineChart j (p (e.val.symm z)))) = _
      rw [hrep, pairing_smul_left]
      rfl
    have hcoord : DifferentiableAt ℂ (g ∘ e.val.symm) (e.val x) :=
      (hasFDerivAt_pairing_chartLift p p.contMDiff ((mem_chartLiftDomain_iff p hex).mpr hj)
        (affineLift i ζ)).differentiableAt
    have hD := (hcoord.hasFDerivAt.const_mul a).fderiv
    have hsing : ∀ v, chartDeriv e v (memberEquation p (affinePoint i ζ) j) x = 0 := by
      intro v
      unfold chartDeriv
      rw [hrel, hD]
      change a * fderiv ℂ (g ∘ e.val.symm) (e.val x) v = 0
      have hv := hn v
      rw [scalarDifferential_preferred hg] at hv
      change fderiv ℂ (g ∘ e.val.symm) (e.val x) v = 0 at hv
      rw [hv, mul_zero]
    exact ((isSmoothHypersurfaceMember_iff p p.contMDiff (affinePoint i ζ)).mp hsm x) ⟨hx, hsing⟩
  obtain ⟨v, hv⟩ := hnonzero
  refine ⟨(nativeScalarDifferential g x v)⁻¹ • v, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]

/-- Produced pointwise right inverse on the ACTUAL original physical
normal line, at EVERY actual original smooth hypersurface member point. -/
def nativeBertiniNormalLift (x : X) (hx : x ∈ member p (affinePoint i ζ))
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    (nativeBertiniHyperplaneBundle p).Fiber x →ₗ[ℂ] TangentSpace 𝓘(ℂ, ComplexModel n) x where
  toFun w := nativeBertiniCoordinateFiberEquiv p (chartIndex (p x)) x (mem_affineChart_chartIndex (p x)) w •
    Classical.choose (exists_nativeBertiniScalarNormal p i ζ x hx hsm)
  map_add' u v := by rw [map_add, add_smul]
  map_smul' a v := by
    change nativeBertiniCoordinateFiberEquiv p (chartIndex (p x)) x (mem_affineChart_chartIndex (p x)) (a • v) •
      Classical.choose (exists_nativeBertiniScalarNormal p i ζ x hx hsm) =
      a • (nativeBertiniCoordinateFiberEquiv p (chartIndex (p x)) x (mem_affineChart_chartIndex (p x)) v •
        Classical.choose (exists_nativeBertiniScalarNormal p i ζ x hx hsm))
    rw [map_smul, smul_smul]
    rfl

theorem nativeBertiniNormalLift_spec (x : X) (hx : x ∈ member p (affinePoint i ζ))
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ))
    (w : (nativeBertiniHyperplaneBundle p).Fiber x) :
    nativeBertiniIntrinsicConormal p i ζ x hx (nativeBertiniNormalLift p i ζ x hx hsm w) = w := by
  let j := chartIndex (p x)
  let A := nativeBertiniCoordinateFiberEquiv p j x (mem_affineChart_chartIndex (p x))
  let ν := Classical.choose (exists_nativeBertiniScalarNormal p i ζ x hx hsm)
  have hν := Classical.choose_spec (exists_nativeBertiniScalarNormal p i ζ x hx hsm)
  change nativeBertiniIntrinsicConormal p i ζ x hx (A w • ν) = w
  rw [map_smul]
  unfold nativeBertiniIntrinsicConormal
  rw [nativeBertiniSectionDifferentialAtZero p i ζ j x (mem_affineChart_chartIndex (p x)) hx ν,
    hν, one_smul]
  apply A.injective
  rw [map_smul]
  have hA : A (nativeBertiniCoordinateSection p j x) = 1 :=
    nativeBertiniCoordinateFiberEquiv_coordinate p j x _
  rw [hA, smul_eq_mul, mul_one]

theorem nativeBertiniIntrinsicConormal_surjective (x : X) (hx : x ∈ member p (affinePoint i ζ))
    (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ)) :
    Function.Surjective (nativeBertiniIntrinsicConormal p i ζ x hx) := by
  intro w
  exact ⟨nativeBertiniNormalLift p i ζ x hx hsm w, nativeBertiniNormalLift_spec p i ζ x hx hsm w⟩

end SGPT.Trace.Bertini
