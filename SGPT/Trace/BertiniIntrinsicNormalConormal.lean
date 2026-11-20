import SGPT.Trace.BertiniNativeZeroSectionDifferential

/-! Actual intrinsic P-valued conormal from the ORIGINAL native defining section.

Actual incidence coefficient, holomorphy, vanishing and physical product
identity are produced from the original map and member. Projective frame
independence follows from the actual intrinsic original section differential.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.LineBundle.TMetric SGPT.PSH.GlobalL2
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original native scalar derivative, with its actual scalar target
read explicitly as the original scalar model rather than its tangent synonym. -/
def nativeScalarDifferential (g : X → ℂ) (x : X) :
    TangentSpace 𝓘(ℂ, ComplexModel n) x →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x

theorem nativeSectionDifferentialAtZero_eq_scalarProduct
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (T S : HolomorphicSections (n := n) E.Fiber) (g : X → ℂ) (x : X)
    (hT : T x = 0) (hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x)
    (hg0 : g x = 0) (hrel : ∀ᶠ y in 𝓝 x, T y = g y • S y)
    (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    nativeSectionDifferentialAtZero E T x hT v = nativeScalarDifferential g x v • S x := by
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let := e.property
  have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  have hS : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (sectionCoefficient E.Fiber e.val S) x :=
    ((e.val.contMDiffAt_section_iff hx).mp (S.contMDiff x)).mdifferentiableAt (by simp)
  have heq : sectionCoefficient E.Fiber e.val T =ᶠ[𝓝 x]
      (fun y => g y * sectionCoefficient E.Fiber e.val S y) := by
    filter_upwards [hrel, e.val.open_baseSet.mem_nhds hx] with y hy hey
    change e.val.linearEquivAt ℂ y hey (T y) = g y * e.val.linearEquivAt ℂ y hey (S y)
    rw [hy, map_smul, smul_eq_mul]
  have hprod := (hg.hasMFDerivAt.mul hS.hasMFDerivAt).congr_of_eventuallyEq heq
  let DS : TangentSpace 𝓘(ℂ, ComplexModel n) x →L[ℂ] ℂ :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (sectionCoefficient E.Fiber e.val S) x
  let DT : TangentSpace 𝓘(ℂ, ComplexModel n) x →L[ℂ] ℂ :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (sectionCoefficient E.Fiber e.val T) x
  have hd : DT v = sectionCoefficient E.Fiber e.val S x * nativeScalarDifferential g x v := by
    have h := DFunLike.congr_fun hprod.mfderiv v
    change DT v = g x * DS v + sectionCoefficient E.Fiber e.val S x * nativeScalarDifferential g x v at h
    simpa only [hg0, zero_mul, zero_add] using h
  rw [nativeSectionDifferentialAtZero_in_frame E T x hT e hx]
  change DT v • e.val.symm x 1 = _
  rw [hd]
  have hs := trivialization_eq_coef_smul_frame e.val hx (S x)
  have hs' : S x = sectionCoefficient E.Fiber e.val S x • e.val.symm x 1 := by
    change S x = (e.val ⟨x, S x⟩).2 • e.val.symm x 1
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hx] at hs
    exact hs
  rw [hs', smul_smul, mul_comm]

/-- Literal original incidence coefficient in the original target affine chart. -/
def nativeBertiniLocalEquation
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j : Fin (N + 1)) : X → ℂ :=
  fun x => pairing (affineLift i ζ) (affineLift j (affineChart j (p x)))

omit [IsComplexManifold n X] in
theorem nativeBertiniLocalEquation_mdifferentiableAt
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j : Fin (N + 1)) (x : X) (hx : p x ∈ (affineChart j).source) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (nativeBertiniLocalEquation p i ζ j) x := by
  have hpair : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ℂ) ∞
      (fun z => pairing (affineLift i ζ) (affineLift j z)) (affineChart j (p x)) :=
    (contDiff_pairing_affineLift (affineLift i ζ) j).contMDiff.contMDiffAt
  exact (hpair.comp x ((contMDiffAt_affineChart j hx).comp x (p.contMDiff x))).mdifferentiableAt (by simp)

theorem nativeBertiniLocalEquation_zero
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j : Fin (N + 1)) (x : X) (hx : p x ∈ (affineChart j).source)
    (hmem : x ∈ member p (affinePoint i ζ)) : nativeBertiniLocalEquation p i ζ j x = 0 := by
  have hz := (nativeBertiniAffineSection_zero_iff p i ζ x).mpr hmem
  rw [nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j x hx] at hz
  exact (smul_eq_zero.mp hz).resolve_right (nativeBertiniCoordinateSection_ne_zero p j x hx)

/-- The intrinsic differential of the ACTUAL original defining section is
the ACTUAL original incidence coefficient derivative times its SAME physical
coordinate-section frame. All product/zero/holomorphy inputs are produced. -/
theorem nativeBertiniSectionDifferentialAtZero
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j : Fin (N + 1)) (x : X) (hx : p x ∈ (affineChart j).source)
    (hmem : x ∈ member p (affinePoint i ζ))
    (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    nativeSectionDifferentialAtZero (nativeBertiniHyperplaneBundle p) (nativeBertiniAffineSection p i ζ)
      x ((nativeBertiniAffineSection_zero_iff p i ζ x).mpr hmem) v =
      nativeScalarDifferential (nativeBertiniLocalEquation p i ζ j) x v • nativeBertiniCoordinateSection p j x := by
  apply nativeSectionDifferentialAtZero_eq_scalarProduct
  · exact nativeBertiniLocalEquation_mdifferentiableAt p i ζ j x hx
  · exact nativeBertiniLocalEquation_zero p i ζ j x hx hmem
  · filter_upwards [p.contMDiff.continuous.continuousAt.eventually ((affineChart j).open_source.mem_nhds hx)] with y hy
    exact nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j y hy

/-- Different ORIGINAL target projective frames give the SAME actual
intrinsic original P-valued conormal at every original member point. -/
theorem nativeBertiniConormal_frame_independent
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j k : Fin (N + 1)) (x : X) (hj : p x ∈ (affineChart j).source)
    (hk : p x ∈ (affineChart k).source) (hmem : x ∈ member p (affinePoint i ζ))
    (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    nativeScalarDifferential (nativeBertiniLocalEquation p i ζ j) x v • nativeBertiniCoordinateSection p j x =
      nativeScalarDifferential (nativeBertiniLocalEquation p i ζ k) x v • nativeBertiniCoordinateSection p k x :=
  (nativeBertiniSectionDifferentialAtZero p i ζ j x hj hmem v).symm.trans
    (nativeBertiniSectionDifferentialAtZero p i ζ k x hk hmem v)

end SGPT.Trace.Bertini
