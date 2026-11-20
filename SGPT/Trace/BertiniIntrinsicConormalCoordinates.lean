import SGPT.Trace.BertiniIntrinsicNormalConormal
import SGPT.Trace.BertiniNativeCanonicalFiberResidue
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! The ORIGINAL intrinsic normal conormal in ORIGINAL native tangent coordinates.

The actual native manifold chain rule relates it to the original inverse
flattening derivative; an original native normal and true surjectivity are
produced, without normal/nonvanishing/surjectivity certificates.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- Actual native scalar conormal readback through the ACTUAL original
ambient chart derivative, from the native chain rule and original equation. -/
theorem originalNativeScalarConormal_coordinates
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (v : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q)) :
    nativeScalarDifferential (nativeBertiniLocalEquation ⟨p, hp⟩ c.i q.1.val c.j) (c.tangentPoint q) v =
      c.originalMemberConormal q
        (nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 v) := by
  have hpoint := c.tangentPoint_chart_coordinates q
  have heq : nativeBertiniLocalEquation ⟨p, hp⟩ c.i q.1.val c.j =ᶠ[𝓝 (c.tangentPoint q)]
      (c.originalFixedMemberEquation q ∘ c.e.val) := by
    filter_upwards [c.e.val.open_source.mem_nhds hpoint.1] with y hy
    change pairing (affineLift c.i q.1.val) (affineLift c.j (affineChart c.j (p y))) =
      pairing (affineLift c.i q.1.val) (chartLift p c.e c.j (c.e.val y))
    rw [chartLift_chart p hy]
  have hg : MDifferentiableAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ)
      (c.originalFixedMemberEquation q) (c.e.val (c.tangentPoint q)) :=
    (hasFDerivAt_pairing_chartLift p hp hpoint.2.2 (affineLift c.i q.1.val)).differentiableAt.mdifferentiableAt
  have hchart := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (d + 1))) c.e.property hpoint.1
  have hcomp := mfderiv_comp (c.tangentPoint q) hg hchart
  rw [mfderiv_eq_fderiv, c.originalFixedMemberEquation_fderiv hp q] at hcomp
  rw [nativeOriginalChartTangentEquiv_apply]
  unfold nativeScalarDifferential
  rw [heq.mfderiv_eq, hcomp]
  rfl

/-- The actual intrinsic original P-valued section differential, retaining
the original normal bundle and ORIGINAL native tangent/fibre objects. -/
def originalIntrinsicConormal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q) →ₗ[ℂ]
      (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q) :=
  nativeSectionDifferentialAtZero (nativeBertiniHyperplaneBundle ⟨p, hp⟩)
    (nativeBertiniAffineSection ⟨p, hp⟩ c.i q.1.val) (c.tangentPoint q)
    ((nativeBertiniAffineSection_zero_iff ⟨p, hp⟩ c.i q.1.val (c.tangentPoint q)).mpr
      (c.tangentPoint_mem_member q))

theorem originalIntrinsicConormal_coordinates
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (v : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q)) :
    c.originalIntrinsicConormal hp q v =
      c.originalMemberConormal q
        (nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 v) •
      nativeBertiniCoordinateSection ⟨p, hp⟩ c.j (c.tangentPoint q) := by
  have hpoint := c.tangentPoint_chart_coordinates q
  have hpx := (mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2
  unfold originalIntrinsicConormal
  rw [nativeBertiniSectionDifferentialAtZero ⟨p, hp⟩ c.i q.1.val c.j (c.tangentPoint q) hpx
    (c.tangentPoint_mem_member q) v, c.originalNativeScalarConormal_coordinates hp q v]

/-- The original coordinate normal is transported back by the ACTUAL
original chart tangent isomorphism, producing an actual native normal. -/
def originalIntrinsicNormal (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q) :=
  (nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1).symm
    (c.originalNormalizedNormal q)

theorem originalIntrinsicNormal_spec
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    c.originalIntrinsicConormal hp q (c.originalIntrinsicNormal q) =
      nativeBertiniCoordinateSection ⟨p, hp⟩ c.j (c.tangentPoint q) := by
  rw [c.originalIntrinsicConormal_coordinates hp q, originalIntrinsicNormal,
    LinearEquiv.apply_symm_apply, c.originalNormalizedNormal_spec hp q, one_smul]

/-- True surjectivity of the ORIGINAL intrinsic conormal onto the ORIGINAL
physical normal line, with normal and nonzero frame both produced internally. -/
theorem originalIntrinsicConormal_surjective
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) : Function.Surjective (c.originalIntrinsicConormal hp q) := by
  intro w
  have hpoint := c.tangentPoint_chart_coordinates q
  have hpx := (mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2
  let A := nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q) hpx
  refine ⟨A w • c.originalIntrinsicNormal q, ?_⟩
  rw [map_smul, c.originalIntrinsicNormal_spec hp q]
  apply A.injective
  rw [map_smul]
  have hA : A (nativeBertiniCoordinateSection ⟨p, hp⟩ c.j (c.tangentPoint q)) = 1 :=
    nativeBertiniCoordinateFiberEquiv_coordinate _ _ _ _
  rw [hA, smul_eq_mul, mul_one]

end SGPT.Trace.Bertini.SliceChart
