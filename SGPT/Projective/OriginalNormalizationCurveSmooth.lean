import SGPT.Projective.OriginalNormalizationCurveDVR
import SGPT.NAPotential.RegularPrimeSmooth
import SGPT.GAGA.H0LRegular
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! The ACTUAL normalization of an arbitrary integral ORIGINAL projective
curve is genuinely smooth over the SAME complex base, including all branches.
Blueprint: original-normalization-curve-smooth.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Algebra

/-- Every genuine original complex-valued point is a true closed ORIGINAL
scheme point, using its actual section over the one-point complex spectrum. -/
theorem originalComplexPointImage_isClosed {Y : Scheme.{0}}
    (g : Y ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint g) :
    IsClosed ({schemeComplexPointImage g p} : Set Y) := by
  let : IsClosedImmersion p.val := isClosedImmersion_of_comp_eq_id g p.val p.property
  rw [← schemeComplexPoint_range g p]
  exact p.val.isClosedEmbedding.isClosed_range

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include E hcurve in
/-- At EVERY actual closed normalized branch the actual structural stalk
map is formally smooth. Its true DVR, essentially-finite-type algebra and
perfect actual base stalk are manufactured from the original curve. -/
theorem originalNormalizationCurve_closedPoint_stalkMap_formallySmooth
    (z : originalNormalizationScheme X)
    (hz : IsClosed ({z} : Set (originalNormalizationScheme X))) :
    ((originalNormalizationMap X ≫ f).stalkMap z).hom.FormallySmooth := by
  let := originalNormalizationMap_finite X f E
  let := E.locallyOfFiniteType
  let g := originalNormalizationMap X ≫ f
  let : LocallyOfFiniteType g := inferInstance
  have := LocallyOfFiniteType.stalkMap g z
  algebraize [(g.stalkMap z).hom]
  let K' := (Spec.structureSheaf ℂ).presheaf.stalk (g z)
  let e : ℂ ≃ₐ[ℂ] K' := IsLocalization.atUnits _ (g z).asIdeal.primeCompl
    (fun x hx => by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic ℂ K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField ℂ)).toField
  let : Field ((Spec (.of ℂ)).presheaf.stalk (g z)) := this
  have : PerfectField ((Spec (.of ℂ)).presheaf.stalk (g z)) :=
    Algebra.IsAlgebraic.perfectField (K := ℂ) (L := K')
  let : IsDiscreteValuationRing ((originalNormalizationScheme X).presheaf.stalk z) :=
    originalNormalizationCurve_closedPoint_isDiscreteValuationRing f E hcurve z hz
  exact SGPT.NAPotential.RegularPrimeSmooth.formallySmooth_of_dvr _ _

include E hcurve in
/-- The SAME actual normalized original curve is smooth over the SAME
complex base. True smooth-locus openness and genuine complex-point
detection include EVERY branch and EVERY original normalized point. -/
theorem originalNormalizationCurve_smooth : Smooth (originalNormalizationMap X ≫ f) := by
  let := originalNormalizationMap_finite X f E
  let := E.locallyOfFiniteType
  let g := originalNormalizationMap X ≫ f
  let : LocallyOfFiniteType g := inferInstance
  let : LocallyOfFinitePresentation g := inferInstance
  apply g.smoothLocus_eq_top_iff.mp
  apply le_antisymm le_top
  apply SGPT.GAGA.H0L.le_of_forall_schemeComplexPoint g
  intro p _
  rw [Scheme.Hom.mem_smoothLocus]
  exact originalNormalizationCurve_closedPoint_stalkMap_formallySmooth f E hcurve
    (schemeComplexPointImage g p) (originalComplexPointImage_isClosed g p)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
