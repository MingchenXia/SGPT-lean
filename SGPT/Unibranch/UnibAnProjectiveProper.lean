import SGPT.Unibranch.UnibAnMorphismGlobal
import SGPT.Foundations.Schemes.NativeProjectiveFano

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology SGPT.Foundations.Analysis.FirstPass
open SGPT.Unibranch SGPT.Foundations.Schemes

namespace SGPT.Unibranch.UnibAn

/-- An analytic morphism from the analytification of a projective scheme has a proper point map. -/
theorem isProperMap_of_projective_source
    {X Y : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {g : Y ⟶ Spec (.of ℂ)}
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated g] [QuasiCompact g] [LocallyOfFiniteType g]
    (E : ClosedProjectiveEmbedding g) (F : analytification g ⟶ analytification f) :
    IsProperMap F.hom.left.base := by
  let : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
  let : CompactSpace (SchemeComplexPoint g) := E.analyticCompact
  have hC : CompactSpace (analytificationLRS g) := (pointHomeomorph g).symm.compactSpace
  exact @Continuous.isProperMap _ _ _ _ _ hC (analytification_t2Space (f := f))
    F.hom.left.base.hom.continuous


end SGPT.Unibranch.UnibAn
