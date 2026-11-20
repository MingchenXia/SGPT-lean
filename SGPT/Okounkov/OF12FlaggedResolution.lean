import SGPT.Okounkov.OF12NormalProjectiveExistence
import SGPT.Okounkov.OF15ResolvedPresentation
import SGPT.Unibranch.CHPrimeRealization
import SGPT.Unibranch.HironakaG10GenBlowupBridge

set_option autoImplicit false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov.ValCurr
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SmoothCentreModification
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences

noncomputable section

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] {m : ℕ}

local instance resolutionPointTopology (R : Resolution f m) :
    TopologicalSpace (SchemeComplexPoint R.fY) :=
  schemeAnalyticPointTopology R.fY

local instance resolutionPointCharts (R : Resolution f m) :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTNChartedSpace R.fY (m + 1)

local instance resolutionPointManifold (R : Resolution f m) :
    IsComplexManifold (m + 1) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTN_isComplexManifold R.fY (m + 1)

/-- The actual projection of the smooth flagged carrier to the original analytification. -/
def Presentation.flaggedProjection
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) :
    wholeModel (n := m + 1) Q.P.F.carrier ⟶ UnibAn.analytification f :=
  nativeMorphism (n := m + 1) (m := m + 1) Q.P.isBlowupSequence.contMDiff ≫ Q.R.π

/-- The blow-up part of the projection is a finite smooth-centre modification. -/
theorem Presentation.flaggedProjection_tower_isModification
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) :
    IsModification
      (nativeMorphism (n := m + 1) (m := m + 1) Q.P.isBlowupSequence.contMDiff) :=
  HironakaG10GenBlowupBridge.isModification_nativeMorphism Q.P.isBlowupSequence

/-- The flag lies on the source of a proper bimeromorphic resolution of the actual original base. -/
theorem Presentation.flaggedProjection_isResolution
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) : IsResolution Q.flaggedProjection :=
  ⟨isSmooth_wholeModel, CHPrimeRealization.isProperBimeromorphic_comp
    (CHPrimeRealization.isProperBimeromorphic_of_isModification
      Q.flaggedProjection_tower_isModification) Q.R.isProperBimeromorphic⟩

/-- The projection on points is the given tower projection followed by the scheme resolution. -/
theorem Presentation.flaggedProjection_point_eq
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) (w : Q.P.F.carrier) :
    UnibAn.pointMap f (Q.flaggedProjection.hom.left.base ⟨w, mem_univ w⟩) =
      schemeComplexPointMap Q.R.fY f Q.R.ρ Q.R.comp_eq (Q.P.π w) := by
  change UnibAn.pointMap f (Q.R.π.hom.left.base ⟨Q.P.π w, mem_univ (Q.P.π w)⟩) = _
  exact Q.R.point_eq (Q.P.π w)

/-- The corrected valuation on the flagged carrier, read through the same resolution, is
literally the original valuation of the ground function field. -/
theorem Presentation.flaggedProjection_valuation_eq
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) :
    ν = lexMapValuation Q.P.G Q.P.unitriangular
      ((OF2.modificationFlagValuation Q.R.fY Q.P.F Q.P.isModification).comap Q.R.φ.toRingHom) := by
  calc
    ν = (Q.R.transport ν).comap Q.R.φ.toRingHom := (Q.R.transport_comap ν).symm
    _ = (lexMapValuation Q.P.G Q.P.unitriangular
        (OF2.modificationFlagValuation Q.R.fY Q.P.F Q.P.isModification)).comap Q.R.φ.toRingHom :=
      congrArg (fun v => v.comap Q.R.φ.toRingHom) Q.P.presents
    _ = _ := lexMapValuation_comap Q.R.φ.toRingHom Q.P.unitriangular _

/-- The smooth flagged analytic resolution and exact valuation required by the remark
exist for a normal projective base in positive dimension. -/
theorem exists_flaggedResolution_of_normalProjective
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : letI := schemeFunctionFieldAlgebra f
      Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ))
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ Q : Presentation f m ν, IsResolution Q.flaggedProjection ∧
      ν = lexMapValuation Q.P.G Q.P.unitriangular
        ((OF2.modificationFlagValuation Q.R.fY Q.P.F Q.P.isModification).comap Q.R.φ.toRingHom) := by
  obtain ⟨R⟩ := nonempty_resolution_of_normalProjective f E hX m hdim
  obtain ⟨Q⟩ := OF15.nonempty_presentation_of_resolution R ν hν
  exact ⟨Q, Q.flaggedProjection_isResolution, Q.flaggedProjection_valuation_eq⟩

end

end SGPT.Okounkov.OF12
