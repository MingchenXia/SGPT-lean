import SGPT.Projective.AlgebraicCurveChernDegree
import SGPT.Projective.OriginalSectionUnit
import SGPT.Projective.ArtinianSchemeIsoLength

/-! Actual ordinary original Γ(L), independent original zero-cycle degree,
and SAME original physical Chern period. Blueprint: ordinary-curve-chern-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Okounkov SGPT.NAPotential.GAGAMult
open scoped BigOperators
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L)

omit [IsSeparated f] [QuasiCompact f] in
/-- SAME independently defined original structural cycle degree under actual tensor-left-unit. -/
theorem sectionZeroCycleDegree_originalSectionUnit (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (b : Spec (.of ℂ)) :
    sectionZeroCycleDegree f E (a.tensorPower 1) (originalSectionUnit s)
      ((originalSectionUnit_ne_zero_iff s).mpr hs) b = sectionZeroCycleDegree f E a s hs b := by
  let := sectionZero_isArtinian f E a s hs
  let := sectionZero_isArtinian f E (a.tensorPower 1) (originalSectionUnit s)
    ((originalSectionUnit_ne_zero_iff s).mpr hs)
  rw [sectionZeroCycleDegree_eq_sum_lengths, sectionZeroCycleDegree_eq_sum_lengths]
  exact congrArg (fun q : ℕ∞ => (q.toNat : ℤ))
    (artinian_selfLength_sum_eq_of_iso (originalSectionUnit_zeroSchemeIso a s))

local instance ordinaryPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance ordinaryPointCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1
local instance ordinaryPointMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance ordinaryPointBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
local instance ordinaryPointManifold : IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1

/-- Ordinary original Γ(L) degree equals the SAME original supplied metric Chern period. -/
theorem ordinarySectionZeroCycleDegree_eq_originalChernPeriod (H : SchemeLineBundleMetric f 1 E L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (b : Spec (.of ℂ))
    (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ((sectionZeroCycleDegree f E a s hs b : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have h := sectionZeroCycleDegree_eq_originalChernPeriod f E a H 0 (originalSectionUnit s)
    ((originalSectionUnit_ne_zero_iff s).mpr hs) b κ
  rw [sectionZeroCycleDegree_originalSectionUnit f E a s hs b] at h
  simpa only [Nat.zero_add, Nat.cast_one, one_mul] using h

end SGPT.Projective.NumEq.AlgebraicCurveDegree
