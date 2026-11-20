import SGPT.Toric.ExceptionalCurve
import SGPT.Toric.HyperplaneSectionNonampleness
import SGPT.Toric.ExceptionalHyperplaneRestriction
import SGPT.Projective.FubiniStudy
import Lean.Elab.Command

section ExceptionalCanonicalFragment001
/- BEGIN OriginalHyperplaneDivisorPullbackDraft; original source SHA256 101667ef6dc54ea7a54db780962ee2f3b4f837c18cbbbab0a163211fea8cbc24 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff
variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME original Cartier section χ⁰, one of the original three blowdown sections. -/
def originalHyperplaneCartierSection : toricSections (blowupHyperplaneDivisor hs) :=
  originalMonomialSection (blowupHyperplaneDivisor hs) (blowdownLatticePoint hs 0)

/-- Actual full-H0 physical realization of that exact original section. -/
def originalHyperplanePhysicalSection : ToricNativeHolomorphicSections (nativeSourceHyperplaneMetric hs) :=
  (toricNativeFullSectionEquiv (nativeSourceHyperplaneMetric hs)).symm (originalHyperplaneCartierSection hs)

/-- Actual source frame coefficient is the SAME X0 coefficient in the actual blowdown vector. -/
theorem originalHyperplanePhysicalSection_coefficient (k : Fin 4) (z : Fin 2 → ℂ) :
    (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) (blowupVertex k)
      ⟨blowupOriginalChartPoint hs k z,
        originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k z)⟩).2 =
      blowdownChartVector k z 0 := by
  unfold originalHyperplanePhysicalSection
  rw [toricNativeFullSectionEquiv_symm_coefficient _ _ _ (blowupOriginalChartPoint_mem hs k z)]
  unfold originalHyperplaneCartierSection
  rw [originalMonomialSection_coefficient, blowupOriginalChartPoint_coordinate]
  exact congrFun (blowdownOriginalVector hs k z) (0 : Fin 3)

/-- BOTH exact printed local Cartier equations: 1,s,a,1 on the WHOLE original affine charts. -/
theorem originalHyperplanePhysicalSection_literal (k : Fin 4) (z : Fin 2 → ℂ) :
    (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) (blowupVertex k)
      ⟨blowupOriginalChartPoint hs k z,
        originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k z)⟩).2 =
      (![1, z 1, z 0, 1] : Fin 4 → ℂ) k := by
  rw [originalHyperplanePhysicalSection_coefficient]
  fin_cases k <;> rfl

/-- The four actual identically-one target normalization pivots. -/
def originalHyperplanePullbackPivot : Fin 4 → Fin 3 := ![0, 1, 2, 0]

theorem originalHyperplanePullbackPivot_coefficient (k : Fin 4) (z : Fin 2 → ℂ) :
    blowdownChartVector k z (originalHyperplanePullbackPivot k) = 1 := by
  fin_cases k <;> rfl

/-- Actual normalized pullback defining function of the coordinate hyperplane X0=0. -/
theorem originalHyperplanePullback_ratio (k : Fin 4) (z : Fin 2 → ℂ) :
    projectiveCoordinateRatio 0 (originalHyperplanePullbackPivot k)
      (originalBlowdown hs (blowupOriginalChartPoint hs k z)) = blowdownChartVector k z 0 := by
  rw [originalBlowdown_chart, projectiveCoordinateRatio_mk, originalHyperplanePullbackPivot_coefficient, div_one]

/-- Actual physical Cartier section coefficient equals the actual pulled-back hyperplane equation. -/
theorem originalHyperplanePhysicalSection_pullback_equation (k : Fin 4) (z : Fin 2 → ℂ) :
    (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) (blowupVertex k)
      ⟨blowupOriginalChartPoint hs k z,
        originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k z)⟩).2 =
      projectiveCoordinateRatio 0 (originalHyperplanePullbackPivot k)
        (originalBlowdown hs (blowupOriginalChartPoint hs k z)) :=
  (originalHyperplanePhysicalSection_coefficient hs k z).trans (originalHyperplanePullback_ratio hs k z).symm

def blowupHyperplaneRay : PolytopeToricRays blowupGenerator hs :=
  ⟨blowupRay4, by rw [blowup_rays hs]; simp⟩

theorem originalHyperplaneRay_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupOriginalChartPoint hs k z ∈ toricPrimeDivisor (blowupHyperplaneRay hs) ↔
      (![False, z 1 = 0, z 0 = 0, False] : Fin 4 → Prop) k := by
  rw [originalPrimeDivisor_chart]
  fin_cases k <;> norm_num [Fin.exists_fin_two, blowupBasis, blowupHyperplaneRay,
    vertexConeRay_lattice2Basis_zero, vertexConeRay_lattice2Basis_one, blowupRay4]

theorem originalHyperplanePhysicalSection_zero_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k z) = 0 ↔
      blowdownChartVector k z 0 = 0 := by
  let p := blowupOriginalChartPoint hs k z
  let e := toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) (blowupVertex k)
  have hp : p ∈ e.baseSet := blowupOriginalChartPoint_mem hs k z
  rw [← originalHyperplanePhysicalSection_coefficient hs k z]
  change originalHyperplanePhysicalSection hs p = 0 ↔
    e.linearEquivAt ℂ p hp (originalHyperplanePhysicalSection hs p) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (e.linearEquivAt ℂ p hp).injective
    simpa only [map_zero] using h

/-- Exact SAME original prime divisor is the actual zero locus of the actual physical χ⁰ section. -/
theorem originalHyperplanePhysicalSection_zero_locus :
    {p | originalHyperplanePhysicalSection hs p = 0} = toricPrimeDivisor (blowupHyperplaneRay hs) := by
  ext p
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  change originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k z) = 0 ↔ _
  rw [originalHyperplanePhysicalSection_zero_chart, originalHyperplaneRay_chart]
  fin_cases k <;> simp [blowdownChartVector]

/-- Literal coordinate hyperplane pullback equals that SAME actual original Cartier divisor support.
The preceding WHOLE-chart identities retain the primitive order-one equations, not only this set equality. -/
theorem originalHyperplaneDivisor_pullback_support :
    {p : PolytopeToricVariety blowupGenerator hs | (originalBlowdown hs p).rep 0 = 0} =
      toricPrimeDivisor (blowupHyperplaneRay hs) := by
  ext p
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  change (originalBlowdown hs (blowupOriginalChartPoint hs k z)).rep 0 = 0 ↔ _
  rw [originalBlowdown_chart, projective_rep_mk_eq_zero_iff, originalHyperplaneRay_chart]
  fin_cases k <;> simp [blowdownChartVector]

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END OriginalHyperplaneDivisorPullbackDraft -/
end ExceptionalCanonicalFragment001

section ExceptionalCanonicalFragment002
/- BEGIN ActualHyperplaneCartierEquationsDraft; original source SHA256 d38c87082b20f4353cb039967b895fb4101900257b769efee8a40068092c3899 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff
variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The ENTIRE actual original chart maps into the indicated genuine affine target chart;
the normalized equations below therefore never use a zero denominator. -/
theorem originalHyperplanePullback_chart_mem (k : Fin 4) (z : Fin 2 → ℂ) :
    originalBlowdown hs (blowupOriginalChartPoint hs k z) ∈
      (SGPT.Projective.ComplexProjectiveSpace.affineChart (originalHyperplanePullbackPivot k)).source := by
  rw [originalBlowdown_chart, SGPT.Projective.ComplexProjectiveSpace.mk_mem_affineChart_source_iff,
    originalHyperplanePullbackPivot_coefficient]
  exact one_ne_zero

/-- SAME actual physical coefficient in actual source ordered affine-model coordinates. -/
def originalHyperplanePhysicalModelCoefficient (k : Fin 4) (z : ComplexModel 2) : ℂ :=
  (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) (blowupVertex k)
    ⟨blowupOriginalChartPoint hs k (WithLp.ofLp z),
      originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k (WithLp.ofLp z))⟩).2

theorem originalHyperplanePhysicalModelCoefficient_one :
    originalHyperplanePhysicalModelCoefficient hs 1 = fun z : ComplexModel 2 => z 1 := by
  funext z
  exact originalHyperplanePhysicalSection_literal hs 1 (WithLp.ofLp z)

theorem originalHyperplanePhysicalModelCoefficient_two :
    originalHyperplanePhysicalModelCoefficient hs 2 = fun z : ComplexModel 2 => z 0 := by
  funext z
  exact originalHyperplanePhysicalSection_literal hs 2 (WithLp.ofLp z)

/-- The actual section has literal primitive coordinate, hence simple, equations on BOTH
charts containing the hyperplane divisor, with the genuine nonzero coordinate differential. -/
theorem originalHyperplanePhysicalSection_simple_equations (z : ComplexModel 2) :
    HasFDerivAt (originalHyperplanePhysicalModelCoefficient hs 1)
      (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)) z ∧
    HasFDerivAt (originalHyperplanePhysicalModelCoefficient hs 2)
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) z ∧
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)) ≠ 0 ∧
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) ≠ 0 := by
  rw [originalHyperplanePhysicalModelCoefficient_one, originalHyperplanePhysicalModelCoefficient_two]
  refine ⟨(EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).hasFDerivAt,
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).hasFDerivAt, ?_, ?_⟩
  · intro h
    have hval := congrArg (fun L : ComplexModel 2 →L[ℂ] ℂ => L (modelPoint (Pi.single 1 1))) h
    norm_num [modelPoint_apply] at hval
  · intro h
    have hval := congrArg (fun L : ComplexModel 2 →L[ℂ] ℂ => L (modelPoint (Pi.single 0 1))) h
    norm_num [modelPoint_apply] at hval

/-- Exact whole-chart Cartier pullback data, SAME actual section and SAME actual global pi. -/
theorem originalHyperplaneCartier_pullback_equations (k : Fin 4) (z : Fin 2 → ℂ) :
    originalBlowdown hs (blowupOriginalChartPoint hs k z) ∈
      (SGPT.Projective.ComplexProjectiveSpace.affineChart (originalHyperplanePullbackPivot k)).source ∧
    (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) (blowupVertex k)
      ⟨blowupOriginalChartPoint hs k z,
        originalHyperplanePhysicalSection hs (blowupOriginalChartPoint hs k z)⟩).2 =
      projectiveCoordinateRatio 0 (originalHyperplanePullbackPivot k)
        (originalBlowdown hs (blowupOriginalChartPoint hs k z)) ∧
    projectiveCoordinateRatio 0 (originalHyperplanePullbackPivot k)
      (originalBlowdown hs (blowupOriginalChartPoint hs k z)) = (![1, z 1, z 0, 1] : Fin 4 → ℂ) k := by
  refine ⟨originalHyperplanePullback_chart_mem hs k z,
    originalHyperplanePhysicalSection_pullback_equation hs k z, ?_⟩
  rw [← originalHyperplanePhysicalSection_pullback_equation, originalHyperplanePhysicalSection_literal]

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END ActualHyperplaneCartierEquationsDraft -/
end ExceptionalCanonicalFragment002

section ExceptionalCanonicalFragment003
/- BEGIN SourceExceptionalRestrictionDraft; original source SHA256 7f159a587dc9c1d964ca97af2d38eae5d531e8b3765ff195a1ce9afc7196cf30 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem exceptionalZeroPoint_eq_curve : exceptionalZeroPoint hs =
    originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 0) := by
  unfold exceptionalZeroPoint
  rw [originalExceptionalCurve_affine]
  change blowupOriginalChartPoint hs 0 0 = blowupOriginalChartPoint hs 0 ![0, 0]
  apply congrArg (blowupOriginalChartPoint hs 0)
  funext j
  fin_cases j <;> rfl

theorem exceptionalInfinityPoint_eq_curve : exceptionalInfinityPoint hs =
    originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint 1 0) := by
  unfold exceptionalInfinityPoint
  rw [originalExceptionalCurve_affine]
  change blowupOriginalChartPoint hs 3 0 = blowupOriginalChartPoint hs 3 ![0, 0]
  apply congrArg (blowupOriginalChartPoint hs 3)
  funext j
  fin_cases j <;> rfl

theorem exceptional_endpoints_mem_primeDivisor :
    exceptionalZeroPoint hs ∈ toricPrimeDivisor (blowupExceptionalRay hs) ∧
      exceptionalInfinityPoint hs ∈ toricPrimeDivisor (blowupExceptionalRay hs) := by
  rw [← originalExceptionalCurve_range hs, exceptionalZeroPoint_eq_curve, exceptionalInfinityPoint_eq_curve]
  exact ⟨mem_range_self _, mem_range_self _⟩

/-- Source-only actual exceptional projective line, with smoothness manufactured internally. -/
abbrev sourceOriginalExceptionalCurve := originalExceptionalCurve blowup_edgeSmooth

/-- Source-only actual physical H restriction isomorphism, with no outgoing certificate input. -/
def sourceExceptionalHyperplaneTrivialization := exceptionalHyperplaneBundleHomeomorph blowup_edgeSmooth

def sourceExceptionalHyperplaneFullSectionsEquiv := exceptionalRestrictionFullSectionsEquiv blowup_edgeSmooth

/-- Genuine source-only geometry and physical obstruction. This theorem deliberately does
not assert an equivalence with scheme IsAmple or a numerical intersection dictionary. -/
theorem source_original_exceptional_hyperplane_obstruction :
    IsClosedEmbedding sourceOriginalExceptionalCurve ∧
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞ sourceOriginalExceptionalCurve ∧
    range sourceOriginalExceptionalCurve = toricPrimeDivisor (blowupExceptionalRay blowup_edgeSmooth) ∧
    (∀ u, originalBlowdown blowup_edgeSmooth (sourceOriginalExceptionalCurve u) = blowdownOrigin) ∧
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞ sourceExceptionalHyperplaneTrivialization ∧
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞ sourceExceptionalHyperplaneTrivialization.symm ∧
    exceptionalZeroPoint blowup_edgeSmooth ≠ exceptionalInfinityPoint blowup_edgeSmooth ∧
    (∀ (q r : ℕ)
      (s : Fin (r + 1) → ToricNativePlainPowerSections (nativeSourceHyperplaneMetric blowup_edgeSmooth) q)
      (hbf : PhysicalPowerBasepointFree (nativeSourceHyperplaneMetric blowup_edgeSmooth) q s),
      ¬ Function.Injective (physicalPowerSectionProjectiveMap
        (nativeSourceHyperplaneMetric blowup_edgeSmooth) q s hbf)) ∧
    ¬ GeometricPhysicalSectionAmple (nativeSourceHyperplaneMetric blowup_edgeSmooth) :=
  ⟨isClosedEmbedding_originalExceptionalCurve _, contMDiff_originalExceptionalCurve _,
    originalExceptionalCurve_range _, originalExceptionalCurve_blowdown _,
    contMDiff_exceptionalHyperplaneTotalMap _, contMDiff_exceptionalHyperplaneTotalInv _,
    exceptionalZeroPoint_ne_infinity _, fun q _ s hbf =>
      not_injective_physicalHyperplanePowerSectionMap _ q s hbf,
    not_geometricPhysicalSectionAmple_hyperplane _⟩

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END SourceExceptionalRestrictionDraft -/
end ExceptionalCanonicalFragment003

section ExceptionalCanonicalFragment004
/- BEGIN SourceP2BlowupExampleDraft; original source SHA256 b388991b96d5343fad362f8c9d472fe0709407f3d8aa87645dff1cebf57e89a8 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Toric.BlowdownDraft SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff

/-- A genuine source-only Chern integral, with BOTH the actual integration background and
actual flat metric manufactured internally. No background/metric/nonemptiness input. -/
def sourceExceptionalHyperplaneDegree : ℝ :=
  exceptionalHyperplaneCurveDegree blowup_edgeSmooth
    (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1))
    (exceptionalFlatHermitianMetric blowup_edgeSmooth)

theorem sourceExceptionalHyperplaneDegree_zero : sourceExceptionalHyperplaneDegree = 0 :=
  exceptionalHyperplaneCurveDegree_eq_zero _ _ _

/-- Literal native source ex:P2bl1pt: actual point blowup/exceptional divisor, genuine
physical H pullback, SAME Cartier section and all primitive local divisor equations,
actual degree-zero reason and absence of every positive-power projective embedding.
The prior exact fan/Cartier/polytope/face canonical bindings remain unchanged. -/
theorem source_P2bl1pt_hyperplane_geometry :
    IsBlowupAlong 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))
      sourceOriginalBlowdown ∧
    {p : SourceOriginalBlowupSurface | sourceOriginalBlowdown p = blowdownOrigin} =
      toricPrimeDivisor (blowupExceptionalRay blowup_edgeSmooth) ∧
    IsClosedEmbedding sourceOriginalExceptionalCurve ∧
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞ sourceOriginalExceptionalCurve ∧
    range sourceOriginalExceptionalCurve = toricPrimeDivisor (blowupExceptionalRay blowup_edgeSmooth) ∧
    ContMDiff ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ sourceOriginalHyperplaneBundleIsomorphism ∧
    ContMDiff ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ sourceOriginalHyperplaneBundleIsomorphism.symm ∧
    {p | originalHyperplanePhysicalSection blowup_edgeSmooth p = 0} =
      toricPrimeDivisor (blowupHyperplaneRay blowup_edgeSmooth) ∧
    {p : SourceOriginalBlowupSurface | (sourceOriginalBlowdown p).rep 0 = 0} =
      toricPrimeDivisor (blowupHyperplaneRay blowup_edgeSmooth) ∧
    (∀ (k : Fin 4) (z : Fin 2 → ℂ),
      originalBlowdown blowup_edgeSmooth (blowupOriginalChartPoint blowup_edgeSmooth k z) ∈
        (SGPT.Projective.ComplexProjectiveSpace.affineChart (originalHyperplanePullbackPivot k)).source ∧
      (toricNativeLineTrivialization (nativeSourceHyperplaneMetric blowup_edgeSmooth) (blowupVertex k)
        ⟨blowupOriginalChartPoint blowup_edgeSmooth k z,
          originalHyperplanePhysicalSection blowup_edgeSmooth (blowupOriginalChartPoint blowup_edgeSmooth k z)⟩).2 =
        projectiveCoordinateRatio 0 (originalHyperplanePullbackPivot k)
          (originalBlowdown blowup_edgeSmooth (blowupOriginalChartPoint blowup_edgeSmooth k z)) ∧
      projectiveCoordinateRatio 0 (originalHyperplanePullbackPivot k)
        (originalBlowdown blowup_edgeSmooth (blowupOriginalChartPoint blowup_edgeSmooth k z)) =
          (![1, z 1, z 0, 1] : Fin 4 → ℂ) k) ∧
    (∀ z : ComplexModel 2,
      HasFDerivAt (originalHyperplanePhysicalModelCoefficient blowup_edgeSmooth 1)
        (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)) z ∧
      HasFDerivAt (originalHyperplanePhysicalModelCoefficient blowup_edgeSmooth 2)
        (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) z ∧
      (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)) ≠ 0 ∧
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) ≠ 0) ∧
    (∀ (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
      (h : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber blowup_edgeSmooth)),
      exceptionalHyperplaneCurveDegree blowup_edgeSmooth κ h = 0) ∧
    sourceExceptionalHyperplaneDegree = 0 ∧
    ¬ GeometricPhysicalSectionAmple (nativeSourceHyperplaneMetric blowup_edgeSmooth) := by
  have hE := source_original_exceptional_hyperplane_obstruction
  exact ⟨source_original_point_blowup, originalBlowdown_fibre_origin _, hE.1, hE.2.1, hE.2.2.1,
    source_original_hyperplane_bundle_pullback.1, source_original_hyperplane_bundle_pullback.2,
    originalHyperplanePhysicalSection_zero_locus _, originalHyperplaneDivisor_pullback_support _,
    originalHyperplaneCartier_pullback_equations _, originalHyperplanePhysicalSection_simple_equations _,
    exceptionalHyperplaneCurveDegree_eq_zero _, sourceExceptionalHyperplaneDegree_zero,
    not_geometricPhysicalSectionAmple_hyperplane _⟩

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END SourceP2BlowupExampleDraft -/
end ExceptionalCanonicalFragment004


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalExceptionalCurveDraft, `NativeHolomorphicPullbackLiftDraft, `NativeHolomorphicPullbackMkDraft, `ExceptionalHyperplaneRestrictionDraft, `ExceptionalRestrictionFullSectionsDraft, `PhysicalPowerExceptionalValuesDraft, `OriginalFullSectionProjectiveMapDraft, `PhysicalHyperplaneNonseparationDraft, `SourceExceptionalRestrictionDraft, `ExceptionalFlatHermitianMetricDraft, `ExceptionalCurveDegreeDraft, `OriginalHyperplaneDivisorPullbackDraft, `ActualHyperplaneCartierEquationsDraft, `SourceP2BlowupExampleDraft, `OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private source or geometry provider in proper exceptional module: {m}"
