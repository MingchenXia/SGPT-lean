import SGPT.Toric.ExceptionalHyperplaneRestriction
import Mathlib.Geometry.Manifold.Complex
import SGPT.Toric.SourcePointBlowupOkounkov
import SGPT.Projective.Maps
import Lean.Elab.Command

section ExceptionalCanonicalFragment001
/- BEGIN PhysicalPowerExceptionalValuesDraft; original source SHA256 d339db644c5cd0c2293eb447b3e0cd45e903590bf334e2ef1303a586116d4de2 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual monomial value at an original vertex origin, retaining ALL lattice sections. -/
theorem toricMonomial_at_vertex_zero (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints D) :
    toricMonomial D v m 0 = if m = toricCartierDatum D v then 1 else 0 := by
  classical
  by_cases h : m = toricCartierDatum D v
  · simp [h, toricMonomial]
  · rw [if_neg h]
    have hpos : ∃ j, 0 < intPairing m (polytopeToricRayGenerator γ hs v j) -
        intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j) := by
      by_contra hn
      push Not at hn
      apply h
      apply eq_of_intPairing_rayGenerator_eq v
      intro j
      have hp := (mem_toricLatticePoints_iff D m).mp hm v j
      have hj := hn j
      omega
    obtain ⟨j, hj⟩ := hpos
    unfold toricMonomial
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    exact zero_pow (by omega)

/-- Actual FULL Cartier coefficient readback at a vertex; no monomial subspace is substituted. -/
theorem toricSectionCoeff_at_vertex_zero (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D) :
    toricSectionCoeff D v g 0 = ∑ m ∈ (finite_toricLatticePoints D).toFinset,
      toricSectionLaurentCoeff g m * (if m = toricCartierDatum D v then 1 else 0) := by
  classical
  rw [toricSectionCoeff_eq_sum hg v]
  apply Finset.sum_congr rfl
  intro m hm
  rw [toricMonomial_at_vertex_zero D v ((finite_toricLatticePoints D).mem_toFinset.mp hm)]

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The two actual source toric points, both on the same exceptional P1. -/
def exceptionalZeroPoint : PolytopeToricVariety blowupGenerator hs := blowupOriginalChartPoint hs 0 0

def exceptionalInfinityPoint : PolytopeToricVariety blowupGenerator hs := blowupOriginalChartPoint hs 3 0

theorem blowupOriginalChartPoint_zero_vertex (k : Fin 4) :
    blowupOriginalChartPoint hs k 0 = vertexPoint hs (blowupVertex k) 0 := by
  unfold blowupOriginalChartPoint vertexPoint
  congr 1

/-- EVERY actual full physical power section has equal coefficients at the two exceptional points. -/
theorem physicalPower_exceptional_endpoint_coefficients (q : ℕ)
    (s : ToricNativePlainPowerSections (nativeSourceHyperplaneMetric hs) q) :
    ((physicalPlainPowerFrame (nativeSourceHyperplaneMetric hs) (blowupVertex 0) q).val
      ⟨exceptionalZeroPoint hs, s (exceptionalZeroPoint hs)⟩).2 =
    ((physicalPlainPowerFrame (nativeSourceHyperplaneMetric hs) (blowupVertex 3) q).val
      ⟨exceptionalInfinityPoint hs, s (exceptionalInfinityPoint hs)⟩).2 := by
  unfold exceptionalZeroPoint exceptionalInfinityPoint
  rw [physicalPlainPowerFrame_fullSection_coefficient _ q s (blowupVertex 0)
    (blowupOriginalChartPoint_mem hs 0 0),
    physicalPlainPowerFrame_fullSection_coefficient _ q s (blowupVertex 3)
      (blowupOriginalChartPoint_mem hs 3 0)]
  rw [blowupOriginalChartPoint_zero_vertex, blowupOriginalChartPoint_zero_vertex,
    chart_vertexPoint, chart_vertexPoint]
  rw [toricSectionCoeff_at_vertex_zero _ _ (toricNativePlainPowerFullSectionEquiv _ q s).property,
    toricSectionCoeff_at_vertex_zero _ _ (toricNativePlainPowerFullSectionEquiv _ q s).property,
    toricCartierDatum_smul, toricCartierDatum_smul,
    (toricCartierDatum_blowupHyperplaneDivisor hs).1,
    (toricCartierDatum_blowupHyperplaneDivisor hs).2.1]

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END PhysicalPowerExceptionalValuesDraft -/
end ExceptionalCanonicalFragment001

section ExceptionalCanonicalFragment002
/- BEGIN OriginalFullSectionProjectiveMapDraft; original source SHA256 b77638cc7c7db709e367ca05aa007902a4540d9f4347bd2fdeaeb65c1080a12b -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Filter Topology Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Manifold ContDiff BigOperators
variable {n r : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Vector of genuine FULL Cartier section coefficients, not monomials only. -/
def originalFullSectionVector (D : ToricDivisor γ hs) (g : Fin (r + 1) → toricSections D)
    (v : latticePolytopeVertices γ) (z : ComplexModel n) : Fin (r + 1) → ℂ :=
  fun i => toricOriginalSectionCoeff (g i) v z

/-- The local-frame expression of the ordinary no-common-zero condition. -/
def OriginalFullSectionBasepointFree (D : ToricDivisor γ hs)
    (g : Fin (r + 1) → toricSections D) : Prop :=
  ∀ (v : latticePolytopeVertices γ) (p : PolytopeToricVariety γ hs),
    p ∈ (originalPolytopeNativeModelChart γ hs v).source →
      originalFullSectionVector D g v (originalPolytopeNativeModelChart γ hs v p) ≠ 0

/-- The actual projective section map is internally manufactured on the SAME source. -/
def originalFullSectionProjectiveMap (D : ToricDivisor γ hs)
    (g : Fin (r + 1) → toricSections D) (hbf : OriginalFullSectionBasepointFree D g)
    (p : PolytopeToricVariety γ hs) : SGPT.Projective.ComplexProjectiveSpace r :=
  let v := toricNativePreferredVertex γ hs p
  SGPT.Projective.ComplexProjectiveSpace.mk
    (originalFullSectionVector D g v (originalPolytopeNativeModelChart γ hs v p))
    (hbf v p (toricNativePreferredVertex_mem p))

/-- Literal coefficient readback in EVERY original whole vertex source. -/
theorem originalFullSectionProjectiveMap_eq_chart (D : ToricDivisor γ hs)
    (g : Fin (r + 1) → toricSections D) (hbf : OriginalFullSectionBasepointFree D g)
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    originalFullSectionProjectiveMap D g hbf p = SGPT.Projective.ComplexProjectiveSpace.mk
      (originalFullSectionVector D g v (originalPolytopeNativeModelChart γ hs v p)) (hbf v p hv) := by
  let w := toricNativePreferredVertex γ hs p
  have hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source := toricNativePreferredVertex_mem p
  apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨toricCartierTransition D v w p, ?_⟩
  funext i
  exact (toricOriginalSectionCoeff_transition (g i) v w hv hw).symm

theorem contMDiff_originalFullSectionProjectiveMap (D : ToricDivisor γ hs)
    (g : Fin (r + 1) → toricSections D) (hbf : OriginalFullSectionBasepointFree D g) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel r) ∞
      (originalFullSectionProjectiveMap D g hbf) := by
  intro p
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
  have hchart : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun q : PolytopeToricVariety γ hs => originalPolytopeNativeModelChart γ hs v q) p :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas
      (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (show originalPolytopeNativeModelChart γ hs v ∈
        atlas (ComplexModel n) (PolytopeToricVariety γ hs) from ⟨v, rfl⟩)) hv
  have hdiff : Differentiable ℂ (originalFullSectionVector D g v) :=
    differentiable_pi.mpr fun i => differentiable_toricOriginalSectionCoeff (g i) v
  have hsmooth : ContDiff ℂ ∞ (originalFullSectionVector D g v) :=
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex hdiff.differentiableOn isOpen_univ)
  apply SGPT.Projective.ComplexProjectiveSpace.contMDiffAt_of_lift
    (hsmooth.contMDiff.contMDiffAt.comp p hchart) (hbf v p hv)
  filter_upwards [(originalPolytopeNativeModelChart γ hs v).open_source.mem_nhds hv] with q hq
  exact ⟨hbf v q hq, originalFullSectionProjectiveMap_eq_chart D g hbf v hq⟩

/-- Pointwise no-common-zero condition for independent actual physical full H0 sections. -/
def PhysicalPowerBasepointFree {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ)
    (s : Fin (r + 1) → ToricNativePlainPowerSections h q) : Prop :=
  ∀ p : PolytopeToricVariety γ hs, ∃ i, s i p ≠ 0

/-- The actual physical BF condition internally produces the Cartier BF property. -/
theorem physicalPower_fullSection_basepointFree {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (s : Fin (r + 1) → ToricNativePlainPowerSections h q) (hbf : PhysicalPowerBasepointFree h q s) :
    OriginalFullSectionBasepointFree ((q : ℤ) • D)
      (fun i => toricNativePlainPowerFullSectionEquiv h q (s i)) := by
  intro v p hp hz
  obtain ⟨i, hi⟩ := hbf p
  apply hi
  let e := physicalPlainPowerFrame h v q
  have he : p ∈ e.val.baseSet := physicalPlainPowerFrame_mem h v q hp
  have hc : (e.val ⟨p, s i p⟩).2 = 0 := by
    rw [physicalPlainPowerFrame_fullSection_coefficient h q (s i) v hp,
      ← originalSectionCoeff_eq_sectionCoeff]
    exact congrFun hz i
  apply (e.val.linearEquivAt ℂ p he).injective
  simpa only [map_zero, Trivialization.linearEquivAt_apply] using hc

/-- Actual map of arbitrary actual physical sections: every map and compatibility is outgoing. -/
def physicalPowerSectionProjectiveMap {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (s : Fin (r + 1) → ToricNativePlainPowerSections h q) (hbf : PhysicalPowerBasepointFree h q s) :
    PolytopeToricVariety γ hs → SGPT.Projective.ComplexProjectiveSpace r :=
  originalFullSectionProjectiveMap ((q : ℤ) • D)
    (fun i => toricNativePlainPowerFullSectionEquiv h q (s i))
    (physicalPower_fullSection_basepointFree h q s hbf)

theorem contMDiff_physicalPowerSectionProjectiveMap {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (s : Fin (r + 1) → ToricNativePlainPowerSections h q) (hbf : PhysicalPowerBasepointFree h q s) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel r) ∞
      (physicalPowerSectionProjectiveMap h q s hbf) :=
  contMDiff_originalFullSectionProjectiveMap _ _ _

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END OriginalFullSectionProjectiveMapDraft -/
end ExceptionalCanonicalFragment002

section ExceptionalCanonicalFragment003
/- BEGIN PhysicalHyperplaneNonseparationDraft; original source SHA256 b163bd21c22d263693864d099ad8754c4aa0670422f97b31076821bfe8ad077d -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff
variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Two genuinely distinct points of the SAME actual source exceptional fibre. -/
theorem exceptionalZeroPoint_ne_infinity : exceptionalZeroPoint hs ≠ exceptionalInfinityPoint hs := by
  intro h
  have hρ := congrArg (originalBlowupDirection hs) h
  change originalBlowupDirection hs (blowupOriginalChartPoint hs 0 0) =
    originalBlowupDirection hs (blowupOriginalChartPoint hs 3 0) at hρ
  rw [originalBlowupDirection_chart, originalBlowupDirection_chart] at hρ
  obtain ⟨c, hc⟩ := (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mp hρ
  have hc0 := congrFun hc 0
  change c * (0 : ℂ) = 1 at hc0
  norm_num only [mul_zero] at hc0

/-- Literal readback at an arbitrary source point in an arbitrary frame. -/
theorem physicalPower_cartierVector_coordinate {r : ℕ} (q : ℕ)
    (s : Fin (r + 1) → ToricNativePlainPowerSections (nativeSourceHyperplaneMetric hs) q)
    (v : latticePolytopeVertices blowupGenerator) {p : PolytopeToricVariety blowupGenerator hs}
    (hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source) (i : Fin (r + 1)) :
    originalFullSectionVector ((q : ℤ) • blowupHyperplaneDivisor hs)
      (fun i => toricNativePlainPowerFullSectionEquiv (nativeSourceHyperplaneMetric hs) q (s i)) v
        (originalPolytopeNativeModelChart blowupGenerator hs v p) i =
      ((physicalPlainPowerFrame (nativeSourceHyperplaneMetric hs) v q).val ⟨p, s i p⟩).2 := by
  change toricOriginalSectionCoeff
    (toricNativePlainPowerFullSectionEquiv (nativeSourceHyperplaneMetric hs) q (s i)) v _ = _
  rw [originalSectionCoeff_eq_sectionCoeff]
  exact (physicalPlainPowerFrame_fullSection_coefficient _ q (s i) v hp).symm

/-- Every actual projectivized FULL physical power-section system identifies the two points.
There is no supplied projective map, compatibility or obstruction premise. -/
theorem physicalPowerSectionProjectiveMap_exceptional_endpoints {r : ℕ} (q : ℕ)
    (s : Fin (r + 1) → ToricNativePlainPowerSections (nativeSourceHyperplaneMetric hs) q)
    (hbf : PhysicalPowerBasepointFree (nativeSourceHyperplaneMetric hs) q s) :
    physicalPowerSectionProjectiveMap (nativeSourceHyperplaneMetric hs) q s hbf (exceptionalZeroPoint hs) =
      physicalPowerSectionProjectiveMap (nativeSourceHyperplaneMetric hs) q s hbf (exceptionalInfinityPoint hs) := by
  unfold exceptionalZeroPoint exceptionalInfinityPoint
  unfold physicalPowerSectionProjectiveMap
  rw [originalFullSectionProjectiveMap_eq_chart _ _ _ (blowupVertex 0)
    (blowupOriginalChartPoint_mem hs 0 0),
    originalFullSectionProjectiveMap_eq_chart _ _ _ (blowupVertex 3)
      (blowupOriginalChartPoint_mem hs 3 0)]
  apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨1, ?_⟩
  rw [one_smul]
  funext i
  rw [physicalPower_cartierVector_coordinate hs q s (blowupVertex 3)
      (blowupOriginalChartPoint_mem hs 3 0) i,
    physicalPower_cartierVector_coordinate hs q s (blowupVertex 0)
      (blowupOriginalChartPoint_mem hs 0 0) i]
  exact (physicalPower_exceptional_endpoint_coefficients hs q (s i)).symm

/-- Actual geometric nonseparation, for ALL degrees, ALL target dimensions and ALL full sections. -/
theorem not_injective_physicalHyperplanePowerSectionMap {r : ℕ} (q : ℕ)
    (s : Fin (r + 1) → ToricNativePlainPowerSections (nativeSourceHyperplaneMetric hs) q)
    (hbf : PhysicalPowerBasepointFree (nativeSourceHyperplaneMetric hs) q s) :
    ¬ Function.Injective (physicalPowerSectionProjectiveMap (nativeSourceHyperplaneMetric hs) q s hbf) := by
  intro hinj
  exact exceptionalZeroPoint_ne_infinity hs
    (hinj (physicalPowerSectionProjectiveMap_exceptional_endpoints hs q s hbf))

/-- Standard geometric PHYSICAL ampleness: an actual positive power has actual full H0
sections whose internally constructed map is a closed holomorphic immersion embedding.
This definition is explicitly distinct from the repository's scheme-theoretic IsAmple;
no scheme/native equivalence is asserted here. -/
def GeometricPhysicalSectionAmple {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
    {γ : K → Fin n → ℤ} {hs' : latticePolytopeEdgeSmooth γ}
    {D : ToricDivisor γ hs'} (h : BigToricMetric D) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ (r : ℕ) (s : Fin (r + 1) → ToricNativePlainPowerSections h q)
    (hbf : PhysicalPowerBasepointFree h q s),
    IsClosedEmbedding (physicalPowerSectionProjectiveMap h q s hbf) ∧
      ∀ p, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel r)
        (physicalPowerSectionProjectiveMap h q s hbf) p)

/-- The same actual physical H bundle has NO positive-power projective embedding system. -/
theorem not_geometricPhysicalSectionAmple_hyperplane :
    ¬ GeometricPhysicalSectionAmple (nativeSourceHyperplaneMetric hs) := by
  rintro ⟨q, -, r, s, hbf, he, -⟩
  exact not_injective_physicalHyperplanePowerSectionMap hs q s hbf he.injective

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END PhysicalHyperplaneNonseparationDraft -/
end ExceptionalCanonicalFragment003


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalExceptionalCurveDraft, `NativeHolomorphicPullbackLiftDraft, `NativeHolomorphicPullbackMkDraft, `ExceptionalHyperplaneRestrictionDraft, `ExceptionalRestrictionFullSectionsDraft, `PhysicalPowerExceptionalValuesDraft, `OriginalFullSectionProjectiveMapDraft, `PhysicalHyperplaneNonseparationDraft, `SourceExceptionalRestrictionDraft, `ExceptionalFlatHermitianMetricDraft, `ExceptionalCurveDegreeDraft, `OriginalHyperplaneDivisorPullbackDraft, `ActualHyperplaneCartierEquationsDraft, `SourceP2BlowupExampleDraft, `OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private source or geometry provider in proper exceptional module: {m}"
