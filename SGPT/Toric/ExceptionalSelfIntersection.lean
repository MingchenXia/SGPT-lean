import SGPT.Toric.ExceptionalCurve
import SGPT.Toric.ExceptionalHyperplaneRestriction
import SGPT.Projective.FubiniStudy
import SGPT.Hodge.SourceSmoothMixedCohomology
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN OriginalExceptionalTransitionDraft; original source SHA256 83d36514b234eb9f3ff9d0933bd702a8b6583e4434007912588e20234e1ed564 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual original exceptional Cartier divisor E=D_sigma7. -/
def originalExceptionalDivisor : ToricDivisor blowupGenerator hs :=
  toricDivisorOfCoeff hs fun u => if u = blowupRay7 then 1 else 0

/-- The four original dual-basis Cartier data, including BOTH exceptional charts. -/
def originalExceptionalDatum : Fin 4 → Fin 2 → ℤ :=
  ![![-1, 0], ![0, 0], ![0, 0], ![0, -1]]

theorem originalExceptional_cartierDatum (k : Fin 4) :
    toricCartierDatum (originalExceptionalDivisor hs) (blowupVertex k) =
      originalExceptionalDatum k := by
  apply toricCartierDatum_ofCoeff (fun u => if u = blowupRay7 then 1 else 0)
    (blowupVertex k) (blowup_isVertexConeBasis k)
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [originalExceptionalDatum, blowupBasis, vertexConeRay_lattice2Basis_zero,
      vertexConeRay_lattice2Basis_one, blowupRay7, intPairing, Fin.sum_univ_two]

/-- Reindex the ACTUAL original Cartier coefficient transition by the derived source bases. -/
theorem originalExceptional_transition_ordered (k l : Fin 4) (z : Fin 2 → ℂ) :
    toricCartierLaurentModel (originalExceptionalDivisor hs) (blowupVertex k) (blowupVertex l)
      (blowupOriginalCoordinates hs k z) =
    ∏ j : Fin 2, z j ^ intPairing (originalExceptionalDatum k - originalExceptionalDatum l)
      (vertexConeRay (blowupBasis k) j) := by
  unfold toricCartierLaurentModel toricCartierTransitionExponent
  simp only [originalExceptional_cartierDatum, blowupOriginalCoordinates, modelPoint_apply,
    polytopeToricRayGenerator_eq_vertexConeRay hs (blowupVertex k)
      (blowupOriginalPermutation_basis hs k)]
  exact Equiv.prod_comp (blowupOriginalPermutation hs k) (fun j : Fin 2 =>
    z j ^ intPairing (originalExceptionalDatum k - originalExceptionalDatum l)
      (vertexConeRay (blowupBasis k) j))

/-- The actual original O(E) coefficient transition on the entire chart0 formula is z_1. -/
theorem originalExceptional_transition_zero_three (z : Fin 2 → ℂ) :
    toricCartierTransition (originalExceptionalDivisor hs) (blowupVertex 0) (blowupVertex 3)
      (blowupOriginalChartPoint hs 0 z) = z 1 := by
  unfold toricCartierTransition
  rw [blowupOriginalChartPoint_coordinate, originalExceptional_transition_ordered]
  norm_num [Fin.prod_univ_two, originalExceptionalDatum, Matrix.cons_val_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, blowupBasis, vertexConeRay_lattice2Basis_zero,
    vertexConeRay_lattice2Basis_one, intPairing, Fin.sum_univ_two]

/-- The reverse actual original coefficient transition is z_0 on the other whole chart. -/
theorem originalExceptional_transition_three_zero (z : Fin 2 → ℂ) :
    toricCartierTransition (originalExceptionalDivisor hs) (blowupVertex 3) (blowupVertex 0)
      (blowupOriginalChartPoint hs 3 z) = z 0 := by
  unfold toricCartierTransition
  rw [blowupOriginalChartPoint_coordinate, originalExceptional_transition_ordered]
  norm_num [Fin.prod_univ_two, originalExceptionalDatum, Matrix.cons_val_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, blowupBasis, vertexConeRay_lattice2Basis_zero,
    vertexConeRay_lattice2Basis_one, intPairing, Fin.sum_univ_two]

/-- On the actual exceptional embedding [1:z], the SAME original transition is z. -/
theorem originalExceptional_transition_affine_zero (z : ComplexModel 1) :
    toricCartierTransition (originalExceptionalDivisor hs) (blowupVertex 0) (blowupVertex 3)
      (originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 z)) = z 0 := by
  rw [originalExceptionalCurve_affine]
  change toricCartierTransition _ _ _ (blowupOriginalChartPoint hs 0 ![0, z 0]) = z 0
  exact originalExceptional_transition_zero_three hs _

/-- On the other actual exceptional affine chart [w:1], the reverse transition is w. -/
theorem originalExceptional_transition_affine_one (z : ComplexModel 1) :
    toricCartierTransition (originalExceptionalDivisor hs) (blowupVertex 3) (blowupVertex 0)
      (originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint 1 z)) = z 0 := by
  rw [originalExceptionalCurve_affine]
  change toricCartierTransition _ _ _ (blowupOriginalChartPoint hs 3 ![z 0, 0]) = z 0
  exact originalExceptional_transition_three_zero hs _

/-- A genuine smooth physical O(E) metric exists internally; no curvature conclusion is input. -/
def originalExceptionalMetric : BigToricMetric (originalExceptionalDivisor hs) :=
  Classical.choice (exists_bigToricMetric _)

/-- The physical O(E) frame coefficients have the actual original Cartier transition
on every genuine overlap, including all exceptional points on that overlap. -/
theorem originalExceptional_physical_transition
    {p : PolytopeToricVariety blowupGenerator hs}
    (h0 : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex 0)).source)
    (h3 : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex 3)).source)
    (t : ToricNativeLineFiber (originalExceptionalMetric hs) p) :
    (toricNativeLineTrivialization (originalExceptionalMetric hs) (blowupVertex 3) ⟨p, t⟩).2 =
      toricCartierTransition (originalExceptionalDivisor hs) (blowupVertex 0) (blowupVertex 3) p *
        (toricNativeLineTrivialization (originalExceptionalMetric hs) (blowupVertex 0) ⟨p, t⟩).2 := by
  change toricNativeFrameCoefficient (originalExceptionalMetric hs) (blowupVertex 3) p *
      (show ℂ from t) = _
  rw [← toricNativeFrameCoefficient_transition (originalExceptionalMetric hs)
    (blowupVertex 0) (blowupVertex 3) h0 h3]
  exact mul_assoc _ _ _

end SGPT.Toric.F1IntersectionDraft

end
/- END OriginalExceptionalTransitionDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN ExceptionalDivisorRestrictionDraft; original source SHA256 1a83ed16407f3cb3cf502563aed90986dc994f78331f16cbb4f96d44079cb069 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME physical O(E) restricted by the actual original exceptional embedding. -/
abbrev ExceptionalDivisorFiber :=
  originalExceptionalHolomorphicMap hs *ᵖ (ToricNativeLineFiber (originalExceptionalMetric hs))

instance exceptionalDivisorNormed (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    NormedAddCommGroup (ExceptionalDivisorFiber hs u) :=
  inferInstanceAs (NormedAddCommGroup
    (ToricNativeLineFiber (originalExceptionalMetric hs) (originalExceptionalCurve hs u)))

instance exceptionalDivisorHermitian (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    InnerProductSpace ℂ (ExceptionalDivisorFiber hs u) :=
  inferInstanceAs (InnerProductSpace ℂ
    (ToricNativeLineFiber (originalExceptionalMetric hs) (originalExceptionalCurve hs u)))

/-- The actual restricted original frame; no topology is reassigned. -/
def exceptionalDivisorFrame (i : Fin 2) :
    Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ (ExceptionalDivisorFiber hs) →
      SGPT.Projective.ComplexProjectiveSpace 1) :=
  (toricNativeLineTrivialization (originalExceptionalMetric hs)
    (blowupVertex (exceptionalChartIndex i))).pullback (originalExceptionalHolomorphicMap hs)

instance exceptionalDivisorFrame_memAtlas (i : Fin 2) :
    MemTrivializationAtlas (exceptionalDivisorFrame hs i) := by
  constructor
  exact ⟨toricNativeLineTrivialization (originalExceptionalMetric hs)
    (blowupVertex (exceptionalChartIndex i)), inferInstance, rfl⟩

theorem exceptionalDivisorFrame_mem (i : Fin 2) {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hu : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    u ∈ (exceptionalDivisorFrame hs i).baseSet := by
  change originalExceptionalCurve hs u ∈
    (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex (exceptionalChartIndex i))).source
  have heq : SGPT.Projective.ComplexProjectiveSpace.affinePoint i
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i u) = u :=
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i).left_inv hu
  rw [← heq, originalExceptionalCurve_affine]
  exact blowupOriginalChartPoint_mem hs _ _

/-- BOTH literal exceptional affine transition ratios, including self changes. -/
theorem exceptionalDivisor_transition_affine (i l : Fin 2) (z : ComplexModel 1) :
    toricCartierTransition (originalExceptionalDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l))
      (originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint i z)) =
      SGPT.Projective.ComplexProjectiveSpace.affineLift i z l := by
  fin_cases i <;> fin_cases l
  · simp [toricCartierTransition, toricCartierLaurentModel, toricCartierTransitionExponent, intPairing]
  · simpa [exceptionalChartIndex, SGPT.Projective.ComplexProjectiveSpace.affineLift] using
      originalExceptional_transition_affine_zero hs z
  · change toricCartierTransition (originalExceptionalDivisor hs) (blowupVertex 3) (blowupVertex 0)
      (originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint 1 z)) =
        SGPT.Projective.ComplexProjectiveSpace.affineLift (1 : Fin 2) z 0
    rw [show SGPT.Projective.ComplexProjectiveSpace.affineLift (1 : Fin 2) z 0 = z 0 from
      SGPT.Projective.ComplexProjectiveSpace.affineLift_succAbove 1 z 0]
    exact originalExceptional_transition_affine_one hs z
  · simp [toricCartierTransition, toricCartierLaurentModel, toricCartierTransitionExponent, intPairing]

/-- Every actual affine normalized lift is the SAME original representative divided by its pivot. -/
theorem exceptional_normalizedLift (i : Fin 2) {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hu : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    SGPT.Projective.ComplexProjectiveSpace.affineLift i
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i u) = (u.rep i)⁻¹ • u.rep := by
  have hi : u.rep i ≠ 0 := (SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_source_iff i u).mp hu
  have hc : SGPT.Projective.ComplexProjectiveSpace.affineChart i u =
      SGPT.Projective.ComplexProjectiveSpace.affineRatio i u.rep := by
    conv_lhs => rw [← SGPT.Projective.ComplexProjectiveSpace.mk_rep u]
    exact SGPT.Projective.ComplexProjectiveSpace.affineChart_mk i u.rep_ne_zero hi
  rw [hc]
  exact SGPT.Projective.ComplexProjectiveSpace.affineLift_affineRatio i hi

/-- The actual O(E) transition on E is precisely the true homogeneous coordinate ratio. -/
theorem exceptionalDivisor_transition_ratio (i l : Fin 2) {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hu : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    toricCartierTransition (originalExceptionalDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l))
      (originalExceptionalCurve hs u) = u.rep l / u.rep i := by
  have heq : SGPT.Projective.ComplexProjectiveSpace.affinePoint i
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i u) = u :=
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i).left_inv hu
  calc
    _ = SGPT.Projective.ComplexProjectiveSpace.affineLift i
        (SGPT.Projective.ComplexProjectiveSpace.affineChart i u) l := by
      conv_lhs => rw [← heq]
      exact exceptionalDivisor_transition_affine hs i l _
    _ = _ := by rw [exceptional_normalizedLift i hu]; simp [div_eq_inv_mul]

/-- Actual linear frame coordinates of the SAME restricted physical fibre. -/
def exceptionalDivisorCoordinate (i : Fin 2) (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    ExceptionalDivisorFiber hs u →ₗ[ℂ] ℂ :=
  (exceptionalDivisorFrame hs i).linearMapAt ℂ u

/-- The real native physical coefficients, on EVERY genuine pair of exceptional affine opens. -/
theorem exceptionalDivisorCoordinate_transition (i l : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (hl : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart l).source)
    (t : ExceptionalDivisorFiber hs u) :
    exceptionalDivisorCoordinate hs l u t =
      (u.rep l / u.rep i) * exceptionalDivisorCoordinate hs i u t := by
  have hiE := exceptionalDivisorFrame_mem hs i hi
  have hlE := exceptionalDivisorFrame_mem hs l hl
  have htrans := toricNativeFrameCoefficient_transition (originalExceptionalMetric hs)
    (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l)) hiE hlE
  change toricCartierTransition (originalExceptionalDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l))
      (originalExceptionalCurve hs u) *
      toricNativeFrameCoefficient (originalExceptionalMetric hs) (blowupVertex (exceptionalChartIndex i))
        (originalExceptionalCurve hs u) =
      toricNativeFrameCoefficient (originalExceptionalMetric hs) (blowupVertex (exceptionalChartIndex l))
        (originalExceptionalCurve hs u) at htrans
  rw [exceptionalDivisor_transition_ratio hs i l hi] at htrans
  rw [exceptionalDivisorCoordinate, exceptionalDivisorCoordinate,
    Trivialization.coe_linearMapAt_of_mem _ hiE, Trivialization.coe_linearMapAt_of_mem _ hlE]
  change toricNativeFrameCoefficient (originalExceptionalMetric hs)
      (blowupVertex (exceptionalChartIndex l)) (originalExceptionalCurve hs u) *
        (show ℂ from t) = _
  rw [← htrans]
  exact mul_assoc _ _ _

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalDivisorRestrictionDraft -/
end F1CanonicalFragment002

section F1CanonicalFragment003
/- BEGIN ExceptionalTautologicalVectorDraft; original source SHA256 5bea2308ecbb0b3b80c9b54435295d4274efc7ff9ad0c3b64c0a4f02487b2e45 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual normalized homogeneous lift in the genuine Euclidean two-dimensional model. -/
def exceptionalLiftModel (i : Fin 2) (u : SGPT.Projective.ComplexProjectiveSpace 1) : ComplexModel 2 :=
  modelPoint (SGPT.Projective.ComplexProjectiveSpace.affineLift i
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i u))

/-- The two genuine physical frame descriptions give the SAME actual tautological vector. -/
theorem exceptionalTautologicalVector_independent (i l : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (hl : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart l).source)
    (t : ExceptionalDivisorFiber hs u) :
    exceptionalDivisorCoordinate hs l u t • exceptionalLiftModel l u =
      exceptionalDivisorCoordinate hs i u t • exceptionalLiftModel i u := by
  rw [exceptionalDivisorCoordinate_transition hs i l hi hl t]
  have hli := exceptional_normalizedLift i hi
  have hll := exceptional_normalizedLift l hl
  have hni := (SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_source_iff i u).mp hi
  have hnl := (SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_source_iff l u).mp hl
  ext j
  simp only [PiLp.smul_apply, exceptionalLiftModel, modelPoint_apply]
  rw [hli, hll]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- A genuine linear map into the actual homogeneous line, with its preferred chart chosen internally. -/
def exceptionalTautologicalLinear (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    ExceptionalDivisorFiber hs u →ₗ[ℂ] ComplexModel 2 where
  toFun t := exceptionalDivisorCoordinate hs (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) u t •
    exceptionalLiftModel (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) u
  map_add' s t := by simp only [map_add, add_smul]
  map_smul' a t := by
    change exceptionalDivisorCoordinate hs (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) u (a • t) •
      exceptionalLiftModel (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) u = _
    rw [(exceptionalDivisorCoordinate hs (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) u).map_smul]
    exact smul_assoc _ _ _

/-- EVERY actual affine chart reads the SAME internally manufactured global linear map. -/
theorem exceptionalTautologicalLinear_local (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (t : ExceptionalDivisorFiber hs u) :
    exceptionalTautologicalLinear hs u t =
      exceptionalDivisorCoordinate hs i u t • exceptionalLiftModel i u :=
  exceptionalTautologicalVector_independent hs i
    (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) hi
    (SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u) t

/-- The actual homogeneous-line map is injective on every physical O(E)|E fibre. -/
theorem exceptionalTautologicalLinear_injective (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    Function.Injective (exceptionalTautologicalLinear hs u) := by
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex u
  have hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u
  intro s t heq
  rw [exceptionalTautologicalLinear_local hs i hi s,
    exceptionalTautologicalLinear_local hs i hi t] at heq
  have hcoeff := congrArg (fun v : ComplexModel 2 => v i) heq
  simp only [PiLp.smul_apply, exceptionalLiftModel, modelPoint_apply,
    SGPT.Projective.ComplexProjectiveSpace.affineLift_same, smul_eq_mul, mul_one] at hcoeff
  rw [exceptionalDivisorCoordinate, (exceptionalDivisorFrame hs i).linearMapAt_def_of_mem
    (exceptionalDivisorFrame_mem hs i hi)] at hcoeff
  exact ((exceptionalDivisorFrame hs i).linearEquivAt ℂ u
    (exceptionalDivisorFrame_mem hs i hi)).injective hcoeff

/-- The ambient actual total-space map into C². -/
def exceptionalTautologicalVector (x : TotalSpace ℂ (ExceptionalDivisorFiber hs)) : ComplexModel 2 :=
  exceptionalTautologicalLinear hs x.proj x.snd

/-- Actual frame coefficient holomorphy in the genuine restricted bundle topology. -/
theorem contMDiffAt_exceptionalDivisorCoordinate (i : Fin 2)
    {x : TotalSpace ℂ (ExceptionalDivisorFiber hs)}
    (hi : x.proj ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    ContMDiffAt ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ℂ) ∞
      (fun y : TotalSpace ℂ (ExceptionalDivisorFiber hs) =>
        exceptionalDivisorCoordinate hs i y.proj y.snd) x := by
  let e := exceptionalDivisorFrame hs i
  have hx : x ∈ e.source := e.mem_source.mpr (exceptionalDivisorFrame_mem hs i hi)
  have h := ((e.contMDiffOn (IB := 𝓘(ℂ, ComplexModel 1)) (n := ∞)).contMDiffAt
    (e.open_source.mem_nhds hx)).snd
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℂ) e (e.mem_source.mp hy)) y.snd

/-- Smoothness of each literal normalized homogeneous model lift. -/
theorem contDiff_exceptionalAffineLift (i : Fin 2) :
    ContDiff ℂ ∞ (fun z : ComplexModel 1 =>
      modelPoint (SGPT.Projective.ComplexProjectiveSpace.affineLift i z)) := by
  apply (contDiff_piLp 2).mpr
  intro j
  simpa only [modelPoint_apply] using
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
      (SGPT.Projective.ComplexProjectiveSpace.differentiable_affineLift_apply i j).differentiableOn
      isOpen_univ)

/-- Holomorphy of the actual normalized lift on its genuine projective affine open. -/
theorem contMDiffAt_exceptionalLiftModel (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞ (exceptionalLiftModel i) u := by
  exact (contDiff_exceptionalAffineLift i).contMDiff.contMDiffAt.comp u
    (SGPT.Projective.ComplexProjectiveSpace.contMDiffAt_affineChart i hi)

/-- A local tautological vector is an actual product of holomorphic native coordinates. -/
theorem contMDiffAt_exceptionalLocalVector (i : Fin 2)
    {x : TotalSpace ℂ (ExceptionalDivisorFiber hs)}
    (hi : x.proj ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    ContMDiffAt ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ComplexModel 2) ∞
      (fun y : TotalSpace ℂ (ExceptionalDivisorFiber hs) =>
        exceptionalDivisorCoordinate hs i y.proj y.snd • exceptionalLiftModel i y.proj) x := by
  have hproj : ContMDiffAt ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      𝓘(ℂ, ComplexModel 1) ∞
      (TotalSpace.proj : TotalSpace ℂ (ExceptionalDivisorFiber hs) →
        SGPT.Projective.ComplexProjectiveSpace 1) x := contMDiffAt_proj _
  have hl : ContMDiffAt ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ComplexModel 2) ∞
      (fun y : TotalSpace ℂ (ExceptionalDivisorFiber hs) => exceptionalLiftModel i y.proj) x :=
    (contMDiffAt_exceptionalLiftModel i hi).comp x hproj
  exact (contMDiffAt_exceptionalDivisorCoordinate hs i hi).smul hl

/-- Genuine global holomorphy of the manufactured tautological embedding into C². -/
theorem contMDiff_exceptionalTautologicalVector :
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ComplexModel 2) ∞
      (exceptionalTautologicalVector hs) := by
  intro x
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex x.proj
  have hi : x.proj ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex x.proj
  have hlocal := contMDiffAt_exceptionalLocalVector hs i hi
  have hU : IsOpen ((TotalSpace.proj : TotalSpace ℂ (ExceptionalDivisorFiber hs) →
      SGPT.Projective.ComplexProjectiveSpace 1) ⁻¹'
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :=
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source.preimage
      (FiberBundle.continuous_proj ℂ (ExceptionalDivisorFiber hs))
  have heq : exceptionalTautologicalVector hs =ᶠ[𝓝 x]
      (fun y : TotalSpace ℂ (ExceptionalDivisorFiber hs) =>
        exceptionalDivisorCoordinate hs i y.proj y.snd • exceptionalLiftModel i y.proj) := by
    filter_upwards [hU.mem_nhds hi] with y hy
    exact exceptionalTautologicalLinear_local hs i hy y.snd
  exact hlocal.congr_of_eventuallyEq heq

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalTautologicalVectorDraft -/
end F1CanonicalFragment003

section F1CanonicalFragment004
/- BEGIN ExceptionalTautologicalFiberDraft; original source SHA256 cd7e679b1b66a36b011c3141e98d0bda8c07dccaa34d67044532796e75eb44a6 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff BigOperators

/-- The actual independently specified tautological line over the original projective point. -/
def actualTautologicalLine (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    Submodule ℂ (ComplexModel 2) := Submodule.span ℂ {modelPoint u.rep}

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Literal value in the original homogeneous line, produced from the actual physical bundle. -/
theorem exceptionalTautologicalLinear_eq_rep (u : SGPT.Projective.ComplexProjectiveSpace 1)
    (t : ExceptionalDivisorFiber hs u) :
    exceptionalTautologicalLinear hs u t =
      (exceptionalDivisorCoordinate hs (SGPT.Projective.ComplexProjectiveSpace.chartIndex u) u t /
        u.rep (SGPT.Projective.ComplexProjectiveSpace.chartIndex u)) • modelPoint u.rep := by
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex u
  have hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u
  rw [exceptionalTautologicalLinear_local hs i hi]
  ext j
  simp only [PiLp.smul_apply, exceptionalLiftModel, modelPoint_apply]
  rw [exceptional_normalizedLift i hi]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]
  rfl

/-- Actual line membership; this is proved, not an incoming model-identification hypothesis. -/
theorem exceptionalTautologicalLinear_mem (u : SGPT.Projective.ComplexProjectiveSpace 1)
    (t : ExceptionalDivisorFiber hs u) :
    exceptionalTautologicalLinear hs u t ∈ actualTautologicalLine u := by
  rw [exceptionalTautologicalLinear_eq_rep]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton _))

/-- Actual full physical fibre map into the independent literal tautological line. -/
def exceptionalTautologicalToLine (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    ExceptionalDivisorFiber hs u →ₗ[ℂ] actualTautologicalLine u :=
  (exceptionalTautologicalLinear hs u).codRestrict _ (exceptionalTautologicalLinear_mem hs u)

theorem exceptionalTautologicalToLine_bijective (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    Function.Bijective (exceptionalTautologicalToLine hs u) := by
  constructor
  · intro s t heq
    exact exceptionalTautologicalLinear_injective hs u (congrArg Subtype.val heq)
  · intro v
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.property
    let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex u
    have hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
      SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u
    have hni := (SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_source_iff i u).mp hi
    let e := (exceptionalDivisorFrame hs i).linearEquivAt ℂ u (exceptionalDivisorFrame_mem hs i hi)
    refine ⟨e.symm (a * u.rep i), Subtype.ext ?_⟩
    change exceptionalTautologicalLinear hs u (e.symm (a * u.rep i)) = v.val
    rw [exceptionalTautologicalLinear_eq_rep]
    have hc : exceptionalDivisorCoordinate hs i u (e.symm (a * u.rep i)) = a * u.rep i := by
      rw [exceptionalDivisorCoordinate, (exceptionalDivisorFrame hs i).linearMapAt_def_of_mem
        (exceptionalDivisorFrame_mem hs i hi)]
      exact e.apply_symm_apply _
    change (exceptionalDivisorCoordinate hs i u (e.symm (a * u.rep i)) / u.rep i) • modelPoint u.rep = _
    rw [hc, mul_div_cancel_right₀ a hni]
    exact ha

/-- Genuine physical O(E)|E ≃ O_P1(-1) on EVERY actual fibre, with no supplied isomorphism. -/
def exceptionalTautologicalFiberEquiv (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    ExceptionalDivisorFiber hs u ≃ₗ[ℂ] actualTautologicalLine u :=
  LinearEquiv.ofBijective (exceptionalTautologicalToLine hs u) (exceptionalTautologicalToLine_bijective hs u)

/-- The actual inverse is the ordinary vector coordinate in EVERY genuine tautological affine chart. -/
theorem exceptionalTautologicalFiberEquiv_inverse_coordinate (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (v : actualTautologicalLine u) :
    exceptionalDivisorCoordinate hs i u ((exceptionalTautologicalFiberEquiv hs u).symm v) = v.val i := by
  have h := congrArg (fun w : actualTautologicalLine u => w.val i)
    ((exceptionalTautologicalFiberEquiv hs u).apply_symm_apply v)
  change exceptionalTautologicalLinear hs u ((exceptionalTautologicalFiberEquiv hs u).symm v) i = v.val i at h
  rw [exceptionalTautologicalLinear_local hs i hi] at h
  simpa only [PiLp.smul_apply, exceptionalLiftModel, modelPoint_apply,
    SGPT.Projective.ComplexProjectiveSpace.affineLift_same, smul_eq_mul, mul_one] using h

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalTautologicalFiberDraft -/
end F1CanonicalFragment004

section F1CanonicalFragment005
/- BEGIN ExceptionalTautologicalInverseDraft; original source SHA256 a10e47d8548314175d8bc537015dd04cacde86ed3d2979c4b5e58ba49080bbce -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Inverse of the actual fibre equivalence on the independent tautological incidence condition. -/
def exceptionalTautologicalInverseValue (u : SGPT.Projective.ComplexProjectiveSpace 1)
    (v : ComplexModel 2) (hv : v ∈ actualTautologicalLine u) : ExceptionalDivisorFiber hs u :=
  (exceptionalTautologicalFiberEquiv hs u).symm ⟨v, hv⟩

/-- Genuine inverse holomorphy: for every holomorphic map into the literal tautological
incidence, the manufactured inverse is holomorphic in the ORIGINAL native bundle atlas. -/
theorem contMDiff_exceptionalTautologicalInverse
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℂ EQ] [TopologicalSpace HQ]
    (IQ : ModelWithCorners ℂ EQ HQ) [TopologicalSpace Q] [ChartedSpace HQ Q]
    (f : Q → SGPT.Projective.ComplexProjectiveSpace 1) (v : Q → ComplexModel 2)
    (hv : ∀ y, v y ∈ actualTautologicalLine (f y))
    (hf : ContMDiff IQ 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hV : ContMDiff IQ 𝓘(ℂ, ComplexModel 2) ∞ v) :
    ContMDiff IQ ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y => (⟨f y, exceptionalTautologicalInverseValue hs (f y) (v y) (hv y)⟩ :
        TotalSpace ℂ (ExceptionalDivisorFiber hs))) := by
  intro x
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex (f x)
  let e := exceptionalDivisorFrame hs i
  let F := fun y => (⟨f y, exceptionalTautologicalInverseValue hs (f y) (v y) (hv y)⟩ :
    TotalSpace ℂ (ExceptionalDivisorFiber hs))
  have hi : f x ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex (f x)
  have hx : F x ∈ e.source := e.mem_source.mpr (exceptionalDivisorFrame_mem hs i hi)
  have hvi : ContMDiffAt IQ 𝓘(ℂ, ℂ) ∞ (fun y => v y i) x :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).contDiff.contMDiff.contMDiffAt).comp x (hV x)
  have hco : (fun y => (e (F y)).2) =ᶠ[𝓝 x] (fun y => v y i) := by
    have hU := (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source.preimage hf.continuous
    filter_upwards [hU.mem_nhds hi] with y hy
    have hE := exceptionalDivisorFrame_mem hs i hy
    have h := exceptionalTautologicalFiberEquiv_inverse_coordinate hs i hy ⟨v y, hv y⟩
    rw [exceptionalDivisorCoordinate, Trivialization.coe_linearMapAt_of_mem (R := ℂ) e hE] at h
    exact h
  exact (e.contMDiffAt_iff (f := F) (x₀ := x) hx).mpr
    ⟨hf x, hvi.congr_of_eventuallyEq hco⟩

/-- Independently specified ACTUAL tautological total space, with its subspace topology
inside the SAME original projective line times Euclidean C². -/
abbrev ActualTautologicalTotal :=
  {q : SGPT.Projective.ComplexProjectiveSpace 1 × ComplexModel 2 |
    q.2 ∈ actualTautologicalLine q.1}

/-- Forward map into the actual tautological incidence, not a renamed physical carrier. -/
def exceptionalTautologicalTotalMap (x : TotalSpace ℂ (ExceptionalDivisorFiber hs)) :
    ActualTautologicalTotal :=
  ⟨(x.proj, exceptionalTautologicalVector hs x), exceptionalTautologicalLinear_mem hs x.proj x.snd⟩

def exceptionalTautologicalTotalInv (q : ActualTautologicalTotal) :
    TotalSpace ℂ (ExceptionalDivisorFiber hs) :=
  ⟨q.val.1, exceptionalTautologicalInverseValue hs q.val.1 q.val.2 q.property⟩

theorem exceptionalTautologicalTotalMap_leftInverse :
    Function.LeftInverse (exceptionalTautologicalTotalInv hs) (exceptionalTautologicalTotalMap hs) := by
  intro x
  change (⟨x.proj, (exceptionalTautologicalFiberEquiv hs x.proj).symm
    (exceptionalTautologicalFiberEquiv hs x.proj x.snd)⟩ :
      TotalSpace ℂ (ExceptionalDivisorFiber hs)) = x
  rw [LinearEquiv.symm_apply_apply]

theorem exceptionalTautologicalTotalMap_rightInverse :
    Function.RightInverse (exceptionalTautologicalTotalInv hs) (exceptionalTautologicalTotalMap hs) := by
  intro q
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val ((exceptionalTautologicalFiberEquiv hs q.val.1).apply_symm_apply
      (⟨q.val.2, q.property⟩ : actualTautologicalLine q.val.1))

theorem continuous_exceptionalTautologicalTotalMap : Continuous (exceptionalTautologicalTotalMap hs) :=
  ((FiberBundle.continuous_proj ℂ (ExceptionalDivisorFiber hs)).prodMk
    (contMDiff_exceptionalTautologicalVector hs).continuous).subtype_mk _

/-- Local inverse frame coordinates prove continuity for the INDEPENDENT actual
subspace topology, without transporting a topology through our output map. -/
theorem continuous_exceptionalTautologicalTotalInv : Continuous (exceptionalTautologicalTotalInv hs) := by
  rw [continuous_iff_continuousAt]
  intro q
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex q.val.1
  let e := exceptionalDivisorFrame hs i
  have hi : q.val.1 ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex q.val.1
  have hbase : Continuous (fun y : ActualTautologicalTotal => y.val.1) := continuous_fst.comp continuous_subtype_val
  have hvec : Continuous (fun y : ActualTautologicalTotal => y.val.2 i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp (continuous_snd.comp continuous_subtype_val)
  have ht : (q.val.1, q.val.2 i) ∈ e.target :=
    e.mem_target.mpr (exceptionalDivisorFrame_mem hs i hi)
  have he : ContinuousAt e.toOpenPartialHomeomorph.symm (q.val.1, q.val.2 i) :=
    e.toOpenPartialHomeomorph.continuousOn_invFun.continuousAt (e.open_target.mem_nhds ht)
  have hc : ContinuousAt
      (fun y : ActualTautologicalTotal => e.toOpenPartialHomeomorph.symm (y.val.1, y.val.2 i)) q :=
    ContinuousAt.comp (f := fun y : ActualTautologicalTotal => (y.val.1, y.val.2 i))
      (x := q) he (hbase.prodMk hvec).continuousAt
  have hEq : exceptionalTautologicalTotalInv hs =ᶠ[𝓝 q]
      (fun y : ActualTautologicalTotal => e.toOpenPartialHomeomorph.symm (y.val.1, y.val.2 i)) := by
    have hU := (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source.preimage hbase
    filter_upwards [hU.mem_nhds hi] with y hy
    have hyE := exceptionalDivisorFrame_mem hs i hy
    have hyS : exceptionalTautologicalTotalInv hs y ∈ e.source := e.mem_source.mpr hyE
    have hcoeff := exceptionalTautologicalFiberEquiv_inverse_coordinate hs i hy
      (⟨y.val.2, y.property⟩ : actualTautologicalLine y.val.1)
    rw [exceptionalDivisorCoordinate, Trivialization.coe_linearMapAt_of_mem (R := ℂ) e hyE] at hcoeff
    have hread : e (exceptionalTautologicalTotalInv hs y) = (y.val.1, y.val.2 i) :=
      Prod.ext (e.proj_toFun _ hyS) hcoeff
    rw [← hread]
    exact (e.toOpenPartialHomeomorph.left_inv hyS).symm
  exact hc.congr_of_eventuallyEq hEq

/-- Actual topological bundle identification with the literal tautological subbundle;
forward holomorphy and holomorphic inverse-chart criterion are proved separately above. -/
def exceptionalTautologicalBundleHomeomorph : TotalSpace ℂ (ExceptionalDivisorFiber hs) ≃ₜ
    ActualTautologicalTotal where
  toFun := exceptionalTautologicalTotalMap hs
  invFun := exceptionalTautologicalTotalInv hs
  left_inv := exceptionalTautologicalTotalMap_leftInverse hs
  right_inv := exceptionalTautologicalTotalMap_rightInverse hs
  continuous_toFun := continuous_exceptionalTautologicalTotalMap hs
  continuous_invFun := continuous_exceptionalTautologicalTotalInv hs

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalTautologicalInverseDraft -/
end F1CanonicalFragment005

section F1CanonicalFragment006
/- BEGIN ExceptionalNegativeMetricDraft; original source SHA256 8a6388045986e5d83ddf7b95772144fa64113699f6fae8f49c9f1abb1dda143d -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open SGPT.PSH SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The genuine Euclidean tautological metric on the SAME physical O(E)|E fibre. -/
def exceptionalNegativeHermitianForm (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    HermitianForm (ExceptionalDivisorFiber hs u) where
  toSesq := ((innerₛₗ ℂ : ComplexModel 2 →ₗ⋆[ℂ] ComplexModel 2 →ₗ[ℂ] ℂ).compl₂
    (exceptionalTautologicalLinear hs u)).comp (exceptionalTautologicalLinear hs u)
  pos' v hv := by
    have hne : exceptionalTautologicalLinear hs u v ≠ 0 := by
      intro heq
      apply hv
      apply exceptionalTautologicalLinear_injective hs u
      simpa only [map_zero] using heq
    refine ⟨‖exceptionalTautologicalLinear hs u v‖ ^ 2, sq_pos_of_pos (norm_pos_iff.mpr hne), ?_⟩
    change inner ℂ (exceptionalTautologicalLinear hs u v) (exceptionalTautologicalLinear hs u v) = _
    simpa only [Complex.ofReal_pow] using!
      (inner_self_eq_norm_sq_to_K (exceptionalTautologicalLinear hs u v))

theorem exceptionalNegativeHermitianForm_normSq (u : SGPT.Projective.ComplexProjectiveSpace 1)
    (v : ExceptionalDivisorFiber hs u) :
    (exceptionalNegativeHermitianForm hs u).normSq v = ‖exceptionalTautologicalLinear hs u v‖ ^ 2 := by
  change (inner ℂ (exceptionalTautologicalLinear hs u v) (exceptionalTautologicalLinear hs u v)).re = _
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (exceptionalTautologicalLinear hs u v)

/-- Smoothness is verified for EVERY local holomorphic section of the actual native restriction. -/
def exceptionalNegativeHermitianMetric : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs) where
  form := exceptionalNegativeHermitianForm hs
  smooth := by
    intro s U hU hsU c z hz
    have hn (j : Fin 2) : ContDiffAt ℝ ∞
        (fun w => Complex.normSq (exceptionalTautologicalVector hs
          (⟨c.val.symm w, s (c.val.symm w)⟩ : TotalSpace ℂ (ExceptionalDivisorFiber hs)) j)) z := by
      let g : SGPT.Projective.ComplexProjectiveSpace 1 → ℂ :=
        fun u => exceptionalTautologicalVector hs (⟨u, s u⟩ : TotalSpace ℂ (ExceptionalDivisorFiber hs)) j
      have hF : MDifferentiable ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ℂ)
          (fun y : TotalSpace ℂ (ExceptionalDivisorFiber hs) => exceptionalTautologicalVector hs y j) :=
        (((EuclideanSpace.proj (𝕜 := ℂ) j).contDiff.contMDiff).comp
          (contMDiff_exceptionalTautologicalVector hs)).mdifferentiable (by simp)
      have hg : MDifferentiableOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) g U := by
        intro u hu
        exact (hF (⟨u, s u⟩ : TotalSpace ℂ (ExceptionalDivisorFiber hs))).comp_mdifferentiableWithinAt u
          (hsU u hu)
      apply SGPT.Foundations.Analysis.Pending.BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [(c.val.isOpen_inter_preimage_symm hU).mem_nhds hz] with w hw
      exact differentiableAt_comp_chart_symm c hw.1 ((hg _ hw.2).mdifferentiableAt (hU.mem_nhds hw.2))
    simp only [exceptionalNegativeHermitianForm_normSq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    have h0 := hn 0
    have h1 := hn 1
    simp only [Complex.normSq_eq_norm_sq, exceptionalTautologicalVector] at h0 h1
    exact (h0.add h1).contDiffWithinAt

/-- The SAME actual physical frame is sent to the literal normalized homogeneous vector. -/
theorem exceptionalTautological_frame (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    exceptionalTautologicalLinear hs u ((exceptionalDivisorFrame hs i).symm u 1) = exceptionalLiftModel i u := by
  rw [exceptionalTautologicalLinear_local hs i hi]
  have hc : exceptionalDivisorCoordinate hs i u ((exceptionalDivisorFrame hs i).symm u 1) = 1 := by
    rw [exceptionalDivisorCoordinate,
      Trivialization.coe_linearMapAt_of_mem _ (exceptionalDivisorFrame_mem hs i hi)]
    exact congrArg Prod.snd ((exceptionalDivisorFrame hs i).apply_mk_symm
      (exceptionalDivisorFrame_mem hs i hi) 1)
  rw [hc, one_smul]

/-- The actual O(E)|E frame has norm squared 1+|z|² on BOTH original exceptional charts. -/
theorem exceptionalNegative_frame_normSq (i : Fin 2) (z : ComplexModel 1) :
    (exceptionalNegativeHermitianForm hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint i z)).normSq
      ((exceptionalDivisorFrame hs i).symm (SGPT.Projective.ComplexProjectiveSpace.affinePoint i z) 1) =
      1 + Complex.normSq (z 0) := by
  rw [exceptionalNegativeHermitianForm_normSq, exceptionalTautological_frame hs i
    (SGPT.Projective.ComplexProjectiveSpace.affinePoint_mem_source i z)]
  simp only [exceptionalLiftModel, SGPT.Projective.ComplexProjectiveSpace.affineChart_affinePoint]
  change ‖(WithLp.toLp 2 (SGPT.Projective.ComplexProjectiveSpace.affineLift i z) : ComplexModel 2)‖ ^ 2 = _
  rw [← SGPT.Projective.ComplexProjectiveSpace.homNormSq_eq_norm_sq,
    SGPT.Projective.ComplexProjectiveSpace.homNormSq_affineLift]
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Complex.normSq_eq_norm_sq]

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalNegativeMetricDraft -/
end F1CanonicalFragment006

section F1CanonicalFragment007
/- BEGIN ExceptionalNegativeChernDraft; original source SHA256 f7ae7aa177c571e8baac313f294c0fd7685ac869548bda18443906ed1b25597f -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open SGPT.PSH SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual original frame on each genuine exceptional affine chart. -/
def exceptionalNegativeFrame (i : Fin 2) :
    (u : SGPT.Projective.ComplexProjectiveSpace 1) → ExceptionalDivisorFiber hs u :=
  fun u => (exceptionalDivisorFrame hs i).symm u 1

theorem exceptionalNegativeFrame_coordinate (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hu : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    exceptionalDivisorCoordinate hs i u (exceptionalNegativeFrame hs i u) = 1 := by
  rw [exceptionalDivisorCoordinate,
    Trivialization.coe_linearMapAt_of_mem _ (exceptionalDivisorFrame_mem hs i hu)]
  exact congrArg Prod.snd ((exceptionalDivisorFrame hs i).apply_mk_symm
    (exceptionalDivisorFrame_mem hs i hu) 1)

/-- Holomorphy is in the actual native restricted bundle, on the entire genuine affine open. -/
theorem exceptionalNegativeFrame_holomorphic (i : Fin 2) :
    IsHolomorphicSectionOn (n := 1) (ExceptionalDivisorFiber hs) (exceptionalNegativeFrame hs i)
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source := by
  let e := exceptionalDivisorFrame hs i
  rw [IsHolomorphicSectionOn, e.mdifferentiableOn_section_iff
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source
    (fun u hu => exceptionalDivisorFrame_mem hs i hu)]
  apply (mdifferentiableOn_const (c := (1 : ℂ))).congr
  intro u hu
  exact congrArg Prod.snd (e.apply_mk_symm (exceptionalDivisorFrame_mem hs i hu) 1)

theorem exceptionalNegativeFrame_ne_zero (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hu : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    exceptionalNegativeFrame hs i u ≠ 0 := by
  intro heq
  have h := exceptionalNegativeFrame_coordinate hs i hu
  rw [heq, map_zero] at h
  exact zero_ne_one h

/-- The genuine standard affine chart as a native complex chart on the SAME source P1. -/
def exceptionalProjectiveChart (i : Fin 2) :
    ComplexChart 1 (SGPT.Projective.ComplexProjectiveSpace 1) :=
  ⟨SGPT.Projective.ComplexProjectiveSpace.affineChart i,
    SGPT.Projective.ComplexProjectiveSpace.affineChart_mem_atlas i⟩

/-- The ACTUAL negative Chern weight, from the actual physical frame norm. -/
theorem exceptionalNegativeFrame_localWeight (i : Fin 2) :
    localWeight (exceptionalNegativeHermitianMetric hs) (exceptionalNegativeFrame hs i)
      (exceptionalProjectiveChart i) =
      fun z => -SGPT.Projective.ComplexProjectiveSpace.fsPotential z := by
  funext z
  change -Real.log ((exceptionalNegativeHermitianForm hs
    (SGPT.Projective.ComplexProjectiveSpace.affinePoint i z)).normSq
      ((exceptionalDivisorFrame hs i).symm (SGPT.Projective.ComplexProjectiveSpace.affinePoint i z) 1)) = _
  rw [exceptionalNegative_frame_normSq]
  simp only [SGPT.Projective.ComplexProjectiveSpace.fsPotential, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_one, Complex.normSq_eq_norm_sq]

/-- The actual Chern coefficient is the negative FS coefficient on BOTH whole exceptional charts. -/
theorem exceptionalNegative_firstChern_coeff (i : Fin 2) (z : ComplexModel 1) :
    (firstChernForm (exceptionalNegativeHermitianMetric hs)).val.coeff (exceptionalProjectiveChart i) z =
      -smoothDDC (SGPT.Projective.ComplexProjectiveSpace.fsPotential (N := 1)) z := by
  have hz : z ∈ (exceptionalProjectiveChart i).val.target := by
    exact mem_univ _
  have hU : (exceptionalProjectiveChart i).val.symm z ∈
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.affinePoint_mem_source i z
  have hc := isFirstChernForm_firstChernForm (exceptionalNegativeHermitianMetric hs)
    (exceptionalNegativeFrame hs i) (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source
    (exceptionalNegativeFrame_holomorphic hs i)
    (fun u hu => exceptionalNegativeFrame_ne_zero hs i hu) (exceptionalProjectiveChart i) z hz hU
  rw [exceptionalNegativeFrame_localWeight] at hc
  exact hc.trans (smoothDDC_neg isOpen_univ
    SGPT.Projective.ComplexProjectiveSpace.contDiff_fsPotential.contDiffOn (mem_univ z))

/-- Genuine geometric equality of the SAME physical E restriction's Chern form with -omega_FS. -/
theorem exceptionalNegative_firstChern_geometrically :
    (firstChernForm (exceptionalNegativeHermitianMetric hs)).val.GeometricallyEq
      (-SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1)).val := by
  intro c z hz
  obtain ⟨i, hi⟩ := (SGPT.Projective.ComplexProjectiveSpace.mem_atlas_iff c.val).mp c.property
  have hci : c = exceptionalProjectiveChart i := Subtype.ext hi
  subst c
  rw [ClosedRealOneOneForm.coeff_neg]
  change (firstChernForm (exceptionalNegativeHermitianMetric hs)).val.coeff
    (exceptionalProjectiveChart i) z = -smoothDDC (SGPT.Projective.ComplexProjectiveSpace.fsPotential (N := 1)) z
  exact exceptionalNegative_firstChern_coeff hs i z

/-- Every smooth metric on the SAME actual O(E)|E has the actual negative FS first Chern CLASS. -/
theorem exceptionalDivisor_firstChernClass
    (h : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs)) :
    RealBottChern.ofRepresentative (firstChernForm h) =
      RealBottChern.ofRepresentative (-SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1)) := by
  calc
    _ = RealBottChern.ofRepresentative (firstChernForm (exceptionalNegativeHermitianMetric hs)) :=
      firstChernClass_eq h (exceptionalNegativeHermitianMetric hs)
    _ = _ := RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (exceptionalNegative_firstChern_geometrically hs)

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalNegativeChernDraft -/
end F1CanonicalFragment007

section F1CanonicalFragment008
/- BEGIN ExceptionalCurveChernIntegralDraft; original source SHA256 e55af4d233d548a4d1b91ea5cf5e84aaf4e2a13e02943b248da7f01fae832086 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open SGPT.PSH SGPT.PSH.LineBundleMetric
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Genuine curve degree of the SAME original E restriction: the existing native
first-Chern-class integral of its actual smooth Hermitian metric. -/
def exceptionalDivisorCurveDegree
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (h : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs)) : ℝ :=
  classSlotIntegral κ (fun _ : Fin 1 => RealBottChern.ofRepresentative (firstChernForm h))

/-- Actual signed first-Chern integration, for every metric and integration background.
No assigned degree or FS normalization is an incoming hypothesis. -/
theorem exceptionalDivisorCurveDegree_eq_neg_FS
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (h : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs)) :
    exceptionalDivisorCurveDegree hs κ h =
      -classSlotIntegral κ (fun _ : Fin 1 =>
        RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))) := by
  unfold exceptionalDivisorCurveDegree
  simp_rw [exceptionalDivisor_firstChernClass hs h]
  rw [classSlotIntegral_ofRepresentative, classSlotIntegral_ofRepresentative]
  have hneg := slotIntegral_update_smul κ
    (fun _ : Fin 1 => SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))
    (0 : Fin 1) (-1)
    (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))
  simp only [neg_one_smul] at hneg
  have heq : Function.update
      (fun _ : Fin 1 => SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))
      (0 : Fin 1) (-SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1)) =
      fun _ : Fin 1 => -SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1) := by
    funext i
    fin_cases i
    simp
  rw [heq, Function.update_eq_self] at hneg
  exact hneg

/-- A source-only genuine E Chern integral, with the actual negative metric and
actual CP1 integration background manufactured internally. -/
def sourceExceptionalDivisorDegree : ℝ :=
  exceptionalDivisorCurveDegree blowup_edgeSmooth
    (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1))
    (exceptionalNegativeHermitianMetric blowup_edgeSmooth)

theorem sourceExceptionalDivisorDegree_readback :
    sourceExceptionalDivisorDegree =
      -classSlotIntegral (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1))
        (fun _ : Fin 1 =>
          RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))) :=
  exceptionalDivisorCurveDegree_eq_neg_FS _ _ _

end SGPT.Toric.F1IntersectionDraft

end
/- END ExceptionalCurveChernIntegralDraft -/
end F1CanonicalFragment008


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"
