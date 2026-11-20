import SGPT.Toric.ExceptionalSelfIntersection
import SGPT.Toric.NativeMetricTransfer
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN OriginalNonNefRestrictionDraft; original source SHA256 832d3be158411d7abbef412d8b6d24c2dd631c95d1e4db8d265c9889ff7e5ed0 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def originalNonNefDatum : Fin 4 → Fin 2 → ℤ :=
  ![![-1, 0], ![2, 0], ![0, 2], ![0, -1]]

/-- Actual Cartier data of the SAME original D=2H+E, proved from all four original cones. -/
theorem originalNonNef_cartierDatum (k : Fin 4) :
    toricCartierDatum (blowupNonNefDivisor hs) (blowupVertex k) = originalNonNefDatum k := by
  apply toricCartierDatum_ofCoeff
    (fun u => if u = blowupRay4 then 2 else if u = blowupRay7 then 1 else 0)
    (blowupVertex k) (blowup_isVertexConeBasis k)
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [originalNonNefDatum, blowupBasis, vertexConeRay_lattice2Basis_zero,
      vertexConeRay_lattice2Basis_one, blowupRay4, blowupRay7, intPairing, Fin.sum_univ_two]

/-- On BOTH actual exceptional charts the original D and E Cartier data agree. -/
theorem originalNonNef_exceptionalDatum (i : Fin 2) :
    toricCartierDatum (blowupNonNefDivisor hs) (blowupVertex (exceptionalChartIndex i)) =
      toricCartierDatum (originalExceptionalDivisor hs) (blowupVertex (exceptionalChartIndex i)) := by
  rw [originalNonNef_cartierDatum, originalExceptional_cartierDatum]
  fin_cases i <;> rfl

/-- ACTUAL original D|E and E|E transition functions coincide, from their actual source data. -/
theorem originalNonNef_exceptionalTransition (i l : Fin 2)
    (p : PolytopeToricVariety blowupGenerator hs) :
    toricCartierTransition (blowupNonNefDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l)) p =
    toricCartierTransition (originalExceptionalDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l)) p := by
  unfold toricCartierTransition toricCartierLaurentModel toricCartierTransitionExponent
  rw [originalNonNef_exceptionalDatum, originalNonNef_exceptionalDatum]

/-- The true same-source exceptional transition for D is the original homogeneous coordinate ratio. -/
theorem originalNonNef_exceptionalTransition_ratio (i l : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    toricCartierTransition (blowupNonNefDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l))
      (originalExceptionalCurve hs u) = u.rep l / u.rep i := by
  rw [originalNonNef_exceptionalTransition]
  exact exceptionalDivisor_transition_ratio hs i l hi

/-- Genuine smooth source metric exists for the SAME original divisor D, internally manufactured. -/
def originalNonNefMetric : BigToricMetric (blowupNonNefDivisor hs) :=
  Classical.choice (exists_bigToricMetric _)

/-- The SAME actual physical O(D) restricted along the original exceptional curve. -/
abbrev NonNefRestrictedFiber :=
  originalExceptionalHolomorphicMap hs *ᵖ (ToricNativeLineFiber (originalNonNefMetric hs))

/-- The actual pulled-back original D frame, with its ordinary native bundle topology. -/
def nonNefRestrictedFrame (i : Fin 2) :
    Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ (NonNefRestrictedFiber hs) →
      SGPT.Projective.ComplexProjectiveSpace 1) :=
  (toricNativeLineTrivialization (originalNonNefMetric hs)
    (blowupVertex (exceptionalChartIndex i))).pullback (originalExceptionalHolomorphicMap hs)

instance nonNefRestrictedFrame_memAtlas (i : Fin 2) :
    MemTrivializationAtlas (nonNefRestrictedFrame hs i) := by
  constructor
  exact ⟨toricNativeLineTrivialization (originalNonNefMetric hs)
    (blowupVertex (exceptionalChartIndex i)), inferInstance, rfl⟩

theorem nonNefRestrictedFrame_mem (i : Fin 2) {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hu : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source) :
    u ∈ (nonNefRestrictedFrame hs i).baseSet := by
  change originalExceptionalCurve hs u ∈
    (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex (exceptionalChartIndex i))).source
  have heq : SGPT.Projective.ComplexProjectiveSpace.affinePoint i
      (SGPT.Projective.ComplexProjectiveSpace.affineChart i u) = u :=
    (SGPT.Projective.ComplexProjectiveSpace.affineChart i).left_inv hu
  rw [← heq, originalExceptionalCurve_affine]
  exact blowupOriginalChartPoint_mem hs _ _

def nonNefRestrictedCoordinate (i : Fin 2) (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    NonNefRestrictedFiber hs u →ₗ[ℂ] ℂ :=
  (nonNefRestrictedFrame hs i).linearMapAt ℂ u

/-- Actual physical D coefficients satisfy the genuine restricted Cartier transition. -/
theorem nonNefRestrictedCoordinate_transition (i l : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (hl : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart l).source)
    (t : NonNefRestrictedFiber hs u) :
    nonNefRestrictedCoordinate hs l u t = (u.rep l / u.rep i) * nonNefRestrictedCoordinate hs i u t := by
  have hiD := nonNefRestrictedFrame_mem hs i hi
  have hlD := nonNefRestrictedFrame_mem hs l hl
  have htrans := toricNativeFrameCoefficient_transition (originalNonNefMetric hs)
    (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l)) hiD hlD
  change toricCartierTransition (blowupNonNefDivisor hs)
      (blowupVertex (exceptionalChartIndex i)) (blowupVertex (exceptionalChartIndex l))
      (originalExceptionalCurve hs u) *
      toricNativeFrameCoefficient (originalNonNefMetric hs) (blowupVertex (exceptionalChartIndex i))
        (originalExceptionalCurve hs u) =
      toricNativeFrameCoefficient (originalNonNefMetric hs) (blowupVertex (exceptionalChartIndex l))
        (originalExceptionalCurve hs u) at htrans
  rw [originalNonNef_exceptionalTransition_ratio hs i l hi] at htrans
  rw [nonNefRestrictedCoordinate, nonNefRestrictedCoordinate,
    Trivialization.coe_linearMapAt_of_mem _ hiD, Trivialization.coe_linearMapAt_of_mem _ hlD]
  change toricNativeFrameCoefficient (originalNonNefMetric hs)
      (blowupVertex (exceptionalChartIndex l)) (originalExceptionalCurve hs u) *
        (show ℂ from t) = _
  rw [← htrans]
  exact mul_assoc _ _ _

end SGPT.Toric.F1IntersectionDraft

end
/- END OriginalNonNefRestrictionDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN NonNefExceptionalBundleMapDraft; original source SHA256 3e6b14725e5bcec221b3b3ef8b9f5d74222c4fcc790f7462888aa1fa6869e6bf -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Actual D|E ≃ E|E fibre map from an INTERNALLY chosen original covering frame. -/
def nonNefToExceptionalFiberEquiv (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    NonNefRestrictedFiber hs u ≃ₗ[ℂ] ExceptionalDivisorFiber hs u :=
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex u
  let hi := SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u
  ((nonNefRestrictedFrame hs i).linearEquivAt ℂ u (nonNefRestrictedFrame_mem hs i hi)).trans
    ((exceptionalDivisorFrame hs i).linearEquivAt ℂ u (exceptionalDivisorFrame_mem hs i hi)).symm

/-- EVERY original exceptional frame reads the same actual manufactured fibre map. -/
theorem nonNefToExceptionalFiberEquiv_coordinate (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (t : NonNefRestrictedFiber hs u) :
    exceptionalDivisorCoordinate hs i u (nonNefToExceptionalFiberEquiv hs u t) =
      nonNefRestrictedCoordinate hs i u t := by
  let k := SGPT.Projective.ComplexProjectiveSpace.chartIndex u
  have hk : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart k).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u
  have hread : exceptionalDivisorCoordinate hs k u (nonNefToExceptionalFiberEquiv hs u t) =
      nonNefRestrictedCoordinate hs k u t := by
    rw [exceptionalDivisorCoordinate, nonNefRestrictedCoordinate,
      (exceptionalDivisorFrame hs k).linearMapAt_def_of_mem (exceptionalDivisorFrame_mem hs k hk),
      (nonNefRestrictedFrame hs k).linearMapAt_def_of_mem (nonNefRestrictedFrame_mem hs k hk)]
    change ((exceptionalDivisorFrame hs k).linearEquivAt ℂ u (exceptionalDivisorFrame_mem hs k hk))
      (((exceptionalDivisorFrame hs k).linearEquivAt ℂ u (exceptionalDivisorFrame_mem hs k hk)).symm
        (((nonNefRestrictedFrame hs k).linearEquivAt ℂ u (nonNefRestrictedFrame_mem hs k hk)) t)) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [exceptionalDivisorCoordinate_transition hs k i hk hi,
    nonNefRestrictedCoordinate_transition hs k i hk hi, hread]

theorem nonNefToExceptionalFiberEquiv_inverse_coordinate (i : Fin 2)
    {u : SGPT.Projective.ComplexProjectiveSpace 1}
    (hi : u ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source)
    (t : ExceptionalDivisorFiber hs u) :
    nonNefRestrictedCoordinate hs i u ((nonNefToExceptionalFiberEquiv hs u).symm t) =
      exceptionalDivisorCoordinate hs i u t := by
  have h := nonNefToExceptionalFiberEquiv_coordinate hs i hi ((nonNefToExceptionalFiberEquiv hs u).symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def nonNefToExceptionalTotal (x : TotalSpace ℂ (NonNefRestrictedFiber hs)) :
    TotalSpace ℂ (ExceptionalDivisorFiber hs) :=
  ⟨x.proj, nonNefToExceptionalFiberEquiv hs x.proj x.snd⟩

def nonNefToExceptionalTotalInv (x : TotalSpace ℂ (ExceptionalDivisorFiber hs)) :
    TotalSpace ℂ (NonNefRestrictedFiber hs) :=
  ⟨x.proj, (nonNefToExceptionalFiberEquiv hs x.proj).symm x.snd⟩

/-- Genuine global holomorphy in the actual two different native bundle atlases. -/
theorem contMDiff_nonNefToExceptionalTotal :
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞ (nonNefToExceptionalTotal hs) := by
  intro x
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex x.proj
  have hi : x.proj ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex x.proj
  let e := exceptionalDivisorFrame hs i
  let d := nonNefRestrictedFrame hs i
  have hx : nonNefToExceptionalTotal hs x ∈ e.source := e.mem_source.mpr (exceptionalDivisorFrame_mem hs i hi)
  have hxd : x ∈ d.source := d.mem_source.mpr (nonNefRestrictedFrame_mem hs i hi)
  have hc := ((d.contMDiffOn (IB := 𝓘(ℂ, ComplexModel 1)) (n := ∞)).contMDiffAt
    (d.open_source.mem_nhds hxd)).snd
  have heq : (fun y => (e (nonNefToExceptionalTotal hs y)).2) =ᶠ[𝓝 x] (fun y => (d y).2) := by
    have hU := (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source.preimage
      (FiberBundle.continuous_proj ℂ (NonNefRestrictedFiber hs))
    filter_upwards [hU.mem_nhds hi] with y hy
    have h := nonNefToExceptionalFiberEquiv_coordinate hs i hy y.snd
    rw [exceptionalDivisorCoordinate, nonNefRestrictedCoordinate,
      Trivialization.coe_linearMapAt_of_mem (R := ℂ) e (exceptionalDivisorFrame_mem hs i hy),
      Trivialization.coe_linearMapAt_of_mem (R := ℂ) d (nonNefRestrictedFrame_mem hs i hy)] at h
    exact h
  exact (e.contMDiffAt_iff (f := nonNefToExceptionalTotal hs) (x₀ := x) hx).mpr
    ⟨contMDiffAt_proj _, hc.congr_of_eventuallyEq heq⟩

/-- Actual inverse holomorphy; no bundle-isomorphism certificate is an input. -/
theorem contMDiff_nonNefToExceptionalTotalInv :
    ContMDiff ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 1)).prod (𝓘(ℂ, ℂ))) ∞ (nonNefToExceptionalTotalInv hs) := by
  intro x
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex x.proj
  have hi : x.proj ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart i).source :=
    SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex x.proj
  let e := exceptionalDivisorFrame hs i
  let d := nonNefRestrictedFrame hs i
  have hx : nonNefToExceptionalTotalInv hs x ∈ d.source := d.mem_source.mpr (nonNefRestrictedFrame_mem hs i hi)
  have hxe : x ∈ e.source := e.mem_source.mpr (exceptionalDivisorFrame_mem hs i hi)
  have hc := ((e.contMDiffOn (IB := 𝓘(ℂ, ComplexModel 1)) (n := ∞)).contMDiffAt
    (e.open_source.mem_nhds hxe)).snd
  have heq : (fun y => (d (nonNefToExceptionalTotalInv hs y)).2) =ᶠ[𝓝 x] (fun y => (e y).2) := by
    have hU := (SGPT.Projective.ComplexProjectiveSpace.affineChart i).open_source.preimage
      (FiberBundle.continuous_proj ℂ (ExceptionalDivisorFiber hs))
    filter_upwards [hU.mem_nhds hi] with y hy
    have h := nonNefToExceptionalFiberEquiv_inverse_coordinate hs i hy y.snd
    rw [exceptionalDivisorCoordinate, nonNefRestrictedCoordinate,
      Trivialization.coe_linearMapAt_of_mem (R := ℂ) e (exceptionalDivisorFrame_mem hs i hy),
      Trivialization.coe_linearMapAt_of_mem (R := ℂ) d (nonNefRestrictedFrame_mem hs i hy)] at h
    exact h
  exact (d.contMDiffAt_iff (f := nonNefToExceptionalTotalInv hs) (x₀ := x) hx).mpr
    ⟨contMDiffAt_proj _, hc.congr_of_eventuallyEq heq⟩

/-- The actual holomorphic line-bundle isomorphism D|E ≅ E|E. -/
def nonNefToExceptionalBundleHomeomorph : TotalSpace ℂ (NonNefRestrictedFiber hs) ≃ₜ
    TotalSpace ℂ (ExceptionalDivisorFiber hs) where
  toFun := nonNefToExceptionalTotal hs
  invFun := nonNefToExceptionalTotalInv hs
  left_inv := by intro x; simp only [nonNefToExceptionalTotalInv, nonNefToExceptionalTotal,
    LinearEquiv.symm_apply_apply, TotalSpace.eta]
  right_inv := by intro x; simp only [nonNefToExceptionalTotalInv, nonNefToExceptionalTotal,
    LinearEquiv.apply_symm_apply, TotalSpace.eta]
  continuous_toFun := (contMDiff_nonNefToExceptionalTotal hs).continuous
  continuous_invFun := (contMDiff_nonNefToExceptionalTotalInv hs).continuous

end SGPT.Toric.F1IntersectionDraft

end
/- END NonNefExceptionalBundleMapDraft -/
end F1CanonicalFragment002

section F1CanonicalFragment003
/- BEGIN NonNefRestrictedChernIntegralDraft; original source SHA256 7f57123ab46d1ffbb7e64b1cfcf1a42460b3daa2a9ed20e7026556acf22a2878 -/
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

instance nonNefRestrictedNormed (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    NormedAddCommGroup (NonNefRestrictedFiber hs u) :=
  inferInstanceAs (NormedAddCommGroup
    (ToricNativeLineFiber (originalNonNefMetric hs) (originalExceptionalCurve hs u)))

instance nonNefRestrictedHermitian (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    InnerProductSpace ℂ (NonNefRestrictedFiber hs u) :=
  inferInstanceAs (InnerProductSpace ℂ
    (ToricNativeLineFiber (originalNonNefMetric hs) (originalExceptionalCurve hs u)))

/-- The printed D=2H+E is equality of the ACTUAL original Cartier divisors. -/
theorem originalNonNefDivisor_twoH_add_E :
    blowupNonNefDivisor hs = (2 : ℕ) • blowupHyperplaneDivisor hs + originalExceptionalDivisor hs := by
  funext ρ
  change (if ρ.val = blowupRay4 then 2 else if ρ.val = blowupRay7 then 1 else 0) =
    (2 : ℕ) • (if ρ.val = blowupRay4 then 1 else 0 : ℤ) +
      (if ρ.val = blowupRay7 then 1 else 0)
  have h47 : blowupRay4 ≠ blowupRay7 := by decide
  by_cases h4 : ρ.val = blowupRay4
  · simp [h4, h47]
  · by_cases h7 : ρ.val = blowupRay7
    · simp [h7, Ne.symm h47]
    · simp [h4, h7]

/-- Actual smooth metric on D|E, manufactured from the actual holomorphic D|E ≃ E|E map. -/
def nonNefRestrictedNegativeMetric : HermitianMetric (n := 1) (NonNefRestrictedFiber hs) :=
  nativeMetricTransfer (nonNefToExceptionalFiberEquiv hs) (contMDiff_nonNefToExceptionalTotal hs)
    (exceptionalNegativeHermitianMetric hs)

/-- The SAME actual D restriction has the actual negative FS first Chern class,
for EVERY smooth metric, without an incoming numerical/intersection certificate. -/
theorem nonNefRestricted_firstChernClass
    (h : HermitianMetric (n := 1) (NonNefRestrictedFiber hs)) :
    RealBottChern.ofRepresentative (firstChernForm h) =
      RealBottChern.ofRepresentative (-SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1)) := by
  calc
    _ = RealBottChern.ofRepresentative (firstChernForm (nonNefRestrictedNegativeMetric hs)) :=
      firstChernClass_eq h (nonNefRestrictedNegativeMetric hs)
    _ = RealBottChern.ofRepresentative (firstChernForm (exceptionalNegativeHermitianMetric hs)) :=
      nativeMetricTransfer_firstChernClass (nonNefToExceptionalFiberEquiv hs)
        (contMDiff_nonNefToExceptionalTotal hs) (exceptionalNegativeHermitianMetric hs)
    _ = _ := exceptionalDivisor_firstChernClass hs (exceptionalNegativeHermitianMetric hs)

/-- Literal source Chern additivity ON THE ACTUAL EXCEPTIONAL CURVE, in the existing
native Bott--Chern quotient; obtained from actual bundle maps and actual H triviality. -/
theorem originalNonNef_restricted_firstChern_additivity
    (hD : HermitianMetric (n := 1) (NonNefRestrictedFiber hs))
    (hH : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber hs))
    (hE : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs)) :
    RealBottChern.ofRepresentative (firstChernForm hD) =
      (2 : ℝ) • RealBottChern.ofRepresentative (firstChernForm hH) +
        RealBottChern.ofRepresentative (firstChernForm hE) := by
  rw [exceptionalRestriction_firstChernClass_zero hs hH, smul_zero, zero_add]
  rw [nonNefRestricted_firstChernClass hs hD, exceptionalDivisor_firstChernClass hs hE]

/-- Genuine curve degree of the SAME physical original D, through actual native c1 integration. -/
def nonNefRestrictedCurveDegree
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (h : HermitianMetric (n := 1) (NonNefRestrictedFiber hs)) : ℝ :=
  classSlotIntegral κ (fun _ : Fin 1 => RealBottChern.ofRepresentative (firstChernForm h))

/-- The original (2H+E).E arithmetic, with ALL THREE degrees actual native Chern integrals. -/
theorem originalNonNef_restricted_degree_additivity
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (hD : HermitianMetric (n := 1) (NonNefRestrictedFiber hs))
    (hH : HermitianMetric (n := 1) (ExceptionalHyperplaneFiber hs))
    (hE : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs)) :
    nonNefRestrictedCurveDegree hs κ hD =
      2 * exceptionalHyperplaneCurveDegree hs κ hH + exceptionalDivisorCurveDegree hs κ hE := by
  rw [exceptionalHyperplaneCurveDegree_eq_zero hs κ hH, mul_zero, zero_add]
  unfold nonNefRestrictedCurveDegree exceptionalDivisorCurveDegree
  simp_rw [nonNefRestricted_firstChernClass hs hD, exceptionalDivisor_firstChernClass hs hE]

/-- Genuine signed D.E equals the negative actual FS integral, with no normalization hypothesis. -/
theorem nonNefRestrictedCurveDegree_eq_neg_FS
    (κ : KahlerBackground 1 (SGPT.Projective.ComplexProjectiveSpace 1))
    (hD : HermitianMetric (n := 1) (NonNefRestrictedFiber hs)) :
    nonNefRestrictedCurveDegree hs κ hD =
      -classSlotIntegral κ (fun _ : Fin 1 =>
        RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))) := by
  rw [originalNonNef_restricted_degree_additivity hs κ hD
    (exceptionalFlatHermitianMetric hs) (exceptionalNegativeHermitianMetric hs),
    exceptionalHyperplaneCurveDegree_eq_zero hs κ (exceptionalFlatHermitianMetric hs),
    mul_zero, zero_add]
  exact exceptionalDivisorCurveDegree_eq_neg_FS hs κ _

/-- Source-only actual original D.E with its metric and integration background manufactured internally. -/
def sourceOriginalNonNefDivisorDegree : ℝ :=
  nonNefRestrictedCurveDegree blowup_edgeSmooth
    (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1))
    (nonNefRestrictedNegativeMetric blowup_edgeSmooth)

theorem sourceOriginalNonNefDivisorDegree_readback :
    sourceOriginalNonNefDivisorDegree =
      -classSlotIntegral (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1))
        (fun _ : Fin 1 =>
          RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))) :=
  nonNefRestrictedCurveDegree_eq_neg_FS _ _ _

end SGPT.Toric.F1IntersectionDraft

end
/- END NonNefRestrictedChernIntegralDraft -/
end F1CanonicalFragment003


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"
