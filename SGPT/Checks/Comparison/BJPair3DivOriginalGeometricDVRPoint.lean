import SGPT.Checks.Comparison.BJPair3DivOriginalPrimeDivisorFieldPullback
import SGPT.Checks.Comparison.BJPair3DivNativeDVRScale

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/OriginalGeometricDVRPoint.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # Actual geometric DVR scales are literal original divisorial points
The whole generic triangle, canonical residue pullback, actual model order
and rational weight produce source points on ALL original fractions.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical NNReal WithZero

namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.Berkovich SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
  (V : letI := p.stalkAlgebra (genericPoint X); Subalgebra ℂ X.functionField)
  [Algebra.EssFiniteType ℂ V] [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]

local instance geometricPointProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper
local instance geometricPointVariety : SGPT.Support.Alterations.IsVariety p := {}

/-- The normalized original DVR valuation is exactly the true source order
under the ACTUAL source residue pullback, on every nonzero original fraction. -/
theorem geometricDVR_originalOrder_value (a : X.functionField) (ha : a ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal V).valuation X.functionField a =
      WithZero.exp (-(primeDivisorOfGeometricDVR p V).ord
        (SchemeValuedPoint.genericResidueEquiv X
          ((primeDivisorOfGeometricDVR p V).π (genericPoint (primeDivisorOfGeometricDVR p V).Y))
          (primeDivisorOfGeometricDVR p V).isGenericPoint_image a)) := by
  let E := primeDivisorOfGeometricDVR p V
  let g := Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ DVRProperModel.centeredTrait p V
  have hinv := primeDivisorGenericPullback_fieldHom E g (DVRProperModel.centeredTrait_genericProjection p V)
  have hh := RingHom.congr_fun hinv a
  calc
    _ = (IsDiscreteValuationRing.maximalIdeal V).valuation X.functionField
        ((SchemeGenericFieldGraph.fieldHom g) (primeDivisorGenericPullback E a)) :=
      congrArg ((IsDiscreteValuationRing.maximalIdeal V).valuation X.functionField) hh.symm
    _ = _ := primeDivisor_nativeOrder_value p V (primeDivisorGenericPullback E a)
      ((map_ne_zero_iff _ (primeDivisorGenericPullback E).injective).mpr ha)

/-- A true normalized scale has the exact negative native order exponential. -/
theorem normalizedScale_exp_value (s : ℝ≥0) (n : ℤ) :
    ((DiscreteValuationRealScale.scale s (WithZero.exp n) : ℝ≥0) : ℝ) =
      Real.exp ((s : ℝ) * (n : ℝ)) := by
  have hz : DiscreteValuationRealScale.scale s (WithZero.exp n) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr WithZero.exp_ne_zero).map (DiscreteValuationRealScale.scale s)).ne_zero
  have hp : 0 < ((DiscreteValuationRealScale.scale s (WithZero.exp n) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hz)
  calc
    _ = Real.exp (Real.log ((DiscreteValuationRealScale.scale s (WithZero.exp n) : ℝ≥0) : ℝ)) :=
      (Real.exp_log hp).symm
    _ = _ := congrArg Real.exp (DiscreteValuationRealScale.log_scale_exp s n)

/-- A derived positive rational normalized DVR scale is EXACTLY the
literal original positive rational t ord_E point on its WHOLE K(X). -/
theorem geometricDVR_originalPoint_genericValuation (d : ℚ) (hd : 0 < d) :
    SchemeValuedPoint.genericValuation
      (pointEquiv p ((primeDivisorOfGeometricDVR p V).ordVal p d (by exact_mod_cast hd))).1
      ((primeDivisorOfGeometricDVR p V).ordVal_support_eq_genericPoint (f := p) d (by exact_mod_cast hd)) =
    DiscreteValuationRealScale.valuation
      ((IsDiscreteValuationRing.maximalIdeal V).valuation X.functionField)
      ⟨(d : ℝ), (by exact_mod_cast hd.le)⟩ := by
  let E := primeDivisorOfGeometricDVR p V
  apply Valuation.ext
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  apply NNReal.eq
  change (((pointEquiv p (E.ordVal p d (by exact_mod_cast hd))).1.residueVal
    (SchemeValuedPoint.genericResidueEquiv X (E.π (genericPoint E.Y)) E.isGenericPoint_image a)) : ℝ) = _
  rw [pointEquiv_ordVal_value p E d (by exact_mod_cast hd)
    ((map_ne_zero_iff _ (SchemeValuedPoint.genericResidueEquiv X
      (E.π (genericPoint E.Y)) E.isGenericPoint_image).injective).mpr ha)]
  rw [DiscreteValuationRealScale.valuation_apply, geometricDVR_originalOrder_value p V a ha,
    normalizedScale_exp_value]
  congr 1
  simp only [Int.cast_neg]
  change -((d : ℝ) * (E.ord _ : ℝ)) = (d : ℝ) * (-(E.ord _ : ℝ))
  ring

end SGPT.NAPotential.BJ.Pair3Div
