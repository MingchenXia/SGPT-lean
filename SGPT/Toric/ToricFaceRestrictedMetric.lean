import SGPT.Toric.ToricFaceMetricTransition
import SGPT.Toric.ToricFaceNativeHolomorphic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology BigOperators Classical Manifold ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The whole native insertion is genuinely complex smooth: it is an
actual linear map between the original finite-dimensional complex models. -/
theorem contDiff_toricFaceNativeCoordinateInsertion
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    ContDiff ℂ ∞ (toricFaceNativeCoordinateInsertion v J w) :=
  (LinearMap.toContinuousLinearMap (toricFaceNativeCoordinateInsertion v J w)).contDiff

/-- The literal restricted weights of the SAME original Hermitian metric
are smooth on EVERY entire native target chart, including point strata. -/
theorem toricFaceRestrictedWeight_smooth {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : latticePolytopeVertices (toricFaceProjectedFamily (hs := hs) v J)) :
    ContDiff ℝ ∞ (toricFaceRestrictedWeight h v J q) := by
  exact (h.smooth ((toricFaceVertexEquiv (hs := hs) v J).symm q).val).comp
    ((contDiff_toricFaceNativeCoordinateInsertion v J _).restrict_scalars ℝ)

/-- The ACTUAL target chart action and actual lifted original chart action
commute with the literal whole-chart insertion. Global genuine equivariance
and actual chart inverses prove this equality on every model point. -/
theorem toricFaceNativeCoordinateInsertion_action
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (a : Fin (toricFaceDimension J) → ℂˣ) (z : ComplexModel (toricFaceDimension J)) :
    toricFaceNativeCoordinateInsertion v J w
      (originalPolytopeNativeModelActionLinear (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv v J w) a z) =
      originalPolytopeNativeModelActionLinear γ hs w.val (toricFaceTorusSection (hs := hs) v J a)
        (toricFaceNativeCoordinateInsertion v J w z) := by
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  have h := toricFaceNativeEmbedding_equivariant v J (toricFaceTorusSection (hs := hs) v J a)
    (vertexPoint hY (toricFaceVertexEquiv v J w) z)
  rw [toricFaceTorusQuotient_section] at h
  change toricFaceNativeEmbedding v J
      (polytopeToricAction (toricFaceProjectedFamily (hs := hs) v J) hY a
        (vertexPoint hY (toricFaceVertexEquiv v J w) z)) =
    polytopeToricAction γ hs (toricFaceTorusSection (hs := hs) v J a)
      (toricFaceNativeEmbedding v J (vertexPoint hY (toricFaceVertexEquiv v J w) z)) at h
  rw [toricAction_vertexPoint, toricFaceNativeEmbedding_vertexPoint,
    toricFaceNativeEmbedding_vertexPoint, toricAction_vertexPoint] at h
  have hc := congrArg (originalPolytopeNativeModelChart γ hs w.val) h
  rw [chart_vertexPoint, chart_vertexPoint] at hc
  exact hc

/-- Actual compact target invariance of the SAME restricted smooth weights.
The actual compact lift and the genuine whole-chart action identity produce
the conclusion; no invariant target metric presentation is assumed. -/
theorem toricFaceRestrictedWeight_invariant {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : latticePolytopeVertices (toricFaceProjectedFamily (hs := hs) v J))
    (a : Fin (toricFaceDimension J) → ℂˣ) (ha : IsCompactTorusElement a)
    (z : ComplexModel (toricFaceDimension J)) :
    toricFaceRestrictedWeight h v J q
      (originalPolytopeNativeModelActionLinear (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) q a z) =
      toricFaceRestrictedWeight h v J q z := by
  obtain ⟨w, rfl⟩ := (toricFaceVertexEquiv (hs := hs) v J).surjective q
  simp only [toricFaceRestrictedWeight, Equiv.symm_apply_apply]
  rw [toricFaceNativeCoordinateInsertion_action]
  exact h.invariant w.val (toricFaceTorusSection (hs := hs) v J a) (toricFaceTorusSection_compact v J a ha) _

/-- The restricted smooth reference form is the ACTUAL holomorphic tensor
pullback of the SAME original curvature, in the SAME native face model. -/
def toricFaceRestrictedForm {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ClosedRealOneOneForm (toricFaceDimension J)
      (PolytopeToricVariety (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)) := by
  letI := originalPolytopeNativeChartedSpace γ hs
  letI := originalPolytopeNativeIsComplexManifold γ hs
  letI := originalPolytopeNativeChartedSpace (toricFaceProjectedFamily (hs := hs) v J)
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
  letI := originalPolytopeNativeIsComplexManifold (toricFaceProjectedFamily (hs := hs) v J)
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
  exact ClosedRealOneOneForm.pullback (contMDiff_toricFaceNativeEmbedding (hs := hs) v J) h.form

/-- The ACTUAL restricted tensor coefficient equals ddC of the SAME
restricted smooth weight on the ENTIRE target chart. Genuine holomorphic
ddC pullback and the literal chart insertion prove the full alternating form. -/
theorem toricFaceRestrictedForm_coeff_native {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (z : ComplexModel (toricFaceDimension J)) :
    (toricFaceRestrictedForm h v J).val.coeff
      (polytopeToricVertexChart (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv v J w)) z =
      smoothDDC (fun y => h.weight w.val (toricFaceNativeCoordinateInsertion v J w y)) z := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  let := originalPolytopeNativeChartedSpace γY hY
  let := originalPolytopeNativeIsComplexManifold γY hY
  let e := polytopeToricVertexChart γY hY (toricFaceVertexEquiv v J w)
  let d := polytopeToricVertexChart γ hs w.val
  have hz : z ∈ HolomorphicMaps.coordinateDomain (toricFaceNativeEmbedding (hs := hs) v J) e d := by
    refine ⟨?_, ?_⟩
    · change z ∈ (originalPolytopeNativeModelChart γY hY (toricFaceVertexEquiv v J w)).target
      rw [originalPolytopeNativeModelChart_target]
      exact mem_univ _
    · change toricFaceNativeEmbedding v J (vertexPoint hY (toricFaceVertexEquiv v J w) z) ∈
        (originalPolytopeNativeModelChart γ hs w.val).source
      rw [toricFaceNativeEmbedding_vertexPoint]
      exact vertexPoint_mem_source _ _
  have hcoord : HolomorphicMaps.coordinateMap (toricFaceNativeEmbedding (hs := hs) v J) e d =
      toricFaceNativeCoordinateInsertion v J w := by
    funext y
    change originalPolytopeNativeModelChart γ hs w.val
      (toricFaceNativeEmbedding v J (vertexPoint hY (toricFaceVertexEquiv v J w) y)) = _
    rw [toricFaceNativeEmbedding_vertexPoint, chart_vertexPoint]
  change (ClosedRealOneOneForm.pullback (contMDiff_toricFaceNativeEmbedding v J) h.form).val.coeff e z = _
  rw [ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff (contMDiff_toricFaceNativeEmbedding v J) h.form.val e d hz, hcoord]
  change (h.form.val.coeff (polytopeToricVertexChart γ hs w.val)
    (toricFaceNativeCoordinateInsertion v J w z)).compContinuousLinearMap _ = _
  rw [h.coeff]
  exact (HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ
    (contDiff_toricFaceNativeCoordinateInsertion v J w).contDiffOn (h.smooth w.val).contDiffOn
    (mapsTo_univ _ _) (mem_univ z)).symm

/-- A REAL invariant smooth Hermitian metric on the LITERAL original
restricted divisor DY, constructed internally from the SAME original metric.
Its form is actual restriction; its frames are (χ^mσ sD)|Y with the actual
Cartier transition characters. All dimensions, boundary points and arbitrary
original valid mσ are retained. -/
def toricFaceRestrictedMetric {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ) :
    BigToricMetric (toricFaceRestrictedDivisor D v J mσ) where
  form := toricFaceRestrictedForm h v J
  weight := toricFaceRestrictedWeight h v J
  smooth := toricFaceRestrictedWeight_smooth h v J
  coeff := by
    intro q z
    obtain ⟨w, rfl⟩ := (toricFaceVertexEquiv (hs := hs) v J).surjective q
    simpa only [toricFaceRestrictedWeight, Equiv.symm_apply_apply] using
      toricFaceRestrictedForm_coeff_native h v J w z
  invariant := toricFaceRestrictedWeight_invariant h v J
  transition := toricFaceRestrictedWeight_transition h v J mσ hσ

/-- Exact original curvature readback, not just a claimed cohomology class. -/
theorem toricFaceRestrictedMetric_form {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ) :
    (toricFaceRestrictedMetric h v J mσ hσ).form = toricFaceRestrictedForm h v J := rfl

end SGPT.Toric
