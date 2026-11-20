import SGPT.Toric.ToricFaceRestrictedDivisor
import SGPT.Toric.ToricFaceCharacterLog
import SGPT.Toric.ToricFaceWholeChart
import SGPT.Toric.BigToricMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Restriction of the SAME original smooth Hermitian metric weight in an
actual target chart, through its genuinely proved whole-chart insertion. -/
def toricFaceRestrictedWeight {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : latticePolytopeVertices (toricFaceProjectedFamily (hs := hs) v J)) :
    ComplexModel (toricFaceDimension J) → ℝ :=
  let w := (toricFaceVertexEquiv (hs := hs) v J).symm q
  fun z => h.weight w.val (toricFaceNativeCoordinateInsertion v J w z)

/-- Actual boundary restriction of the ORIGINAL dense-torus metric transition
law. The normal degeneration stays in the original ambient torus; the same
smooth weights have actual limits, and the original annihilator transition
character is constant. This does not apply a torus-only premise at Y's boundary. -/
theorem toricFaceRestrictedWeight_transition_native
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (w w' : ToricNativeFaceVertex (hs := hs) v J)
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    h.weight w.val (toricFaceNativeCoordinateInsertion v J w
      (originalPolytopeNativeModelChart (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w)
        (polytopeToricEmbedding (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) a))) +
      latticeFunctional (toricCartierDatum (toricFaceRestrictedDivisor D v J mσ)
        (toricFaceVertexEquiv (hs := hs) v J w)) (unitTorusLog a) =
    h.weight w'.val (toricFaceNativeCoordinateInsertion v J w'
      (originalPolytopeNativeModelChart (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w')
        (polytopeToricEmbedding (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) a))) +
      latticeFunctional (toricCartierDatum (toricFaceRestrictedDivisor D v J mσ)
        (toricFaceVertexEquiv (hs := hs) v J w')) (unitTorusLog a) := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let p : PolytopeToricVariety γY hY := polytopeToricEmbedding γY hY a
  let q := toricFaceNativeEmbedding (hs := hs) v J p
  have hp (s : ToricNativeFaceVertex (hs := hs) v J) :
      p ∈ (originalPolytopeNativePiChart γY hY (toricFaceVertexEquiv v J s)).source :=
    originalPolytopeNativeOrbitMap_mem_chart_source γY hY _ a
  have hq (s : ToricNativeFaceVertex (hs := hs) v J) :
      q ∈ (originalPolytopeNativeModelChart γ hs s.val).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact (toricFaceNativeEmbedding_mem_chart_source_iff v J s p).mpr (hp s)
  have hcurve : Tendsto
      (fun N => polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N)) atTop (𝓝 q) :=
    tendsto_toricFaceNormalCurve v J a
  have hlim (s : ToricNativeFaceVertex (hs := hs) v J) :
      Tendsto (fun N => h.weight s.val (originalPolytopeNativeModelChart γ hs s.val
        (polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N)))) atTop
        (𝓝 (h.weight s.val (originalPolytopeNativeModelChart γ hs s.val q))) := by
    have hc := (originalPolytopeNativeModelChart γ hs s.val).continuousOn.continuousAt
      ((originalPolytopeNativeModelChart γ hs s.val).open_source.mem_nhds (hq s))
    exact (((h.smooth s.val).continuous.continuousAt.comp hc).tendsto).comp hcurve
  let m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
    ⟨toricCartierDatum D w'.val - toricCartierDatum D w.val,
      sub_mem_toricStratumCharacterLattice_of_Cartier_data
        (isToricCartierDatumAlong_face_vertex D v J w')
        (isToricCartierDatumAlong_face_vertex D v J w)⟩
  have hseq :
      (fun N => h.weight w.val (originalPolytopeNativeModelChart γ hs w.val
          (polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N))) -
        h.weight w'.val (originalPolytopeNativeModelChart γ hs w'.val
          (polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N)))) =
      fun _ => latticeFunctional (toricFaceCharacterCoordinates (hs := hs) v J m) (unitTorusLog a) := by
    funext N
    have htrans := h.transition w.val w'.val (toricFaceNormalCurve (hs := hs) v J a N)
    have hlog := latticeFunctional_toricFaceNormalCurve v J m a N
    change latticeFunctional (toricCartierDatum D w'.val - toricCartierDatum D w.val)
      (unitTorusLog (toricFaceNormalCurve (hs := hs) v J a N)) = _ at hlog
    rw [latticeFunctional_sub_index] at hlog
    linarith
  have hdiff := (hlim w).sub (hlim w')
  rw [hseq] at hdiff
  have hvalue := tendsto_nhds_unique hdiff tendsto_const_nhds
  have hcart := toricFaceRestrictedDivisor_cartier_sub D v J mσ hσ w' w
  change _ = toricFaceCharacterCoordinates (hs := hs) v J m at hcart
  rw [← hcart, latticeFunctional_sub_index] at hvalue
  rw [toricFaceNativeEmbedding_whole_chart v J w p (hp w),
    toricFaceNativeEmbedding_whole_chart v J w' p (hp w')] at hvalue
  linarith

/-- All actual target vertices satisfy the genuine restricted metric
transition law, with the literal source restricted divisor and rational frame. -/
theorem toricFaceRestrictedWeight_transition
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (q q' : latticePolytopeVertices (toricFaceProjectedFamily (hs := hs) v J))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    toricFaceRestrictedWeight h v J q
        (originalPolytopeNativeModelChart (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) q
          (polytopeToricEmbedding (toricFaceProjectedFamily (hs := hs) v J)
            (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) a)) +
      latticeFunctional (toricCartierDatum (toricFaceRestrictedDivisor D v J mσ) q) (unitTorusLog a) =
    toricFaceRestrictedWeight h v J q'
        (originalPolytopeNativeModelChart (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) q'
          (polytopeToricEmbedding (toricFaceProjectedFamily (hs := hs) v J)
            (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) a)) +
      latticeFunctional (toricCartierDatum (toricFaceRestrictedDivisor D v J mσ) q') (unitTorusLog a) := by
  obtain ⟨w, rfl⟩ := (toricFaceVertexEquiv (hs := hs) v J).surjective q
  obtain ⟨w', rfl⟩ := (toricFaceVertexEquiv (hs := hs) v J).surjective q'
  simpa only [toricFaceRestrictedWeight, Equiv.symm_apply_apply] using
    toricFaceRestrictedWeight_transition_native h v J mσ hσ w w' a

end SGPT.Toric
