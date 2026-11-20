import SGPT.Unibranch.PDThetaForms
import SGPT.Unibranch.ComplexSpaceFormPullbackClosed
import SGPT.Unibranch.KSNormalizedSubvariety
import SGPT.Trace.TYNormalization

/-!
# The forms `θ|_Ỹ` are smooth closed real `(1,1)`-forms in the sense of `cor:PSH`

Source: `chapter_trace.tex`, Section "The definition of the trace operator" (the forms `θ|_Ỹ` on
the normalization `Ỹ` of an irreducible analytic subset `Y` of a compact Kähler manifold `X`, for
`θ` a smooth closed real `(1,1)`-form on `X`), and Appendix B, `def:unibranch:L105` and `cor:PSH`
("`θ` a smooth closed real `(1,1)`-form on `X`; closed means that locally `θ` is defined by a
closed form under a local embedding").

Lane PD formalized the book's notion of a smooth closed real `(1,1)`-form on a complex space as
`SGPT.Unibranch.PD.IsLocallyClosedOneOne θ` (near every point ONE smooth ambient real two-form
under a local embedding, closed and `J`-invariant, restricting to `θ`); `cor:PSH` for general `θ`
is stated with this hypothesis. This file proves that the forms used by the trace theory satisfy
it:

* `IsLocallyClosedOneOne.pullback`: the notion is stable under pull-back of forms along an
  arbitrary morphism of complex spaces (the ambient representative is pulled back along the local
  holomorphic lift of the morphism; pull-back along a holomorphic map preserves closedness and type
  `(1,1)`);
* `isLocallyClosedOneOne_ofClosedAnalytic`: a smooth closed real `(1,1)`-form `θ` of the manifold
  `M`, restricted to a closed analytic subset `C` (the complex space `(C, 𝒪_M/𝓘_C)`), is one (the
  local embeddings are the charts of `M`, the ambient representative is the chart coefficient of
  `θ`);
* `isLocallyClosedOneOne_restrictForm`: hence so is `θ|_Ỹ` (the `restrictForm`, the
  pull-back of `θ|_C` along the normalization map);
* `Normalization.restrict_isLocallyClosedOneOne`: for the normalization as a `TildeY`
  (`normalizationTildeY`), every `θ|_Ỹ` satisfies the hypothesis of `cor:PSH`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

namespace SGPT.Unibranch.PD

/-- **Pull-back of smooth closed real `(1,1)`-forms.** If `θ` is a smooth closed real
`(1,1)`-form on `X` (`IsLocallyClosedOneOne`), so is its pull-back `f^*θ` along any morphism of
complex spaces `f : Y → X`. -/
theorem IsLocallyClosedOneOne.pullback {X Y : SourceReducedComplexSpace} {θ : SpaceForm X 2}
    (hθ : IsLocallyClosedOneOne θ) (f : Y ⟶ X) :
    IsLocallyClosedOneOne (SpaceForm.pullback θ f) := by
  intro y
  obtain ⟨e, he, v, hv, hclosed, htype, hres⟩ := hθ (f.hom.left.base y)
  obtain ⟨A, hA⟩ := SpaceForm.morphismChartLift_cover f e y he
  refine ⟨A.source, hA, pullbackForm A.lift v, ?_, ?_, ?_,
    SpaceForm.pullback_restrictsTo_of_lift θ f hres A.source A.holomorphic A.maps A.factor⟩
  · apply SmoothRealForm.contDiffOn_compContinuousLinearMap
    · exact hv.comp (A.holomorphic.restrict_scalars ℝ) A.maps
    · exact (A.holomorphic.restrict_scalars ℝ).fderiv_of_isOpen A.source.ambient.isOpen (by simp)
  · intro z hz
    have hdiff := (hv.contDiffAt (e.ambient.isOpen.mem_nhds (A.maps hz))).differentiableAt
      (by simp)
    have hnat := extDeriv_pullback hdiff
      ((A.holomorphic.restrict_scalars ℝ).contDiffAt (A.source.ambient.isOpen.mem_nhds hz))
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    change extDeriv (fun w => (v (A.lift w)).compContinuousLinearMap (fderiv ℝ A.lift w)) z = 0
    rw [hnat, hclosed _ (A.maps hz)]
    ext w
    rfl
  · intro z hz a b
    have hd := (A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.source.ambient.isOpen.mem_nhds hz)
    have hlin (w : ComplexModel A.source.dim) :
        fderiv ℝ A.lift z (Complex.I • w) = Complex.I • fderiv ℝ A.lift z w := by
      rw [hd.fderiv_restrictScalars ℝ]
      exact (fderiv ℂ A.lift z).map_smul Complex.I w
    change v (A.lift z) ((fderiv ℝ A.lift z) ∘ ![Complex.I • a, Complex.I • b]) =
      v (A.lift z) ((fderiv ℝ A.lift z) ∘ ![a, b])
    have hvec : ((fderiv ℝ A.lift z) ∘ ![Complex.I • a, Complex.I • b]) =
        ![Complex.I • fderiv ℝ A.lift z a, Complex.I • fderiv ℝ A.lift z b] := by
      funext i
      fin_cases i <;> simp [hlin]
    have hvec' : ((fderiv ℝ A.lift z) ∘ ![a, b]) =
        ![fderiv ℝ A.lift z a, fderiv ℝ A.lift z b] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec, hvec']
    exact htype (A.lift z) (A.maps hz) (fderiv ℝ A.lift z a) (fderiv ℝ A.lift z b)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`θ|_C` is a smooth closed real `(1,1)`-form** on the complex space `(C, 𝒪_M/𝓘_C)`, for a
smooth closed real `(1,1)`-form `θ` on the manifold `M`: near every point of `C`, the chart of `M`
is a local embedding and the chart coefficient of `θ` is ONE ambient representative, closed and of
type `(1,1)`. -/
theorem isLocallyClosedOneOne_ofClosedAnalytic (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) {θ : SmoothRealForm n M 2} (hθc : θ.IsClosed)
    (hθ : θ.IsTypeOneOne) :
    IsLocallyClosedOneOne (SpaceForm.ofClosedAnalytic C hC θ) := by
  intro c
  exact ⟨LocalEmbedding.ofChart C hC c.val, mem_range_chartModelMap (n := n) C c.property,
    θ.coeff (complexChartAt c.val), θ.smooth (complexChartAt c.val),
    fun z hz => hθc (complexChartAt c.val) z hz,
    fun z hz a b => hθ (complexChartAt c.val) z hz a b,
    SpaceForm.ofClosedAnalytic_restrictsTo C hC θ c.val⟩

/-- **`θ|_Ỹ` is a smooth closed real `(1,1)`-form** on the normalization `Ỹ` of `(C, 𝒪_M/𝓘_C)`
(the `restrictForm`, the pull-back of `θ|_C` along the normalization map), for a smooth
closed real `(1,1)`-form `θ` on `M`. -/
theorem isLocallyClosedOneOne_restrictForm (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    {θ : SmoothRealForm n M 2} (hθc : θ.IsClosed) (hθ : θ.IsTypeOneOne) :
    IsLocallyClosedOneOne (KSNormalizedSubvariety.restrictForm C hC θ) :=
  (isLocallyClosedOneOne_ofClosedAnalytic C hC hθc hθ).pullback _

/-- The same for a `ClosedRealOneOneForm` of `M`. -/
theorem isLocallyClosedOneOne_restrictForm' (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (θ : ClosedRealOneOneForm n M) :
    IsLocallyClosedOneOne (KSNormalizedSubvariety.restrictForm C hC θ.val) :=
  isLocallyClosedOneOne_restrictForm C hC θ.property.1 θ.property.2

end SGPT.Unibranch.PD

namespace SGPT.Trace.TY.Normalization

open SGPT.Unibranch

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- **The forms `θ|_Ỹ` of the trace theory satisfy the hypothesis of `cor:PSH`**: for the
normalization `Ỹ` of `Y` (`normalizationTildeY`) and every smooth closed real `(1,1)`-form `θ`
on `X`, `θ|_Ỹ` is a smooth closed real `(1,1)`-form on `Ỹ` in the sense of
`PD.IsLocallyClosedOneOne` (one closed `(1,1)` ambient representative near each point). -/
theorem restrict_isLocallyClosedOneOne (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (θ : ClosedRealOneOneForm n X) :
    PD.IsLocallyClosedOneOne ((normalizationTildeY omega Y).restrict θ) :=
  PD.isLocallyClosedOneOne_restrictForm' Y.carrier Y.analytic θ

end SGPT.Trace.TY.Normalization
