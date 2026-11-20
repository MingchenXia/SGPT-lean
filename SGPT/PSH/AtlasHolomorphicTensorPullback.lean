import SGPT.PSH.AtlasHolomorphicCoordinates

/-! # Actual global tensor pullback in independently dimensional original atlases

The chart is chosen pointwise only to define a total coefficient. The genuine
tensor law and real derivative chain rule prove that this coefficient agrees
locally with every admissible chart expression, which supplies smoothness.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y} {p : ℕ}

/-- The literal full alternating tensor pullback in one valid chart pair. -/
def atlasChartPullbackCoeff (a : AtlasSmoothRealForm B p) (f : X → Y)
    (i : A.Index) (j : B.Index) (z : ComplexModel (A.dimension i)) :
    ComplexModel (A.dimension i) [⋀^Fin p]→L[ℝ] ℝ :=
  (a.coeff j (atlasCoordinateMap A B f i j z)).compContinuousLinearMap
    (fderiv ℝ (atlasCoordinateMap A B f i j) z)

/-- Actual target-chart independence follows from the entire tensor law and
the genuine real derivative chain rule, including independently declared dimensions. -/
theorem atlasChartPullbackCoeff_change_target {f : X → Y} (hf : A.IsHolomorphic B f)
    (a : AtlasSmoothRealForm B p) (i : A.Index) (j j' : B.Index)
    {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j)
    (hz' : z ∈ atlasCoordinateDomain A B f i j') :
    atlasChartPullbackCoeff a f i j z = atlasChartPullbackCoeff a f i j' z := by
  ext w
  change a.coeff j (atlasCoordinateMap A B f i j z)
      (fun t => fderiv ℝ (atlasCoordinateMap A B f i j) z (w t)) =
    a.coeff j' (atlasCoordinateMap A B f i j' z)
      (fun t => fderiv ℝ (atlasCoordinateMap A B f i j') z (w t))
  rw [atlasCoordinateMap_fderiv_change_target hf i j j' hz hz',
    atlasCoordinateMap_change_target (j' := j') hz]
  exact a.compatible j j' _ (atlasCoordinateMap_mem_transition_source hz hz') _

/-- Smooth fixed-chart pullback is a genuine finite tensor-composition polynomial. -/
theorem atlasChartPullbackCoeff_contDiffOn {f : X → Y} (hf : A.IsHolomorphic B f)
    (a : AtlasSmoothRealForm B p) (i : A.Index) (j : B.Index) :
    ContDiffOn ℝ ∞ (atlasChartPullbackCoeff a f i j) (atlasCoordinateDomain A B f i j) := by
  apply SmoothRealForm.contDiffOn_compContinuousLinearMap
  · exact (a.smooth j).comp (atlasCoordinateMap_contDiffOn_real hf i j)
      (fun _ hz => atlasCoordinateMap_mem_target hz)
  · exact (atlasCoordinateMap_contDiffOn_real hf i j).fderiv_of_isOpen
      (atlasCoordinateDomain_isOpen hf i j) (by simp)

/-- Pointwise target-chart selection defines a whole coefficient; smoothness
is proved by local agreement rather than imposed on the choice function. -/
def atlasPullbackCoeff (a : AtlasSmoothRealForm B p) (f : X → Y)
    (i : A.Index) (z : ComplexModel (A.dimension i)) :
    ComplexModel (A.dimension i) [⋀^Fin p]→L[ℝ] ℝ :=
  atlasChartPullbackCoeff a f i (Classical.choose (B.cover (f ((A.chart i).symm z)))) z

/-- The chosen tensor agrees with EVERY admissible original target chart. -/
theorem atlasPullbackCoeff_eq_chartPullbackCoeff {f : X → Y}
    (hf : A.IsHolomorphic B f) (a : AtlasSmoothRealForm B p)
    (i : A.Index) (j : B.Index) {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    atlasPullbackCoeff a f i z = atlasChartPullbackCoeff a f i j z :=
  atlasChartPullbackCoeff_change_target hf a i _ j
    ⟨hz.1, Classical.choose_spec (B.cover (f ((A.chart i).symm z)))⟩ hz

/-- Actual agreement on an OPEN neighborhood is the smoothness and exterior
differentiation bridge; equality only at the centre would not suffice. -/
theorem atlasPullbackCoeff_eventuallyEq_chartPullbackCoeff {f : X → Y}
    (hf : A.IsHolomorphic B f) (a : AtlasSmoothRealForm B p)
    (i : A.Index) (j : B.Index) {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    atlasPullbackCoeff a f i =ᶠ[𝓝 z] atlasChartPullbackCoeff a f i j := by
  filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hz] with y hy
  exact atlasPullbackCoeff_eq_chartPullbackCoeff hf a i j hy

/-- The whole selected coefficients are smooth on every ORIGINAL chart target. -/
theorem atlasPullbackCoeff_contDiffOn {f : X → Y} (hf : A.IsHolomorphic B f)
    (a : AtlasSmoothRealForm B p) (i : A.Index) :
    ContDiffOn ℝ ∞ (atlasPullbackCoeff a f i) (A.chart i).target := by
  intro z hz
  let j := Classical.choose (B.cover (f ((A.chart i).symm z)))
  have hzj : z ∈ atlasCoordinateDomain A B f i j :=
    ⟨hz, Classical.choose_spec (B.cover (f ((A.chart i).symm z)))⟩
  exact ((atlasChartPullbackCoeff_contDiffOn hf a i j).contDiffAt
    ((atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj)).congr_of_eventuallyEq
      (atlasPullbackCoeff_eventuallyEq_chartPullbackCoeff hf a i j hzj) |>.contDiffWithinAt

/-- The same selected coefficients satisfy the FULL original source tensor
law, using a common admissible target chart and the true source chain rule. -/
theorem atlasPullbackCoeff_compatible {f : X → Y} (hf : A.IsHolomorphic B f)
    (a : AtlasSmoothRealForm B p) (i i' : A.Index)
    {z : ComplexModel (A.dimension i)}
    (hz : z ∈ ((A.chart i).symm.trans (A.chart i')).source)
    (w : Fin p → ComplexModel (A.dimension i)) :
    atlasPullbackCoeff a f i z w =
      atlasPullbackCoeff a f i' (((A.chart i).symm.trans (A.chart i')) z)
        (fun t => fderiv ℝ ((A.chart i).symm.trans (A.chart i')) z (w t)) := by
  let j := Classical.choose (B.cover (f ((A.chart i).symm z)))
  have hzj : z ∈ atlasCoordinateDomain A B f i j :=
    ⟨hz.1, Classical.choose_spec (B.cover (f ((A.chart i).symm z)))⟩
  rw [atlasPullbackCoeff_eq_chartPullbackCoeff hf a i j hzj,
    atlasPullbackCoeff_eq_chartPullbackCoeff hf a i' j (atlasCoordinateDomain_change_source hz hzj)]
  simp only [atlasChartPullbackCoeff, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [atlasCoordinateMap_fderiv_change_source hf i i' j hz hzj,
    atlasCoordinateMap_change_source (j := j) hz]
  rfl

/-- The actual global smooth real form on the original variable-dimensional atlas. -/
def AtlasSmoothRealForm.holomorphicPullback (a : AtlasSmoothRealForm B p)
    {f : X → Y} (hf : A.IsHolomorphic B f) : AtlasSmoothRealForm A p where
  coeff := atlasPullbackCoeff a f
  smooth := atlasPullbackCoeff_contDiffOn hf a
  compatible := fun i i' _ hz w => atlasPullbackCoeff_compatible hf a i i' hz w

/-- The complete coefficient formula holds on every admissible chart pair. -/
theorem AtlasSmoothRealForm.holomorphicPullback_coeff (a : AtlasSmoothRealForm B p)
    {f : X → Y} (hf : A.IsHolomorphic B f) (i : A.Index) (j : B.Index)
    {z : ComplexModel (A.dimension i)} (hz : z ∈ atlasCoordinateDomain A B f i j) :
    (a.holomorphicPullback hf).coeff i z =
      (a.coeff j (atlasCoordinateMap A B f i j z)).compContinuousLinearMap
        (fderiv ℝ (atlasCoordinateMap A B f i j) z) :=
  atlasPullbackCoeff_eq_chartPullbackCoeff hf a i j hz

/-- Exterior differentiation of the WHOLE chosen coefficients is the literal
pulled exterior derivative, internally using local fixed-chart agreement. -/
theorem AtlasSmoothRealForm.extDeriv_holomorphicPullback_coeff
    (a : AtlasSmoothRealForm B p) {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (j : B.Index) {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    extDeriv ((a.holomorphicPullback hf).coeff i) z =
      (extDeriv (a.coeff j) (atlasCoordinateMap A B f i j z)).compContinuousLinearMap
        (fderiv ℝ (atlasCoordinateMap A B f i j) z) := by
  change extDeriv (atlasPullbackCoeff a f i) z = _
  rw [(atlasPullbackCoeff_eventuallyEq_chartPullbackCoeff hf a i j hz).extDeriv_eq]
  exact extDeriv_pullback
    ((a.smooth j).contDiffAt ((B.chart j).open_target.mem_nhds
      (atlasCoordinateMap_mem_target hz)) |>.differentiableAt (by simp))
    (atlasCoordinateMap_contDiffAt_real hf hz)
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- A closed actual original background remains closed without dimension,
injectivity, compactness, connectedness or nondegeneracy assumptions. -/
theorem AtlasClosedRealOneOneForm.holomorphicPullback_closed
    (θ : AtlasClosedRealOneOneForm B) {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) {z : ComplexModel (A.dimension i)} (hz : z ∈ (A.chart i).target) :
    extDeriv ((θ.toAtlasSmoothRealForm.holomorphicPullback hf).coeff i) z = 0 := by
  let j := Classical.choose (B.cover (f ((A.chart i).symm z)))
  have hzj : z ∈ atlasCoordinateDomain A B f i j :=
    ⟨hz, Classical.choose_spec (B.cover (f ((A.chart i).symm z)))⟩
  rw [AtlasSmoothRealForm.extDeriv_holomorphicPullback_coeff θ.toAtlasSmoothRealForm hf i j hzj,
    θ.closed j _ (atlasCoordinateMap_mem_target hzj)]
  ext w
  rfl

/-- Genuine complex linearity of the actual derivative preserves type (1,1). -/
theorem AtlasClosedRealOneOneForm.holomorphicPullback_typeOneOne
    (θ : AtlasClosedRealOneOneForm B) {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) {z : ComplexModel (A.dimension i)} (hz : z ∈ (A.chart i).target) :
    IsOneOne ((θ.toAtlasSmoothRealForm.holomorphicPullback hf).coeff i z) := by
  intro u v
  let j := Classical.choose (B.cover (f ((A.chart i).symm z)))
  have hzj : z ∈ atlasCoordinateDomain A B f i j :=
    ⟨hz, Classical.choose_spec (B.cover (f ((A.chart i).symm z)))⟩
  rw [AtlasSmoothRealForm.holomorphicPullback_coeff θ.toAtlasSmoothRealForm hf i j hzj]
  let L := fderiv ℝ (atlasCoordinateMap A B f i j) z
  have hvec (u v : ComplexModel (A.dimension i)) : L ∘ ![u, v] = ![L u, L v] := by
    funext t
    fin_cases t <;> rfl
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change θ.coeff j (atlasCoordinateMap A B f i j z) (L ∘ ![Complex.I • u, Complex.I • v]) =
    θ.coeff j (atlasCoordinateMap A B f i j z) (L ∘ ![u, v])
  rw [hvec, hvec, atlasCoordinateMap_fderiv_map_smul_complex hf hzj Complex.I u,
    atlasCoordinateMap_fderiv_map_smul_complex hf hzj Complex.I v]
  exact θ.typeOneOne j _ (atlasCoordinateMap_mem_target hzj) (L u) (L v)

/-- The WHOLE actual original closed (1,1) tensor is manufactured on the
source variable atlas. No target-shaped PSH or local-potential field is assumed. -/
def AtlasClosedRealOneOneForm.holomorphicPullback (θ : AtlasClosedRealOneOneForm B)
    {f : X → Y} (hf : A.IsHolomorphic B f) : AtlasClosedRealOneOneForm A where
  toAtlasSmoothRealForm := θ.toAtlasSmoothRealForm.holomorphicPullback hf
  closed := fun i _ hz => θ.holomorphicPullback_closed hf i hz
  typeOneOne := fun i _ hz => θ.holomorphicPullback_typeOneOne hf i hz

/-- Every admissible original chart pair reads the complete manufactured
background, not merely its diagonal or a selected scalar potential. -/
theorem AtlasClosedRealOneOneForm.holomorphicPullback_coeff
    (θ : AtlasClosedRealOneOneForm B) {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (j : B.Index) {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    (θ.holomorphicPullback hf).coeff i z =
      (θ.coeff j (atlasCoordinateMap A B f i j z)).compContinuousLinearMap
        (fderiv ℝ (atlasCoordinateMap A B f i j) z) :=
  θ.toAtlasSmoothRealForm.holomorphicPullback_coeff hf i j hz

end SGPT.PSH.VariableComplexAtlas
