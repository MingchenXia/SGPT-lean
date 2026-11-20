import SGPT.Foundations.Schemes.NativeProjectiveFubiniStudyPullback
import SGPT.Foundations.Schemes.SchemeTangentEndomorphism
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Genuine native smooth Riemannian metric on an actual smooth projective source

The metric is the literal Fubini–Study pullback through the actual native
closed-immersion tangent derivative. Smoothness is derived from the actual
fundamental form and imaginary operator; the actual tangent left inverse
proves bounded unit balls for the existing fiber topology.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle Set Filter Bornology
open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] projectiveFubiniStudyPointTopology projectiveFubiniStudyPointChartedSpace
  projectiveFubiniStudyPointRealManifold

section ActualMetric

variable {X : Scheme} (N n : ℕ) (e : X ⟶ polynomialProj ℂ N) [IsClosedImmersion e]
  [SmoothOfRelativeDimension n (e ≫ polynomialProjStructureMap ℂ N)]

local instance riemannianPointTopology :
    TopologicalSpace (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :=
  schemeAnalyticPointTopology (e ≫ polynomialProjStructureMap ℂ N)

local instance riemannianPointChartedSpace :
    ChartedSpace (Fin n → ℂ) (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :=
  smoothSchemeComplexChartedSpace (e ≫ polynomialProjStructureMap ℂ N) n

local instance riemannianPointRealManifold :
    IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :=
  smoothSchemeReal_isManifold (e ≫ polynomialProjStructureMap ℂ N) n ∞

/-- Recover the literal pullback metric from its genuine fundamental form and actual `J²=-id`. -/
theorem nativeProjectiveFubiniStudyMetricPullback_eq_form
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyMetricPullback N n e x v w =
      nativeProjectiveFubiniStudyFundamentalPullback N n e x
        ![-smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v, w] := by
  rw [nativeProjectiveFubiniStudyFundamentalPullback_eq_metric, map_neg,
    smoothSchemeTangentJ_square_apply, neg_neg]

/-- Actual tangent left inverses transfer target unit-ball boundedness to the existing source topology. -/
theorem nativeProjectiveFubiniStudyMetricPullback_isVonNBounded
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    IsVonNBounded ℝ {v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x |
      nativeProjectiveFubiniStudyMetricPullback N n e x v v < 1} := by
  obtain ⟨L, hL⟩ := exists_nativeClosedImmersionRealPoint_mfderiv_leftInverse
    (polynomialProjStructureMap ℂ N) e n N x
  have hA : L.comp (nativeProjectivePointTangentMap N n e x) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) x) := hL
  apply ((polynomialProjFubiniStudyMetric N).isVonNBounded
    (nativeProjectivePointMap N e x)).image L |>.subset
  intro v hv
  refine ⟨nativeProjectivePointTangentMap N n e x v, ?_, ?_⟩
  · change (polynomialProjFubiniStudyMetric N).inner (nativeProjectivePointMap N e x)
      (nativeProjectivePointTangentMap N n e x v) (nativeProjectivePointTangentMap N n e x v) < 1
    rwa [← nativeProjectiveFubiniStudyMetricPullback_apply]
  · exact congrArg (fun M : TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) x => M v) hA

/-- Actual model coefficients recovered from the genuine two-form coefficients by constant model `-J`. -/
def nativeProjectiveFubiniStudyMetricCoefficients
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  (nativeAlternatingBilinearCLM n (nativeProjectiveFubiniStudyPullbackCoefficients N n e p z)).bilinearComp
    (-smoothComplexModelJ n) (ContinuousLinearMap.id ℝ (Fin n → ℂ))

set_option synthInstance.maxHeartbeats 200000 in
/-- The actual metric model coefficients are genuinely smooth on the actual source chart target. -/
theorem nativeProjectiveFubiniStudyMetricCoefficients_contDiffOn
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    ContDiffOn ℝ ∞ (nativeProjectiveFubiniStudyMetricCoefficients N n e p)
      (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).target := by
  have hL : ContDiff ℝ ∞ (nativeAlternatingBilinearCLM n) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)
      (F := (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (nativeAlternatingBilinearCLM n)
  have hA := hL.comp_contDiffOn
    (nativeProjectiveFubiniStudyPullbackCoefficients_contDiffOn N n e p)
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ ∞ (fun z => nativeAlternatingBilinearCLM n
    (nativeProjectiveFubiniStudyPullbackCoefficients N n e p z)
      (-smoothComplexModelJ n v) w) _
  exact (hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const

omit [IsClosedImmersion e] in
/-- The actual inverse native tangent trivialization intertwines the genuine imaginary maps. -/
theorem nativeProjectiveRiemannian_symmL_J
    (p x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (hx : x ∈ (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).source)
    (v : Fin n → ℂ) :
    (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x
        (smoothComplexModelJ n v) =
      smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x
        ((trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x v) := by
  let a := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
  have ha : x ∈ a.baseSet := hx
  have hJ := smoothSchemeTangentJ_inCoordinates (e ≫ polynomialProjStructureMap ℂ N) n p x hx
  rw [ContinuousLinearMap.inCoordinates_eq ha ha] at hJ
  have hv := congrArg (fun A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) => A v) hJ
  change (a.continuousLinearEquivAt ℝ x ha)
    (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x
      ((a.continuousLinearEquivAt ℝ x ha).symm v)) = smoothComplexModelJ n v at hv
  have h := congrArg (a.continuousLinearEquivAt ℝ x ha).symm hv
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [← a.symm_continuousLinearEquivAt_eq' ha]
  exact h.symm

/-- Actual bilinear Hom coordinates read exactly the recovered metric coefficients. -/
theorem nativeProjectiveFubiniStudyMetricPullback_trivialization
    (p x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (hx : x ∈ (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).source) :
    (trivializationAt ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p
      (TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (nativeProjectiveFubiniStudyMetricPullback N n e x))).2 =
      nativeProjectiveFubiniStudyMetricCoefficients N n e p
        (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p x) := by
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  let a := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  have hcot : x ∈ (trivializationAt ((Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p).baseSet :=
    ⟨hx, Set.mem_univ x⟩
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hcot]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  have hscalar : (trivializationAt ℝ
      (fun _ : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N) => ℝ) p).continuousLinearMapAt ℝ x =
      ContinuousLinearMap.id ℝ ℝ :=
    Bundle.Trivial.continuousLinearMapAt_trivialization ℝ
      (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) ℝ x
  rw [hscalar, ContinuousLinearMap.id_apply, nativeProjectiveFubiniStudyMetricPullback_eq_form]
  change nativeProjectiveFubiniStudyFundamentalPullback N n e x
      ![-smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x (a.symmL ℝ x v), a.symmL ℝ x w] =
    nativeAlternatingBilinearCLM n
      (nativeProjectiveFubiniStudyPullbackCoefficients N n e p (c x)) (-smoothComplexModelJ n v) w
  rw [nativeAlternatingBilinearCLM_apply]
  change _ = ((nativeProjectiveFubiniStudyFundamentalPullback N n e (c.symm (c x))).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) c.symm (c x))) ![-smoothComplexModelJ n v, w]
  rw [c.left_inv hx, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ← nativeProjectivePullback_standard_symmL N n e p x hx]
  congr 1
  ext j
  fin_cases j
  · change -smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x (a.symmL ℝ x v) =
      a.symmL ℝ x (-smoothComplexModelJ n v)
    rw [map_neg, nativeProjectiveRiemannian_symmL_J N n e p x hx]
  · rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The literal pullback metric is a genuine smooth section of the actual native bilinear Hom bundle. -/
theorem nativeProjectiveFubiniStudyMetricPullback_contMDiff :
    ContMDiff 𝓘(ℝ, Fin n → ℂ)
      (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (nativeProjectiveFubiniStudyMetricPullback N n e x)) := by
  intro p
  rw [contMDiffAt_section p]
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  have hp : p ∈ c.source := schemeAnalyticCoordinateChart_point_mem_source _ n p
  have heq : (fun x => (trivializationAt ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p
      (TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (nativeProjectiveFubiniStudyMetricPullback N n e x))).2) =ᶠ[𝓝 p]
      (fun x => nativeProjectiveFubiniStudyMetricCoefficients N n e p (c x)) := by
    filter_upwards [c.open_source.mem_nhds hp] with x hx
    exact nativeProjectiveFubiniStudyMetricPullback_trivialization N n e p x hx
  have hcoeff := (nativeProjectiveFubiniStudyMetricCoefficients_contDiffOn N n e p).contDiffAt
    (c.open_target.mem_nhds (c.map_source hp))
  have hc : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ∞ c p :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp
  exact (hcoeff.contMDiffAt.comp p hc).congr_of_eventuallyEq heq

/-- The genuine native smooth Riemannian metric on the existing actual source tangent bundle. -/
def nativeProjectiveFubiniStudyRiemannianMetric :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) where
  inner := nativeProjectiveFubiniStudyMetricPullback N n e
  symm := nativeProjectiveFubiniStudyMetricPullback_symm N n e
  pos := nativeProjectiveFubiniStudyMetricPullback_pos N n e
  isVonNBounded := nativeProjectiveFubiniStudyMetricPullback_isVonNBounded N n e
  contMDiff := nativeProjectiveFubiniStudyMetricPullback_contMDiff N n e

/-- The actual native metric inner product is the original literal Fubini–Study pullback. -/
theorem nativeProjectiveFubiniStudyRiemannianMetric_inner
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    (nativeProjectiveFubiniStudyRiemannianMetric N n e).inner x v w =
      nativeProjectiveFubiniStudyMetricPullback N n e x v w := rfl

/-- Genuine Hermitian invariance for this actual native smooth Riemannian metric. -/
theorem nativeProjectiveFubiniStudyRiemannianMetric_hermitian
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    (nativeProjectiveFubiniStudyRiemannianMetric N n e).inner x
      (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v)
      (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x w) =
    (nativeProjectiveFubiniStudyRiemannianMetric N n e).inner x v w :=
  nativeProjectiveFubiniStudyMetricPullback_hermitian N n e x v w

/-- Registering this exact native metric preserves the existing actual tangent topology. -/
@[instance_reducible]
def nativeProjectiveFubiniStudyRiemannianBundle :
    RiemannianBundle (fun x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N) =>
      TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :=
  ⟨(nativeProjectiveFubiniStudyRiemannianMetric N n e).toRiemannianMetric⟩

/-- Mathlib derives the actual native smooth Riemannian-bundle property from the constructed metric. -/
theorem nativeProjectiveFubiniStudy_isContMDiffRiemannianBundle :
    letI := nativeProjectiveFubiniStudyRiemannianBundle N n e
    IsContMDiffRiemannianBundle 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) := by
  exact inferInstance

end ActualMetric

section ActualStructuralMetric

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)
  (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The literal structural equality transports the genuine metric to the given actual source point space. -/
def ClosedProjectiveEmbedding.nativeFubiniStudyRiemannianMetric :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : SchemeComplexPoint f => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyRiemannianMetric N n e

/-- Its actual inner product is recovered from the already constructed genuine source fundamental form. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudyRiemannianMetric_inner_form :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    ∀ (x : SchemeComplexPoint f) (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      (E.nativeFubiniStudyRiemannianMetric n).inner x v w =
        E.nativeFubiniStudyFundamentalForm n x ![-smoothSchemeTangentJ f n x v, w] := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyMetricPullback_eq_form N n e

/-- The transported actual metric remains genuinely Hermitian for the given native source `J`. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudyRiemannianMetric_hermitian :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    ∀ (x : SchemeComplexPoint f) (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      (E.nativeFubiniStudyRiemannianMetric n).inner x
        (smoothSchemeTangentJ f n x v) (smoothSchemeTangentJ f n x w) =
      (E.nativeFubiniStudyRiemannianMetric n).inner x v w := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyRiemannianMetric_hermitian N n e

/-- The exact transported metric gives a native Riemannian bundle on the existing actual source fibers. -/
@[instance_reducible]
def ClosedProjectiveEmbedding.nativeFubiniStudyRiemannianBundle :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    RiemannianBundle (fun x : SchemeComplexPoint f => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :=
  letI := schemeAnalyticPointTopology f
  letI := smoothSchemeComplexChartedSpace f n
  letI := smoothSchemeReal_isManifold f n ∞
  ⟨(E.nativeFubiniStudyRiemannianMetric n).toRiemannianMetric⟩

/-- The genuine given-source metric derives Mathlib's native smooth Riemannian-bundle property. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudy_isContMDiffRiemannianBundle :
    letI := schemeAnalyticPointTopology f
    letI := smoothSchemeComplexChartedSpace f n
    letI := smoothSchemeReal_isManifold f n ∞
    letI := E.nativeFubiniStudyRiemannianBundle n
    IsContMDiffRiemannianBundle 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : SchemeComplexPoint f => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) := by
  exact inferInstance

/-- Actual smooth projective Fano data produce a genuine native smooth Riemannian metric without a metric premise. -/
def SmoothProjectiveFano.nativeProjectiveRiemannianMetric {n : ℕ} (F : SmoothProjectiveFano n) :
    letI := schemeAnalyticPointTopology F.structureMap
    letI := smoothSchemeComplexChartedSpace F.structureMap n
    letI := smoothSchemeReal_isManifold F.structureMap n ∞
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : SchemeComplexPoint F.structureMap => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :=
  F.projective.nativeFubiniStudyRiemannianMetric n

/-- The actual Fano metric's inner product is the previously constructed genuine fundamental form. -/
theorem SmoothProjectiveFano.nativeProjectiveRiemannianMetric_inner_form
    {n : ℕ} (F : SmoothProjectiveFano n) :
    letI := schemeAnalyticPointTopology F.structureMap
    letI := smoothSchemeComplexChartedSpace F.structureMap n
    letI := smoothSchemeReal_isManifold F.structureMap n ∞
    ∀ (x : SchemeComplexPoint F.structureMap) (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      F.nativeProjectiveRiemannianMetric.inner x v w =
        F.nativeProjectiveFundamentalForm x ![-smoothSchemeTangentJ F.structureMap n x v, w] :=
  F.projective.nativeFubiniStudyRiemannianMetric_inner_form n

end ActualStructuralMetric

end

end SGPT.Foundations.Schemes
