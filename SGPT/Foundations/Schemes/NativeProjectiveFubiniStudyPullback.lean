import SGPT.Foundations.Schemes.NativeProjectiveAnalyticImmersionGlobal
import SGPT.Foundations.Schemes.ProjectiveFubiniStudyFormCoefficients
import SGPT.Foundations.Schemes.NativeProjectiveFano
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Actual projective fundamental-form pullback

The input is a literal closed immersion into native polynomial Proj and actual
smoothness of its structural composite. The actual native tangent derivative
defines the pullback; its injectivity and imaginary compatibility are derived.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] projectiveFubiniStudyPointTopology projectiveFubiniStudyPointChartedSpace
  projectiveFubiniStudyPointRealManifold

/-- The actual projective metric topology is literally the derived scheme topology. -/
theorem nativeProjectiveFubiniStudyPointTopology_eq (N : ℕ) :
    projectiveFubiniStudyPointTopology N = schemeAnalyticPointTopology (polynomialProjStructureMap ℂ N) := rfl

/-- Ratio charts compute tensors in the same actual native uniform scheme charted space. -/
theorem nativeProjectiveFubiniStudyPointChartedSpace_eq (N : ℕ) :
    projectiveFubiniStudyPointChartedSpace N =
      smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ N) N := rfl

/- The finite-dimensional alternating retraction argument adapts the mathematical
   proof in SGPT.Foundations.Analysis/Pending/NaturalSmoothTensorPullback.lean, lines
   31–76 (Mathlib-style Apache-2.0 development). No sibling module is imported:
   the genuine linear retraction and its identity are proved here from Mathlib. -/
private def pullbackAlternatingRetraction {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) W) →L[ℝ]
      V [⋀^Fin 2]→L[ℝ] W := by
  let : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) W) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  exact (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ)).leftInverse
    |>.toContinuousLinearMap

private theorem pullbackAlternatingRetraction_apply {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (A : V [⋀^Fin 2]→L[ℝ] W) :
    pullbackAlternatingRetraction A.toContinuousMultilinearMap = A := by
  change (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ)).leftInverse
    (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ) A) = A
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr ContinuousAlternatingMap.toContinuousMultilinearMap_injective

private theorem pullbackAlternating_contDiffOn {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : Set U} {A : U → W [⋀^Fin 2]→L[ℝ] ℝ} {L : U → V →L[ℝ] W}
    (hA : ContDiffOn ℝ ∞ A S) (hL : ContDiffOn ℝ ∞ L S) :
    ContDiffOn ℝ ∞ (fun x => (A x).compContinuousLinearMap (L x)) S := by
  let B := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin 2 => V) (fun _ : Fin 2 => W) ℝ
  have hpi : ContDiffOn ℝ ∞ (fun x => fun _ : Fin 2 => L x) S :=
    contDiffOn_pi.mpr fun _ => hL
  have hB : ContDiff ℝ ∞ (B : (Fin 2 → V →L[ℝ] W) →
      (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => W) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (E := fun _ : Fin 2 => V →L[ℝ] W)
      (F := (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => W) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) B
  have hc := hB.comp_contDiffOn hpi
  have ha : ContDiffOn ℝ ∞ (fun x => (A x).toContinuousMultilinearMap) S :=
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ :
      (W [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => W) ℝ).contDiff.comp_contDiffOn hA
  have hr := (pullbackAlternatingRetraction (V := V) (W := ℝ)).contDiff.comp_contDiffOn
    (hc.clm_apply ha)
  convert hr using 1
  funext x
  exact (pullbackAlternatingRetraction_apply ((A x).compContinuousLinearMap (L x))).symm

/-- Genuine bounded linear currying of an actual two-form into a native bilinear Hom fiber. -/
def nativeAlternatingBilinearCLM (n : ℕ) :
    ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
      ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) :=
  ((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Fin n → ℂ) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.postcomp
      (Fin n → ℂ)).comp ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap

/-- This bounded linear operation reads exactly the two genuine tangent arguments. -/
theorem nativeAlternatingBilinearCLM_apply (n : ℕ)
    (A : (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v w : Fin n → ℂ) :
    nativeAlternatingBilinearCLM n A v w = A ![v, w] := by
  change ((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Fin n → ℂ) (F := ℝ) (0 : Fin 1)).symm (A.curryLeft v)) w = _
  change (ContinuousAlternatingMap.ofSubsingleton ℝ (Fin n → ℂ) ℝ (0 : Fin 1)).symm
    (A.curryLeft v) w = _
  rw [ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

section ActualPullback

variable {X : Scheme} (N n : ℕ) (e : X ⟶ polynomialProj ℂ N) [IsClosedImmersion e]
  [SmoothOfRelativeDimension n (e ≫ polynomialProjStructureMap ℂ N)]

local instance pullbackPointTopology :
    TopologicalSpace (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :=
  schemeAnalyticPointTopology (e ≫ polynomialProjStructureMap ℂ N)

local instance pullbackPointChartedSpace :
    ChartedSpace (Fin n → ℂ) (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :=
  smoothSchemeComplexChartedSpace (e ≫ polynomialProjStructureMap ℂ N) n

local instance pullbackPointRealManifold :
    IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :=
  smoothSchemeReal_isManifold (e ≫ polynomialProjStructureMap ℂ N) n ∞

/-- The actual point map induced by the actual projective closed immersion. -/
def nativeProjectivePointMap : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N) →
    SchemeComplexPoint (polynomialProjStructureMap ℂ N) :=
  schemeComplexPointMap (e ≫ polynomialProjStructureMap ℂ N)
    (polynomialProjStructureMap ℂ N) e rfl

/-- The actual point map is native real smooth in every order. -/
theorem nativeProjectivePointMap_contMDiff (k : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin N → ℂ) k (nativeProjectivePointMap N e) :=
  nativeClosedImmersionRealPoint_contMDiff (polynomialProjStructureMap ℂ N) e n N k

/-- Its derivative is the actual native real tangent map. -/
def nativeProjectivePointTangentMap
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin N → ℂ) (nativeProjectivePointMap N e x) :=
  mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin N → ℂ) (nativeProjectivePointMap N e) x

/-- The actual real tangent map is injective, derived from genuine retraction germs. -/
theorem nativeProjectivePointTangentMap_injective
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    Function.Injective (nativeProjectivePointTangentMap N n e x) :=
  nativeClosedImmersionRealPoint_mfderiv_injective (polynomialProjStructureMap ℂ N) e n N x

/-- The actual tangent map intertwines the two actual native imaginary structures. -/
theorem nativeProjectivePointTangentMap_commutes_J
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectivePointTangentMap N n e x
      (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v) =
    smoothSchemeTangentJ (polynomialProjStructureMap ℂ N) N (nativeProjectivePointMap N e x)
      (nativeProjectivePointTangentMap N n e x v) :=
  nativeClosedImmersionRealPoint_mfderiv_commutes_J (polynomialProjStructureMap ℂ N) e n N x v

/-- The literal pullback of the genuine projective tangent metric. -/
def nativeProjectiveFubiniStudyMetricPullback
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ] ℝ := by
  change (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ
  let G : (Fin N → ℂ) →L[ℝ] (Fin N → ℂ) →L[ℝ] ℝ :=
    polynomialProjFubiniStudyTangentForm N (nativeProjectivePointMap N e x)
  let A : (Fin n → ℂ) →L[ℝ] (Fin N → ℂ) := nativeProjectivePointTangentMap N n e x
  exact G.bilinearComp A A

/-- The actual alternating tangent two-form is pulled back through the actual tangent derivative. -/
def nativeProjectiveFubiniStudyFundamentalPullback
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) x [⋀^Fin 2]→L[ℝ] ℝ :=
  (polynomialProjFubiniStudyFundamentalForm N (nativeProjectivePointMap N e x)).compContinuousLinearMap
    (nativeProjectivePointTangentMap N n e x)

omit [IsClosedImmersion e] in
/-- Literal metric pullback evaluation, without any injectivity premise. -/
theorem nativeProjectiveFubiniStudyMetricPullback_apply
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyMetricPullback N n e x v w =
      (polynomialProjFubiniStudyMetric N).inner (nativeProjectivePointMap N e x)
        (nativeProjectivePointTangentMap N n e x v) (nativeProjectivePointTangentMap N n e x w) := rfl

omit [IsClosedImmersion e] in
/-- Symmetry of the actual pulled-back metric. -/
theorem nativeProjectiveFubiniStudyMetricPullback_symm
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyMetricPullback N n e x v w =
      nativeProjectiveFubiniStudyMetricPullback N n e x w v := by
  change polynomialProjFubiniStudyTangentForm N (nativeProjectivePointMap N e x)
    (nativeProjectivePointTangentMap N n e x v) (nativeProjectivePointTangentMap N n e x w) =
    polynomialProjFubiniStudyTangentForm N (nativeProjectivePointMap N e x)
    (nativeProjectivePointTangentMap N n e x w) (nativeProjectivePointTangentMap N n e x v)
  exact polynomialProjFubiniStudyTangentForm_symm N _ _ _

/-- Actual tangent injectivity produces strict metric positivity. -/
theorem nativeProjectiveFubiniStudyMetricPullback_pos
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) (hv : v ≠ 0) :
    0 < nativeProjectiveFubiniStudyMetricPullback N n e x v v := by
  rw [nativeProjectiveFubiniStudyMetricPullback_apply]
  apply (polynomialProjFubiniStudyMetric N).pos
  intro h
  exact hv (nativeProjectivePointTangentMap_injective N n e x (by simpa using h))

set_option maxHeartbeats 800000 in
/-- The actual pullback metric is Hermitian for the actual source tangent structure. -/
theorem nativeProjectiveFubiniStudyMetricPullback_hermitian
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyMetricPullback N n e x
      (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v)
      (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x w) =
      nativeProjectiveFubiniStudyMetricPullback N n e x v w := by
  rw [nativeProjectiveFubiniStudyMetricPullback_apply, nativeProjectiveFubiniStudyMetricPullback_apply,
    nativeProjectivePointTangentMap_commutes_J, nativeProjectivePointTangentMap_commutes_J]
  exact polynomialProjFubiniStudyMetric_hermitian N _ _ _

omit [IsClosedImmersion e] in
/-- Literal evaluation of the actual alternating pullback. -/
theorem nativeProjectiveFubiniStudyFundamentalPullback_apply
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyFundamentalPullback N n e x ![v, w] =
      polynomialProjFubiniStudyFundamentalForm N (nativeProjectivePointMap N e x)
        ![nativeProjectivePointTangentMap N n e x v, nativeProjectivePointTangentMap N n e x w] := by
  rw [nativeProjectiveFubiniStudyFundamentalPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

/-- The actual pulled-back fundamental form is the imaginary part of the actual pulled-back metric. -/
theorem nativeProjectiveFubiniStudyFundamentalPullback_eq_metric
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyFundamentalPullback N n e x ![v, w] =
      nativeProjectiveFubiniStudyMetricPullback N n e x
        (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v) w := by
  rw [nativeProjectiveFubiniStudyFundamentalPullback_apply,
    polynomialProjFubiniStudyFundamentalForm_apply]
  change _ = polynomialProjFubiniStudyTangentForm N (nativeProjectivePointMap N e x)
    (nativeProjectivePointTangentMap N n e x
      (smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v))
    (nativeProjectivePointTangentMap N n e x w)
  rw [nativeProjectivePointTangentMap_commutes_J]
  rfl

/-- Genuine Hermitian invariance of the actual pulled-back form. -/
theorem nativeProjectiveFubiniStudyFundamentalPullback_type_one_one
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyFundamentalPullback N n e x
      ![smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v,
        smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x w] =
      nativeProjectiveFubiniStudyFundamentalPullback N n e x ![v, w] := by
  rw [nativeProjectiveFubiniStudyFundamentalPullback_apply,
    nativeProjectiveFubiniStudyFundamentalPullback_apply,
    nativeProjectivePointTangentMap_commutes_J, nativeProjectivePointTangentMap_commutes_J]
  exact polynomialProjFubiniStudyFundamentalForm_type_one_one N _ _ _

/-- Strict positive complex diagonal follows from the derived actual tangent injectivity. -/
theorem nativeProjectiveFubiniStudyFundamentalPullback_complex_diagonal_pos
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) (hv : v ≠ 0) :
    0 < nativeProjectiveFubiniStudyFundamentalPullback N n e x
      ![v, smoothSchemeTangentJ (e ≫ polynomialProjStructureMap ℂ N) n x v] := by
  rw [nativeProjectiveFubiniStudyFundamentalPullback_apply,
    nativeProjectivePointTangentMap_commutes_J]
  apply polynomialProjFubiniStudyFundamentalForm_complex_diagonal_pos
  intro h
  apply hv
  exact nativeProjectivePointTangentMap_injective N n e x (by simpa using h)

/-- Literal preferred-chart coefficients of the actual alternating pullback tensor. -/
def nativeProjectiveFubiniStudyPullbackCoefficients
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  (nativeProjectiveFubiniStudyFundamentalPullback N n e (c.symm z)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) c.symm z)

/-- Actual ambient coefficient pullback through the actual source-target coordinate map. -/
def nativeProjectiveFubiniStudyCoordinatePullback
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (q : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  let T := nativeClosedImmersionCoordinateMap (polynomialProjStructureMap ℂ N) e n N p q
  (polynomialProjFubiniStudyFormStandardCoefficients N q (T z)).compContinuousLinearMap
    (fderiv ℝ T z)

/-- The actual native chain rule identifies the coordinate derivative on the genuine domain. -/
theorem nativeProjectiveCoordinateMap_real_fderiv
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (q : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) (z : Fin n → ℂ)
    (hz : z ∈ nativeClosedImmersionCoordinateDomain (polynomialProjStructureMap ℂ N) e n N p q) :
    fderiv ℝ (nativeClosedImmersionCoordinateMap (polynomialProjStructureMap ℂ N) e n N p q) z =
      (mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, Fin N → ℂ)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q)
        (nativeProjectivePointMap N e
          ((schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).symm z))).comp
      ((nativeProjectivePointTangentMap N n e
        ((schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).symm z)).comp
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
          (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).symm z)) := by
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  let d := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q
  have hc : c.MDifferentiable 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) := mdifferentiable_chart p
  have hd : d.MDifferentiable 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, Fin N → ℂ) := mdifferentiable_chart q
  have hF := (nativeProjectivePointMap_contMDiff N n e 1).mdifferentiableAt one_ne_zero
    (x := c.symm z)
  have hs := hc.mdifferentiableAt_symm hz.1
  have ht := hd.mdifferentiableAt hz.2
  have h := mfderiv_comp z ht (hF.comp z hs)
  rw [mfderiv_comp z hF hs, mfderiv_eq_fderiv] at h
  exact h

/-- Actual inverse-chart derivatives cancel in the literal coefficient readback. -/
theorem nativeProjectiveFubiniStudyPullbackCoefficients_readback
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (q : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) (z : Fin n → ℂ)
    (hz : z ∈ nativeClosedImmersionCoordinateDomain (polynomialProjStructureMap ℂ N) e n N p q) :
    nativeProjectiveFubiniStudyPullbackCoefficients N n e p z =
      nativeProjectiveFubiniStudyCoordinatePullback N n e p q z := by
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  let d := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q
  let x := c.symm z
  let y := nativeProjectivePointMap N e x
  let A : (Fin n → ℂ) →L[ℝ] (Fin N → ℂ) := nativeProjectivePointTangentMap N n e x
  let C : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) c.symm z
  let B : (Fin N → ℂ) →L[ℝ] (Fin N → ℂ) :=
    mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, Fin N → ℂ) d y
  let D : (Fin N → ℂ) →L[ℝ] (Fin N → ℂ) :=
    mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, Fin N → ℂ) d.symm (d y)
  have hy : y ∈ d.source := hz.2
  have hd : d.MDifferentiable 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, Fin N → ℂ) := mdifferentiable_chart q
  have hDB : D.comp B = ContinuousLinearMap.id ℝ (Fin N → ℂ) := hd.symm_comp_deriv hy
  have hT := nativeProjectiveCoordinateMap_real_fderiv N n e p q z hz
  change fderiv ℝ (nativeClosedImmersionCoordinateMap (polynomialProjStructureMap ℂ N) e n N p q) z =
    B.comp (A.comp C) at hT
  change ((polynomialProjFubiniStudyFundamentalForm N y).compContinuousLinearMap A).compContinuousLinearMap C =
    ((polynomialProjFubiniStudyFundamentalForm N (d.symm (d y))).compContinuousLinearMap D).compContinuousLinearMap
      (fderiv ℝ (nativeClosedImmersionCoordinateMap (polynomialProjStructureMap ℂ N) e n N p q) z)
  rw [d.left_inv hy, hT]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  exact (congrArg (fun L : (Fin N → ℂ) →L[ℝ] (Fin N → ℂ) => L (A (C (v j)))) hDB).symm

/-- The literal coordinate pullback is genuinely smooth on its actual open domain. -/
theorem nativeProjectiveFubiniStudyCoordinatePullback_contDiffOn
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (q : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :
    ContDiffOn ℝ ∞ (nativeProjectiveFubiniStudyCoordinatePullback N n e p q)
      (nativeClosedImmersionCoordinateDomain (polynomialProjStructureMap ℂ N) e n N p q) := by
  let T := nativeClosedImmersionCoordinateMap (polynomialProjStructureMap ℂ N) e n N p q
  let S := nativeClosedImmersionCoordinateDomain (polynomialProjStructureMap ℂ N) e n N p q
  have hT : ContDiffOn ℝ ∞ T S :=
    (nativeClosedImmersionCoordinateMap_contDiffOn (polynomialProjStructureMap ℂ N) e n N p q ∞).restrict_scalars ℝ
  have hA : ContDiffOn ℝ ∞ (fun z => polynomialProjFubiniStudyFormStandardCoefficients N q (T z)) S :=
    (polynomialProjFubiniStudyFormStandardCoefficients_contDiffOn N q).comp hT
      (fun z hz => (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q).map_source hz.2)
  exact pullbackAlternating_contDiffOn hA
    (hT.fderiv_of_isOpen (nativeClosedImmersionCoordinateDomain_isOpen
      (polynomialProjStructureMap ℂ N) e n N p q) (by simp))

/-- True preferred-chart coefficients of the actual pullback are smooth everywhere on the actual target. -/
theorem nativeProjectiveFubiniStudyPullbackCoefficients_contDiffOn
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    ContDiffOn ℝ ∞ (nativeProjectiveFubiniStudyPullbackCoefficients N n e p)
      (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).target := by
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  intro z hz
  let q := nativeProjectivePointMap N e (c.symm z)
  have hD : z ∈ nativeClosedImmersionCoordinateDomain (polynomialProjStructureMap ℂ N) e n N p q :=
    ⟨hz, schemeAnalyticCoordinateChart_point_mem_source (polynomialProjStructureMap ℂ N) N q⟩
  have hs := nativeClosedImmersionCoordinateDomain_eventually (polynomialProjStructureMap ℂ N) e n N p q z hD
  have heq : nativeProjectiveFubiniStudyPullbackCoefficients N n e p =ᶠ[𝓝 z]
      nativeProjectiveFubiniStudyCoordinatePullback N n e p q := by
    filter_upwards [hs] with w hw
    exact nativeProjectiveFubiniStudyPullbackCoefficients_readback N n e p q w hw
  exact ((nativeProjectiveFubiniStudyCoordinatePullback_contDiffOn N n e p q).contDiffAt hs)
    |>.congr_of_eventuallyEq heq |>.contDiffWithinAt

/-- Actual exterior differentiation of the actual source coefficients vanishes. -/
theorem nativeProjectiveFubiniStudyPullbackCoefficients_closed
    (p : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (z : Fin n → ℂ)
    (hz : z ∈ (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).target) :
    extDeriv (nativeProjectiveFubiniStudyPullbackCoefficients N n e p) z = 0 := by
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  let q := nativeProjectivePointMap N e (c.symm z)
  let T := nativeClosedImmersionCoordinateMap (polynomialProjStructureMap ℂ N) e n N p q
  have hD : z ∈ nativeClosedImmersionCoordinateDomain (polynomialProjStructureMap ℂ N) e n N p q :=
    ⟨hz, schemeAnalyticCoordinateChart_point_mem_source (polynomialProjStructureMap ℂ N) N q⟩
  have hs := nativeClosedImmersionCoordinateDomain_eventually (polynomialProjStructureMap ℂ N) e n N p q z hD
  have heq : nativeProjectiveFubiniStudyPullbackCoefficients N n e p =ᶠ[𝓝 z]
      nativeProjectiveFubiniStudyCoordinatePullback N n e p q := by
    filter_upwards [hs] with w hw
    exact nativeProjectiveFubiniStudyPullbackCoefficients_readback N n e p q w hw
  rw [heq.extDeriv_eq]
  have hT : ContDiffAt ℝ ∞ T z :=
    ((nativeClosedImmersionCoordinateMap_contDiffOn (polynomialProjStructureMap ℂ N) e n N p q ∞).restrict_scalars ℝ).contDiffAt hs
  have ht : T z ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q).target :=
    (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q).map_source hD.2
  have hA := (polynomialProjFubiniStudyFormStandardCoefficients_contDiffOn N q).contDiffAt
    ((schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ N) N q).open_target.mem_nhds ht)
  change extDeriv (fun w => (polynomialProjFubiniStudyFormStandardCoefficients N q (T w)).compContinuousLinearMap
    (fderiv ℝ T w)) z = 0
  rw [extDeriv_pullback (hA.differentiableAt (by simp)) hT
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
    polynomialProjFubiniStudyFormStandardCoefficients_closed N q (T z) ht]
  rfl

/-- The genuine two-form, as an actual native bilinear Hom fiber. -/
def nativeProjectiveFubiniStudyPullbackBilinear
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ] ℝ := by
  change (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ
  exact nativeAlternatingBilinearCLM n (nativeProjectiveFubiniStudyFundamentalPullback N n e x)

omit [IsClosedImmersion e] in
/-- Its bilinear readback is exactly the literal alternating-form evaluation. -/
theorem nativeProjectiveFubiniStudyPullbackBilinear_apply
    (x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    nativeProjectiveFubiniStudyPullbackBilinear N n e x v w =
      nativeProjectiveFubiniStudyFundamentalPullback N n e x ![v, w] :=
  nativeAlternatingBilinearCLM_apply n _ _ _

omit [IsClosedImmersion e] in
/-- Actual preferred tangent trivializations are the actual inverse-chart derivatives. -/
theorem nativeProjectivePullback_standard_symmL
    (p x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (hx : x ∈ (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).source) :
    (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x =
      mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).symm
          (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p x) := by
  have h := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, Fin n → ℂ)) (x₀ := p) (x := x) hx
  simp only [mfld_simps, mfderivWithin_univ] at h
  convert! h using 1

omit [IsClosedImmersion e] in
/-- Genuine native Hom trivializations read exactly the actual preferred-chart coefficients. -/
theorem nativeProjectiveFubiniStudyPullbackBilinear_trivialization
    (p x : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N))
    (hx : x ∈ (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p).source) :
    (trivializationAt ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p
      (TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (nativeProjectiveFubiniStudyPullbackBilinear N n e x))).2 =
      nativeAlternatingBilinearCLM n (nativeProjectiveFubiniStudyPullbackCoefficients N n e p
        (schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p x)) := by
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [nativeProjectivePullback_standard_symmL N n e p x hx]
  have hcot : x ∈ (trivializationAt ((Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p).baseSet :=
    ⟨hx, Set.mem_univ x⟩
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hcot]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [nativeProjectivePullback_standard_symmL N n e p x hx]
  have hscalar : (trivializationAt ℝ
      (fun _ : SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N) => ℝ) p).continuousLinearMapAt ℝ x =
      ContinuousLinearMap.id ℝ ℝ := by
    exact Bundle.Trivial.continuousLinearMapAt_trivialization ℝ
      (SchemeComplexPoint (e ≫ polynomialProjStructureMap ℂ N)) ℝ x
  rw [hscalar, ContinuousLinearMap.id_apply, nativeProjectiveFubiniStudyPullbackBilinear_apply,
    nativeAlternatingBilinearCLM_apply]
  change _ = ((nativeProjectiveFubiniStudyFundamentalPullback N n e (c.symm (c x))).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) c.symm (c x))) ![v, w]
  rw [c.left_inv hx, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The actual pulled-back fundamental form is a genuine smooth native bilinear Hom section. -/
theorem nativeProjectiveFubiniStudyPullbackBilinear_contMDiff :
    ContMDiff 𝓘(ℝ, Fin n → ℂ)
      (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (nativeProjectiveFubiniStudyPullbackBilinear N n e x)) := by
  intro p
  rw [contMDiffAt_section p]
  let c := schemeAnalyticCoordinateChart (e ≫ polynomialProjStructureMap ℂ N) n p
  have hp : p ∈ c.source := schemeAnalyticCoordinateChart_point_mem_source _ n p
  have heq : (fun x => (trivializationAt ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p
      (TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (nativeProjectiveFubiniStudyPullbackBilinear N n e x))).2) =ᶠ[𝓝 p]
      (fun x => nativeAlternatingBilinearCLM n (nativeProjectiveFubiniStudyPullbackCoefficients N n e p (c x))) := by
    filter_upwards [c.open_source.mem_nhds hp] with x hx
    exact nativeProjectiveFubiniStudyPullbackBilinear_trivialization N n e p x hx
  have hcoeff := (nativeProjectiveFubiniStudyPullbackCoefficients_contDiffOn N n e p).contDiffAt
    (c.open_target.mem_nhds (c.map_source hp))
  have hL : ContDiff ℝ ∞ (nativeAlternatingBilinearCLM n) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)
      (F := (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (nativeAlternatingBilinearCLM n)
  have hbil := hL.contDiffAt.comp (c p) hcoeff
  have hc : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ∞ c p :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp
  exact (hbil.contMDiffAt.comp p hc).congr_of_eventuallyEq heq

end ActualPullback

section ActualStructuralMap

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)
  (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Transport along the literal over-base equality gives the genuine form on the given source point space. -/
def ClosedProjectiveEmbedding.nativeFubiniStudyFundamentalForm :
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace f n
    (x : SchemeComplexPoint f) → TangentSpace 𝓘(ℝ, Fin n → ℂ) x [⋀^Fin 2]→L[ℝ] ℝ := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyFundamentalPullback N n e

/-- The actual given source form has the derived positive complex diagonal. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudyFundamentalForm_pos :
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace f n
    ∀ (x : SchemeComplexPoint f) (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x), v ≠ 0 →
      0 < E.nativeFubiniStudyFundamentalForm n x ![v, smoothSchemeTangentJ f n x v] := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyFundamentalPullback_complex_diagonal_pos N n e

/-- The actual given source form has genuine type-(1,1) invariance. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudyFundamentalForm_type_one_one :
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace f n
    ∀ (x : SchemeComplexPoint f) (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      E.nativeFubiniStudyFundamentalForm n x
        ![smoothSchemeTangentJ f n x v, smoothSchemeTangentJ f n x w] =
      E.nativeFubiniStudyFundamentalForm n x ![v, w] := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyFundamentalPullback_type_one_one N n e

/-- Literal inverse-chart readback of the genuine form on the actual given structural map. -/
def ClosedProjectiveEmbedding.nativeFubiniStudyFormCoefficients :
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace f n
    SchemeComplexPoint f → (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace f n
  fun p z =>
    let c := schemeAnalyticCoordinateChart f n p
    (E.nativeFubiniStudyFundamentalForm n (c.symm z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) c.symm z)

/-- The actual given source coefficients are smooth on every genuine chart target. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudyFormCoefficients_contDiffOn :
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace f n
    ∀ p : SchemeComplexPoint f,
      ContDiffOn ℝ ∞ (E.nativeFubiniStudyFormCoefficients n p)
        (schemeAnalyticCoordinateChart f n p).target := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyPullbackCoefficients_contDiffOn N n e

/-- Actual native exterior differentiation vanishes for the actual given source coefficients. -/
theorem ClosedProjectiveEmbedding.nativeFubiniStudyFormCoefficients_closed :
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace f n
    ∀ (p : SchemeComplexPoint f) (z : Fin n → ℂ),
      z ∈ (schemeAnalyticCoordinateChart f n p).target →
      extDeriv (E.nativeFubiniStudyFormCoefficients n p) z = 0 := by
  rcases E with ⟨N, e, he, h⟩
  subst f
  let : IsClosedImmersion e := he
  exact nativeProjectiveFubiniStudyPullbackCoefficients_closed N n e

/-- Actual smooth projective Fano data produce a positive closed fundamental form, without a form premise. -/
def SmoothProjectiveFano.nativeProjectiveFundamentalForm {n : ℕ} (F : SmoothProjectiveFano n) :
    let := schemeAnalyticPointTopology F.structureMap
    let := smoothSchemeComplexChartedSpace F.structureMap n
    (x : SchemeComplexPoint F.structureMap) → TangentSpace 𝓘(ℝ, Fin n → ℂ) x [⋀^Fin 2]→L[ℝ] ℝ :=
  F.projective.nativeFubiniStudyFundamentalForm n

end ActualStructuralMap

end

end SGPT.Foundations.Schemes
