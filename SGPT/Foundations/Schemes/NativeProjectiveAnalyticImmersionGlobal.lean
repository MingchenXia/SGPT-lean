import SGPT.Foundations.Schemes.NativeProjectiveAnalyticMorphismGerms
import SGPT.Foundations.Schemes.SchemeTangentComplex
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Native smoothness and tangent injectivity of an actual closed immersion

The literal map on complex scheme points is smooth in the already constructed
native charted spaces. Its native derivatives are the actual coordinate
derivatives proved by genuine principal-refinement retraction germs.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold
open scoped Topology

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
  (n m : ℕ) [SmoothOfRelativeDimension n (i ≫ f)] [SmoothOfRelativeDimension m f]

/-- The literal actual scheme-point map is native complex smooth in every order. -/
theorem nativeClosedImmersionComplexPoint_contMDiff (k : WithTop ℕ∞) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) k
      (schemeComplexPointMap (i ≫ f) f i rfl) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  let := smoothSchemeComplex_isManifold (i ≫ f) n k
  let := smoothSchemeComplex_isManifold f m k
  rw [contMDiff_iff]
  refine ⟨closedImmersionComplexPointMap_continuous f i, ?_⟩
  intro p q
  simpa only [mfld_simps, smoothSchemeComplexChartedSpace_chartAt,
    nativeClosedImmersionCoordinateMap, nativeClosedImmersionCoordinateDomain,
    Function.comp_def, Set.preimage] using
    nativeClosedImmersionCoordinateMap_contDiffOn f i n m p q k

/-- The literal actual scheme-point map is native real smooth in every order. -/
theorem nativeClosedImmersionRealPoint_contMDiff (k : WithTop ℕ∞) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ) k
      (schemeComplexPointMap (i ≫ f) f i rfl) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  let := smoothSchemeReal_isManifold (i ≫ f) n k
  let := smoothSchemeReal_isManifold f m k
  rw [contMDiff_iff]
  refine ⟨closedImmersionComplexPointMap_continuous f i, ?_⟩
  intro p q
  simpa only [mfld_simps, smoothSchemeComplexChartedSpace_chartAt,
    nativeClosedImmersionCoordinateMap, nativeClosedImmersionCoordinateDomain,
    Function.comp_def, Set.preimage] using
    (nativeClosedImmersionCoordinateMap_contDiffOn f i n m p q k).restrict_scalars ℝ

/-- Its genuine complex manifold derivative is the actual preferred-chart derivative. -/
theorem nativeClosedImmersionComplexPoint_mfderiv (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ)
      (schemeComplexPointMap (i ≫ f) f i rfl) p =
    fderiv ℂ (nativeClosedImmersionCoordinateMap f i n m p
      (schemeComplexPointMap (i ≫ f) f i rfl p))
      (schemeAnalyticCoordinateChart (i ≫ f) n p p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  have hd := (nativeClosedImmersionComplexPoint_contMDiff f i n m 1).mdifferentiable
    (by norm_num) p
  simp only [mfderiv, hd, ↓reduceIte, mfld_simps, fderivWithin_univ,
    smoothSchemeComplexChartedSpace_chartAt, nativeClosedImmersionCoordinateMap, Function.comp_def]

/-- Its genuine real manifold derivative is the actual preferred-chart real derivative. -/
theorem nativeClosedImmersionRealPoint_mfderiv (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ)
      (schemeComplexPointMap (i ≫ f) f i rfl) p =
    fderiv ℝ (nativeClosedImmersionCoordinateMap f i n m p
      (schemeComplexPointMap (i ≫ f) f i rfl p))
      (schemeAnalyticCoordinateChart (i ≫ f) n p p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  have hd := (nativeClosedImmersionRealPoint_contMDiff f i n m 1).mdifferentiable
    (by norm_num) p
  simp only [mfderiv, hd, ↓reduceIte, mfld_simps, fderivWithin_univ,
    smoothSchemeComplexChartedSpace_chartAt, nativeClosedImmersionCoordinateMap, Function.comp_def]

/-- The genuine complex tangent derivative has a derived continuous-linear left inverse. -/
theorem exists_nativeClosedImmersionComplexPoint_mfderiv_leftInverse
    (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    ∃ L : TangentSpace 𝓘(ℂ, Fin m → ℂ) (schemeComplexPointMap (i ≫ f) f i rfl p)
        →L[ℂ] TangentSpace 𝓘(ℂ, Fin n → ℂ) p,
      L.comp (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ)
        (schemeComplexPointMap (i ≫ f) f i rfl) p) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, Fin n → ℂ) p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  dsimp only
  rw [nativeClosedImmersionComplexPoint_mfderiv f i n m p]
  exact exists_nativeClosedImmersionCoordinateMap_fderiv_leftInverse f i n m p
    (schemeComplexPointMap (i ≫ f) f i rfl p) _
    (nativeClosedImmersionCoordinateDomain_point_mem f i n m p)

/-- The actual complex native tangent map of the closed immersion is injective. -/
theorem nativeClosedImmersionComplexPoint_mfderiv_injective
    (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    Function.Injective (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ)
      (schemeComplexPointMap (i ≫ f) f i rfl) p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  dsimp only
  rw [nativeClosedImmersionComplexPoint_mfderiv f i n m p]
  exact nativeClosedImmersionCoordinateMap_fderiv_injective f i n m p
    (schemeComplexPointMap (i ≫ f) f i rfl p) _
    (nativeClosedImmersionCoordinateDomain_point_mem f i n m p)

/-- The actual real tangent derivative is the scalar restriction of the actual complex one. -/
theorem nativeClosedImmersionRealPoint_mfderiv_restrictScalars
    (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ)
      (schemeComplexPointMap (i ≫ f) f i rfl) p =
      (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ)
        (schemeComplexPointMap (i ≫ f) f i rfl) p).restrictScalars ℝ := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  dsimp only
  rw [nativeClosedImmersionRealPoint_mfderiv f i n m p,
    nativeClosedImmersionComplexPoint_mfderiv f i n m p]
  exact (nativeClosedImmersionCoordinateMap_analyticOnNhd f i n m p
    (schemeComplexPointMap (i ≫ f) f i rfl p) _
    (nativeClosedImmersionCoordinateDomain_point_mem f i n m p)).differentiableAt.fderiv_restrictScalars ℝ

/-- Restricting the genuine complex left inverse gives a genuine real tangent left inverse. -/
theorem exists_nativeClosedImmersionRealPoint_mfderiv_leftInverse
    (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    ∃ L : TangentSpace 𝓘(ℝ, Fin m → ℂ) (schemeComplexPointMap (i ≫ f) f i rfl p)
        →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℂ) p,
      L.comp (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ)
        (schemeComplexPointMap (i ≫ f) f i rfl) p) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  dsimp only
  obtain ⟨L, hL⟩ := exists_nativeClosedImmersionComplexPoint_mfderiv_leftInverse f i n m p
  refine ⟨L.restrictScalars ℝ, ?_⟩
  rw [nativeClosedImmersionRealPoint_mfderiv_restrictScalars f i n m p]
  ext v
  exact congrArg (fun A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => A v) hL

/-- The actual real native tangent map of the closed immersion is injective. -/
theorem nativeClosedImmersionRealPoint_mfderiv_injective
    (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    Function.Injective (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ)
      (schemeComplexPointMap (i ≫ f) f i rfl) p) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  dsimp only
  rw [nativeClosedImmersionRealPoint_mfderiv_restrictScalars f i n m p]
  exact nativeClosedImmersionComplexPoint_mfderiv_injective f i n m p

/-- The actual tangent map intertwines the two derived native complex structures. -/
theorem nativeClosedImmersionRealPoint_mfderiv_commutes_J
    (p : SchemeComplexPoint (i ≫ f)) :
    let := schemeAnalyticPointTopology (i ≫ f)
    let := schemeAnalyticPointTopology f
    let := smoothSchemeComplexChartedSpace (i ≫ f) n
    let := smoothSchemeComplexChartedSpace f m
    ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℂ) p,
      mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ)
        (schemeComplexPointMap (i ≫ f) f i rfl) p (smoothSchemeTangentJ (i ≫ f) n p v) =
      smoothSchemeTangentJ f m (schemeComplexPointMap (i ≫ f) f i rfl p)
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin m → ℂ)
          (schemeComplexPointMap (i ≫ f) f i rfl) p v) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let := smoothSchemeComplexChartedSpace (i ≫ f) n
  let := smoothSchemeComplexChartedSpace f m
  dsimp only
  change ∀ v : Fin n → ℂ, _
  intro v
  rw [nativeClosedImmersionRealPoint_mfderiv_restrictScalars f i n m p]
  change (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ)
    (schemeComplexPointMap (i ≫ f) f i rfl) p) (Complex.I • v) =
    Complex.I • (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ)
      (schemeComplexPointMap (i ≫ f) f i rfl) p) v
  exact map_smul _ _ _

end

end SGPT.Foundations.Schemes
