import SGPT.Foundations.Schemes.ProjectiveAnalyticRatioCharts
import SGPT.Foundations.Schemes.SchemeAffineEvaluationGerms
import SGPT.Foundations.Schemes.SchemeRealManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Actual projective ratio charts in the scheme-derived maximal atlas

Every mixed transition is analytic because its actual affine regular-function
evaluations are genuine fractions of the other actual chart evaluations.
The actual ratio charts therefore belong to the existing maximal atlas.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold
open scoped Topology

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialProjStandardToRatioTransition (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm.trans
    (polynomialProjRatioChart n i)

def polynomialProjRatioToStandardTransition (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (polynomialProjRatioChart n i).symm.trans
    (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p)

theorem polynomialProjStandardToRatioTransition_analyticOnNhd (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    AnalyticOnNhd ℂ (polynomialProjStandardToRatioTransition n p i)
      (polynomialProjStandardToRatioTransition n p i).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let f := polynomialProjStructureMap ℂ n
  let c := polynomialProjComplexAffineChart n i
  let d := (standardSmoothComplexAffineChart f n p).val
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  intro t ht
  change t ∈ (schemeAnalyticCoordinateChart f n p).target ∧
    (schemeAnalyticCoordinateChart f n p).symm t ∈ (polynomialProjRatioChart n i).source at ht
  let E := fun u => polynomialProjRatioAffineSourcePoint n i
    ((schemeAnalyticCoordinateChart f n p).symm u)
  let G := schemeAnalyticCoordinateAffineInversePoint f n p
  have hs : ∀ᶠ u in 𝓝 t, (schemeAnalyticCoordinateChart f n p).symm u ∈
      (polynomialProjRatioChart n i).source :=
    Filter.Tendsto.eventually ((schemeAnalyticCoordinateChart f n p).continuousAt_symm ht.1)
      ((polynomialProjRatioChart n i).open_source.mem_nhds ht.2)
  have hxy : (fun u => complexAffineChartPointMap f d (G u)) =ᶠ[𝓝 t]
      (fun u => complexAffineChartPointMap f c (E u)) := by
    filter_upwards [hs] with u hu
    exact (schemeAnalyticCoordinateAffineInversePoint_map f n p u).trans
      (polynomialProjRatioAffineSourcePoint_map n i _ hu).symm
  have hG : ∀ a : d.ring, AnalyticAt ℂ
      (fun u => affineSchemePointEquivOfStructure (d.map ≫ f) (G u) a) t := by
    intro a
    change AnalyticAt ℂ (fun u => affineSchemePointHomeomorphOfStructure (d.map ≫ f) (G u) a) t
    simpa [G, d, schemeAnalyticCoordinateAffineInversePoint] using
      schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p a t ht.1
  apply AnalyticAt.pi
  intro a
  have ha := complexAffineEvaluation_analyticAt f c d n E G t hxy hG
    (polynomialProjCoordinateRatio ℂ n i (i.succAbove a))
  apply ha.congr
  exact Filter.Eventually.of_forall (fun u => polynomialProjRatioAffineSourcePoint_eval n i
    ((schemeAnalyticCoordinateChart f n p).symm u) a)

theorem polynomialProjRatioToStandardTransition_analyticOnNhd (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    AnalyticOnNhd ℂ (polynomialProjRatioToStandardTransition n i p)
      (polynomialProjRatioToStandardTransition n i p).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let f := polynomialProjStructureMap ℂ n
  let c := (standardSmoothComplexAffineChart f n p).val
  let d := polynomialProjComplexAffineChart n i
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  intro t ht
  change t ∈ (polynomialProjRatioChart n i).target ∧
    (polynomialProjRatioChart n i).symm t ∈ (schemeAnalyticCoordinateChart f n p).source at ht
  let E := fun u => schemeAnalyticCoordinateAffineSourcePoint f n p
    ((polynomialProjRatioChart n i).symm u)
  let G := polynomialProjRatioAffineInverse n i
  have hs : ∀ᶠ u in 𝓝 t, (polynomialProjRatioChart n i).symm u ∈
      (schemeAnalyticCoordinateChart f n p).source :=
    Filter.Tendsto.eventually ((polynomialProjRatioChart n i).continuousAt_symm ht.1)
      ((schemeAnalyticCoordinateChart f n p).open_source.mem_nhds ht.2)
  have hxy : (fun u => complexAffineChartPointMap f d (G u)) =ᶠ[𝓝 t]
      (fun u => complexAffineChartPointMap f c (E u)) := by
    filter_upwards [hs] with u hu
    exact (congrFun (polynomialProjRatioChart_symm n i) u).symm.trans
      (schemeAnalyticCoordinateAffineSourcePoint_map f n p _ hu).symm
  have hG : ∀ a : d.ring, AnalyticAt ℂ
      (fun u => affineSchemePointEquivOfStructure (d.map ≫ f) (G u) a) t := by
    intro a
    exact polynomialProjRatioAffineInverse_eval_analyticOnNhd n i a t (Set.mem_univ t)
  apply AnalyticAt.pi
  intro a
  have ha := complexAffineEvaluation_analyticAt f c d n E G t hxy hG
    (standardSmoothComplexChartFreeGenerator f n p a)
  apply ha.congr
  filter_upwards [hs] with u hu
  calc
    affineSchemePointEquivOfStructure (c.map ≫ f) (E u)
        (standardSmoothComplexChartFreeGenerator f n p a) =
      standardSmoothComplexPointOpenChart f n p ((polynomialProjRatioChart n i).symm u)
        (standardSmoothComplexChartFreeGenerator f n p a) := by
          change (affineSchemePointHomeomorphOfStructure (c.map ≫ f)
            ((affineSchemePointHomeomorphOfStructure (c.map ≫ f)).symm _)) _ = _
          rw [Homeomorph.apply_symm_apply]
    _ = polynomialProjRatioToStandardTransition n i p u a :=
      (schemeAnalyticCoordinateChart_apply f n p _ hu a).symm

theorem polynomialProjStandardToRatioTransition_contDiffOn (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ContDiffOn ℂ k (polynomialProjStandardToRatioTransition n p i)
      (polynomialProjStandardToRatioTransition n p i).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (polynomialProjStandardToRatioTransition_analyticOnNhd n p i).contDiffOn
    (polynomialProjStandardToRatioTransition n p i).open_source.uniqueDiffOn

theorem polynomialProjRatioToStandardTransition_contDiffOn (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ContDiffOn ℂ k (polynomialProjRatioToStandardTransition n i p)
      (polynomialProjRatioToStandardTransition n i p).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (polynomialProjRatioToStandardTransition_analyticOnNhd n i p).contDiffOn
    (polynomialProjRatioToStandardTransition n i p).open_source.uniqueDiffOn

theorem polynomialProjStandardToRatioTransition_symm (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    (polynomialProjStandardToRatioTransition n p i).symm =
      polynomialProjRatioToStandardTransition n i p := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rfl

theorem polynomialProjStandardToRatioTransition_mem_contDiffGroupoid (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    polynomialProjStandardToRatioTransition n p i ∈ contDiffGroupoid k 𝓘(ℂ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      polynomialProjStandardToRatioTransition_contDiffOn n p i k
  · have h := polynomialProjRatioToStandardTransition_contDiffOn n i p k
    have ht : (polynomialProjStandardToRatioTransition n p i).target =
        (polynomialProjRatioToStandardTransition n i p).source := rfl
    simpa only [contDiffPregroupoid, mfld_simps,
      polynomialProjStandardToRatioTransition_symm, ht] using h

theorem polynomialProjStandardToRatioTransition_mem_real_contDiffGroupoid (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    polynomialProjStandardToRatioTransition n p i ∈ contDiffGroupoid k 𝓘(ℝ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      (polynomialProjStandardToRatioTransition_contDiffOn n p i k).restrict_scalars ℝ
  · have h := (polynomialProjRatioToStandardTransition_contDiffOn n i p k).restrict_scalars ℝ
    have ht : (polynomialProjStandardToRatioTransition n p i).target =
        (polynomialProjRatioToStandardTransition n i p).source := rfl
    simpa only [contDiffPregroupoid, mfld_simps,
      polynomialProjStandardToRatioTransition_symm, ht] using h

/-- These genuine charts belong to the existing scheme-derived complex maximal atlas. -/
theorem polynomialProjRatioChart_mem_maximalAtlas (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    polynomialProjRatioChart n i ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) k
      (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro e he
  change e ∈ Set.range (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n) at he
  obtain ⟨p, rfl⟩ := he
  have h := polynomialProjStandardToRatioTransition_mem_contDiffGroupoid n p i k
  exact ⟨(contDiffGroupoid k 𝓘(ℂ, Fin n → ℂ)).symm h, h⟩

/-- Their real maximal-atlas membership is derived in the same existing charted space. -/
theorem polynomialProjRatioChart_mem_real_maximalAtlas (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    polynomialProjRatioChart n i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℂ) k
      (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro e he
  change e ∈ Set.range (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n) at he
  obtain ⟨p, rfl⟩ := he
  have h := polynomialProjStandardToRatioTransition_mem_real_contDiffGroupoid n p i k
  exact ⟨(contDiffGroupoid k 𝓘(ℝ, Fin n → ℂ)).symm h, h⟩

theorem polynomialProjRatioChart_contMDiffOn (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) k (polynomialProjRatioChart n i)
      (polynomialProjRatioChart n i).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  exact contMDiffOn_of_mem_maximalAtlas (polynomialProjRatioChart_mem_maximalAtlas n i k)

theorem polynomialProjRatioChart_symm_contMDiffOn (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) k (polynomialProjRatioChart n i).symm
      (polynomialProjRatioChart n i).target := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  exact contMDiffOn_symm_of_mem_maximalAtlas (polynomialProjRatioChart_mem_maximalAtlas n i k)

theorem polynomialProjRatioChart_real_contMDiffOn (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    ContMDiffOn 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) k (polynomialProjRatioChart n i)
      (polynomialProjRatioChart n i).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  exact contMDiffOn_of_mem_maximalAtlas (polynomialProjRatioChart_mem_real_maximalAtlas n i k)

theorem polynomialProjRatioChart_symm_real_contMDiffOn (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    ContMDiffOn 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) k (polynomialProjRatioChart n i).symm
      (polynomialProjRatioChart n i).target := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  exact contMDiffOn_symm_of_mem_maximalAtlas (polynomialProjRatioChart_mem_real_maximalAtlas n i k)

theorem polynomialProjRatioChart_mdifferentiable (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    (polynomialProjRatioChart n i).MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  exact ⟨(polynomialProjRatioChart_contMDiffOn n i 1).mdifferentiableOn one_ne_zero,
    (polynomialProjRatioChart_symm_contMDiffOn n i 1).mdifferentiableOn one_ne_zero⟩

theorem polynomialProjRatioChart_real_mdifferentiable (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    (polynomialProjRatioChart n i).MDifferentiable 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  exact ⟨(polynomialProjRatioChart_real_contMDiffOn n i 1).mdifferentiableOn one_ne_zero,
    (polynomialProjRatioChart_symm_real_contMDiffOn n i 1).mdifferentiableOn one_ne_zero⟩

/-- The actual native real chart derivative is a genuine tangent equivalence. -/
def polynomialProjRatioChartRealTangentEquiv (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    p ∈ (polynomialProjRatioChart n i).source →
      TangentSpace 𝓘(ℝ, Fin n → ℂ) p ≃L[ℝ] (Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  let := smoothSchemeReal_isManifold (polynomialProjStructureMap ℂ n) n 1
  intro hp
  exact (polynomialProjRatioChart_real_mdifferentiable n i).mfderiv hp

theorem polynomialProjRatioChartRealTangentEquiv_apply (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    letI := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
    ∀ (hp : p ∈ (polynomialProjRatioChart n i).source)
      (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) p),
      polynomialProjRatioChartRealTangentEquiv n i p hp v =
        mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p v := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n
  intro hp v
  rfl

end

end SGPT.Foundations.Schemes
