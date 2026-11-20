import SGPT.NAPotential.FSPosMetric
import SGPT.Projective.FubiniStudy
import SGPT.Foundations.Analysis.Pending.KahlerPerturbation
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# The Chern form of the Fubini–Study metric of `𝒪_X(1)` is Kähler

Blueprint `claude-fs-pos:kahler`.

Let `X` be smooth of relative dimension `n` over `ℂ` with a closed projective embedding
`E.map : X ⟶ ℙᴺ`, and `H = fubiniStudyMetric f E n` the Fubini–Study metric of
`𝒪_X(1) = E.map^* 𝒪(1)`.

* `affineCoordMap`: the embedding in the affine coordinates of `D₊(xᵢ)`, read in a chart `e` of
  `X(ℂ)`: `z ↦ ((x_k/x_i)(e⁻¹ z))_{k ≠ i} ∈ ℂᴺ`; it is holomorphic on `e(Uᵢ(ℂ))`.
* `neg_log_frameNormSq_atlas`: in the frame `xᵢ`, the local weight of `H` is the pull-back of the
  Fubini–Study potential: `-log |xᵢ|²_H = log(1 + ∑_{k ≠ i} |x_k/x_i|²)`.
* `fubiniStudy_isKahler`: **the Chern form `H.curvature` is a Kähler form on `X(ℂ)`.**  In the
  preferred chart at a point it is the pull-back of `ddᶜ log(1 + ‖w‖²)` by `affineCoordMap`
  (holomorphic functoriality of `ddᶜ`), which is strictly positive on `ℂᴺ`
  (`SGPT.Projective.ComplexProjectiveSpace.fsPotential_strictlyPositive`), and `affineCoordMap`
  is an immersion (`eq_zero_of_fderiv_ratio_eq_zero`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.FSPos

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.Projective.ComplexProjectiveSpace
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance fsPosKahlerTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fsPosKahlerCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance fsPosKahlerManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The embedding in the affine coordinates of `D₊(xᵢ)`, read in a chart `e` of `X(ℂ)`:
`z ↦ ((x_k/x_i)(e⁻¹ z))_{k ≠ i}`. -/
def affineCoordMap (i : Fin (E.ambientDimension + 1)) (e : ComplexChart n (SchemeComplexPoint f))
    (z : ComplexModel n) : ComplexModel E.ambientDimension :=
  WithLp.toLp 2 fun a => schemeOpenRegularFunction f n E (coordOpen E i)
    (ratio E i (i.succAbove a)) (e.val.symm z)

/-- The chart image of `Uᵢ(ℂ)`. -/
def coordChartDomain (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) : Set (ComplexModel n) :=
  e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' (coordOpen E i : Set X))

omit [IsSeparated f] [QuasiCompact f] in
theorem isOpen_coordChartDomain (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) : IsOpen (coordChartDomain f E n i e) :=
  e.val.isOpen_inter_preimage_symm
    ((coordOpen E i).isOpen.preimage (schemeComplexPointImage_continuous f))

theorem differentiableAt_affineCoordMap_apply (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) {z : ComplexModel n}
    (hz : z ∈ coordChartDomain f E n i e) (a : Fin E.ambientDimension) :
    DifferentiableAt ℂ (fun w => schemeOpenRegularFunction f n E (coordOpen E i)
      (ratio E i (i.succAbove a)) (e.val.symm w)) z :=
  FactorizedWeightForm.differentiableAt_comp_chart_symm e hz.1
    (schemeOpenRegularFunction_holomorphicAt f n E (coordOpen E i) _ (e.val.symm z)
      hz.2).mdifferentiableAt

theorem differentiableAt_affineCoordMap (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) {z : ComplexModel n}
    (hz : z ∈ coordChartDomain f E n i e) :
    DifferentiableAt ℂ (affineCoordMap f E n i e) z :=
  differentiableAt_euclidean.mpr fun a => differentiableAt_affineCoordMap_apply f E n i e hz a

theorem contDiffOn_affineCoordMap (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℂ ∞ (affineCoordMap f E n i e) (coordChartDomain f E n i e) :=
  contDiffOn_of_differentiableOn_complex
    (fun _ hz => (differentiableAt_affineCoordMap f E n i e hz).differentiableWithinAt)
    (isOpen_coordChartDomain f E n i e)

omit [IsSeparated f] [QuasiCompact f] in
/-- In the frame `xᵢ`, `∑_k |x_k/x_i|² = 1 + ‖affine coordinates‖²`. -/
theorem coordNormSq_atlas (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) {z : ComplexModel n}
    (hz : z ∈ coordChartDomain f E n i e) :
    coordNormSq f E n ((hyperplaneAtlas E).frame i) (e.val.symm z) =
      1 + ‖affineCoordMap f E n i e z‖ ^ 2 := by
  have hk : ∀ k, coordFun f E n ((hyperplaneAtlas E).frame i) k (e.val.symm z) =
      schemeOpenRegularFunction f n E (coordOpen E i) (ratio E i k) (e.val.symm z) := by
    intro k
    rw [coordFun, coordCoef_atlas]
  have hi : schemeOpenRegularFunction f n E (coordOpen E i) (ratio E i i) (e.val.symm z) = 1 := by
    rw [ratio_self]
    exact schemeOpenRegularFunction_one f n E (coordOpen E i) hz.2
  unfold coordNormSq
  simp only [hk]
  rw [Fin.sum_univ_succAbove _ i, hi, Complex.normSq_one, EuclideanSpace.norm_sq_eq]
  simp only [affineCoordMap, Complex.normSq_eq_norm_sq]

omit [IsSeparated f] [QuasiCompact f] in
/-- In the frame `xᵢ`, the weight of the Fubini–Study metric is the pull-back of the
Fubini–Study potential `log(1 + ‖w‖²)` by the affine coordinates of the embedding. -/
theorem neg_log_frameNormSq_atlas (i : Fin (E.ambientDimension + 1))
    (e : ComplexChart n (SchemeComplexPoint f)) {z : ComplexModel n}
    (hz : z ∈ coordChartDomain f E n i e) :
    -Real.log ((fubiniStudyMetric f E n).frameNormSq ((hyperplaneAtlas E).frame i)
        (e.val.symm z)) =
      fsPotential (affineCoordMap f E n i e z) := by
  rw [fubiniStudyMetric_frameNormSq, Real.log_inv, neg_neg, coordNormSq_atlas f E n i e hz,
    fsPotential]

/-- **Strict positivity of the Fubini–Study Chern form at a point**, in the preferred chart. -/
theorem fubiniStudy_strictPosAt (y : SchemeComplexPoint f) :
    KahlerPerturbation.StrictPosAt
      ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val y := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (E.ambientDimension + 1),
      schemeComplexPointImage f y ∈ coordOpen E i :=
    (hyperplaneAtlas E).covers (schemeComplexPointImage f y)
  let e : ComplexChart n (SchemeComplexPoint f) := complexChartAt (n := n) y
  let u : ComplexModel n := e.val y
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  have hu : u ∈ e.val.target := e.val.map_source hy
  have hsymm : e.val.symm u = y := e.val.left_inv hy
  have huS : u ∈ coordChartDomain f E n i e := ⟨hu, by
    show schemeComplexPointImage f (e.val.symm u) ∈ coordOpen E i
    rw [hsymm]; exact hi⟩
  have hS := isOpen_coordChartDomain f E n i e
  let T := affineCoordMap f E n i e
  have hcoeff := (fubiniStudyMetric f E n).curvature_coeff_frame (hyperplaneAtlas E)
    ((hyperplaneAtlas E).frame i) e hu huS.2
  have heq : (fun z => -Real.log ((fubiniStudyMetric f E n).frameNormSq
      ((hyperplaneAtlas E).frame i) (e.val.symm z))) =ᶠ[𝓝 u] fun z => fsPotential (T z) := by
    filter_upwards [hS.mem_nhds huS] with z hz
    exact neg_log_frameNormSq_atlas f E n i e hz
  have hcomp := HolomorphicDDC.smoothDDC_comp hS isOpen_univ (contDiffOn_affineCoordMap f E n i e)
    (contDiff_fsPotential (N := E.ambientDimension)).contDiffOn (mapsTo_univ _ _) huS
  have hT : DifferentiableAt ℂ T u := differentiableAt_affineCoordMap f E n i e huS
  intro v hv
  change 0 < (((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.coeff e u)
    ![v, Complex.I • v]
  rw [hcoeff, smoothDDC_congr heq, hcomp]
  -- the derivative of the affine coordinates does not kill `v`
  have hne : fderiv ℂ T u v ≠ 0 := by
    intro h0
    apply hv
    refine eq_zero_of_fderiv_ratio_eq_zero f E n y i hi v fun a => ?_
    have hproj : (fun w => schemeOpenRegularFunction f n E (coordOpen E i)
        (ratio E i (i.succAbove a)) (e.val.symm w)) =
        (EuclideanSpace.proj a : ComplexModel E.ambientDimension →L[ℂ] ℂ) ∘ T := by
      funext w
      rfl
    change fderiv ℂ (fun w => schemeOpenRegularFunction f n E (coordOpen E i)
      (ratio E i (i.succAbove a)) (e.val.symm w)) u v = 0
    rw [hproj, fderiv_comp u (EuclideanSpace.proj a).differentiableAt hT,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, h0, map_zero]
  have hR : fderiv ℝ T u = (fderiv ℂ T u).restrictScalars ℝ := hT.fderiv_restrictScalars ℝ
  have hvec : (fun j => fderiv ℝ T u ((![v, Complex.I • v] : Fin 2 → ComplexModel n) j)) =
      ![fderiv ℂ T u v, Complex.I • fderiv ℂ T u v] := by
    funext j
    fin_cases j
    · simp [hR]
    · simp [hR]
  change 0 < smoothDDC fsPotential (T u)
    (fun j => fderiv ℝ T u ((![v, Complex.I • v] : Fin 2 → ComplexModel n) j))
  rw [hvec]
  exact fsPotential_strictlyPositive (T u) hne

/-- **The Chern form of the Fubini–Study metric of `𝒪_X(1)` is a Kähler form on `X(ℂ)`.** -/
theorem fubiniStudy_isKahler :
    ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.IsKahler :=
  ExceptionalMetricProof.isKahler_of_isStrictlyPositive fun e z hz => by
    have h := (fubiniStudy_strictPosAt f E n (e.val.symm z)).isStrictlyPositive e
      (e.val.map_target hz)
    rwa [e.val.right_inv hz] at h

end SGPT.NAPotential.FSPos
