import SGPT.Checks.Comparison.GFRationalHull
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

/-! ACTUAL original rational GF/hull slices have the original analytic singularity type.
Source `thm:comp_traceop`; blueprint `trace-gf-analytic-type.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsIntegral X]

local instance traceTypePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance traceTypePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance traceTypePointManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (H : SchemeLineBundleMetric f n E L)

/-- The ACTUAL original normalized physical section maximum has rational
analytic type, produced from the same actual frame coefficients and bounded
metric remainder, including every common zero locus and dimension zero. -/
theorem normalized_sectionMaximum_hasManifoldAnalyticSingularityType
    [IsSeparated f] [QuasiCompact f]
    (a : LineBundleAtlas L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N) :
    HasManifoldAnalyticSingularityType (n := n)
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E a N t H p) := by
  intro e z hz
  obtain ⟨j, _hx, U, R, C, hU, hxU, hUa, hRC, heq⟩ :=
    exists_local_presentation f n E a N t H (e.val.symm z)
  let g : Fin (Fintype.card J) → SchemeComplexPoint f → ℂ :=
    fun k => frameCoeff f n E a N t j ((Fintype.equivFin J).symm k)
  have hgd : ∀ k, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g k) U := by
    intro k y hy
    exact ((frameCoeff_holomorphicAt f n E a N t j _ (hUa hy)).self_of_nhds).mdifferentiableWithinAt
  have hV : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) := e.val.isOpen_inter_preimage_symm hU
  have hzV : z ∈ e.val.target ∩ e.val.symm ⁻¹' U := ⟨hz, hxU⟩
  have hC : 0 ≤ C := (abs_nonneg _).trans (hRC _ hxU)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  refine ⟨(K : ℚ)⁻¹, Fintype.card J, fun k w => g k (e.val.symm w), ?_⟩
  refine ⟨by simpa only [Rat.cast_inv, Rat.cast_natCast] using inv_pos.mpr hKR,
    ⟨_, hV, hzV, fun k =>
      QuasiEquisingularApproximationDemailly.differentiableOn_comp_symm hU (hgd k)⟩,
    fun w => (K : ℝ)⁻¹ * R (e.val.symm w),
    ⟨(K : ℝ)⁻¹ * C, mul_nonneg (inv_nonneg.mpr hKR.le) hC, ?_⟩, ?_⟩
  · filter_upwards [hV.mem_nhds hzV] with w hw
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hKR.le)]
    exact mul_le_mul_of_nonneg_left (hRC _ hw.2) (inv_nonneg.mpr hKR.le)
  · filter_upwards [hV.mem_nhds hzV] with w hw
    change (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E a N t H (e.val.symm w) = _
    rw [heq _ hw.2]
    simp only [Rat.cast_inv, Rat.cast_natCast]
    rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr hKR.le)) (EReal.coe_ne_top _), ← EReal.coe_mul]
    rfl

/-- The ORIGINAL regularized hull has the actual rational analytic type,
manufactured from its original common-degree products rather than supplied
as a hypothesis. -/
theorem originalHull_hasManifoldAnalyticSingularityType [IsProper f]
    (a : LineBundleAtlas L) (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ j, ∃ q : ℚ, D.τ j = q)
    (I : Fin (D.N + 1) → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (t : (j : Fin (D.N + 1)) → I j → bundlePowerGlobalSections L N)
    (ht : ∀ j k, t j k ≠ 0)
    (hA : ∀ j, D.A j = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun k => H.sectionLogNormSq a N (t j k)) p)
    (q : ℚ) (hq : (q : ℝ) ≤ D.τ 0) :
    HasManifoldAnalyticSingularityType (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ))) := by
  obtain ⟨Q, hQ, F, _hF, heq, _hval⟩ :=
    exists_originalHull_commonSectionFamily n E H a N K hK D hτ I t ht hA q hq
  rw [heq]
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    normalized_sectionMaximum_hasManifoldAnalyticSingularityType f n E H a
      (N * Q) (K * Q) (Nat.mul_pos hK hQ) F.sections

/-- The SAME actual hull slice retains its original rational analytic type
under EVERY actual holomorphic restriction, in particular the actual map
from the original resolution target. No analytic-type certificate input. -/
theorem originalHull_restriction_hasManifoldAnalyticSingularityType [IsProper f]
    (a : LineBundleAtlas L) (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ j, ∃ q : ℚ, D.τ j = q)
    (I : Fin (D.N + 1) → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (t : (j : Fin (D.N + 1)) → I j → bundlePowerGlobalSections L N)
    (ht : ∀ j k, t j k ≠ 0)
    (hA : ∀ j, D.A j = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun k => H.sectionLogNormSq a N (t j k)) p)
    (q : ℚ) (hq : (q : ℝ) ≤ D.τ 0)
    {V : Type*} {k : ℕ} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι) :
    HasManifoldAnalyticSingularityType (n := k)
      (fun y => uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)) (ι y)) :=
  AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hι
    (originalHull_hasManifoldAnalyticSingularityType f n E H a N K hK D hτ I t ht hA q hq)

end SGPT.NAPotential.TraceComparison
