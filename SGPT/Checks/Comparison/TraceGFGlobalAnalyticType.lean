import SGPT.Checks.Comparison.TraceAnalytificationPullback
import SGPT.Checks.Comparison.TraceGFAnalyticType
import SGPT.Foundations.Analysis.Pending.IdealComparisonResidual
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction

/-! Global analytic type of the ACTUAL original physical maximum in its SAME whole ideal.
Source `thm:comp_traceop`; blueprint `trace-gf-global-ideal-type.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.GfIm
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves GlobalAnalyticSingularities
open scoped Topology Manifold ContDiff

section Germs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

private theorem spanGerms_range_eq_span {J : Type*} (g : J → M → ℂ) (x : M)
    (hg : ∀ j, HolomorphicAt n (g j) x) :
    spanGerms (n := n) (· ∈ range g) x =
      Ideal.span (range fun j => NativeHolGerm.mk (g j) (hg j)) := by
  unfold spanGerms
  congr 1
  ext γ
  constructor
  · rintro ⟨s, hs, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨g j, hg j, ⟨j, rfl⟩, rfl⟩

end Germs

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsIntegral X]
  [IsSeparated f] [QuasiCompact f]

local instance traceGlobalTypeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance traceGlobalTypeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance traceGlobalTypeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

omit [IsIntegral X] in
/-- The original physical frame coefficients generate the WHOLE original
analytic section ideal on the actual frame open; no generator square is supplied. -/
theorem analyticIdeal_sectionFamily_frame_generation (a : LineBundleAtlas L) (N : ℕ)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (j : a.I) (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ a.opens j)
    (h : SchemeComplexPoint f → ℂ) :
    (analytificationIdeal f n E (sectionsIdeal a N t)).mem x h ↔
      IsInSpanAt (n := n) (· ∈ range fun r : Fin (Fintype.card J) =>
        frameCoeff f n E a N t j ((Fintype.equivFin J).symm r)) x h := by
  let g : Fin (Fintype.card J) → SchemeComplexPoint f → ℂ :=
    fun r => frameCoeff f n E a N t j ((Fintype.equivFin J).symm r)
  have hg : ∀ r, HolomorphicAt n (g r) x :=
    fun r => frameCoeff_holomorphicAt f n E a N t j _ hx
  have hwhole : anGerms f n E (sectionsIdeal a N t) x =
      spanGerms (n := n) (· ∈ range g) x := by
    rw [anGerms_sectionsIdeal f n E a N t j hx, spanGerms_range_eq_span g x hg]
    congr 1
    ext γ
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨Fintype.equivFin J r, ?_⟩
      simp only [g, Equiv.symm_apply_apply]
    · rintro ⟨r, rfl⟩
      exact ⟨(Fintype.equivFin J).symm r, rfl⟩
  constructor
  · intro hh
    have hmem := (mem_analytificationIdeal_iff_mk f n E _ x hh.1).mp hh
    rw [hwhole] at hmem
    exact isInSpanAt_of_mk_mem_spanGerms hh.1 hmem
  · intro hh
    have hmem := mk_mem_spanGerms_of_isInSpanAt
      (fun s hs => by rcases hs with ⟨r, rfl⟩; exact hg r) hh
    rw [← hwhole] at hmem
    exact (mem_analytificationIdeal_iff_mk f n E _ x hh.1).mpr hmem

variable (H : SchemeLineBundleMetric f n E L)

/-- The ACTUAL unnormalized physical maximum has global type1 in its
SAME entire original section ideal; coherence and every generator are produced. -/
theorem sectionMaximum_has_global_actual_ideal_type (a : LineBundleAtlas L) (N : ℕ)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N) :
    HasAnalyticSingularitiesOfType (n := n) (sectionsMaxLog f n E a N t H) 1
      (analytificationIdeal f n E (sectionsIdeal a N t)) := by
  have hlocal (x : SchemeComplexPoint f) := exists_local_presentation f n E a N t H x
  have hcoh : (analytificationIdeal f n E (sectionsIdeal a N t)).IsCoherent := by
    intro x
    obtain ⟨j, hx, U, R, C, hU, hxU, hUa, hRC, heq⟩ := hlocal x
    refine ⟨U, hU, hxU, Fintype.card J,
      fun r => frameCoeff f n E a N t j ((Fintype.equivFin J).symm r), ?_, ?_⟩
    · intro r y hy
      exact ((frameCoeff_holomorphicAt f n E a N t j _ (hUa hy)).self_of_nhds).mdifferentiableWithinAt
    · intro y hy h
      exact analyticIdeal_sectionFamily_frame_generation f n E a N t j y (hUa hy) h
  refine ⟨by norm_num, hcoh, fun x => ?_⟩
  obtain ⟨j, hx, U, R, C, hU, hxU, hUa, hRC, heq⟩ := hlocal x
  refine ⟨U, hU, hxU, Fintype.card J,
    fun r => frameCoeff f n E a N t j ((Fintype.equivFin J).symm r), ?_, ?_, R, C, hRC, ?_⟩
  · intro r y hy
    exact ((frameCoeff_holomorphicAt f n E a N t j _ (hUa hy)).self_of_nhds).mdifferentiableWithinAt
  · intro y hy h
    exact analyticIdeal_sectionFamily_frame_generation f n E a N t j y (hUa hy) h
  · intro y hy
    simpa only [Rat.cast_one, EReal.coe_one, one_mul] using heq y hy

/-- The ORIGINAL normalization is exactly the rational coefficient1/K in
the SAME whole original ideal, including zero terms/common zero loci. -/
theorem normalized_sectionMaximum_has_global_actual_ideal_type
    (a : LineBundleAtlas L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N) :
    HasAnalyticSingularitiesOfType (n := n)
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E a N t H p)
      (K : ℚ)⁻¹ (analytificationIdeal f n E (sectionsIdeal a N t)) := by
  have hk : 0 < (K : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hK)
  simpa only [Rat.cast_inv, Rat.cast_natCast, mul_one] using
    IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul hk
      (sectionMaximum_has_global_actual_ideal_type f n E H a N t)

section Restriction

variable {Y : Scheme.{0}} (i : Y ⟶ X) (k : ℕ)
  [SmoothOfRelativeDimension k (i ≫ f)] [IsSeparated (i ≫ f)] [QuasiCompact (i ≫ f)]
  (EY : ClosedProjectiveEmbedding (i ≫ f))

local instance traceGlobalRestTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticPointTopology (i ≫ f)
local instance traceGlobalRestCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceGlobalRestManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (i ≫ f) k

/-- The LITERAL original physical analytic restriction has global type1/K
in the TRUE entire restricted ideal. The actual whole ideal functoriality
and holomorphicity are produced internally from the original scheme map. -/
theorem normalized_sectionMaximum_restriction_has_global_actual_ideal_type
    (a : LineBundleAtlas L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N) :
    HasAnalyticSingularitiesOfType (n := k)
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p))
      (K : ℚ)⁻¹ (analytificationIdeal (i ≫ f) k EY ((sectionsIdeal a N t).comap i)) := by
  have h := AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp
    (schemeComplexPointMap_contMDiff f i k n ∞)
    (normalized_sectionMaximum_has_global_actual_ideal_type f n E H a N K hK t)
  rw [← analytificationIdeal_comap f i n k E EY] at h
  exact h

end Restriction

end SGPT.NAPotential.TraceComparison
