import SGPT.TestCurve.SkodaRWNReduction
import SGPT.NAPotential.GAGAMult2Algebraic
import SGPT.PSH.GlobalL2PointMain
import SGPT.PSH.GlobalL2SectionsPosMass

/-!
# The point extension for algebraic sections from GAGA for `H⁰(X, L^k)`

The first analytic input of [RWN14, Proposition 7.11] in `SkodaRWNReduction` is
`SchemePointExtension`: the uniform `L²` extension from a point by *algebraic* sections of `L^k`.
This file derives it from

* the uniform `L²` extension from a point for holomorphic sections on a compact Kähler manifold
  (`SGPT.PSH.GlobalL2.globalPointExtension`, proved; Xia, *Foundations of pluripotential theory*,
  `thm:compact-point-extension`), applied to the analytification `(L, h)^{an}` of the metrized
  algebraic line bundle (`SGPT.NAPotential.GAGAMult.schemeHermitianLineBundle`), and
* GAGA for the sections of `L^k`, `k ≫ 0`: every holomorphic section of `((L, h)^{an})^{⊗ k}` is
  the analytification of an algebraic section
  (`SGPT.NAPotential.GAGAMult.SchemeSectionsAlgebraic`, a statement that is open in this project).

## Main results

* `norm_sq_eq_sectionNormSq_of_isAnalytificationOf`: if `s = σ^{an}`, then
  `|s(p)|² = |σ|²_{h^k}(p)` at every point.
* **`schemePointExtension_of_sectionsAlgebraic`**: GAGA for the sections of `L^k`, `k ≫ 0`, implies
  `SchemePointExtension` for every smooth positive volume and every Kähler form.
* `rwnSkodaClause_of_sectionsAlgebraic_of_skodaInclusion`,
  **`phongSturmRemark_of_sectionsAlgebraic_of_skodaInclusion`**: [RWN14, Proposition 7.11] and
  `rmk:PhongSturm` for `μ = (dd^c φ)ⁿ` from GAGA for `H⁰(X, L^k)` and the Skoda inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaRWN

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
  SGPT.TestCurve.TestConfig
open MeasureTheory Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.NAPotential.GAGAMult SGPT.PSH.GlobalL2 SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaPETopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaPECharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaPEManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance skodaPEMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance skodaPEBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

section Analytification

variable [IsSeparated f] [QuasiCompact f]

/-- The frame of the trivial bundle has norm one. -/
theorem norm_unitAtlasFrame_symm_eq_one (p : SchemeComplexPoint f) :
    ‖(unitAtlasFrame (n := n) (M := SchemeComplexPoint f)).val.symm p 1‖ = 1 := by
  change ‖(Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ).symm p 1‖ = 1
  rw [Bundle.Trivial.trivialization_symm_apply, norm_one]

/-- The analytification of an algebraic section has the same pointwise norm:
if `s = σ^{an}`, then `|s(p)|² = |σ|²_{h^j}(p)`. -/
theorem norm_sq_eq_sectionNormSq_of_isAnalytificationOf {j : ℕ}
    {s : twistedSections (schemeHermitianLineBundle f n E a H) unit j}
    {σ : SectionSpace f L j} (hσ : IsAnalytificationOf f n E a H s σ)
    (p : SchemeComplexPoint f) : ‖s p‖ ^ 2 = H.sectionNormSq a j σ p := by
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  have hpe : p ∈ (schemeHermitianAtlasFrame f n E a H (a.frame i)).val.baseSet := hi
  have hpu : p ∈ (unitAtlasFrame (n := n) (M := SchemeComplexPoint f)).val.baseSet := mem_univ p
  have hcoef := hσ i p hi
  have hmem := mem_twistedFrame_baseSet f n E a H (a.frame i) j hi
  have hlin : (twistedFrame f n E a H (a.frame i) j).val.continuousLinearMapAt ℂ p (s p) =
      ((twistedFrame f n E a H (a.frame i) j).val ⟨p, s p⟩).2 :=
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ)
      (e := (twistedFrame f n E a H (a.frame i) j).val) hmem (s p)
  rw [hlin] at hcoef
  rw [twistedSection_norm_sq_frame (schemeHermitianAtlasFrame f n E a H (a.frame i))
      unitAtlasFrame j s hpe hpu,
    schemeHermitianAtlasFrame_norm_sq f n E a H (a.frame i) hi,
    norm_unitAtlasFrame_symm_eq_one, one_pow, mul_one,
    H.sectionNormSq_frame a (a.frame i) j σ p hi, Complex.normSq_eq_norm_sq]
  congr 2
  exact congrArg norm hcoef

end Analytification

/-- **The point extension for algebraic sections from GAGA** (first input of
[RWN14, Proposition 7.11]): if every holomorphic section of `((L, h)^{an})^{⊗ j}` is algebraic
for `j ≫ 0`, the uniform `L²` extension from a point holds for the algebraic sections of `L^k`,
for every smooth positive volume `μ` and every Kähler form `ω` on `X^{an}`. -/
theorem schemePointExtension_of_sectionsAlgebraic (μ : Measure (SchemeComplexPoint f))
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground n (SchemeComplexPoint f))
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j) :
    SchemePointExtension H a μ omega := by
  let := E.isSeparated
  let := E.quasiCompact
  have hX : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro δ hδ
  obtain ⟨k₀, C, hC, hext⟩ := globalPointExtension (n := n) (X := SchemeComplexPoint f) hX omega μ
    hμ (schemeHermitianLineBundle f n E a H) unit
    (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f n E a H)
    isSourceSmoothHermitianMetric_unit (H.curvature a)
    (isOwnFirstChernForm_schemeHermitianLineBundle f n E a H) δ hδ
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hgaga
  refine ⟨max k₀ j₀, C, hC, fun k hk φ hφ x hx => ?_⟩
  have hk0 : k₀ ≤ k := (le_max_left _ _).trans hk
  have hkj : j₀ ≤ k := (le_max_right _ _).trans hk
  -- a nonzero vector of the fibre at `x`: the frame vector
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f x)
  let t := twistedFrame f n E a H (a.frame i) k
  have htx : x ∈ t.val.baseSet := mem_twistedFrame_baseSet f n E a H (a.frame i) k hi
  let v : (twistedPower (schemeHermitianLineBundle f n E a H) unit k).Fiber x := t.val.symm x 1
  have hv : v ≠ 0 := by
    intro h0
    have h1 : (t.val ⟨x, v⟩).2 = (1 : ℂ) := by
      change (t.val ⟨x, t.val.symm x 1⟩).2 = 1
      rw [t.val.apply_mk_symm htx]
    have h2 : (t.val ⟨x, v⟩).2 = (0 : ℂ) := by
      rw [h0]
      have h3 := (t.val.continuousLinearMapAt ℂ x).map_zero
      rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) (e := t.val) htx] at h3
      exact h3
    rw [h1] at h2
    exact one_ne_zero h2
  obtain ⟨s, hsx, hs⟩ := hext k hk0 φ hφ x hx v
  obtain ⟨σ, hσ⟩ := hj₀ k hkj s
  have hnorm := norm_sq_eq_sectionNormSq_of_isAnalytificationOf H a hσ
  refine ⟨σ, ?_, ?_⟩
  · rw [← hnorm x, hsx]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  · have hrw : (fun y => ENNReal.ofReal (H.sectionNormSq a k σ y) *
        multiplierWeight (k : ℝ) (φ y)) =
        fun y => ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) := by
      funext y
      rw [hnorm y]
    rw [hrw, ← hnorm x, hsx]
    exact hs

variable [IsIntegral X]

/-- **[RWN14, Proposition 7.11] from GAGA and the Skoda inclusion**: for a positively curved
metric and a finite smooth positive volume `μ`, GAGA for the sections of `L^k` (`k ≫ 0`) and
the Skoda inclusion for `𝓕` imply `P_θ[ψ_τ] = ψ_τ` for all `τ < τ(𝓕)`. -/
theorem rwnSkodaClause_of_sectionsAlgebraic_of_skodaInclusion (F : SectionFiltration f a)
    (μ : Measure (SchemeComplexPoint f)) [IsFiniteMeasure μ]
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSI : SkodaInclusion F H μ) : RWNSkodaClause H F :=
  rwnSkodaClause_of_pointExtension_of_skodaInclusion F H μ hμ hK
    (schemePointExtension_of_sectionsAlgebraic H a μ hμ (curvatureKahlerBackground H a hK) hgaga)
    hSI

/-- **`rmk:PhongSturm` for `μ = (dd^c φ)ⁿ` from GAGA and the Skoda inclusion**: let `L` be ample
and `h = e^{-φ}` positively curved, `μ = (dd^c φ)ⁿ`. If every holomorphic section of
`((L, h)^{an})^{⊗ k}` is algebraic for `k ≫ 0` and the Skoda inclusion
`H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` holds for the filtrations of the ample test configurations of
`(X, L)`, then for every such test configuration the geodesic ray `Γ^{𝓕*}` is the Phong–Sturm
ray. -/
theorem phongSturmRemark_of_sectionsAlgebraic_of_skodaInclusion
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSI : ∀ (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤),
      SkodaInclusion (G.fgFiltration hG h0) H (curvatureVolume H a hK)) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_pointExtension_of_skodaInclusion H P hK
    (schemePointExtension_of_sectionsAlgebraic H a (curvatureVolume H a hK)
      (isSmoothPositiveVolume_curvatureVolume H a hK) (curvatureKahlerBackground H a hK) hgaga)
    hSI

end SGPT.TestCurve.SkodaRWN
