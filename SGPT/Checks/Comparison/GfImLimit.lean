import SGPT.Checks.Comparison.GfImImage
import SGPT.Checks.Comparison.BJExistNet
import SGPT.NAPotential.TowerAlgReflect

/-!
# Decreasing limits of GF functions of the class `L` (a step of the surjectivity in `thm:DXZ`)

Source: `chapter_NApotential.tex`, `thm:DXZ`, proof of surjectivity: *Thanks to `lma:gfinimage`, we
can find `Γ^i` with `(Γ^i)^An = φ_i`. It follows from `lma:anaorder` that `Γ^i ≥ Γ^{i+1}` …
`Γ = inf_i Γ^i` … It follows from `prop:anpreinf` that `Γ^An = φ`.*

This file carries out these steps for a decreasing sequence `φ_i ∈ H^gf_ℚ(L^An)` of the class `L`
itself (the book's sequence has classes `L + ε_i H`, which additionally needs the projections
`P_{θ+ω'}[•]_𝓘` from `PSH^NA(X, θ + ε_i ω)` and the gluing over `ω'`, not done here):

* `IsRationalGF.le_trivial`: GF functions attain their maximum at `v_triv`.
* `exists_naPotential_eq_iInf_of_isRationalGF`: the infimum `φ = inf_i φ_i` (not identically
  `-∞`) is `Γ^An` for `Γ = inf_i Γ^i ∈ PSH^NA(X, θ)`, in positive dimension, under
  `AlgebraicPrimesRealized` (needed by `lma:gfinimage`'s second sentence and by `prop:anpreinf` on
  `X^An`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.BJ.GfIm

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

section MaxPrinciple

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance gfImLimitProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- A rational GF function attains its maximum at the trivial valuation. -/
theorem IsRationalGF.le_trivial {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (hφ : IsRationalGF p L φ) (v : BerkovichPoint p) : φ v ≤ φ (BerkovichPoint.trivial p) := by
  obtain ⟨D, -, rfl⟩ := hφ
  change rationalGFFunction D.atlas D.data v ≤
    rationalGFFunction D.atlas D.data (BerkovichPoint.trivial p)
  unfold rationalGFFunction
  rw [finiteMaximum_trivial]
  exact mul_le_mul_of_nonneg_left (finiteMaximum_le_weightMaximum _ _ v)
    (EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg _)))

end MaxPrinciple

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance gfImLimitProper' : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance gfImLimitPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance gfImLimitPointCharts : ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance gfImLimitPointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **Decreasing limits of GF functions of the class `L` are analytifications** (the
construction of the surjectivity proof of `thm:DXZ`, with all `ε_i = 0`; positive dimension, under
`AlgebraicPrimesRealized`): if `φ_i ∈ H^gf_ℚ(L^An)` decrease and `φ = inf_i φ_i ≢ -∞`, then
`φ = Γ^An` on `X^An` for `Γ = inf_i Γ^i`, `Γ^i ∈ PSH^NA(X, θ)` with `(Γ^i)^An = φ_i`
(`lma:gfinimage`), which decrease by `lma:anaorder`. -/
theorem exists_naPotential_eq_iInf_of_isRationalGF (halg : AlgebraicPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) {φ : ℕ → BerkovichPoint f → EReal}
    (hφ : ∀ j, IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) (φ j))
    (hanti : ∀ v, Antitone fun j => φ j v) (hne : ∃ v, (⨅ j, φ j v) ≠ ⊥) :
    ∃ Γ : SourceNAPotential θ, naPotentialAnAt (k + 1) E Γ ω = fun v => ⨅ j, φ j v := by
  choose A _ _ hΓ using fun j =>
    exists_naPotential_eq_of_isRationalGF f k E b HM hm hθ halg ω (hφ j)
  set Γ : ℕ → SourceNAPotential θ := fun j => PiecewiseLinearData.hullNAPotential (A j) with hΓdef
  have hΓj : ∀ j, naPotentialAnAt (k + 1) E (Γ j) ω = φ j := hΓ
  have ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i) := fun i j hij =>
    (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le ω).mpr fun v => by
      rw [hΓj, hΓj]
      exact hanti v hij
  obtain ⟨v₀, hv₀⟩ := hne
  have hfin : (⨅ j, φ j v₀) ≠ ⊤ :=
    ne_top_of_le_ne_top ((hφ 0).ne_top f v₀) (iInf_le _ 0)
  have hr : (((⨅ j, φ j v₀).toReal : ℝ) : EReal) = ⨅ j, φ j v₀ := EReal.coe_toReal hfin hv₀
  set omega := sourceKahlerFormRepresentative ω with homega
  have hb : BddBelow (range fun j => sourceNAPotentialCutoff omega (Γ j)) := by
    refine ⟨(⨅ j, φ j v₀).toReal, ?_⟩
    rintro _ ⟨j, rfl⟩
    show (⨅ j, φ j v₀).toReal ≤ sourceNAPotentialCutoff omega (Γ j)
    rw [sourceNAPotentialCutoff_eq_component omega (Γ j) ω]
    have h1 := DivDict2.naPotentialAnAt_trivial (E := E) (Γ j) ω
    rw [hΓj] at h1
    have h2 : (((⨅ j, φ j v₀).toReal : ℝ) : EReal) ≤ φ j (BerkovichPoint.trivial f) := by
      rw [hr]
      exact (iInf_le _ j).trans (GfIm.IsRationalGF.le_trivial f (hφ j) v₀)
    rw [h1] at h2
    exact_mod_cast h2
  refine ⟨SourceNAPotential.decreasingInf omega Γ ha hb, ?_⟩
  rw [Exist.naPotentialAnAt_decreasingInf f k E b HM hm hθ halg omega Γ ha hb ω]
  funext v
  simp only [hΓj]

end SGPT.NAPotential.BJ.GfIm
