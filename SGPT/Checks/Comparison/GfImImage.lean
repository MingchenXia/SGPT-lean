import SGPT.Checks.Comparison.GfImCurve
import SGPT.Checks.Comparison.BJExistConsequences
import SGPT.NAPotential.DivDict2Unconditional

/-!
# `lma:gfinimage`, second sentence: rational GF functions lie in the image of `eq:analymap`

Source: `chapter_NApotential.tex`, `lma:gfinimage`: *In particular, `φ` is in the image of
`eq:analymap`*; the book's proof: *The final assertion follows from `lma:psieqpsiprimeondiv` and
`thm:pshdetbydiv`*.

For the curve `A` of the first sentence (`exists_piecewiseLinearData_of_isRationalGF`), the
element `Ã ∈ PSH^NA(X, θ)` of `lma:psieqpsiprimeondiv` is `hullNAPotential A`. Both `A^An`
(`lma:pltest`) and `Ã^An` (`cor:testcurvegivepshme`) are psh metrics on `L^An`; they agree on `X^Div`
by `eq:psieqsiprime` (`DivDict2.curveAn_eq_naPotentialAnAt_hull`, which needs the algebraic half
`AlgebraicPrimesRealized` of the dictionary of prime divisors); hence they agree on `X^An` by
`thm:pshdetbydiv` and `Ã^An = A^An = φ`.

* `isModuleTopologyPSH_of_isRationalGF`: `H^gf_ℚ(L^An) ⊆ PSH(L^An)` (a constant net).
* `exists_naPotential_eq_of_isRationalGF`: **`lma:gfinimage`, second sentence** (positive
  dimension), conditionally on `AlgebraicPrimesRealized`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.GfIm

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

section GF

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance gfImImageProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **Rational GF functions are psh metrics**: `H^gf_ℚ(L^An) ⊆ PSH(L^An)` (`def:BJpshmetric`, with
the constant sequence). -/
theorem isModuleTopologyPSH_of_isRationalGF {L : RationalPicardSpace X}
    {φ : BerkovichPoint p → EReal} (hφ : IsRationalGF p L φ) : IsModuleTopologyPSH.{u} p L φ := by
  obtain ⟨D, hD, rfl⟩ := hφ
  have h := isModuleTopologyPSH_of_antitone_seq.{u} p (fun _ : ℕ => D) (ε := fun _ => 0)
    (H := L) (by simp only [Rat.cast_zero]; exact tendsto_const_nhds) (fun _ => by rw [zero_smul, add_zero, hD])
    (fun v _ _ _ => le_rfl) ⟨BerkovichPoint.trivial p, by
      obtain ⟨r, hr⟩ := D.eval_trivial_finite p
      rw [iInf_const, hr]
      exact EReal.coe_ne_bot r⟩
  have hfun : (fun v => ⨅ _ : ℕ, D.eval p v) = D.eval p := funext fun v => iInf_const
  rwa [hfun] at h

end GF

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance gfImImageProper' : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance gfImImagePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance gfImImagePointCharts : ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance gfImImagePointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`lma:gfinimage`, second sentence** (positive dimension, under `AlgebraicPrimesRealized`):
every `φ ∈ H^gf_ℚ(L^An)`, `L = m⁻¹ [M]`, is `Γ^An` (on all of `X^An`, at any Kähler index `ω`) for
`Γ = Ã ∈ PSH^NA(X, θ)` the inverse system of `lma:psieqpsiprimeondiv` of the piecewise linear
curve `A` of the first sentence; moreover `A^An = φ`. -/
theorem exists_naPotential_eq_of_isRationalGF (halg : AlgebraicPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ A : PiecewiseLinearData θ, (∀ l, ∃ q : ℚ, A.τ l = q) ∧ A.curveAn (k + 1) E = φ ∧
      naPotentialAnAt (k + 1) E (PiecewiseLinearData.hullNAPotential A) ω = φ := by
  obtain ⟨A, hτ, hA⟩ := exists_piecewiseLinearData_of_isRationalGF f (k + 1) E b HM hm hθ hφ
  refine ⟨A, hτ, hA, ?_⟩
  have h1 := Exist.naPotentialAnAt_isModuleTopologyPSH.{0} f (k + 1) E b HM hm hθ
    (PiecewiseLinearData.hullNAPotential A) ω
  have h2 := Assembly.curveAn_isModuleTopologyPSH.{0} f (k + 1) E b HM hm hθ A
  rw [← hA]
  exact Assembly.eq_of_eqOn_sourceDivisorialSet f h1 h2 fun v hv =>
    (DivDict2.curveAn_eq_naPotentialAnAt_hull halg A ω ⟨v, hv⟩).symm

include hm hθ in
/-- **`lma:gfinimage`, second sentence, as membership in the image of `eq:analymap`**
(`Exist.naAnalytification`), under `AlgebraicPrimesRealized`. -/
theorem exists_naAnalytification_eq_of_isRationalGF (halg : AlgebraicPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ Γ : SourceNAPotential θ, (Exist.naAnalytification f (k + 1) E b HM hm hθ ω Γ).1 = φ := by
  obtain ⟨A, -, -, h⟩ := exists_naPotential_eq_of_isRationalGF f k E b HM hm hθ halg ω hφ
  exact ⟨PiecewiseLinearData.hullNAPotential A, h⟩

section DimZero

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance gfImImageProper0 : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance gfImImagePointTopology0 : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance gfImImagePointCharts0 : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance gfImImagePointManifold0 : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f 0 E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`lma:gfinimage`, second sentence, in dimension zero** (unconditional): `X^An` is a point,
every `φ ∈ H^gf_ℚ(L^An)` is a psh metric, and `eq:analymap` is onto in dimension zero
(lane DIM0, `DimZero.naAnalytification_surjective_of_dim_zero`). -/
theorem exists_naAnalytification_eq_of_isRationalGF_of_dim_zero
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ Γ : SourceNAPotential θ, (Exist.naAnalytification f 0 E b HM hm hθ ω Γ).1 = φ := by
  obtain ⟨Γ, hΓ⟩ := SGPT.NAPotential.DimZero.naAnalytification_surjective_of_dim_zero f E b HM hm
    hθ ω ⟨φ, isModuleTopologyPSH_of_isRationalGF.{0} f hφ⟩
  exact ⟨Γ, congrArg Subtype.val hΓ⟩

end DimZero

end SGPT.NAPotential.BJ.GfIm
