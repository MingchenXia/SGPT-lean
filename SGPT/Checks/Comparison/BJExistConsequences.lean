import SGPT.Checks.Comparison.BJExistCurve
import SGPT.Checks.Comparison.BJAsmUnique
import SGPT.NAPotential.QwNANonTrivRestZero
import SGPT.NAPotential.DivDict2Blowup

/-!
# Consequences of the existence clause of `cor:testcurvegivepshme`

Source: `chapter_NApotential.tex`, `cor:testcurvegivepshme`, `eq:analymap`, `lma:anaorder`,
`thm:DXZ`, `lma:non-trivrest` (*The algebraic setting*, *The comparison theorem*).

* `existsUnique_isModuleTopologyPSH_naPotentialAnDiv`: **`cor:testcurvegivepshme`** — the function
  `Γ^An : X^Div → [-∞, ∞)` of `def:Gammaana` (`naPotentialAnDiv`, on the divisorial valuations and
  `v_triv`) admits a unique extension to `PSH(L^An)`; it is the formula `eq:psiandef` on `X^An`
  (`naPotentialAnAt`).
* `eq_naPotentialAnAt_of_isModuleTopologyPSH`: every psh extension of `Γ^An|_{X^Div}` is
  `naPotentialAnAt`.
* `naAnalytification`: the map `eq:analymap`, `PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`;
  `naAnalytification_mono` (order preserving, `lma:anaorder`),
  `naAnalytification_le_iff_of_blowup`, `naAnalytification_injective_of_blowup` (order reflecting
  and injective under the resolution-free dictionary hypothesis `BlowupPrimesRealized`).
* `nonTrivRest_of_isModuleTopologyPSH`: **`lma:non-trivrest` for the psh extension**: for the
  unique extension `ψ ∈ PSH(L^An)` of `Γ^An|_{X^Div}` and an irreducible subvariety
  `Y = closure {y}`, `ψ(v_{Y,triv}) ≠ -∞` iff `ψ|_{Y^An} ≢ -∞` iff `Γ` has a well-defined restriction
  to `Y`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.BJ.Exist

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existConsProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existConsPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existConsPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance existConsPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`cor:testcurvegivepshme`**: for `Γ ∈ PSH^NA(X, θ)`, the function `Γ^An` on `X^Div`
(`def:Gammaana`; divisorial valuations and `v_triv`) admits a unique extension to `PSH(L^An)`. -/
theorem existsUnique_isModuleTopologyPSH_naPotentialAnDiv (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    ∃! ψ : BerkovichPoint f → EReal,
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ ∧
        ∀ v : sourceDivisorialSet f, ψ v = naPotentialAnDiv n E Γ ω v := by
  have h := naPotentialAnAt_isModuleTopologyPSH.{0} f n E b HM hm hθ Γ ω
  refine ⟨naPotentialAnAt n E Γ ω, ⟨h, fun v => rfl⟩, fun ψ hψ => ?_⟩
  exact eq_of_eqOn_sourceDivisorialSet f hψ.1 h fun v hv => hψ.2 ⟨v, hv⟩

include hm hθ in
/-- The psh extension of `Γ^An|_{X^Div}` is the formula `eq:psiandef` on all of `X^An`. -/
theorem eq_naPotentialAnAt_of_isModuleTopologyPSH (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {ψ : BerkovichPoint f → EReal}
    (hψ : IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ)
    (hdiv : ∀ v ∈ sourceDivisorialSet f, ψ v = naPotentialAnAt n E Γ ω v) :
    ψ = naPotentialAnAt n E Γ ω :=
  eq_of_eqOn_sourceDivisorialSet f hψ
    (naPotentialAnAt_isModuleTopologyPSH.{0} f n E b HM hm hθ Γ ω) hdiv

include HM hm hθ in
/-- **The map `eq:analymap`**, `PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An` (computed at the Kähler
index `ω`; `naPotentialAnAt_independent`). -/
def naAnalytification (ω : SourceKahlerForm n (SchemeComplexPoint f)) (Γ : SourceNAPotential θ) :
    {ψ : BerkovichPoint f → EReal //
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ} :=
  ⟨naPotentialAnAt n E Γ ω, naPotentialAnAt_isModuleTopologyPSH.{0} f n E b HM hm hθ Γ ω⟩

theorem naAnalytification_apply (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (Γ : SourceNAPotential θ) (v : BerkovichPoint f) :
    (naAnalytification f n E b HM hm hθ ω Γ).1 v = naPotentialAnAt n E Γ ω v := rfl

/-- **`lma:anaorder`, first sentence**: the map `eq:analymap` is order preserving. -/
theorem naAnalytification_mono (ω : SourceKahlerForm n (SchemeComplexPoint f))
    {Γ Γ' : SourceNAPotential θ} (h : SourceNAPOrder Γ Γ') (v : BerkovichPoint f) :
    (naAnalytification f n E b HM hm hθ ω Γ).1 v ≤ (naAnalytification f n E b HM hm hθ ω Γ').1 v :=
  Berkovich.naPotentialAnAt_mono (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n) h ω v

include HM hm hθ in
/-- **`lma:non-trivrest` for the psh extension**: let `ψ ∈ PSH(L^An)` be the (unique) extension of
`Γ^An|_{X^Div}` and `Y = closure {y}` an irreducible closed subvariety. Then
`ψ(v_{Y,triv}) ≠ -∞` iff `ψ` is not identically `-∞` on `Y^An` iff `Γ` has a well-defined
restriction to `Y`. -/
theorem nonTrivRest_of_isModuleTopologyPSH (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {ψ : BerkovichPoint f → EReal}
    (hψ : IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ)
    (hdiv : ∀ v ∈ sourceDivisorialSet f, ψ v = naPotentialAnAt n E Γ ω v) (y : X) :
    List.TFAE [ψ (NANS.subvarietyTrivial f y) ≠ ⊥,
      ∃ w ∈ NANS.subvarietyAn f y, ψ w ≠ ⊥,
      NATrace.TraceWellDefined (NANS.subvarietyInclusion f y) Γ] := by
  rw [eq_naPotentialAnAt_of_isModuleTopologyPSH f n E b HM hm hθ Γ ω hψ hdiv]
  cases n with
  | zero => exact NANS.source_nonTrivRest_of_dim_zero Γ ω y
  | succ k => exact NANS.source_nonTrivRest Γ ω y

end SGPT.NAPotential.BJ.Exist

namespace SGPT.NAPotential.BJ.Exist

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich SGPT.NAPotential.DivDict2
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

section Blowup

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existConsBlProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existConsBlPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existConsBlPointCharts :
    ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance existConsBlPointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

/-- **`lma:anaorder`** for the map `eq:analymap` (positive dimension), under the resolution-free
dictionary hypothesis `BlowupPrimesRealized`: `Γ^An ≤ Γ'^An` iff `Γ ≤ Γ'`. -/
theorem naAnalytification_le_iff_of_blowup (hbl : BlowupPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) {Γ Γ' : SourceNAPotential θ} :
    (∀ v, (naAnalytification f (k + 1) E b HM hm hθ ω Γ).1 v ≤
      (naAnalytification f (k + 1) E b HM hm hθ ω Γ').1 v) ↔ SourceNAPOrder Γ Γ' :=
  (sourceNAPOrder_iff_naPotentialAnAt_le_of_blowup hbl ω).symm

/-- **`lma:anaorder`, last sentence; `thm:DXZ`, injectivity**: under `BlowupPrimesRealized`, the
map `eq:analymap` into `PSH(L^An)` is injective. -/
theorem naAnalytification_injective_of_blowup (hbl : BlowupPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    Function.Injective (naAnalytification (θ := θ) f (k + 1) E b HM hm hθ ω) := by
  intro Γ Γ' h
  exact naPotentialAnAt_injective_of_blowup hbl ω (congrArg Subtype.val h)

end Blowup

end SGPT.NAPotential.BJ.Exist
