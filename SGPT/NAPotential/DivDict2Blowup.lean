import SGPT.NAPotential.DivDict2Unconditional

/-! # Order reflection needs only prime divisors on blow-up towers

Source `chapter_NApotential.tex`, `lma:anaorder` (order reflection and injectivity of
`Γ ↦ Γ^An`) and the injectivity in `thm:DXZ`, through the `𝓘`-order criterion
`prop:Iequivchar2`.  Blueprint `claude-div-dict2:blowup-criterion`,
`claude-div-dict2:blowup-anaorder`.

DIV-DICT proved order reflection on `X^Div` under `AnalyticPrimesRealized`: *every* analytic
presentation of a prime divisor over `X(ℂ)` (a smooth connected hypersurface in an arbitrary
modification of `X(ℂ)`) is realized by an algebraic prime divisor over the scheme `X`.  Realizing
the hypersurfaces of an arbitrary modification needs the algebraicity of modifications of
`X(ℂ)` (Moishezon / Artin) or the algebraicity of the divisorial valuations they define.

The `𝓘`-order criterion of `SGPT.Foundations.Analysis`
(`iOrder_iff_all_finite_connected_smooth_prime_orders_of_genuine_right`) only tests hypersurfaces
of *finite sequences of blow-ups with smooth centres* (`IsBlowupSequence`).  This file restates
the criterion and the order reflection over these presentations only:

* `sourceIOrder_iff_blowupPresentationComparison`: `u ⪯_𝓘 v` iff `ν(v, E) ≤ ν(u, E)` for every
  prime divisor `E` on a blow-up tower of `X` (`IsBlowupPresentation`);
* `sourceNAPOrder_of_blowupDivisorialTransform_le`: the Lelong-number form of order reflection,
  tested on blow-up presentations only;
* `BlowupPrimesRealized`: every blow-up presentation is realized by an algebraic prime divisor
  over `X`; it follows from `AnalyticPrimesRealized`
  (`blowupPrimesRealized_of_analyticPrimesRealized`);
* `sourceNAPOrder_iff_naPotentialAnDiv_le_of_blowup`, `naPotentialAnDiv_injective_of_blowup`,
  `naPotentialAnAt_injective_of_blowup`: `lma:anaorder` and the injectivity of `thm:DXZ` under
  `BlowupPrimesRealized` (and nothing else).

`BlowupPrimesRealized` is a resolution-free statement: it needs Chow's theorem for the smooth
centres and hypersurfaces, algebraic blow-ups along smooth centres and their comparison with the
analytic ones, but no resolution of singularities and no Moishezon theory.  It is not proved here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.DivDict2

universe u

open Set Filter
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
open BlowupTowers SquaredLogLelongSourceNormalization
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeNumerical
  SGPT.NAPotential.BJPrep

/-! ### The `𝓘`-order criterion over blow-up towers -/

section Criterion

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A presentation of a prime divisor over `M` lives on a blow-up tower if its modification is a
finite sequence of blow-ups with smooth centres. -/
def IsBlowupPresentation (p : PrimePresentation n M) : Prop :=
  IsBlowupSequence n M p.model p.projection

private theorem genuine_of_sourceQPSH' {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

/-- **The `𝓘`-order criterion over blow-up towers** (`prop:Iequivchar2`, the direction used for
order reflection): if `ν(v, E) ≤ ν(u, E)` for every prime divisor `E` on a blow-up tower of `M`,
then `u ⪯_𝓘 v`. -/
theorem sourceIOrder_of_blowupPresentationComparison {u v : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (h : ∀ p : PrimePresentation n M, IsBlowupPresentation p →
      presentationReader v p ≤ presentationReader u p) :
    sourceIOrder (ofFixedModel n M) u v := by
  cases n with
  | zero =>
      apply (sourceIOrder_iff_native hu hv).mpr
      exact ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right
        u (genuine_of_sourceQPSH' hv)
  | succ m =>
      apply (sourceIOrder_iff_native hu hv).mpr
      apply (FiniteConnectedSmoothPrimeIdealOrder.iOrder_iff_all_finite_connected_smooth_prime_orders_of_genuine_right
        (genuine_of_sourceQPSH' hu).1 (genuine_of_sourceQPSH' hv)).mpr
      intro Y _ _ _ π hπ hseq E hclosed hconn hhyper
      obtain ⟨k, hk, hreg⟩ := hhyper
      let p : PrimePresentation (m + 1) M :=
        { model := CMfd.of (n := m + 1) Y
          projection := π
          modification := hπ
          divisor := E
          divisorDimension := k
          smooth := ⟨hclosed, hconn, hreg⟩
          codimension_one := hk }
      apply (iInf_lelongNumber_le_iff_squaredLog (by omega : m + 1 ≠ 0)
        (fun y => u (π y)) (fun y => v (π y)) E).mpr
      simpa only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq,
        p, Function.comp_def] using h p hseq

/-- **The `𝓘`-order is detected on blow-up towers**: `u ⪯_𝓘 v` iff `ν(v, E) ≤ ν(u, E)` for every
prime divisor `E` on a finite sequence of blow-ups of `M` with smooth centres. -/
theorem sourceIOrder_iff_blowupPresentationComparison {u v : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v) :
    sourceIOrder (ofFixedModel n M) u v ↔
      ∀ p : PrimePresentation n M, IsBlowupPresentation p →
        presentationReader v p ≤ presentationReader u p :=
  ⟨fun hI p _ => (sourceIOrder_iff_presentationComparison hu hv).mp hI p,
    sourceIOrder_of_blowupPresentationComparison hu hv⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- **Order reflection for positive `𝓘`-model test curves, tested on blow-up towers.** -/
theorem sourceTestCurvePOrder_of_blowupDivisorialTransform_le (omega : KahlerBackground n M)
    (C D : SourcePositiveIModelTestCurve θ) (hmax : C.val.max ≤ D.val.max)
    (hT : ∀ p : PrimePresentation n M, IsBlowupPresentation p → ∀ t : ℚ, 0 < t →
      curveDivisorialTransform C.val.toSourceTestCurvePredata p t ≤
        curveDivisorialTransform D.val.toSourceTestCurvePredata p t) :
    SourceTestCurvePOrder C.val D.val := by
  refine (sourceTestCurvePOrder_iff omega C.val D.val).mpr ⟨hmax, fun r hr => ?_⟩
  have hmC : sourceIModel θ (C.val.potential ⟨r, hr⟩) := (sourceIModel_iff_native θ _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices omega C.val).mp C.property) ⟨r, hr⟩)
  have hmD : sourceIModel θ (D.val.potential ⟨r, hr.trans_le hmax⟩) :=
    (sourceIModel_iff_native θ _).mpr
      (((sourceIModelTestCurvesPositive_iff_slices omega D.val).mp D.property)
        ⟨r, hr.trans_le hmax⟩)
  have hI : sourceIOrder (ofFixedModel n M) (C.val.potential ⟨r, hr⟩)
      (D.val.potential ⟨r, hr.trans_le hmax⟩) := by
    apply sourceIOrder_of_blowupPresentationComparison ⟨θ, hmC.1⟩ ⟨θ, hmD.1⟩
    intro p hp
    exact presentationReader_le_of_curveDivisorialTransform_le C.val.toSourceTestCurvePredata
      D.val.toSourceTestCurvePredata p hmax (hT p hp) hr
  have hle := (sourceIOrder_iff_sourceIEnvelope_le hmC.1 hmD.1).mp hI
  rw [← hmC.2, ← hmD.2] at hle
  exact hle

/-- **Order reflection on `PSH^NA(X, θ)` in Lelong-number form, tested on blow-up towers**: if
`Γ_max ≤ Γ'_max` and `Γ^An ≤ Γ'^An` at `t ord_E` for every prime divisor `E` on a blow-up tower
and every rational `t > 0`, then `Γ ≤ Γ'`. -/
theorem sourceNAPOrder_of_blowupDivisorialTransform_le {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm n M)
    (hmax : (Γ.component ω).val.max ≤ (Γ'.component ω).val.max)
    (hT : ∀ p : PrimePresentation n M, IsBlowupPresentation p → ∀ t : ℚ, 0 < t →
      naDivisorialTransform Γ ω p t ≤ naDivisorialTransform Γ' ω p t) :
    SourceNAPOrder Γ Γ' :=
  (sourceNAPOrder_iff_component Γ Γ' ω).mpr
    (sourceTestCurvePOrder_of_blowupDivisorialTransform_le (sourceKahlerFormRepresentative ω)
      (Γ.component ω) (Γ'.component ω) hmax hT)

end Criterion

/-! ### Order reflection and injectivity of `Γ ↦ Γ^An` -/

section Berkovich

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance divDict2BlPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDict2BlPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDict2BlPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (m E) in
/-- **The blow-up half of the dictionary**: every presentation of a prime divisor on a blow-up
tower of `X(ℂ)` (finite sequence of blow-ups with smooth centres) is realized by an algebraic
prime divisor over the scheme `X`.  (A statement, not proved here.) -/
def BlowupPrimesRealized : Prop :=
  ∀ p : PrimePresentation (m + 1) (SchemeComplexPoint f), IsBlowupPresentation p →
    ∃ D : PrimeDivisorOver X, D.IsRealizedBy m E p

/-- The analytic half of the dictionary implies its blow-up half. -/
theorem blowupPrimesRealized_of_analyticPrimesRealized
    (han : AnalyticPrimesRealized (f := f) m E) : BlowupPrimesRealized (f := f) m E :=
  fun p _ => han p

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}
  [IsIntegral X]

/-- **Order reflection on `X^Div`** (`lma:anaorder`) under the blow-up half of the dictionary:
if `Γ^An ≤ Γ'^An` on `X^Div`, then `Γ ≤ Γ'`. -/
theorem sourceNAPOrder_of_naPotentialAnDiv_le_of_blowup
    (hbl : BlowupPrimesRealized (f := f) m E) {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (h : ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v ≤ naPotentialAnDiv (m + 1) E Γ' ω v) :
    SourceNAPOrder Γ Γ' := by
  have hmax : (Γ.component ω).val.max ≤ (Γ'.component ω).val.max := by
    have h0 := h ⟨BerkovichPoint.trivial f, trivial_mem_sourceDivisorialSet f⟩
    change naPotentialAnAt (m + 1) E Γ ω (BerkovichPoint.trivial f) ≤
      naPotentialAnAt (m + 1) E Γ' ω (BerkovichPoint.trivial f) at h0
    rw [naPotentialAnAt_trivial, naPotentialAnAt_trivial] at h0
    exact EReal.coe_le_coe_iff.mp h0
  refine sourceNAPOrder_of_blowupDivisorialTransform_le ω hmax fun p hp t ht => ?_
  obtain ⟨D, hD⟩ := hbl p hp
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [← naPotentialAnAt_ordVal hD Γ ω t ht', ← naPotentialAnAt_ordVal hD Γ' ω t ht']
  exact h ⟨D.ordVal f t ht', divisorialSet_subset_sourceDivisorialSet f ⟨D, t, ht', rfl⟩⟩

/-- **`lma:anaorder` on `X^Div`**: `Γ ≤ Γ'` iff `Γ^An ≤ Γ'^An` on `X^Div`, under the blow-up half
of the dictionary. -/
theorem sourceNAPOrder_iff_naPotentialAnDiv_le_of_blowup
    (hbl : BlowupPrimesRealized (f := f) m E) {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v ≤ naPotentialAnDiv (m + 1) E Γ' ω v :=
  ⟨fun h v => naPotentialAnAt_mono h ω v.1,
    sourceNAPOrder_of_naPotentialAnDiv_le_of_blowup hbl ω⟩

/-- **Injectivity of `Γ ↦ Γ^An` on `X^Div`** (`lma:anaorder`, `thm:DXZ`), under the blow-up half
of the dictionary. -/
theorem naPotentialAnDiv_injective_of_blowup (hbl : BlowupPrimesRealized (f := f) m E)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnDiv (m + 1) E Γ ω := by
  intro Γ Γ' h
  have h' : ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v = naPotentialAnDiv (m + 1) E Γ' ω v :=
    fun v => congrFun h v
  exact SourceNAPOrder.antisymm
    (sourceNAPOrder_of_naPotentialAnDiv_le_of_blowup hbl ω fun v => (h' v).le)
    (sourceNAPOrder_of_naPotentialAnDiv_le_of_blowup hbl ω fun v => (h' v).ge)

/-- **`lma:anaorder` for functions on `X^An`**, under the blow-up half of the dictionary. -/
theorem sourceNAPOrder_iff_naPotentialAnAt_le_of_blowup
    (hbl : BlowupPrimesRealized (f := f) m E) {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt (m + 1) E Γ ω v ≤ naPotentialAnAt (m + 1) E Γ' ω v :=
  ⟨fun h v => naPotentialAnAt_mono h ω v,
    fun h => sourceNAPOrder_of_naPotentialAnDiv_le_of_blowup hbl ω fun v => h v.1⟩

/-- **Injectivity of `Γ ↦ Γ^An` as functions on `X^An`** (`lma:anaorder`, `thm:DXZ`), under the
blow-up half of the dictionary. -/
theorem naPotentialAnAt_injective_of_blowup (hbl : BlowupPrimesRealized (f := f) m E)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnAt (m + 1) E Γ ω := by
  intro Γ Γ' h
  exact naPotentialAnDiv_injective_of_blowup hbl ω (funext fun v => congrFun h v.1)

end Berkovich

end SGPT.NAPotential.DivDict2

end
