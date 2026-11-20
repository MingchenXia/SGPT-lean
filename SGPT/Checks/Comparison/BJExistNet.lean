import SGPT.Checks.Comparison.BJExistConsequences
import SGPT.NAPotential.DivDict2Unconditional

/-!
# Decreasing infima of non-Archimedean potentials: `prop:anpreinf` on `X^An`

Source: `chapter_NApotential.tex`, `prop:anpreinf` (*The comparison theorem*): for a decreasing net
`(Γ_i)_{i ∈ I}` in `PSH^NA(X, θ)` satisfying `eq:decnetcontition`,
`(inf_i Γ_i)^An = inf_i Γ_i^An`. The book proves the equality on `X^Div` and concludes on `X^An`
by `thm:pshdetbydiv`, which needs both sides in `PSH(L^An)`.

* `isModuleTopologyPSH_of_antitone_levelNet`: the limit of a decreasing net of rational GF
  functions of classes `L + ε_{ℓ(k)} H` with `ℓ(k) → ∞`, `ε_a → 0`, is a psh metric on `L^An`.
* `iInf_naPotentialAnAt_isModuleTopologyPSH`: `inf_i Γ_i^An ∈ PSH(L^An)`. The grid approximants
  `D^{(i)}_a` of `Γ_i^An` (`exists_gridPackage`) decrease in `a` and in `i` (the slices and the
  limits of the components decrease along the net), so `(i, a) ↦ D^{(i)}_a` is a decreasing net of
  GF functions with infimum `inf_i Γ_i^An`.
* `naPotentialAnAt_decreasingInf`: **`prop:anpreinf` on all of `X^An`**, under the dictionary
  hypothesis `AlgebraicPrimesRealized` of the existing `X^Div` statement
  (`SGPT.NAPotential.DivDict2.naPotentialAnDiv_decreasingInf`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Exist

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

/-- Grid maxima are monotone in the data. -/
theorem gridApprox_mono {F F' : ℕ → ℝ → EReal} {Flim Flim' : ℕ → EReal} {T T' : ℝ}
    (hT : T' ≤ T) (a : ℕ) (hF : ∀ t, t < T' → F' a t ≤ F a t) (hlim : Flim' a ≤ Flim a) :
    gridApprox F' Flim' T' a ≤ gridApprox F Flim T a := by
  apply max_le
  · exact (add_le_add hlim le_rfl).trans (le_gridApprox_tail F Flim T a)
  · refine iSup_le fun ⟨k, hk⟩ => ?_
    obtain ⟨h1, h2⟩ := mem_gridIndex.mp hk
    exact (add_le_add (hF _ h2) le_rfl).trans
      (le_gridApprox_grid F Flim T a (mem_gridIndex.mpr ⟨h1, h2.trans_le hT⟩))

section Net

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- **Decreasing nets of GF functions.** If `D_k ∈ H^gf_ℚ((L + ε_{ℓ(k)} H)^An)` for a directed
index `k`, with `ℓ(k) → ∞` and rational `ε_a → 0`, the `D_k` decrease and their infimum is not
identically `-∞`, then the infimum lies in `PSH(L^An)`. -/
theorem isModuleTopologyPSH_of_antitone_levelNet {κ : Type u} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] (D : κ → RationalGFPackage X) (lev : κ → ℕ) (hlev : Tendsto lev atTop atTop)
    {L H : RationalPicardSpace X} {ε : ℕ → ℚ} (hε : Tendsto (fun a => (ε a : ℝ)) atTop (𝓝 0))
    (hclass : ∀ k, (D k).picardClass = L + ε (lev k) • H)
    (hanti : ∀ v, Antitone (fun k => (D k).eval p v))
    (hne : ∃ v, (⨅ k, (D k).eval p v) ≠ ⊥) :
    IsModuleTopologyPSH.{u} p L (fun v => ⨅ k, (D k).eval p v) := by
  let N : DecreasingGFNet.{u} p :=
    { I := κ
      preorder := inferInstance
      nonempty := inferInstance
      directed := inferInstance
      term := D
      decreasing := hanti }
  refine ⟨hne, N, ?_, fun v => tendsto_atTop_iInf (hanti v)⟩
  change Tendsto (fun k : κ => (D k).numericalClass p) atTop _
  refine ((tendsto_numericalClass_add_smul p (L := L) (H := H) hε).comp hlev).congr fun k => ?_
  change numericalClass p (L + ε (lev k) • H) = numericalClass p (D k).picardClass
  rw [hclass]

end Net

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existNetProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existNetPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existNetPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance existNetPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

/-- Along `Γ' ≤ Γ`, the grid approximants decrease. -/
theorem gridApprox_le_of_sourceNAPOrder {J : ℕ → ℕ} (hJpos : ∀ a, 0 < J a)
    {Γ Γ' : SourceNAPotential θ} (h : SourceNAPOrder Γ' Γ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) (a : ℕ) :
    gridApprox (gridSlice f n E J Γ' ω v) (gridTail f n E J Γ' ω v) (Γ'.component ω).val.max a ≤
      gridApprox (gridSlice f n E J Γ ω v) (gridTail f n E J Γ ω v) (Γ.component ω).val.max a := by
  obtain ⟨hcut, hle⟩ := (sourceTestCurvePOrder_iff (sourceKahlerFormRepresentative ω) _ _).mp
    ((sourceNAPOrder_iff_component Γ' Γ ω).mp h)
  refine gridApprox_mono hcut a (fun t ht => ?_) ?_
  · simp only [gridSlice, dif_pos ht, dif_pos (ht.trans_le hcut)]
    exact approxVal_mono f n E ((Γ.component ω).val.native_thetaPSH _) (hle t ht) (hJpos a) v
  · simp only [gridTail]
    refine approxVal_mono f n E ((isThetaPSH_iff_nativeThetaPotential _ _).mp
      (Γ.component ω).val.limit_thetaPSH) (fun x => ?_) (hJpos a) v
    unfold sourceTestCurveLimit SGPT.PSH.uscSup
    refine uscRegularization_mono (fun y => iSup_le fun τ => ?_) x
    exact (hle τ τ.2 y).trans (le_iSup (fun j => (Γ.component ω).val.potential j y)
      ⟨τ, (τ.2 : (τ : ℝ) < _).trans_le hcut⟩)

include hm hθ in
/-- **Decreasing infima of analytifications are psh**: for a decreasing net `(Γ_i)` in
`PSH^NA(X, θ)` whose cutoffs `Γ_{i,max}` are bounded below (`eq:decnetcontition`),
`inf_i Γ_i^An ∈ PSH(L^An)`. -/
theorem iInf_naPotentialAnAt_isModuleTopologyPSH {I : Type u} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] (omega : KahlerBackground n (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b)
      (fun v => ⨅ i, naPotentialAnAt n E (Γ i) ω v) := by
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  let : IsDirectedOrder (I × ℕ) := ⟨fun x y => by
    obtain ⟨i, h1, h2⟩ := exists_ge_ge x.1 y.1
    exact ⟨(i, max x.2 y.2), ⟨h1, le_max_left _ _⟩, ⟨h2, le_max_right _ _⟩⟩⟩
  choose D hDcls hDev using fun x : I × ℕ => exists_gridPackage f n E b HM hm hθ (Γ x.1) ω x.2
  let J := siuLevel f n E b HM m
  have hJpos : ∀ a, 0 < J a := siuLevel_pos f n E b HM hm
  have hJsucc : ∀ a, ∃ t, 0 < t ∧ J (a + 1) = t * J a := fun a =>
    ⟨_, Nat.mul_pos two_pos (Nat.two_pow_pos _), siuLevel_succ f n E b HM m a⟩
  have hε : Tendsto (fun a => ((1 / ((m * 2 ^ a : ℕ) : ℚ) : ℚ) : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun a : ℕ => ((m : ℝ) * 2 ^ a)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
        (by exact_mod_cast hm)
    refine (tendsto_inv_atTop_zero.comp h2).congr fun a => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hlev : Tendsto (fun x : I × ℕ => x.2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun a => ⟨(Classical.arbitrary I, a), fun x hx => hx.2⟩
  have hanti : ∀ v, Antitone fun x : I × ℕ => (D x).eval f v := by
    intro v x y hxy
    simp only [hDev]
    exact (antitone_gridApprox_component f n E hJpos hJsucc (Γ y.1) ω v hxy.2).trans
      (gridApprox_le_of_sourceNAPOrder f n E hJpos (ha _ _ hxy.1) ω v x.2)
  have hinf : ∀ v, ⨅ x : I × ℕ, (D x).eval f v = ⨅ i, naPotentialAnAt n E (Γ i) ω v := by
    intro v
    rw [iInf_prod]
    refine iInf_congr fun i => ?_
    simp only [hDev]
    exact iInf_gridApprox_component f n E hJpos (siuLevel_strictMono f n E b HM hm) (Γ i) ω v
  -- `inf_i Γ_i^An(v_triv) ≥ inf_i Γ_{i,max} - 1 > -∞`
  have hne : ∃ v, (⨅ x : I × ℕ, (D x).eval f v) ≠ ⊥ := by
    refine ⟨BerkovichPoint.trivial f, ?_⟩
    rw [hinf]
    obtain ⟨c, hc⟩ := hb
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (c - 1)) (le_iInf fun i => ?_)
    have hci : c ≤ ((Γ i).component ω).val.max := by
      rw [← sourceNAPotentialCutoff_eq_component omega (Γ i) ω]
      exact hc ⟨i, rfl⟩
    have hτ : ((Γ i).component ω).val.max - 1 < ((Γ i).component ω).val.max := by linarith
    have hle := le_naPotentialAnAt n E (Γ i) ω (BerkovichPoint.trivial f) ⟨_, hτ⟩
    rw [Berkovich.potentialAn_trivial hA (((Γ i).component ω).val.native_thetaPSH ⟨_, hτ⟩),
      zero_add] at hle
    exact le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hle
  have h := isModuleTopologyPSH_of_antitone_levelNet.{u} f D (fun x => x.2) hlev hε hDcls hanti hne
  have hfun : (fun v => ⨅ x : I × ℕ, (D x).eval f v) =
      fun v => ⨅ i, naPotentialAnAt n E (Γ i) ω v := funext hinf
  rwa [hfun] at h

end SGPT.NAPotential.BJ.Exist

namespace SGPT.NAPotential.BJ.Exist

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.DivDict2
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

section Anpreinf

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existAnpProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existAnpPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existAnpPointCharts :
    ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance existAnpPointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`prop:anpreinf` on `X^An`**: for a decreasing net `(Γ_i)` in `PSH^NA(X, θ)` satisfying
`eq:decnetcontition`, `(inf_i Γ_i)^An = inf_i Γ_i^An` at every point of `X^An`, under the algebraic
half of the dictionary of prime divisors (`AlgebraicPrimesRealized`, as for the existing `X^Div`
statement). Both sides lie in `PSH(L^An)` and agree on `X^Div`. -/
theorem naPotentialAnAt_decreasingInf (halg : AlgebraicPrimesRealized (f := f) k E) {I : Type u}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground (k + 1) (SchemeComplexPoint f)) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    naPotentialAnAt (k + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω =
      fun v => ⨅ i, naPotentialAnAt (k + 1) E (Γ i) ω v := by
  have h1 := naPotentialAnAt_isModuleTopologyPSH.{0} f (k + 1) E b HM hm hθ
    (SourceNAPotential.decreasingInf omega Γ ha hb) ω
  have h2 := (iInf_naPotentialAnAt_isModuleTopologyPSH.{u} f (k + 1) E b HM hm hθ omega Γ ha hb
    ω).shrink f
  exact eq_of_eqOn_sourceDivisorialSet f h1 h2 fun v hv =>
    naPotentialAnDiv_decreasingInf halg omega Γ ha hb ω ⟨v, hv⟩

end Anpreinf

end SGPT.NAPotential.BJ.Exist
