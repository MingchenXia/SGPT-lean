import SGPT.Okounkov.OF5AdmissibleFlagValuation
import SGPT.NAPotential.AlgPrimes2Divisor
import SGPT.NAPotential.AlgPrimesHypersurface
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform

/-!
# A prime divisor of `X` as a prime divisor over `X(ℂ)`, with its order of vanishing

Source: chapter *The theory of Okounkov bodies*, `thm:nuOk` (*let `E` be a prime divisor on
`X`*), `def:primdiv` (a prime divisor over `X` is a connected smooth hypersurface of a
resolution) and `def:pshfunctions:L1112` (`ν(φ, E) = ν(π^* φ, E)`); the book's remark after
`def:primdiv` (*a prime divisor on `Z` does not always define a prime divisor over `Z` if `Z` is
singular*) — here `X` is smooth, and a prime divisor `E = {z}‾` of `X` (possibly singular)
defines a prime divisor over `X(ℂ)` through the strict transform of `E^an` in an embedded
resolution.

## Main result

`exists_primePresentation_ord`: for a point `z` of codimension one of the smooth integral complex
scheme `X`, there is an analytic presentation `p` (a modification `μ : Ỹ → X(ℂ)` and a smooth
connected hypersurface `Ẽ ⊆ Ỹ`, `SGPT.PSH.CompactPrimeOver.PrimePresentation`) with:

* `Ẽ` is the strict transform of an irreducible analytic hypersurface `V ⊆ E^an = {z}‾(ℂ)` (the
  irreducible component of `E^an` through a smooth point of `E`), and
  `ν(φ, Ẽ) = min_{x ∈ V} ν(φ, x)` for every quasi-psh `φ` (`presentationReader`);
* a point `y₀ ∈ Ẽ` over a point of `E` at which **the analytic order along `Ẽ` of every germ `g`
  of `𝒪_{X,μ(y₀)}` is its algebraic order `ord_E(g)`** (Mathlib's `Scheme.ord` at `z`).

The construction follows lanes ALG-PRIMES/ALG-PRIMES2 (`exists_regular_point`,
`exists_divisorFlattening`, the embedded resolution of irreducible analytic subvarieties), with
the comparison of orders made explicit through `SGPT.Okounkov.OF5.ord_eq_multiplicity`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF5

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.NAPotential.Berkovich SGPT.NAPotential.FSPos
open SGPT.GAGA.H0S SGPT.NAPotential.TowerAlg SGPT.NAPotential.AlgPrimes
open SGPT.NAPotential.AlgPrimes2
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.CompactPrimeOver BlowupTowers
open AnalyticModificationLocalDiscrepancy RegularLocusComponent IrreducibleComponentFilling

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance of5PresPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of5PresPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of5PresPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- **The analytic order along `E^an` at a smooth point is `ord_E`.** For a point `z` of
codimension one there are a complex point `y` of `E = {z}‾`, at which `E^an` is a smooth
hypersurface with a flattening `Ψ`, such that the analytic order along `E^an` at `y` of every
nonzero germ `g ∈ 𝒪_{X,y}` is `ord_E(g)`. -/
theorem exists_point_normalOrder_eq_ord (E : ClosedProjectiveEmbedding f) {z : X}
    (hz : Order.coheight z = 1) :
    ∃ (y : SchemeComplexPoint f)
      (Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y),
      z ⤳ schemeComplexPointImage f y ∧
      ∀ g : X.presheaf.stalk (schemeComplexPointImage f y), g ≠ 0 →
        (pullbackNormalOrder HironakaChowLemma.isAnalyticModification_id Ψ (stalkRep m y g)
          (stalkRep_holomorphicAt y g) : ℕ∞) =
          ((Scheme.ord (algebraMap _ X.functionField g) z).toNat : ℕ∞) := by
  classical
  have : IsDiscreteValuationRing (X.presheaf.stalk z) := isDiscreteValuationRing_stalk f (m + 1) hz
  obtain ⟨V, hV, hzV, u, s, hu, -, hsq, hirr, y, hy, hzy, hsy, v, hv⟩ :=
    exists_regular_point f (m + 1) hz
  obtain ⟨Ψ, hΨ⟩ := SGPT.NAPotential.AlgPrimes2.exists_divisorFlattening E hV hzV hu hsq hy hzy hsy hv
  set P := schemeComplexPointImage f y with hPdef
  refine ⟨y, Ψ, hzy, fun g hg => ?_⟩
  set 𝔮 := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with h𝔮
  set 𝔪 := (hV.primeIdealOf ⟨P, hy⟩).asIdeal with h𝔪
  set π := X.presheaf.germ V P hy u with hπ
  have h𝔮𝔪 : 𝔮 ≤ 𝔪 := (specializes_iff_primeIdealOf_le hV hy hzV).mp hzy
  -- the localizations
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hy⟩
  have hlocy : IsLocalization.AtPrime (X.presheaf.stalk P) 𝔪 := hV.isLocalization_stalk ⟨P, hy⟩
  have hgermy : ∀ a, X.presheaf.germ V P hy a ∈ maximalIdeal (X.presheaf.stalk P) ↔ a ∈ 𝔪 :=
    fun a => IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk P) 𝔪 a
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
  have hlocz : IsLocalization.AtPrime (X.presheaf.stalk z) 𝔮 := hV.isLocalization_stalk ⟨z, hzV⟩
  have hgermz : ∀ a, X.presheaf.germ V z hzV a ∈ maximalIdeal (X.presheaf.stalk z) ↔ a ∈ 𝔮 :=
    fun a => IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) 𝔮 a
  have hspec_germ : ∀ a, (X.presheaf.stalkSpecializes hzy).hom (X.presheaf.germ V P hy a) =
      X.presheaf.germ V z hzV a := fun a => by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hsunit : IsUnit (X.presheaf.germ V P hy s) := by
    by_contra h
    exact hsy ((hgermy s).mp h)
  have hπmem : π ∈ maximalIdeal (X.presheaf.stalk P) := (hgermy u).mpr (h𝔮𝔪 hu)
  have hπ0 : π ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    rw [← hspec_germ, ← hπ, h0, map_zero]
  have hπnu : ¬IsUnit π := fun h => (IsLocalRing.mem_maximalIdeal _).mp hπmem h
  -- germs not divisible by `π` are units at `z`
  have hunit_of : ∀ h : X.presheaf.stalk P, ¬π ∣ h →
      IsUnit ((X.presheaf.stalkSpecializes hzy).hom h) := by
    intro h hndvd
    by_contra hnu
    apply hndvd
    obtain ⟨a, t, ht, hht⟩ := exists_germ_mul_eq hV (hV.primeIdealOf ⟨P, hy⟩) hy
      (hV.fromSpec_primeIdealOf ⟨P, hy⟩) h
    have htunit : IsUnit (X.presheaf.germ V P hy t) := by
      by_contra h'
      exact ht ((hgermy t).mp h')
    have hgz : X.presheaf.germ V z hzV a ∈ maximalIdeal (X.presheaf.stalk z) := by
      rw [← hspec_germ, ← hht, map_mul]
      exact Ideal.mul_mem_right _ _ hnu
    have ha : a ∈ 𝔮 := (hgermz a).mp hgz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsq a ha)
    have h1 : X.presheaf.germ V P hy s * X.presheaf.germ V P hy a =
        π * X.presheaf.germ V P hy c := by
      rw [← map_mul, ← map_mul, ← hc, mul_comm]
    obtain ⟨σs, hσs⟩ := hsunit
    obtain ⟨σt, hσt⟩ := htunit
    refine ⟨X.presheaf.germ V P hy c * ↑σs⁻¹ * ↑σt⁻¹, ?_⟩
    calc h = h * X.presheaf.germ V P hy t * ↑σt⁻¹ := by
          rw [← hσt, mul_assoc, Units.mul_inv, mul_one]
      _ = ↑σs * ↑σs⁻¹ * (X.presheaf.germ V P hy a * ↑σt⁻¹) := by
          rw [hht, Units.mul_inv, one_mul]
      _ = (X.presheaf.germ V P hy s * X.presheaf.germ V P hy a) * ↑σs⁻¹ * ↑σt⁻¹ := by
          rw [hσs]; ring
      _ = _ := by rw [h1]; ring
  -- the algebraic order is the multiplicity of `π`
  have hord := ord_eq_multiplicity hz hzy hπ0 hπnu hunit_of hg
  have hfin : FiniteMultiplicity π g := FiniteMultiplicity.of_not_isUnit hπnu hg
  rw [hord, Int.toNat_natCast, ← hfin.emultiplicity_eq_multiplicity]
  -- the analytic order is the multiplicity of the analytic germ of `π`
  change normalOrder Ψ (chartTranslatedGerm y y (mem_chart_source _ y) (stalkRep m y g)
    (stalkRep_holomorphicAt y g)) = _
  rw [chartTranslatedGerm_stalkRep, normalOrder, hΨ]
  exact emultiplicity_map_of_faithfullyFlat _ (stalkToModel_faithfullyFlat y) _ _

/-- **A prime divisor of `X` as a prime divisor over `X(ℂ)`.** For a point `z` of codimension
one there are a presentation `p` (modification `μ : Ỹ → X(ℂ)`, smooth connected hypersurface
`Ẽ ⊆ Ỹ`), an irreducible analytic hypersurface `V ⊆ E^an = {z}‾(ℂ)` with `Ẽ` its strict
transform and `μ(Ẽ) = V`, such that

* `ν(φ, Ẽ) = min_{x ∈ V} ν(φ, x)` for every quasi-psh `φ` (with Lelong numbers `lelongNumber`);
* at a point `y₀ ∈ Ẽ` over `E`, the analytic order along `Ẽ` of every nonzero germ `g` of
  `𝒪_{X,μ(y₀)}` is `ord_E(g)`. -/
theorem exists_primePresentation_ord (E : ClosedProjectiveEmbedding f) {z : X}
    (hz : Order.coheight z = 1) :
    ∃ (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
      (W : ClosedIrreducibleAnalyticSubvariety (m + 1) (SchemeComplexPoint f)),
      W.carrier ⊆ schemeNativeAlgebraicTrace f (closure {z}) ∧ W.dim = m ∧
      p.projection '' p.divisor = W.carrier ∧
      (∀ φ : SchemeComplexPoint f → EReal, ManifoldQuasiPlurisubharmonic (n := m + 1) φ →
        (⨅ y ∈ p.divisor, lelongNumber (n := m + 1) (fun y => φ (p.projection y)) y) =
          ⨅ x ∈ W.carrier, lelongNumber (n := m + 1) φ x) ∧
      ∃ (y₀ : p.model) (_ : y₀ ∈ p.divisor) (Φ₀ : DivisorFlattening (m := m) p.divisor y₀),
        z ⤳ schemeComplexPointImage f (p.projection y₀) ∧
        ∀ g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀)), g ≠ 0 →
          stalkOrd p Φ₀ g = ((Scheme.ord (algebraMap _ X.functionField g) z).toNat : ℕ∞) := by
  classical
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨y, Ψ, hzy, hΨ⟩ := exists_point_normalOrder_eq_ord (m := m) E hz
  have hTan : IsComplexAnalyticSubset (n := m + 1) (schemeNativeAlgebraicTrace f (closure {z})) :=
    schemeNativeAlgebraicTrace_isComplexAnalyticSubset f (m + 1) _ isClosed_closure
  have hreg := IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Ψ
  -- the irreducible component of `E^an` through `y`
  obtain ⟨V, hVdef⟩ : ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) (SchemeComplexPoint f),
      V = componentSubvariety hTan hreg := ⟨_, rfl⟩
  have hVc : V.carrier = closure (component (n := m + 1) (schemeNativeAlgebraicTrace f (closure {z})) y) := by rw [hVdef]; rfl
  have hVdim : V.dim = m := by rw [hVdef]; rfl
  have hVsub : V.carrier ⊆ schemeNativeAlgebraicTrace f (closure {z}) := by rw [hVdef]; exact componentSubvariety_subset hTan hreg
  have hyC : y ∈ component (n := m + 1) (schemeNativeAlgebraicTrace f (closure {z})) y := mem_component_self hreg
  have hVreg : RegularAtDim (n := m + 1) V.carrier y m := by
    rw [hVc]
    exact regularAtDim_closure_component hreg hyC
  have hyV : y ∈ V.carrier := by
    rw [hVc]
    exact subset_closure hyC
  have hysing : y ∉ singularLocus V := by
    intro h
    apply h.2
    change RegularAtDim (n := m + 1) V.carrier y V.dim
    rw [hVdim]
    exact hVreg
  obtain ⟨Ψ'⟩ := DivisorFlattening.nonempty_of_regularAtDim hVreg
  obtain ⟨O, hO, hyO, hTO⟩ := exists_open_inter_subset_component hreg hyC
  have hsetsV : ∀ᶠ w in 𝓝 y, w ∈ V.carrier ↔ id w ∈ schemeNativeAlgebraicTrace f (closure {z}) := by
    filter_upwards [hO.mem_nhds hyO] with w hw
    refine ⟨fun h => hVsub h, fun h => ?_⟩
    rw [hVc]
    exact subset_closure (hTO ⟨h, hw⟩)
  have hid : y ∉ exceptionalLocus (m + 1) (id : SchemeComplexPoint f → SchemeComplexPoint f) := by
    intro h
    apply h
    rw [mfderiv_id]
    exact Function.bijective_id
  -- the embedded resolution of `V`
  obtain ⟨Wt, tWt, cWt, mWt, μ, hμ, hres⟩ := EmbeddedResolution.exists_embeddedResolution V
  let := tWt
  let := cWt
  let := mWt
  have hμmod : IsAnalyticModification (n := m + 1) μ :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hμ
  have hysS : y ∈ (singularLocus V)ᶜ := hysing
  obtain ⟨y₀, hy₀S, hy₀⟩ := hres.1.1.surjOn hysS
  have hy₀exc : y₀ ∉ exceptionalLocus (m + 1) μ := fun h =>
    Set.disjoint_left.mp hres.1.2 hy₀S h
  subst hy₀
  set S : Set Wt := strictTransform (m + 1) μ V.carrier with hSdef
  have hS : IsClosedConnectedSubmanifold (m + 1) S V.dim := hres.2
  have hy₀mem : y₀ ∈ S :=
    (RestrictedVolumePullbackLower.mem_strictTransform_iff hμmod.1.continuous V.isClosed_carrier
      hy₀exc).mpr hyV
  have hreg₀ : RegularAtDim (n := m + 1) S y₀ m := by
    have h := hS.2.2 y₀ hy₀mem
    rwa [hVdim] at h
  obtain ⟨Φ₀⟩ := DivisorFlattening.nonempty_of_regularAtDim hreg₀
  let p : PrimePresentation (m + 1) (SchemeComplexPoint f) :=
    { model := CMfd.of Wt
      projection := μ
      modification := hμmod
      divisor := S
      divisorDimension := V.dim
      smooth := hS
      codimension_one := by rw [hVdim] }
  have hO' : IsOpen (exceptionalLocus (m + 1) μ)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hμmod.1
  have hsets : ∀ᶠ w in 𝓝 y₀, w ∈ S ↔ μ w ∈ V.carrier := by
    filter_upwards [hO'.mem_nhds hy₀exc] with w hw
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hμmod.1.continuous
      V.isClosed_carrier hw
  -- the Lelong numbers along the strict transform
  obtain ⟨Vt, hVt, -, himage, hreader⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hμmod V
      (by rw [hVdim])
  refine ⟨p, V, hVsub, hVdim, ?_, fun φ hφ => ?_, y₀, hy₀mem, Φ₀, hzy, fun g hg => ?_⟩
  · change μ '' S = V.carrier
    rw [hSdef, ← hVt]
    exact himage
  · change (⨅ w ∈ S, lelongNumber (n := m + 1) (fun w => φ (μ w)) w) = _
    rw [hSdef, ← hVt]
    exact hreader φ hφ
  · -- the orders along `Ẽ` at `y₀` are those along `V` and along `E^an` at `y`
    have hord : stalkOrd p Φ₀ g = pullbackNormalOrder HironakaChowLemma.isAnalyticModification_id
        Ψ (stalkRep m (μ y₀) g) (stalkRep_holomorphicAt (μ y₀) g) := by
      have hF : HolomorphicAt (m + 1) (stalkRep m (μ y₀) g ∘ id) (μ y₀) :=
        stalkRep_holomorphicAt (m := m) (μ y₀) g
      have h1 : stalkOrd p Φ₀ g = pullbackNormalOrder HironakaChowLemma.isAnalyticModification_id
          Ψ' (stalkRep m (μ y₀) g) (stalkRep_holomorphicAt (μ y₀) g) := by
        unfold stalkOrd pullbackNormalOrder
        exact UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional hμmod.1 hy₀exc
          Ψ' Φ₀ hsets (stalkRep m (μ y₀) g ∘ id) hF
      rw [h1]
      exact UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional contMDiff_id hid
        Ψ Ψ' hsetsV (stalkRep m (μ y₀) g ∘ id) hF
    rw [hord]
    exact hΨ g hg

end SGPT.Okounkov.OF5
