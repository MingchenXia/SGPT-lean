import SGPT.Bergman.Quant2SharpContactUpper
import SGPT.Bergman.SourcePartialEnergyMeasureData
import SGPT.PSH.SourceIVolumeGoodness

/-!
# Weak convergence of partial Bergman measures for smooth weights

Source `prop:smooth_weak_conv` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 831--938).

Let `X` be a connected compact Kähler manifold with `∫_X ωⁿ = 1`, `(L,h)`, `(T,h_T)` Hermitian
holomorphic line bundles with smooth metrics, `θ = c₁(L,h)`, `v ∈ C^∞(X)` and
`φ ∈ PSH(X,θ)` with analytic singularities such that `θ_φ` is a Kähler current. The book proves

  `β^k_{v,φ,ωⁿ} ⇀ θⁿ_{P_{θ,X}[φ]_I(v)} = θⁿ_{P_{θ,X}[φ](v)}`.

Its proof has two inputs:

* the upper bound `τ ≤ θⁿ_{P_{θ,X}[φ](v)}` for every weak cluster point `τ` (Berman's local
  estimate and the contact-set argument); this is
  `SGPT.Bergman.SharpLocalUpper.sourceSharp_original_filter_cluster_upper_full`
  (files `Quant2Sharp*`);
* the convergence of total masses `eq:betaint_conv`, which the book takes from
  `thm:DXmain1` (asymptotic Riemann--Roch):
  `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ)) → vol(θ_φ)`.

In this file we prove, without any further hypothesis:

* `limsup_normalizedH0_le_iVolume`: the inequality `limsup ≤ vol θ_φ` of `thm:DXmain1` for these
  data (a consequence of the cluster upper bound and compactness);
* the equality `P_{θ,X}[φ]_I(v) = P_{θ,X}[φ](v)` (`smooth_weak_conv_envelopes`).

The remaining inequality `vol θ_φ ≤ liminf n!/kⁿ h⁰(X, L^k ⊗ T ⊗ I(kφ))` of `thm:DXmain1` is the
proposition `RiemannRochLowerBound`; under it we prove the full statement `smooth_weak_conv`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant2

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The form `θ = c₁(L,h)` of a Hermitian line bundle with smooth metric, as an atlas form. -/
abbrev chernForm (L : HermitianHolomorphicLineBundle n X) (hL : IsSourceSmoothHermitianMetric L) :
    AtlasClosedRealOneOneForm (ofFixedModel n X) :=
  nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)

/-- The normalized dimension `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ))`, the total mass of `β^k_{v,φ,μ}`. -/
def normalizedH0 (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n *
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ))

/-- The lower-bound half of `thm:DXmain1` (asymptotic Riemann--Roch) for the data `(L,T,φ)`:
`vol(θ_φ) ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ))`, where `vol(θ_φ) = ∫_X θⁿ_{P_θ[φ]_I}`
(`def:volqpsh`, `sourceIVolume`). This is the only input of the book's proofs of
`prop:smooth_weak_conv`, ..., `prop:weakconvana` that is not formalized here. -/
def RiemannRochLowerBound (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) : Prop :=
  ∃ hφ : (ofFixedModel n X).IsThetaPSH θ φ,
    sourceIVolume θ φ hφ ≤ liminf (fun k => normalizedH0 L T φ k) atTop

/-- A potential `φ` such that `θ_φ` is a Kähler current is `θ`-psh and has positive mass. -/
theorem isThetaPSH_and_pos_of_kahlerCurrent (omega : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle n X) (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    ∃ hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ,
      0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ := by
  have : Nonempty X := sourceNonPluripolar_ambient_nonempty (ofFixedModel n X)
    (wholeWeightedSubset (n := n) (0 : C(X, ℝ))).nonPluripolar_carrier
  obtain ⟨hnative, hmass⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega (sourceNativeFirstChernForm L hL)
    (wholeWeightedSubset (n := n) (0 : C(X, ℝ))).nonPluripolar_carrier hcurrent
  have hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ :=
    (isThetaPSH_iff_nativeThetaPotential _ φ).mpr (by
      simpa only [sourceNativeAtlasForm_roundTrip] using hnative)
  refine ⟨hφ, ?_⟩
  simpa only [sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMass,
    sourceNativeAtlasForm_roundTrip] using hmass


/-- The mass of the partial `I`-envelope of a continuous weight equals `vol(θ_φ)`
(`lma:same_sing_type` and the monotonicity of non-pluripolar masses). -/
theorem partialIEnvelope_mass_eq_sourceIVolume (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set X} (hKc : IsClosed K) (hK : (ofFixedModel n X).NonPluripolar K)
    (w : C(K, ℝ)) (hPI : (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ φ K (fun x => (w x : EReal)))) :
    sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ K (fun x => (w x : EReal))) hPI univ =
      sourceIVolume θ φ hφ := by
  have h := partialIEnvelope_eInfinity_continuous omega hφ hφpos hKc hK w
  have hI := isThetaPSH_sourceIEnvelope hφ
  exact le_antisymm (sourcePotentialNonPluripolarMass_mono omega hPI hI h.2.1)
    (sourcePotentialNonPluripolarMass_mono omega hI hPI h.2.2)

/-- The total mass of `β^k_{v,φ,ωⁿ}` is `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ))`. -/
theorem sourceBergmanFiniteMeasure_mass_eq
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (k : ℕ) (hk : 0 < k) (φ : X → EReal) :
    (sourceBergmanFiniteMeasure omega L T hL hT v hv k hk φ : Measure X) univ =
      normalizedH0 L T φ k := by
  let : IsProbabilityMeasure (kahlerVolume omega) := ⟨hvol⟩
  have hBM := smoothPositiveProbabilityVolume_general_BM L T v (kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
  rw [sourceBergmanFiniteMeasure_toMeasure,
    sourcePartialBergmanMeasure_mass L T _ _ hBM k hk φ, normalizedH0,
    sourceBergmanNormalization, ENNReal.ofReal_mul (by positivity)]

/-- The upper half of `thm:DXmain1` for `φ` with analytic singularities and `θ_φ` a Kähler
current: `limsup_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ)) ≤ vol(θ_φ)`. It follows from the cluster upper
bound of `prop:smooth_weak_conv` (with `v = 0`) and the compactness of bounded sets of finite
measures on `X`. -/
theorem limsup_normalizedH0_le_iVolume
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    limsup (fun k => normalizedH0 L T φ k) atTop ≤ sourceIVolume (chernForm L hL) φ hφ := by
  let v : C(X, ℝ) := 0
  have : Nonempty X := sourceNonPluripolar_ambient_nonempty (ofFixedModel n X)
    (wholeWeightedSubset (n := n) v).nonPluripolar_carrier
  have hv : ChartSmooth (n := n) v := fun e => contDiffOn_const
  let B := fun j : ℕ => sourceBergmanFiniteMeasure omega L T hL hT v hv (j+1) (Nat.succ_pos j) φ
  have hBmass (j : ℕ) : (B j : Measure X) univ = normalizedH0 L T φ (j+1) :=
    sourceBergmanFiniteMeasure_mass_eq omega hvol L T hL hT v hv (j+1) (Nat.succ_pos j) φ
  obtain ⟨_, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  have hshift : limsup (fun k => normalizedH0 L T φ k) atTop =
      limsup (fun j => (B j : Measure X) univ) atTop := by
    simp only [hBmass]
    exact (Filter.limsup_nat_add (fun k => normalizedH0 L T φ k) 1).symm
  rw [hshift]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨b, hb1, hb2⟩ := exists_between hcon
  have hfreq : ∃ᶠ j in atTop, b < (B j : Measure X) univ := frequently_lt_of_lt_limsup
    (by isBoundedDefault) hb2
  obtain ⟨C, hCompact, hBC⟩ := sourceSharp_original_beta_compact_mass_set omega hvol L T hL hT v hv φ
  let l₀ : Filter ℕ := atTop ⊓ 𝓟 {j | b < (B j : Measure X) univ}
  have hl₀ : NeBot l₀ := frequently_iff_neBot.mp hfreq
  obtain ⟨τ, _hτS, hτ⟩ := hCompact.exists_mapClusterPt (f := l₀) (u := B)
    (by rw [Filter.le_principal_iff, Filter.mem_map]; exact Filter.Eventually.of_forall hBC)
  let l : Filter ℕ := Filter.comap B (𝓝 τ) ⊓ l₀
  have hne : NeBot l := neBot_inf_comap_iff_map'.mpr hτ.clusterPt.neBot
  have hll₀ : l ≤ l₀ := inf_le_right
  have hl : l ≤ atTop := hll₀.trans inf_le_left
  have hweak : Tendsto B l (𝓝 τ) := tendsto_comap.mono_left inf_le_left
  obtain ⟨_hP, hPI, _hEq, hupper, _hMA⟩ :=
    sourceSharp_original_filter_cluster_upper_full omega hvol L T hL hT v hv hcurrent han l hl τ hweak
  have hmτ : Tendsto (fun j => (B j : Measure X) univ) l (𝓝 ((τ : Measure X) univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  have hev : ∀ᶠ j in l, b ≤ (B j : Measure X) univ :=
    Filter.Eventually.mono (hll₀ (Filter.mem_inf_of_right (Filter.mem_principal_self _)))
      (fun j hj => le_of_lt hj)
  have hbτ : b ≤ (τ : Measure X) univ := ge_of_tendsto hmτ hev
  have hτM : (τ : Measure X) univ ≤ sourceIVolume (chernForm L hL) φ hφ := by
    calc (τ : Measure X) univ ≤ _ := hupper univ
      _ = _ := partialIEnvelope_mass_eq_sourceIVolume omega hφ hφpos isClosed_univ
          (wholeWeightedSubset (n := n) v).nonPluripolar_carrier
          ⟨fun y => v y.val, by fun_prop⟩ hPI
  exact absurd (hb1.trans_le (hbτ.trans hτM)) (lt_irrefl _)

/-- `thm:DXmain1` for `φ` with analytic singularities and `θ_φ` a Kähler current follows from its
lower-bound half `RiemannRochLowerBound`. -/
theorem tendsto_normalizedH0_of_lowerBound
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ) :
    ∃ hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ,
      Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨hφ, hlow⟩ := hRR
  exact ⟨hφ, tendsto_of_le_liminf_of_limsup_le hlow
    (limsup_normalizedH0_le_iVolume omega hvol L T hL hT hcurrent han hφ)⟩

/-- Source `prop:smooth_weak_conv`, equality part: for `φ` with analytic singularities and `θ_φ`
a Kähler current, `P_{θ,X}[φ]_I(v) = P_{θ,X}[φ](v)`, hence the two Monge--Ampère measures agree. -/
theorem smooth_weak_conv_envelopes (omega : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI),
      PI = P ∧ sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP := by
  intro θ P PI
  have : Nonempty X := sourceNonPluripolar_ambient_nonempty (ofFixedModel n X)
    (wholeWeightedSubset (n := n) v).nonPluripolar_carrier
  obtain ⟨hP, _⟩ := sourceSharp_original_envelope_contact_measure omega L hL v hv hcurrent
  have hIEq : PI = P := sourceSharp_original_analytic_IEnvelope_eq omega L hL v hcurrent han
  have hPI : (ofFixedModel n X).IsThetaPSH θ PI := by rw [hIEq]; exact hP
  exact ⟨hP, hPI, hIEq, by simp only [hIEq]⟩

/-- Source `prop:smooth_weak_conv` (weak convergence, as finite measures, of the positive-degree
sequence `k = j + 1`), assuming the lower-bound half `RiemannRochLowerBound` of `thm:DXmain1`
(the book's `eq:betaint_conv`): `β^k_{v,φ,ωⁿ} ⇀ θⁿ_{P_{θ,X}[φ]_I(v)} = θⁿ_{P_{θ,X}[φ](v)}`. -/
theorem smooth_weak_conv_finiteMeasure
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI)
      (M : FiniteMeasure X), PI = P ∧ (M : Measure X) = sourcePotentialNonPluripolarMeasure θ PI hPI ∧
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv (j+1) (Nat.succ_pos j) φ)
        atTop (𝓝 M) := by
  intro θ P PI
  have : Nonempty X := sourceNonPluripolar_ambient_nonempty (ofFixedModel n X)
    (wholeWeightedSubset (n := n) v).nonPluripolar_carrier
  obtain ⟨hP, hPI, M, hEq, hM, hMA, himp⟩ :=
    sourceSharp_original_weakConvergence_from_actual_mass_limit omega hvol L T hL hT v hv hcurrent han
  refine ⟨hP, hPI, M, hEq, hM, hMA, himp ?_⟩
  obtain ⟨hφ, hlim⟩ := tendsto_normalizedH0_of_lowerBound omega hvol L T hL hT hcurrent han hRR
  obtain ⟨_, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  have hMuniv : (M : Measure X) univ = sourceIVolume θ φ hφ := by
    rw [hM]
    exact partialIEnvelope_mass_eq_sourceIVolume omega hφ hφpos isClosed_univ
      (wholeWeightedSubset (n := n) v).nonPluripolar_carrier ⟨fun y => v y.val, by fun_prop⟩ hPI
  rw [hMuniv]
  simp only [fun j => sourceBergmanFiniteMeasure_mass_eq omega hvol L T hL hT v hv (j+1)
    (Nat.succ_pos j) φ]
  exact (Filter.tendsto_add_atTop_iff_nat 1).mpr hlim

/-- Source `prop:smooth_weak_conv`, assuming the lower-bound half `RiemannRochLowerBound` of
`thm:DXmain1` (the only use of `thm:DXmain1` in the book's proof is `eq:betaint_conv`): for every
continuous test function `f`, `∫ f dβ^k_{v,φ,ωⁿ} → ∫ f dθⁿ_{P_{θ,X}[φ]_I(v)}`, and
`θⁿ_{P_{θ,X}[φ]_I(v)} = θⁿ_{P_{θ,X}[φ](v)}`. -/
theorem smooth_weak_conv
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI),
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      ∀ f : C(X, ℝ), Tendsto (fun k => ∫ x, f x ∂sourcePartialBergmanMeasure L T
          (wholeWeightedSubset v) ((kahlerVolume omega).comap
            (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ)
        atTop (𝓝 (∫ x, f x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) := by
  intro θ P PI
  obtain ⟨hP, hPI, M, _hEq, hM, hMA, hconv⟩ :=
    smooth_weak_conv_finiteMeasure omega hvol L T hL hT v hv hcurrent han hRR
  refine ⟨hP, hPI, hMA, fun f => ?_⟩
  have h := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
    (BoundedContinuousFunction.mkOfCompact f)
  rw [← hM]
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp h


end SGPT.Bergman.Quant2
