import SGPT.Bergman.KBigGap
import SGPT.Bergman.Quant3PBMConvergence
import SGPT.Envelopes.DNTEnvelopes

/-!
# Berman's upper bound without positivity and the bigness criterion

Blueprint `claude-k-big`, nodes `claude-k-big:upper`, `claude-k-big:not-psef` and
`claude-k-big:criterion`. Support for source `thm:DXmain1` (Step 3, the compact Kähler case),
`cor:volbigL` and the bigness notion of `def:testcurve:L1134`.

Let `X` be a connected compact complex manifold with a Kähler form `ω`, `∫_X ωⁿ = 1`, `(L,h)`, `(T,h_T)`
Hermitian holomorphic line bundles with smooth metrics, `θ = c₁(L,h)` and `φ : X → [-∞,∞]`
ARBITRARY. With `P = P_θ(0)` the obstacle envelope (`= V_θ`):

* `cluster_le_envelopeMeasure`: every weak cluster point `τ` of the Bergman measures
  `β^k_{0,φ,ωⁿ}` satisfies `τ ≤ θⁿ_P` (local holomorphic Morse inequality, decay off the contact set
  `{P = 0}`, DNT contact identity);
* `limsup_normalizedH0_le_envelopeMass`: `limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ ∫_X θⁿ_P`;
* `tendsto_normalizedH0_zero_of_not_psef`: if `PSH(X,θ) = ∅` the normalized dimensions tend to `0`;
* `tendsto_normalizedH0_zero_of_not_big`, `exists_kahlerCurrent_of_limsup_pos` (**the bigness
  criterion**): if `c₁(L,h)` carries no Kähler current, `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → 0`; equivalently,
  section growth of order `kⁿ` (for some twist `T` and some `φ`) forces a Kähler current in `c₁(L)`.

No projectivity, ample line bundle or resolution of singularities is used; this replaces the
book's appeal to [MM07, Theorem 2.2.26] in Step 3 of the proof of `thm:DXmain1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Bergman.KBig

open Bundle Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.ContactConcentration
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.Quant2
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The obstacle envelope `P_θ(0) = sup {u ∈ PSH(X,θ) : u ≤ 0}` (upper regularized), `θ = c₁(L,h)`,
in the source-envelope API used by the DNT contact identity. It equals `V_θ`. -/
abbrev obstacleEnvelope (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) : X → EReal :=
  sourceRelativeEnvelope (chernForm L hL) (fun _ => ⊤) (fun x => ((0 : C(X, ℝ)) x : EReal))

/-- The Bergman measures `β^{j+1}_{0,φ,ωⁿ}` with weight `0`. -/
abbrev bergmanSeq (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (j : ℕ) : FiniteMeasure X :=
  sourceBergmanFiniteMeasure omega L T hL hT 0 chartSmooth_zero (j + 1) (Nat.succ_pos j) φ

/-- **Weak cluster points do not charge the set of points without a normalized potential**
(blueprint `claude-k-big:upper`, step (ii)): a weak cluster point `τ` of the Bergman measures gives
zero mass to the set of `x` admitting no `θ`-psh `Q ≤ 0` with `Q(x) = 0`. -/
theorem cluster_measure_noPotential (omega : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (τ : FiniteMeasure X)
    (hweak : Tendsto (bergmanSeq omega L T hL hT φ) l (𝓝 τ)) :
    (τ : Measure X) {x | ¬ ∃ Q : X → EReal,
      IsThetaPshPotential (sourceNativeFirstChernForm L hL).val Q ∧ Q ≤ 0 ∧ Q x = 0} = 0 := by
  let : TopologicalSpace.PseudoMetrizableSpace X :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n X
  have hsub : {x | ¬ ∃ Q : X → EReal,
      IsThetaPshPotential (sourceNativeFirstChernForm L hL).val Q ∧ Q ≤ 0 ∧ Q x = 0} ⊆
      ⋃ i : ℕ, ⋃ m : ℕ, gapSet omega L hL ((i : ℝ) + 1)⁻¹ ((m : ℝ) + 1)⁻¹ := by
    intro x hx
    rcases exists_potential_or_mem_gap omega L hL x with ⟨i, m, h⟩ | h
    · exact mem_iUnion₂.mpr ⟨i, m, h⟩
    · exact absurd h hx
  refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun m => ?_)
  exact sourceSharp_filter_open_zero_of_mass_tendsto_zero l hl hweak (isOpen_gap omega L hL _ _)
    (tendsto_measure_gap omega L T hL hT φ (by positivity) (by positivity))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- A `θ`-psh `Q ≤ 0` (native form) lies below the obstacle envelope `P_θ(0)`. -/
theorem le_obstacleEnvelope (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) {Q : X → EReal}
    (hQ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val Q) (hQ0 : Q ≤ 0) :
    Q ≤ obstacleEnvelope L hL := by
  have hQA : (ofFixedModel n X).IsThetaPSH (chernForm L hL) Q :=
    (isThetaPSH_iff_nativeThetaPotential _ Q).mpr (by
      simpa only [chernForm, sourceNativeAtlasForm_roundTrip] using hQ)
  intro x
  refine SGPT.Envelopes.DNT.le_sourceRelativeEnvelope hQA
    (sourceQuasiEverywhere_of_forall fun y => ?_) (sourceObstacle_topReference Q) x
  simpa using hQ0 y

/-- **The cluster bound** (blueprint `claude-k-big:upper`): if `PSH(X,θ) ≠ ∅`, every weak cluster
point `τ` of the Bergman measures `β^k_{0,φ,ωⁿ}` (any `φ`) satisfies `τ ≤ θⁿ_{P_θ(0)}`. -/
theorem cluster_le_envelopeMeasure (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (hne : ∃ u : X → EReal, (ofFixedModel n X).IsThetaPSH (chernForm L hL) u)
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (τ : FiniteMeasure X)
    (hweak : Tendsto (bergmanSeq omega L T hL hT φ) l (𝓝 τ)) :
    ∃ hP : (ofFixedModel n X).IsThetaPSH (chernForm L hL) (obstacleEnvelope L hL),
      (τ : Measure X) ≤
        sourcePotentialNonPluripolarMeasure (chernForm L hL) (obstacleEnvelope L hL) hP := by
  obtain ⟨hP, hmeas⟩ := SGPT.Okounkov.TranscendentalWNReg.sourceObstacleEnvelope_measure_eq omega
    (chernForm L hL) hne (f := fun x => (0 : C(X, ℝ)) x) chartSmooth_zero
  have hupper := sourceSharp_original_filter_cluster_le_positiveTopMeasure omega hvol L T hL hT 0
    chartSmooth_zero φ (fun j => j + 1) (fun j => Nat.succ_pos j) (tendsto_add_atTop_nat 1) l hl τ
    hweak
  have hle : ∀ x, obstacleEnvelope L hL x ≤ ((0 : C(X, ℝ)) x : EReal) :=
    SGPT.Envelopes.DNT.sourceObstacleEnvelope_le (0 : C(X, ℝ)).continuous hP
  have hnull := cluster_measure_noPotential omega L T hL hT φ l hl τ hweak
  set C := {x | obstacleEnvelope L hL x = ((0 : C(X, ℝ)) x : EReal)} with hCdef
  have hae : ∀ᵐ x ∂(τ : Measure X), x ∈ C := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    rintro ⟨Q, hQ, hQ0, hQx⟩
    apply hx
    refine le_antisymm (hle x) ?_
    have := le_obstacleEnvelope L hL hQ hQ0 x
    rw [hQx] at this
    simpa using this
  refine ⟨hP, ?_⟩
  calc (τ : Measure X) = (τ : Measure X).restrict C := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ ≤ (positiveTopMeasure omega (sourceNativeFirstChernForm L hL +
          ddcClosedForm (fun x => (0 : C(X, ℝ)) x) chartSmooth_zero)).restrict C :=
        Measure.restrict_mono le_rfl hupper
    _ = _ := by
        rw [hmeas]
        simp only [chernForm, sourceNativeAtlasForm_roundTrip]

/-- The limsup of the normalized dimensions is bounded by any common bound for the masses of the
weak cluster points of the Bergman measures (compactness of bounded sets of finite measures). -/
theorem limsup_normalizedH0_le_of_cluster (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (M : ℝ≥0∞)
    (hM : ∀ (l : Filter ℕ) [NeBot l], l ≤ atTop → ∀ τ : FiniteMeasure X,
      Tendsto (bergmanSeq omega L T hL hT φ) l (𝓝 τ) → (τ : Measure X) univ ≤ M) :
    limsup (fun k => normalizedH0 L T φ k) atTop ≤ M := by
  let B := bergmanSeq omega L T hL hT φ
  have hBmass (j : ℕ) : (B j : Measure X) univ = normalizedH0 L T φ (j + 1) :=
    sourceBergmanFiniteMeasure_mass_eq omega hvol L T hL hT 0 chartSmooth_zero (j + 1)
      (Nat.succ_pos j) φ
  have hshift : limsup (fun k => normalizedH0 L T φ k) atTop =
      limsup (fun j => (B j : Measure X) univ) atTop := by
    simp only [hBmass]
    exact (Filter.limsup_nat_add (fun k => normalizedH0 L T φ k) 1).symm
  rw [hshift]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨b, hb1, hb2⟩ := exists_between hcon
  have hfreq : ∃ᶠ j in atTop, b < (B j : Measure X) univ :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hb2
  obtain ⟨C, hCompact, hBC⟩ :=
    sourceSharp_original_beta_compact_mass_set omega hvol L T hL hT 0 chartSmooth_zero φ
  let l₀ : Filter ℕ := atTop ⊓ 𝓟 {j | b < (B j : Measure X) univ}
  have hl₀ : NeBot l₀ := frequently_iff_neBot.mp hfreq
  obtain ⟨τ, _hτS, hτ⟩ := hCompact.exists_mapClusterPt (f := l₀) (u := B)
    (by rw [Filter.le_principal_iff, Filter.mem_map]; exact Filter.Eventually.of_forall hBC)
  let l : Filter ℕ := Filter.comap B (𝓝 τ) ⊓ l₀
  have hne : NeBot l := neBot_inf_comap_iff_map'.mpr hτ.clusterPt.neBot
  have hll₀ : l ≤ l₀ := inf_le_right
  have hl : l ≤ atTop := hll₀.trans inf_le_left
  have hweak : Tendsto B l (𝓝 τ) := tendsto_comap.mono_left inf_le_left
  have hmτ : Tendsto (fun j => (B j : Measure X) univ) l (𝓝 ((τ : Measure X) univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  have hev : ∀ᶠ j in l, b ≤ (B j : Measure X) univ :=
    Filter.Eventually.mono (hll₀ (Filter.mem_inf_of_right (Filter.mem_principal_self _)))
      (fun j hj => le_of_lt hj)
  have hbτ : b ≤ (τ : Measure X) univ := ge_of_tendsto hmτ hev
  exact absurd (hb1.trans_le (hbτ.trans (hM l hl τ hweak))) (lt_irrefl _)

/-- **Berman's upper bound without positivity** (blueprint `claude-k-big:upper`): if
`PSH(X,θ) ≠ ∅`, then for every twist `T` and EVERY `φ`,
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ ∫_X θⁿ_{P_θ(0)}`. -/
theorem limsup_normalizedH0_le_envelopeMass (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (hne : ∃ u : X → EReal, (ofFixedModel n X).IsThetaPSH (chernForm L hL) u) :
    ∃ hP : (ofFixedModel n X).IsThetaPSH (chernForm L hL) (obstacleEnvelope L hL),
      limsup (fun k => normalizedH0 L T φ k) atTop ≤
        sourcePotentialNonPluripolarMeasure (chernForm L hL) (obstacleEnvelope L hL) hP univ := by
  obtain ⟨hP, -⟩ := SGPT.Okounkov.TranscendentalWNReg.sourceObstacleEnvelope_measure_eq omega
    (chernForm L hL) hne (f := fun x => (0 : C(X, ℝ)) x) chartSmooth_zero
  refine ⟨hP, limsup_normalizedH0_le_of_cluster omega hvol L T hL hT φ _ fun l _ hl τ hweak => ?_⟩
  obtain ⟨hP', hτ⟩ := cluster_le_envelopeMeasure omega hvol L T hL hT φ hne l hl τ hweak
  exact hτ univ

/-- **Classes without potentials** (blueprint `claude-k-big:not-psef`): if `PSH(X,θ) = ∅`, then
`n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → 0` for every twist `T` and every `φ`. -/
theorem tendsto_normalizedH0_zero_of_not_psef (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (hne : ¬ ∃ u : X → EReal, (ofFixedModel n X).IsThetaPSH (chernForm L hL) u) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 0) := by
  have hlim : limsup (fun k => normalizedH0 L T φ k) atTop ≤ 0 := by
    refine limsup_normalizedH0_le_of_cluster omega hvol L T hL hT φ 0 fun l _ hl τ hweak => ?_
    have hnull := cluster_measure_noPotential omega L T hL hT φ l hl τ hweak
    refine le_of_eq (measure_mono_null (fun x _ => ?_) hnull)
    rintro ⟨Q, hQ, -, -⟩
    exact hne ⟨Q, (isThetaPSH_iff_nativeThetaPotential _ Q).mpr (by
      simpa only [chernForm, sourceNativeAtlasForm_roundTrip] using hQ)⟩
  exact tendsto_of_le_liminf_of_limsup_le bot_le hlim

/-- **The bigness criterion** (blueprint `claude-k-big:criterion`): if `c₁(L,h)` carries no Kähler
current, then `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → 0` for every twist `T` and every `φ`. -/
theorem tendsto_normalizedH0_zero_of_not_big (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (hnb : ¬ ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 0) := by
  by_cases hne : ∃ u : X → EReal, (ofFixedModel n X).IsThetaPSH (chernForm L hL) u
  · obtain ⟨hP, hlim⟩ := limsup_normalizedH0_le_envelopeMass omega hvol L T hL hT φ hne
    have hzero : sourcePotentialNonPluripolarMeasure (chernForm L hL) (obstacleEnvelope L hL) hP
        univ = 0 := by
      by_contra hpos
      obtain ⟨m, hm, -⟩ := SGPT.Bergman.Quant3.exists_increasing_kahlerCurrent_minorants omega L hL
        hP (pos_iff_ne_zero.mpr hpos)
      exact hnb ⟨m 0, hm 0⟩
    rw [hzero] at hlim
    exact tendsto_of_le_liminf_of_limsup_le bot_le hlim
  · exact tendsto_normalizedH0_zero_of_not_psef omega hvol L T hL hT φ hne

/-- **Section growth forces bigness** (blueprint `claude-k-big:criterion`): if
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) > 0` for some twist `T` and some `φ`, then `c₁(L,h)` carries a
Kähler current. -/
theorem exists_kahlerCurrent_of_limsup_pos (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    (hpos : 0 < limsup (fun k => normalizedH0 L T φ k) atTop) :
    ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ := by
  by_contra hnb
  have h := (tendsto_normalizedH0_zero_of_not_big omega hvol L T hL hT φ hnb).limsup_eq
  rw [h] at hpos
  exact lt_irrefl _ hpos

end SGPT.Bergman.KBig
