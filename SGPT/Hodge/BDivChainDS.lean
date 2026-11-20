import SGPT.Hodge.BDivChainDivisorial
import SGPT.BDivisor.MassPushforwardClassVolume
import SGPT.BDivisor.BlowupModelNef
import SGPT.PSH.SourceGenericLelongModificationConvergence
import SGPT.PSH.SourceSingularityModelSandwich
import SGPT.PSH.SourceSingularityBackgroundChange
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge

/-!
# `d_S`-continuity of the b-divisor map (`prop:dscontbdiv`)

Source `prop:dscontbdiv` (chapter *The theory of b-divisors*): let `θ` be a closed real smooth
`(1,1)`-form on `X` (representing a big class, the standing hypothesis of the `d_S`-pseudometric,
`sec:dsdef`), `(φ_i)_{i ∈ I}` a net in `PSH(X, θ)` and `φ ∈ PSH(X, θ)`.  If `φ_i → φ` in `d_S`,
then `𝔻(θ_{φ_i}) → 𝔻(θ_φ)`.

The formal statement (`currentBDivisor_converges_of_dS`) is for an arbitrary filter on an
arbitrary index type (in particular every net), the book's `d_S` (`sourceSingularityTopology`),
the book's b-divisor `𝔻(T)` (`SGPT.BDivisor.currentBDivisor`, over the book's models: finite
compositions of blow-ups with smooth centres) and the book's convergence of b-divisors
(`WeilBDivisorOn.Converges`: convergence on every model in the Euclidean topology).
`X` is the chapter's connected compact Kähler manifold.

Proof (the book's, with one simplification).  Fix a model `π : Y → X` (`Y` compact connected
Kähler).  `{Reg π^*θ_u} = π^*{θ} - {Div π^*θ_u}`, so it suffices to prove
`{Div π^*θ_{φ_i}} → {Div π^*θ_φ}`.
1. `H^{1,1}(Y, ℝ)` is finite dimensional and `d_S` is a pseudometric: continuity can be tested
   on sequences, and it suffices that every subsequence has a further convergent subsequence.
2. Add a Kähler form: by `cor:dSconv_changetheta` the same functions converge in `d_{S, θ + ω}`,
   and every `θ`-psh function has positive `(θ + ω)`-mass; the masses converge, so they are
   bounded below by some `δ > 0` along a tail.
3. Replace the potentials by their `P`-envelopes (model potentials, `d_S`-distance `0`, same
   `𝓘`-singularity type) and apply `prop:incanddec`: after passing to a subsequence there is an
   increasing sequence `η_j ≤ P[φ_j]`, so `η_0 ≼_P φ_j` for all `j`, hence
   `ν(π^*θ_{φ_j}, E) ≤ ν(π^*θ_{η_0}, E)` for every prime divisor `E` of `Y`.
4. `thm:Lelongcont`: `ν(π^*θ_{φ_j}, E) → ν(π^*θ_φ, E)` for every prime `E` of `Y`.
5. Tannery's theorem (dominated convergence for the Siu series,
   `SGPT.Hodge.BDivChain.tendsto_siuDivisorialPart_inChart_of_dominated`) gives
   `Div π^*θ_{φ_j} → Div π^*θ_φ` weakly, and the weak continuity of the class map
   (`SGPT.Hodge.tendsto_bottChernClass_of_tendsto`) gives the convergence of the classes.

Step 5 replaces the book's monotone reduction and finite-tail argument: the single majorant
`ν(π^*θ_{η_0}, ·)` controls all the tails at once.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-! ### The current of a source potential -/

/-- The current `θ_u = θ + ddᶜu ∈ 𝒵₊(X)` of a source `θ`-psh potential `u`. -/
def sourcePotentialCurrent (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (u : SourceThetaPotentialL1 θ) : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  SGPT.PSH.BookCurrent.thetaPositiveCurrent (atlasClosedFormToNative θ) u.val
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
theorem sourcePotentialCurrent_current (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (u : SourceThetaPotentialL1 θ) :
    (sourcePotentialCurrent θ u).current = thetaPotentialCurrent (atlasClosedFormToNative θ).val
      u.val ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property) := rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- The class of `θ_u` is `{θ}`. -/
theorem bottChernClass_sourcePotentialCurrent
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)) (u : SourceThetaPotentialL1 θ) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨(sourcePotentialCurrent θ u).current,
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (sourcePotentialCurrent θ u)).1,
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (sourcePotentialCurrent θ u)).2.1⟩ =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) :=
  ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent _ u.val
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property)

/-! ### Generic Lelong numbers on a model -/

section Lelong

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The generic Lelong number of `π^*(σ + ddᶜu)` along a prime divisor `E` of `Y` is the source
generic Lelong number of `u ∘ π` along `E` (the reader of `thm:Lelongcont`). -/
theorem currentGenericLelong_pull_thetaPotentialCurrent {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {σ : ClosedRealOneOneForm (m + 1) X} {a : X → EReal} (ha : IsThetaPshPotential σ.val a)
    (hS : SGPT.Siu.IsClosedPositiveCurrent (thetaPotentialCurrent σ.val a ha))
    (E : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y) :
    SGPT.Siu.currentGenericLelong (Modification4.pull hπ (thetaPotentialCurrent σ.val a ha) hS)
        (Modification4.isClosedPositiveCurrent_pull hπ hS) E =
      (ofFixedModel (m + 1) Y).sourceGenericLelong (fun y => a (π y)) E.val := by
  rw [SGPT.Siu.currentGenericLelong_eq_primeGenericLelong _
    (PrimePushforward.pull_eq_thetaPotentialCurrent hπ hS ha rfl)]
  simp only [SGPT.Siu.primeGenericLelong, sourceGenericLelong, sourceLelong_ofFixedModel_eq]

end Lelong

/-! ### The Kähler shift -/

section Shift

variable [ConnectedSpace X]

/-- The Kähler form as a source closed form. -/
abbrev kahlerAtlasForm (ω : KahlerBackground (m + 1) X) :
    AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X) :=
  nativeClosedFormToAtlas ω.form

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
theorem kahlerAtlasForm_semipositive (ω : KahlerBackground (m + 1) X) :
    (atlasClosedFormToNative (kahlerAtlasForm ω)).val.IsSemipositive := by
  rw [sourceNativeAtlasForm_roundTrip]
  exact ω.isSemipositive

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
theorem atlasClosedFormToNative_add_kahler (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (ω : KahlerBackground (m + 1) X) :
    atlasClosedFormToNative (θ.add (kahlerAtlasForm ω)) = atlasClosedFormToNative θ + ω.form := by
  change atlasClosedFormToNative θ + atlasClosedFormToNative (kahlerAtlasForm ω) = _
  rw [sourceNativeAtlasForm_roundTrip]

/-- **Every `θ`-psh function has positive `(θ + ω)`-mass.** -/
theorem sourceMass_pos_add_kahler (ω : KahlerBackground (m + 1) X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)) (u : SourceThetaPotentialL1 θ) :
    0 < sourcePotentialNonPluripolarMeasure (θ.add (kahlerAtlasForm ω))
      (sourceSemipositiveBackgroundPotential (kahlerAtlasForm ω) (kahlerAtlasForm_semipositive ω)
        u).val
      (sourceSemipositiveBackgroundPotential (kahlerAtlasForm ω) (kahlerAtlasForm_semipositive ω)
        u).property univ := by
  have hu := (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (sourceSemipositiveBackgroundPotential (kahlerAtlasForm ω) (kahlerAtlasForm_semipositive ω)
      u).property
  have hθ := (isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property
  have hsub : IsThetaPshPotential
      (atlasClosedFormToNative (θ.add (kahlerAtlasForm ω)) - (1 : ℝ) • ω.form).val u.val := by
    rw [atlasClosedFormToNative_add_kahler, one_smul, add_sub_cancel_right]
    exact hθ
  exact RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul ω one_pos hsub hu

end Shift

/-! ### `P`-envelopes -/

section Envelope

variable [ConnectedSpace X]

/-- The `P`-envelope `P[a]` has the mass of `a`. -/
theorem sourceMass_pEnvelope (ω : KahlerBackground (m + 1) X)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)} (a : SourceThetaPotentialL1 σ) :
    sourcePotentialNonPluripolarMeasure σ (sourceThetaPotentialSingularityEnvelope a).val
        (sourceThetaPotentialSingularityEnvelope a).property univ =
      sourcePotentialNonPluripolarMeasure σ a.val a.property univ := by
  have key : ∀ (b : X → EReal) (hb : (ofFixedModel (m + 1) X).IsThetaPSH σ b),
      b = singularityEnvelope (atlasClosedFormToNative σ).val a.val →
      sourcePotentialNonPluripolarMeasure σ b hb univ =
        sourcePotentialNonPluripolarMeasure σ a.val a.property univ := by
    rintro b hb rfl
    exact singularityEnvelopeMassPreserving ω (atlasClosedFormToNative σ) a.val
      ((isThetaPSH_iff_nativeThetaPotential σ a.val).mp a.property) _
  exact key _ _ (sourceSingularityEnvelope_eq_native σ a.val)

/-- For `a` of positive mass, `P[a]` is a model potential. -/
theorem sourceModelPotential_pEnvelope (ω : KahlerBackground (m + 1) X)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)} (a : SourceThetaPotentialL1 σ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure σ a.val a.property univ) :
    SourceModelPotential σ (sourceThetaPotentialSingularityEnvelope a).val := by
  refine ⟨(sourceThetaPotentialSingularityEnvelope a).property, ?_, ?_⟩
  · change sourceSingularityEnvelope σ a.val =
      sourceSingularityEnvelope σ (sourceSingularityEnvelope σ a.val)
    simp only [sourceSingularityEnvelope_eq_native]
    exact (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass ω _ a.val
      ((isThetaPSH_iff_nativeThetaPotential σ a.val).mp a.property) hpos).symm
  · rw [sourceMass_pEnvelope ω a]
    exact hpos

/-- `a ∼_P P[a]`. -/
theorem sourcePEquivalent_pEnvelope (ω : KahlerBackground (m + 1) X)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)} (a : SourceThetaPotentialL1 σ) :
    SingularGlobalPOrder.SourcePEquivalent (n := m + 1) a.val
      (sourceThetaPotentialSingularityEnvelope a).val := by
  change SingularGlobalPOrder.SourcePEquivalent (n := m + 1) a.val
    (sourceSingularityEnvelope σ a.val)
  rw [sourceSingularityEnvelope_eq_native]
  exact SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope ω _
    ((isThetaPSH_iff_nativeThetaPotential σ a.val).mp a.property)

/-- `d_S(a, P[a]) = 0` for `a` of positive mass. -/
theorem dist_pEnvelope (ω : KahlerBackground (m + 1) X)
    (σ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (hσ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)))
    (a : SourceThetaPotentialL1 σ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure σ a.val a.property univ) :
    letI := sourceSingularityPseudoMetricSpace ω σ hσ
    dist a (sourceThetaPotentialSingularityEnvelope a) = 0 := by
  let := sourceSingularityPseudoMetricSpace ω σ hσ
  rw [sourceSingularityPseudoMetricSpace_dist,
    sourceSingularityDistance_pEnvelope_eq_zero ω σ hσ a hpos]
  rfl

end Envelope

/-! ### The sequential statement on a model -/

section Main

variable [ConnectedSpace X]

/-- **The key sequential step of `prop:dscontbdiv`.** For a model `π : Y → X` carrying a Kähler
form and a sequence `u_k → v` in `d_S`, some subsequence satisfies
`{Div π^*θ_{u_{g k}}} → {Div π^*θ_v}` in the Euclidean topology of `H^{1,1}(Y, ℝ)`. -/
theorem exists_strictMono_tendsto_divPullClass (ω : KahlerBackground (m + 1) X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (π : Modification (m + 1) X) (ωY : KahlerBackground (m + 1) π.carrier)
    (u : ℕ → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : Tendsto u atTop (@nhds _ (sourceSingularityTopology ω θ hbig) v)) :
    ∃ g : ℕ → ℕ, StrictMono g ∧
      Tendsto (fun k => π.divPullClass (sourcePotentialCurrent θ (u (g k))).current
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _)) atTop
        (@nhds _ (euclideanTopology (RealBottChern (m + 1) π.carrier))
          (π.divPullClass (sourcePotentialCurrent θ v).current
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _))) := by
  have : ConnectedSpace π.carrier :=
    connectedSpace_of_isAnalyticModification π.isAnalyticModification
  -- the Kähler shift `σ = θ + ω` (`cor:dSconv_changetheta`)
  set η := kahlerAtlasForm ω with hηdef
  have hη : (atlasClosedFormToNative η).val.IsSemipositive := kahlerAtlasForm_semipositive ω
  set σ := θ.add η with hσdef
  have hσ := sourceBigClass_add_semipositive θ η hbig hη
  set sh : SourceThetaPotentialL1 θ → SourceThetaPotentialL1 σ :=
    sourceSemipositiveBackgroundPotential η hη with hshdef
  have hlim' : Tendsto (fun k => sh (u k)) atTop
      (@nhds _ (sourceSingularityTopology ω σ hσ) (sh v)) :=
    (tendsto_sourceSingularityTopology_iff_semipositive_enlargement ω θ η hbig hη atTop u v).mp
      hlim
  -- the masses converge to a positive finite limit
  have hmass := ((tendsto_sourceSingularityTopology_iff_mixedMass ω σ hσ atTop _ _).mp hlim'
    (Fin.last _)).1
  simp only [sourceMinimalMixedMass_last] at hmass
  set c := sourcePotentialNonPluripolarMeasure σ (sh v).val (sh v).property univ with hcdef
  have hc0 : 0 < c := sourceMass_pos_add_kahler ω θ v
  have hctop : c < ⊤ := by
    have h := sourceMinimalMixedMass_lt_top ω σ hσ (sh v).val (sh v).property (Fin.last _)
    rwa [sourceMinimalMixedMass_last] at h
  have hc2 : c / 2 < c := ENNReal.half_lt_self hc0.ne' hctop.ne
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hmass.eventually (lt_mem_nhds hc2))
  -- a tail with masses `> c / 2`, its `P`-envelopes, and the sandwich (`prop:incanddec`)
  set s : ℕ → SourceThetaPotentialL1 σ := fun k => sh (u (k + K)) with hsdef
  set p : ℕ → SourceThetaPotentialL1 σ := fun k => sourceThetaPotentialSingularityEnvelope (s k)
    with hpdef
  have hspos : ∀ k, c / 2 < sourcePotentialNonPluripolarMeasure σ (s k).val (s k).property univ :=
    fun k => hK (k + K) (Nat.le_add_left K k)
  have hpos : ∀ k, 0 < sourcePotentialNonPluripolarMeasure σ (s k).val (s k).property univ :=
    fun k => zero_le.trans_lt (hspos k)
  have hslim : Tendsto s atTop (@nhds _ (sourceSingularityTopology ω σ hσ) (sh v)) :=
    (tendsto_add_atTop_iff_nat K).mpr hlim'
  have hplim : Tendsto p atTop (@nhds _ (sourceSingularityTopology ω σ hσ) (sh v)) := by
    let := sourceSingularityPseudoMetricSpace ω σ hσ
    have hs2 : Tendsto s atTop (𝓝 (sh v)) := hslim
    have hgoal : Tendsto p atTop (𝓝 (sh v)) := by
      rw [tendsto_iff_dist_tendsto_zero] at hs2 ⊢
      refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hs2
      calc dist (p k) (sh v) ≤ dist (p k) (s k) + dist (s k) (sh v) := dist_triangle _ _ _
        _ = dist (s k) (sh v) := by
          rw [dist_comm, dist_pEnvelope ω σ hσ (s k) (hpos k), zero_add]
    exact hgoal
  have hc2top : c / 2 ≠ ⊤ := ENNReal.div_ne_top hctop.ne (by norm_num)
  have hdelta : 0 < (c / 2).toReal :=
    ENNReal.toReal_pos (ENNReal.half_pos hc0.ne').ne' hc2top
  have hstage : ∀ k, ENNReal.ofReal (c / 2).toReal ≤
      sourcePotentialNonPluripolarMeasure σ (p k).val (p k).property univ := by
    intro k
    rw [ENNReal.ofReal_toReal hc2top, sourceMass_pEnvelope ω (s k)]
    exact (hspos k).le
  have hmodels : ∀ k, SourceModelPotential σ (p k).val :=
    fun k => sourceModelPotential_pEnvelope ω (s k) (hpos k)
  obtain ⟨f, hf, ηs, ψs, -, -, -, hηmono, -, hbetween, -, -⟩ :=
    sourceSingularityModelSandwich ω σ hσ p (sh v) hmodels hdelta hstage hplim
  -- the subsequence and its `d_S`-convergence
  set w : ℕ → SourceThetaPotentialL1 θ := fun k => u (f k + K) with hwdef
  have hw : Tendsto w atTop (@nhds _ (sourceSingularityTopology ω θ hbig) v) :=
    ((tendsto_add_atTop_iff_nat K).mpr hlim).comp hf.tendsto_atTop
  -- the dominating current `σ + ddᶜη₀`: `η₀ ≼_P w_k`
  have hη0 := (isThetaPSH_iff_nativeThetaPotential σ (ηs 0).val).mp (ηs 0).property
  have hG : SGPT.Siu.IsClosedPositiveCurrent
      (thetaPotentialCurrent (atlasClosedFormToNative σ).val (ηs 0).val hη0) :=
    SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hη0
  have hIord : ∀ k, IEnvelope.IOrderOnManifold (n := m + 1) (ηs 0).val (w k).val := by
    intro k
    have hpk := (isThetaPSH_iff_nativeThetaPotential σ (p (f k)).val).mp (p (f k)).property
    have h1 : SingularGlobalPOrder.SourcePOrder (n := m + 1) (ηs 0).val (p (f k)).val :=
      SingularGlobalPOrder.sourcePOrder_of_moreSingularOn ω _ _ hη0 hpk
        ⟨0, fun x _ => by
          have hx := ((hηmono (Nat.zero_le k)) x).trans ((hbetween k).1 x)
          simpa using hx⟩
    have h2 : SingularGlobalPOrder.SourcePOrder (n := m + 1) (p (f k)).val (s (f k)).val :=
      (sourcePEquivalent_pEnvelope ω (s (f k))).2
    exact GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
      (SingularGlobalPOrder.SourcePOrder.trans ω h1 h2)
  have hT : ∀ a : SourceThetaPotentialL1 θ,
      SGPT.Siu.IsClosedPositiveCurrent (sourcePotentialCurrent θ a).current :=
    fun a => SGPT.Siu.isClosedPositiveCurrent_bookCurrent _
  have hdom : ∀ k (E : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.carrier),
      SGPT.Siu.currentGenericLelong
          (Modification4.pull π.isAnalyticModification (sourcePotentialCurrent θ (w k)).current
            (hT (w k)))
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification (hT (w k))) E ≤
        SGPT.Siu.currentGenericLelong
          (Modification4.pull π.isAnalyticModification
            (thetaPotentialCurrent (atlasClosedFormToNative σ).val (ηs 0).val hη0) hG)
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hG) E :=
    fun k E => PrimePushforward.currentGenericLelong_pull_le_of_iOrder π.isAnalyticModification
      hG (hT (w k)) hη0 ((isThetaPSH_iff_nativeThetaPotential θ (w k).val).mp (w k).property)
      rfl rfl (hIord k) E
  -- `thm:Lelongcont` on the model
  have hreader : ∀ (a : SourceThetaPotentialL1 θ) (E : SGPT.PSH.GeometricPrimeCarrier (m + 1)
      π.carrier),
      SGPT.Siu.currentGenericLelong
          (Modification4.pull π.isAnalyticModification (sourcePotentialCurrent θ a).current (hT a))
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification (hT a)) E =
        (ofFixedModel (m + 1) π.carrier).sourceGenericLelong (fun y => a.val (π.map y)) E.val :=
    fun a E => currentGenericLelong_pull_thetaPotentialCurrent (σ := atlasClosedFormToNative θ)
      (a := a.val) π.isAnalyticModification
      ((isThetaPSH_iff_nativeThetaPotential θ a.val).mp a.property) (hT a) E
  have hconv : ∀ E : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.carrier,
      Tendsto (fun k => SGPT.Siu.currentGenericLelong
          (Modification4.pull π.isAnalyticModification (sourcePotentialCurrent θ (w k)).current
            (hT (w k)))
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification (hT (w k))) E)
        atTop (𝓝 (SGPT.Siu.currentGenericLelong
          (Modification4.pull π.isAnalyticModification (sourcePotentialCurrent θ v).current
            (hT v))
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification (hT v)) E)) := by
    intro E
    simp only [hreader]
    exact tendsto_sourceGenericLelong_comp_of_sourceSingularityTopology ω θ hbig
      π.isAnalyticModification atTop w v hw E.val
  refine ⟨fun k => f k + K, hf.add_const K, ?_⟩
  exact tendsto_bottChernClass_siuDivisorialPart ωY
    (fun k => Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification (hT (w k)))
    (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification (hT v))
    (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hG) hconv
    (Eventually.of_forall hdom)

/-- **`prop:dscontbdiv` on one model.** For a modification `π : Y → X` carrying a Kähler form
and a family `(φ_i)` (along any filter) with `φ_i → φ` in `d_S`,
`{Reg π^*θ_{φ_i}} → {Reg π^*θ_φ}` in the Euclidean topology of `H^{1,1}(Y, ℝ)`. -/
theorem tendsto_regPullClass_of_dS (ω : KahlerBackground (m + 1) X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (π : Modification (m + 1) X) (ωY : KahlerBackground (m + 1) π.carrier)
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : Tendsto w F (@nhds _ (sourceSingularityTopology ω θ hbig) v)) :
    Tendsto (fun i => π.regPullClass (sourcePotentialCurrent θ (w i)).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _)) F
      (@nhds _ (euclideanTopology (RealBottChern (m + 1) π.carrier))
        (π.regPullClass (sourcePotentialCurrent θ v).current
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _))) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let Φ : SourceThetaPotentialL1 θ → RealBottChern (m + 1) π.carrier := fun a =>
    π.regPullClass (sourcePotentialCurrent θ a).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _)
  let C : RealBottChern (m + 1) π.carrier := classPullback π.isAnalyticModification.1
    (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))
  have hΦ : ∀ a, Φ a = C - π.divPullClass (sourcePotentialCurrent θ a).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _) := by
    intro a
    change π.regPullClass _ _ = _
    rw [Modification.regPullClass_eq, bottChernClass_sourcePotentialCurrent]
  have key : Tendsto Φ (𝓝 v)
      (@nhds _ (euclideanTopology (RealBottChern (m + 1) π.carrier)) (Φ v)) := by
    let : TopologicalSpace (RealBottChern (m + 1) π.carrier) := euclideanTopology _
    rw [tendsto_nhds_iff_seq_tendsto]
    intro x hx
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨g, -, hg⟩ := exists_strictMono_tendsto_divPullClass ω θ hbig π ωY (x ∘ ns) v
      (hx.comp hns)
    refine ⟨g, ?_⟩
    have hgoal : Tendsto (fun k => C - π.divPullClass (sourcePotentialCurrent θ (x (ns (g k)))).current
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _)) atTop
        (@nhds _ (euclideanTopology (RealBottChern (m + 1) π.carrier))
          (C - π.divPullClass (sourcePotentialCurrent θ v).current
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent _))) := by
      rw [tendsto_euclideanTopology_iff] at hg ⊢
      intro f
      simp only [map_sub]
      exact tendsto_const_nhds.sub (hg f)
    simpa only [Function.comp_def, hΦ] using hgoal
  exact key.comp hlim

/-- **`prop:dscontbdiv`** (chapter *The theory of b-divisors*). Let `X` be a connected compact
Kähler manifold, `θ` a closed real smooth `(1,1)`-form on `X` representing a big class, and
`(φ_i)` a net (here: a family along an arbitrary filter `F`) in `PSH(X, θ)` with
`φ_i → φ ∈ PSH(X, θ)` in `d_S`.  Then `𝔻(θ_{φ_i}) → 𝔻(θ_φ)`: on every model `π : Y → X` (finite
compositions of blow-ups with smooth centres), `𝔻(θ_{φ_i})_Y → 𝔻(θ_φ)_Y` in the Euclidean
topology of `H^{1,1}(Y, ℝ)`. -/
theorem currentBDivisor_converges_of_dS (ω : KahlerBackground (m + 1) X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : Tendsto w F (@nhds _ (sourceSingularityTopology ω θ hbig) v)) :
    WeilBDivisorOn.Converges F (fun i => currentBDivisor (sourcePotentialCurrent θ (w i)))
      (currentBDivisor (sourcePotentialCurrent θ v)) := by
  intro π
  obtain ⟨ωY⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
  exact tendsto_regPullClass_of_dS ω θ hbig π.1 ωY F w v hlim

end Main

end SGPT.Hodge.BDivChain
