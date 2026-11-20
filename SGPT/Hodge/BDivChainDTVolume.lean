import SGPT.Hodge.BDivChainDT
import SGPT.Hodge.BDivCone
import SGPT.Envelopes.SourceClassVolumeModification
import SGPT.Envelopes.SourceEnvelopeContactSupport
import SGPT.Foundations.Analysis.Pending.DominationResidualMass

/-!
# `vol T = vol 𝔻(T)` (`thm:DT`, second assertion)

Source `thm:DT` (chapter *The theory of b-divisors*), `eq:volDT`: for a closed positive
`(1,1)`-current `T` on the connected compact Kähler manifold `X`, `vol T = vol 𝔻(T)`, where
`vol T = vol(θ, φ) = ∫_X (θ + ddᶜP_θ[φ]_𝓘)^n` for any presentation `T = θ + ddᶜφ`
(`def:volqpsh`) and `vol 𝔻(T)` is the volume of the b-divisor (`def:volb`).

The proof follows the book's three steps.

* `vol_eq_classVolume_of_isRealization`: the volume of a pseudo-effective Cartier b-divisor
  realized by `(π, α)` is `vol α` (bimeromorphic invariance of class volumes,
  `sourceClassVolume_modification_pullback`, and the monotonicity `vol g_*β ≥ vol β`).
* Step 2, `currentBDivisorOn_vol_of_hasAnalyticSingularitiesOfType`: for `T = θ + ddᶜu` with
  analytic singularities of a global type, `vol 𝔻(T) = ∫_X ⟨T^n⟩`. On the log resolution
  (`DominationResidualMass.exists_logResolution_mass`), `𝔻(T)` is realized by
  `α = {π^*θ - Θ_F}`. The resolution supplies a bounded real residual in the global
  decomposition and a bounded residual θ-psh potential `b` agreeing with it off `Supp F`;
  the minimal potential of `α` has the singularity type of `b`. For the residual current
  `R = (π^*θ - Θ_F) + ddᶜb`,
  `vol α = ∫_Y ⟨R^n⟩ = ∫_X ⟨T^n⟩` (change of representative off `Supp F` and invariance of
  non-pluripolar masses under blow-ups).
* Step 3, `currentBDivisorOn_vol_of_isKahlerCurrentPotential`: for a Kähler current, along a
  quasi-equisingular approximation `(φ_j)` by Kähler currents with analytic singularities the
  b-divisors `𝔻(θ_{φ_j})` decrease and converge to `𝔻(T)` (`prop:dscontbdiv`), so
  `vol 𝔻(T) = lim vol 𝔻(θ_{φ_j})` (`lma:volbdivnet`) `= lim ∫⟨θ_{φ_j}^n⟩ = vol T`.
* Step 1, `currentBDivisor_vol`: `vol 𝔻(T + ε_k ω) → vol 𝔻(T)` (`lma:volbdivnet`) and
  `vol(T + ε_k ω) → vol T` (`prop:vollinearlimit`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

/-! ### Volumes of Cartier b-divisors -/

section Cartier

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **Bimeromorphic invariance of class volumes along dominations of the book's models**, for a
class with a smooth representative `σ` carrying a `σ`-psh potential. -/
theorem classVolume_classPullbackOfLE_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {π ρ : (ModelSystem.blowup (m + 1) X).Model} (h : π ≤ ρ)
    (σ : ClosedRealOneOneForm (m + 1) π.1.carrier) {b : π.1.carrier → EReal}
    (hb : IsThetaPshPotential σ.val b) :
    Modification.classVolume ρ.1
        (Modification.classPullbackOfLE (show π.1 ≤ ρ.1 from h)
          (RealBottChern.ofRepresentative σ)) =
      Modification.classVolume π.1 (RealBottChern.ofRepresentative σ) := by
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  have : BorelSpace π.1.carrier := ⟨rfl⟩
  let : MeasurableSpace ρ.1.carrier := borel ρ.1.carrier
  have : BorelSpace ρ.1.carrier := ⟨rfl⟩
  have : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.2
  have : ConnectedSpace ρ.1.carrier := Modification.IsBlowupModel.connectedSpace ρ.2
  obtain ⟨ωπ⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
  obtain ⟨ωρ⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK ρ
  have hg := Modification.Dominates.isAnalyticModification (show π.1 ≤ ρ.1 from h)
  have hba : (ofFixedModel (m + 1) π.1.carrier).IsThetaPSH (nativeClosedFormToAtlas σ) b :=
    (isThetaPSH_iff_nativeThetaPotential _ b).mpr hb
  exact sourceClassVolume_modification_pullback hg ωπ ωρ hba

/-- **The volume of a pseudo-effective Cartier b-divisor** realized by `(π, {σ})` is `vol {σ}`. -/
theorem vol_eq_classVolume_of_isRealization (hK : Nonempty (KahlerBackground (m + 1) X))
    {D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m)} (hD : D.IsPseudoeffective)
    {π : (ModelSystem.blowup (m + 1) X).Model} {σ : ClosedRealOneOneForm (m + 1) π.1.carrier}
    (hr : D.IsRealization π (RealBottChern.ofRepresentative σ)) {b : π.1.carrier → EReal}
    (hb : IsThetaPshPotential σ.val b) :
    D.vol = Modification.classVolume π.1 (RealBottChern.ofRepresentative σ) := by
  rw [WeilBDivisorOn.vol_of_isPseudoeffective hD]
  apply le_antisymm
  · refine iInf_le_of_le π ?_
    rw [hr.onModel_eq]
  · refine le_iInf fun ρ => ?_
    obtain ⟨ρ', h1, h2⟩ := ModelSystem.Model.exists_le_le π ρ
    calc Modification.classVolume π.1 (RealBottChern.ofRepresentative σ)
        = Modification.classVolume ρ'.1 (D.onModel ρ') := by
          rw [hr ρ' h1, classVolume_classPullbackOfLE_blowup hK h1 σ hb]
      _ ≤ Modification.classVolume ρ.1 (D.onModel ρ) :=
          WeilBDivisorOn.antitone_classVolume_blowup hK hD h2

end Cartier

/-! ### Step 2: analytic singularities -/

section Analytic

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- On a compact connected Kähler manifold, the class volume of `{σ}` is the mass of any bounded
`σ`-psh potential. -/
theorem sourceClassVolume_eq_mass_of_bounded {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z] [MeasurableSpace Z]
    [BorelSpace Z] [CompactSpace Z] [ConnectedSpace Z] (κ : KahlerBackground (m + 1) Z)
    (σ : ClosedRealOneOneForm (m + 1) Z) {b : Z → EReal} (hb : IsThetaPshPotential σ.val b)
    (C : ℝ) (hlow : ∀ y, ((-C : ℝ) : EReal) ≤ b y) (hup : ∀ y, b y ≤ (C : EReal)) :
    sourceClassVolume (RealBottChern.ofRepresentative σ) = diagonalPotentialMass σ b hb := by
  set σa := nativeClosedFormToAtlas σ
  have hba : (ofFixedModel (m + 1) Z).IsThetaPSH σa b :=
    (isThetaPSH_iff_nativeThetaPotential σa b).mpr hb
  have h1 := sourceClassVolume_eq_minimalEnvelope_mass κ hba
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hba
  have hVn := (isThetaPSH_iff_nativeThetaPotential σa _).mp hV
  change sourceClassVolume (RealBottChern.ofRepresentative (atlasClosedFormToNative σa)) = _
  rw [h1]
  change diagonalPotentialMass σ (sourceMinimalEnvelope σa) hVn = _
  -- `b - C ≤ V ≤ 0`
  have hbC : (ofFixedModel (m + 1) Z).IsThetaPSH σa (fun y => b y - (C : EReal)) :=
    (isThetaPSH_iff_nativeThetaPotential σa _).mpr (hb.sub_const C)
  have hle : ∀ y, b y - (C : EReal) ≤ sourceMinimalEnvelope σa y := fun y =>
    le_iSup (fun v : {v : Z → EReal // (ofFixedModel (m + 1) Z).IsThetaPSH σa v ∧ v ≤ 0} =>
      v.1 y) ⟨_, hbC, fun x => (EReal.sub_le_sub (hup x) le_rfl).trans EReal.sub_self_le_zero⟩
  have hm1 : MoreSingularOn (sourceMinimalEnvelope σa) b univ := by
    refine ⟨C, fun y _ => (sourceMinimalEnvelope_le_zero σa y).trans ?_⟩
    have h := add_le_add (hlow y) (le_refl (C : EReal))
    rw [← EReal.coe_add, neg_add_cancel, EReal.coe_zero] at h
    exact h
  have hm2 : MoreSingularOn b (sourceMinimalEnvelope σa) univ := by
    refine ⟨C, fun y _ => ?_⟩
    calc b y = (b y - (C : EReal)) + (C : EReal) := EReal.sub_add_cancel.symm
      _ ≤ sourceMinimalEnvelope σa y + (C : EReal) := add_le_add (hle y) le_rfl
  exact le_antisymm (diagonalPotentialMass_mono_of_kahler κ hVn hb hm1)
    (diagonalPotentialMass_mono_of_kahler κ hb hVn hm2)

/-- **`thm:DT`, Step 2 (volume): for `T = θ + ddᶜu` with analytic singularities of a global type,
`vol 𝔻(T) = ∫_X ⟨T^n⟩`.** -/
theorem currentBDivisorOn_vol_of_hasAnalyticSingularitiesOfType
    (ωX : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℚ} {𝔞 : GermIdeal (m + 1) X}
    (htype : HasAnalyticSingularitiesOfType u c 𝔞) :
    (currentBDivisorOn (ModelSystem.blowup (m + 1) X) (thetaPotentialCurrent θ.val u hu)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu)).vol =
        diagonalPotentialMass θ u hu := by
  obtain ⟨Z, tZ, cZ, mZ, ρ, hρ, hcpt, hconn, ⟨κ⟩, -, F, L, b, hb, hlow, hup, -, -, hmass⟩ :=
    DominationResidualMass.exists_logResolution_mass (Nat.succ_pos m) ωX θ hu htype
  let πM : (ModelSystem.blowup (m + 1) X).Model :=
    ⟨Modification.ofIsBlowupSequence hρ, Modification.isBlowupModel_ofIsBlowupSequence hρ⟩
  have hreal := currentBDivisorOn_isRealization_of_logSingularities
    (ModelSystem.blowup (m + 1) X) πM θ hu F L
  set σ : ClosedRealOneOneForm (m + 1) Z :=
    ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature with hσ
  have hsub : ∀ a b : ClosedRealOneOneForm (m + 1) Z, RealBottChern.ofRepresentative (a - b) =
      RealBottChern.ofRepresentative a - RealBottChern.ofRepresentative b := by
    intro a b
    have hab : a - b = a + (-1 : ℝ) • b := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hab, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul, neg_one_smul,
      sub_eq_add_neg]
  have hreal' : (currentBDivisorOn (ModelSystem.blowup (m + 1) X)
      (thetaPotentialCurrent θ.val u hu)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu)).IsRealization πM
      (classPullback hρ.contMDiff (RealBottChern.ofRepresentative θ) -
        RealBottChern.ofRepresentative F.curvature) := hreal
  have hα : classPullback hρ.contMDiff (RealBottChern.ofRepresentative θ) -
      RealBottChern.ofRepresentative F.curvature = RealBottChern.ofRepresentative σ := by
    rw [hσ, hsub]
    rfl
  rw [hα] at hreal'
  have hpsef := currentBDivisorOn_isPseudoeffective (ModelSystem.blowup (m + 1) X) _
    (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu)
  rw [vol_eq_classVolume_of_isRealization ⟨ωX⟩ hpsef hreal' hb]
  let : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  change sourceClassVolume (RealBottChern.ofRepresentative σ) = _
  rw [sourceClassVolume_eq_mass_of_bounded κ σ hb L.bound hlow hup]
  exact hmass

end Analytic

/-! ### Step 3: Kähler currents, and Step 1 -/

section Kahler

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- **`thm:DT` (volume) for Kähler currents.** If `θ + ddᶜφ` is a Kähler current, then
`vol 𝔻(θ + ddᶜφ) = vol(θ, φ)`. -/
theorem currentBDivisorOn_vol_of_isKahlerCurrentPotential (θ : ClosedRealOneOneForm (m + 1) X)
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) (hφθ : IsThetaPshPotential θ.val φ) :
    (currentBDivisorOn (ModelSystem.blowup (m + 1) X) (thetaPotentialCurrent θ.val φ hφθ)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφθ)).vol =
        iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφθ := by
  obtain ⟨U, hU⟩ := SGPT.Okounkov.PartialBody.exists_isKahlerQEA hφ
  obtain ⟨ω₀, ε, hnat⟩ := SGPT.PSH.native_of_sourceQuasiEquisingularApproximation hU.1
  have hbig := SGPT.Okounkov.PartialBody.isBigClass_of_isKahlerCurrentPotential hφ
  have hpos := SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ
    hnat.target
  obtain ⟨-, hI, -, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit ω₀ θ hbig
      hnat (fun j => (hU.2 j).1.1) hpos
  let θa := nativeClosedFormToAtlas θ
  let W : ℕ → SourceThetaPotentialL1 θa := fun j =>
    ⟨U j, (isThetaPSH_iff_nativeThetaPotential θa _).mpr (hU.2 j).1.1⟩
  let v : SourceThetaPotentialL1 θa :=
    ⟨iSingularityEnvelope θ.val φ, (isThetaPSH_iff_nativeThetaPotential θa _).mpr hI⟩
  have hsrc : Tendsto W atTop (@nhds _ (sourceSingularityTopology ω₀ θa hbig) v) :=
    (sourceSingularity_tendsto_iff_native atTop ω₀ θa hbig W v).mpr hlim
  have hconv := currentBDivisor_converges_of_dS ω₀ θa hbig atTop W v hsrc
  -- the b-divisors decrease
  have hanti : ∀ i j, i ≤ j → (currentBDivisor (sourcePotentialCurrent θa (W j))).LE
      (currentBDivisor (sourcePotentialCurrent θa (W i))) := by
    intro i j hij
    have hUi := (hU.2 i).1.1
    have hUj := (hU.2 j).1.1
    have hTi := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hUi
    have hTj := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hUj
    have hle : ∀ x, U j x ≤ U i x := fun x => hnat.term_antitone x hij
    have hP : SingularGlobalPOrder.SourcePOrder (n := m + 1) (U j) (U i) :=
      SingularGlobalPOrder.sourcePOrder_of_moreSingularOn ω₀ θ θ hUj hUi
        ⟨0, fun x _ => by simpa using hle x⟩
    have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
          ⟨thetaPotentialCurrent θ.val (U j) hUj, hTj.1, hTj.2.1⟩ =
        bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
          ⟨thetaPotentialCurrent θ.val (U i) hUi, hTi.1, hTi.2.1⟩ :=
      (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hUj).trans
        (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hUi).symm
    exact currentBDivisorOn_le_of_iOrder (ModelSystem.blowup (m + 1) X) hTj hTi hclass
      ⟨θ, θ, U j, U i, hUj, hUi, rfl, rfl,
        GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder hP⟩
  have hvolconv := WeilBDivisorOn.tendsto_vol_of_antitone_blowup ⟨ω₀⟩
    (fun j => currentBDivisor_isPseudoeffective _) hanti hconv
  -- Step 2 on each term
  have hvolj : ∀ j, (currentBDivisor (sourcePotentialCurrent θa (W j))).vol =
      diagonalPotentialMass θ (U j) (hU.2 j).1.1 := by
    intro j
    obtain ⟨c, 𝔞, htype⟩ := (hU.2 j).1.2
    exact currentBDivisorOn_vol_of_hasAnalyticSingularitiesOfType ω₀ θ (hU.2 j).1.1 htype
  have hmassconv := SGPT.Okounkov.PartialBody.tendsto_diagonalPotentialMass_of_isKahlerQEA hφ hU
  have hlimv : (currentBDivisor (sourcePotentialCurrent θa v)).vol =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφθ :=
    tendsto_nhds_unique hvolconv (hmassconv.congr fun j => (hvolj j).symm)
  -- `𝔻(θ_{P[φ]_𝓘}) = 𝔻(θ_φ)`
  have hTv := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hI
  have hTφ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφθ
  have hequiv := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hφθ.1.hasSmoothLocalPotentials φ hφθ
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨thetaPotentialCurrent θ.val (iSingularityEnvelope θ.val φ) hI, hTv.1, hTv.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨thetaPotentialCurrent θ.val φ hφθ, hTφ.1, hTφ.2.1⟩ :=
    (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hI).trans
      (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hφθ).symm
  have heq := currentBDivisorOn_eq_of_iEquivalent (ModelSystem.blowup (m + 1) X) hTv hTφ hclass
    ⟨θ, θ, _, φ, hI, hφθ, rfl, rfl, hequiv.2⟩ ⟨θ, θ, φ, _, hφθ, hI, rfl, rfl, hequiv.1⟩
  rw [← heq]
  exact hlimv

/-- **`thm:DT`, `eq:volDT`: `vol T = vol 𝔻(T)`** for every closed positive `(1,1)`-current `T` on
the connected compact Kähler manifold `X` and every presentation `T = θ + ddᶜφ`
(`vol T = vol(θ, φ)`, `def:volqpsh`; `vol 𝔻(T)`, `def:volb`, over the book's models). -/
theorem currentBDivisor_vol (ω : KahlerBackground (m + 1) X)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) {θ : ClosedRealOneOneForm (m + 1) X}
    {φ : X → EReal} (hpres : SGPT.PSH.BookCurrent.IsPresentation T θ φ) :
    (currentBDivisor T).vol =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hpres.isThetaPsh := by
  obtain ⟨hφ, hTeq⟩ := hpres
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  have hTφ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφ
  change (currentBDivisorOn _ T.current hT).vol = _
  rw [currentBDivisorOn_congr _ hTeq hT hTφ]
  have h0 : IsThetaPshPotential ω.form.val (fun _ : X => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr ω.isSemipositive,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  have hω := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ h0
  have hc : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hk : ∀ k : ℕ, SGPT.Siu.IsClosedPositiveCurrent
      (thetaPotentialCurrent θ.val φ hφ +
        (1 / ((k : ℝ) + 1)) • thetaPotentialCurrent ω.form.val (fun _ => 0) h0) :=
    fun k => hTφ.add (hω.smul (hc k).le)
  have h1 := currentBDivisorOn_tendsto_vol_add_blowup ⟨ω⟩ hTφ ω.form h0 hk
  -- the volume of each perturbation
  have hφk : ∀ k : ℕ, IsThetaPshPotential (θ + (1 / ((k : ℝ) + 1)) • ω.form).val φ := fun k =>
    LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (hc k).le)
  have hvolk : ∀ k : ℕ, (currentBDivisorOn (ModelSystem.blowup (m + 1) X) _ (hk k)).vol =
      iVolume (θ + (1 / ((k : ℝ) + 1)) • ω.form)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ (hφk k) := by
    intro k
    obtain ⟨hsm, hsmeq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul h0 (hc k).le
    obtain ⟨hadd, haddeq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hφ hsm
    have hfun : (fun x => φ x + ((1 / ((k : ℝ) + 1) : ℝ) : EReal) * 0) = φ := by
      funext x
      rw [mul_zero, add_zero]
    have hcur : thetaPotentialCurrent θ.val φ hφ +
        (1 / ((k : ℝ) + 1)) • thetaPotentialCurrent ω.form.val (fun _ => 0) h0 =
        thetaPotentialCurrent (θ + (1 / ((k : ℝ) + 1)) • ω.form).val φ (hφk k) := by
      rw [← hsmeq, ← haddeq]
      congr 1
    rw [currentBDivisorOn_congr _ hcur (hk k)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ (hφk k))]
    have hK : IsKahlerCurrentPotential (θ + (1 / ((k : ℝ) + 1)) • ω.form) φ := by
      refine ⟨KahlerBackground.smul (hc k) ω, ?_⟩
      rw [KahlerBackground.smul_form, add_sub_cancel_right]
      exact hφ
    exact currentBDivisorOn_vol_of_isKahlerCurrentPotential _ hK (hφk k)
  -- `vol(T + ε_k ω) → vol T`
  have h2 := SGPT.Okounkov.PartialBody.tendsto_iVolume_add_smul ω hφ
  let t : ℕ → ℝ≥0 := fun k => ⟨1 / ((k : ℝ) + 1), (hc k).le⟩
  have ht : Tendsto t atTop (𝓝[>] (0 : ℝ≥0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · rw [← NNReal.tendsto_coe]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    · change (0 : ℝ≥0) < t k
      rw [← NNReal.coe_lt_coe]
      exact hc k
  have h3 : Tendsto (fun k : ℕ =>
      (currentBDivisorOn (ModelSystem.blowup (m + 1) X) _ (hk k)).vol) atTop
      (𝓝 (iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ)) :=
    (h2.comp ht).congr fun k => (hvolk k).symm
  exact tendsto_nhds_unique h1 h3

end Kahler

end SGPT.Hodge.BDivChain
