import SGPT.Hodge.BDivChainDTVolume
import SGPT.Hodge.BDivChainLimit
import SGPT.Hodge.BDivChainIEnvelope
import SGPT.Hodge.ExceptionalBDivisor
import SGPT.PSH.SourceIModelGood
import SGPT.PSH.SourceSingularityPositiveCompleteness
import SGPT.PSH.BookCurrentLoci
import SGPT.Siu.SiuDecompositionClassLelong
import SGPT.BDivisor.MassPushforwardClassVolume
import SGPT.Okounkov.TranscendentalVolumeConcavityACVolume

/-!
# Realization of big and nef b-divisors (`thm:bigandnefreal`)

Source `thm:bigandnefreal` (chapter *The theory of b-divisors*): each big and nef b-divisor `𝔻`
over `X` can be realized as `𝔻(T)` for some `T ∈ 𝔻_X`; furthermore `T` may be taken `𝓘`-good.

The proof follows the book.  For every model `π : Y → X` take `T_Y` with minimal singularities in
`𝔻_Y` (`𝔻_Y` is big, `vol 𝔻_Y ≥ vol 𝔻 > 0`, and modified nef, `cor:mn_level_nefb`), so `T_Y` is
non-divisorial.

* `regPullClass_currentPushforward_of_nonDivisorial`: `𝔻(π'_*S)_{π'} = {S}` for `S`
  non-divisorial on `Y_{π'}` (Siu's pull–push lemma: `π'^*π'_*S = S + F_S` with `F_S` exceptional
  divisorial). Hence `𝔻(π_*T_Y)` coincides with `𝔻` on every model dominated by `π`.
* The net `π ↦ π_*T_Y` is decreasing for `≼_𝓘` (`lma:pushIpo`, HODGE-EXC), so the `𝓘`-envelopes
  `ψ_Y = P_θ[φ_Y]_𝓘` of their potentials are pointwise decreasing; their masses are
  `≥ vol 𝔻 > 0` (`∫ (π_*T_Y)^n = ∫ T_Y^n = vol 𝔻_Y`).  The book uses here that the `π_*T_Y` are
  `𝓘`-good (`cor:Igoodpush`, which rests on `prop:vollinearlimit` (5)); passing to the
  `𝓘`-envelopes avoids this.
* `cor:completenessdS` gives a `d_S`-limit `U`, `prop:dscontbdiv` gives `𝔻(θ_{ψ_Y}) → 𝔻(θ_U)`, and
  `𝔻(θ_{ψ_Y}) = 𝔻(π_*T_Y)` (`𝓘`-equivalence), so `𝔻(θ_U) = 𝔻`.
* `𝓘`-goodness: `P_θ[U]_𝓘` is `𝓘`-model of positive mass, hence `𝓘`-good (`ex:ImodelIgood`), with
  the same b-divisor.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

/-! ### `Reg π^*π_*S = S` for non-divisorial `S` -/

section PullPush

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))

/-- **`Reg(π^*π_*S) = S`** for a non-divisorial closed positive current `S` on the source of a
modification (`π^*π_*S = S + F_S`, `F_S` an effective combination of exceptional primes,
`lma:Siudec_pullpush`). -/
theorem siuRegularPart_pullPush {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {S : CurY} (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hnd : SGPT.Siu.IsNonDivisorial S hS) :
    SGPT.Siu.siuRegularPart (Modification4.pullPush hπ S hS)
      (Modification4.isClosedPositiveCurrent_pullPush hπ hS) = S := by
  classical
  obtain ⟨F, c, hF, hP⟩ := Modification4.pullback_pushforward_eq_add hπ hS hnd
  have hR := Exceptional.isClosedPositiveCurrent_sum F c (fun D hD => (hF D hD).2.le)
  have hR0 : SGPT.Currents.AnalyticSupport.CurrentEqOn
      (∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D) 0 (exceptionalLocus (m + 1) π)ᶜ := by
    have h := Modification4.currentEqOn_pullPush_sub_zero hπ hS
    have heq : S + ∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D - S =
        ∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D := by abel
    rw [hP, heq] at h
    exact h
  have hRdiv := (SGPT.Currents.AnalyticSupport.eq_siuDivisorialPart_of_currentEqOn_zero hR
    (HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1)
    (Modification4.interior_exceptionalLocus_eq_empty hπ) hR0).1
  rw [PrimePushforward.siuRegularPart_congr hP _ (hS.add hR),
    PrimePushforward.siuRegularPart_add hS hR (hS.add hR)]
  have h1 : SGPT.Siu.siuRegularPart S hS = S := hnd.symm
  have h2 : SGPT.Siu.siuRegularPart _ hR = 0 := by
    unfold SGPT.Siu.siuRegularPart
    rw [← hRdiv]
    exact sub_self (∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D)
  rw [h1, h2, add_zero]

end PullPush

section RegPush

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- **`𝔻(ρ_*S)_ρ = {S}`** for a non-divisorial closed positive current `S` on the model `ρ`. -/
theorem regPullClass_currentPushforward_of_nonDivisorial (ρ : Modification (m + 1) X)
    {S : GlobalCurrent (m + 1) ρ.carrier (degreeTwo (Nat.succ_pos m))}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hnd : SGPT.Siu.IsNonDivisorial S hS)
    (hPS : SGPT.Siu.IsClosedPositiveCurrent
      (currentPushforward ρ.isAnalyticModification.1 S)) :
    ρ.regPullClass (currentPushforward ρ.isAnalyticModification.1 S) hPS =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩ := by
  unfold Modification.regPullClass Modification.regPull
  apply bottChernClass_congr
  exact siuRegularPart_pullPush ρ.isAnalyticModification hS hnd

end RegPush

/-! ### Minimal singularities on models -/

section Minimal

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [CompactSpace M]

/-- The current `θ + ddᶜV_θ` of the minimal envelope has minimal singularities in `{θ}`. -/
theorem isMinimalSingularities_minimalEnvelope
    (θa : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M))
    (hmin : SourceMinimalSingularities θa (sourceMinimalEnvelope θa))
    (hV : IsThetaPshPotential (atlasClosedFormToNative θa).val (sourceMinimalEnvelope θa)) :
    SGPT.PSH.BookCurrent.IsMinimalSingularities
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θa))
      (SGPT.PSH.BookCurrent.thetaPositiveCurrent _ _ hV) := by
  refine ⟨SGPT.PSH.BookCurrent.currentClass_thetaPositiveCurrent _ _ hV, ?_⟩
  intro T' hT'
  obtain ⟨θ', u', h'⟩ := SGPT.PSH.BookCurrent.exists_presentation T'
  rw [SGPT.PSH.BookCurrent.moreSingular_iff_of_isPresentation h'
    (SGPT.PSH.BookCurrent.isPresentation_thetaPositiveCurrent _ _ hV)]
  have hcl : RealBottChern.ofRepresentative θ' =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θa) := by
    rw [← h'.currentClass_eq, hT']
  obtain ⟨g, hg, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff θ' _).mp hcl
  have hψ : IsThetaPshPotential (atlasClosedFormToNative θa).val (fun x => u' x - (g x : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hg hrel h'.isThetaPsh
  have hψa : (ofFixedModel (m + 1) M).IsThetaPSH θa (fun x => u' x - (g x : EReal)) :=
    (isThetaPSH_iff_nativeThetaPotential θa _).mpr hψ
  exact SGPT.PSH.singularityLE_trans (singularityLE_sub_chartSmooth hg u')
    (hmin.2 _ hψa)

variable [ConnectedSpace M]

/-- In a big modified nef class, the current with minimal singularities is non-divisorial. -/
theorem isNonDivisorial_minimalEnvelope (κ : KahlerBackground (m + 1) M)
    (θa : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M))
    (hmin : SourceMinimalSingularities θa (sourceMinimalEnvelope θa))
    (hV : IsThetaPshPotential (atlasClosedFormToNative θa).val (sourceMinimalEnvelope θa))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θa)))
    (hmn : SGPT.Siu.ClassModifiedNefWithRespectTo κ
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θa))) :
    SGPT.Siu.IsNonDivisorial (thetaPotentialCurrent _ _ hV)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hV) := by
  have hT := isMinimalSingularities_minimalEnvelope θa hmin hV
  have hpsef : SGPT.PSH.BookCurrent.IsPseudoeffective
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θa)) := ⟨_, hT.1⟩
  have hB : SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θa)) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr hbig
  rw [SGPT.Siu.isNonDivisorial_iff]
  intro E
  have h1 := (SGPT.Siu.modifiedNefWithRespectTo_iff_classGenericLelong κ _ hpsef).mp hmn E
  rw [SGPT.Siu.classGenericLelong, if_pos hB, SGPT.Siu.minimalGenericLelong_eq hT E,
    SGPT.Siu.bookGenericLelong_eq] at h1
  exact h1

end Minimal

/-! ### Volumes on models -/

section ModelVolume

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

theorem classVolume_lt_top (π : Modification (m + 1) X) [ConnectedSpace π.carrier]
    (κ : KahlerBackground (m + 1) π.carrier) (α : RealBottChern (m + 1) π.carrier) :
    Modification.classVolume π α < ⊤ := by
  let _ : MeasurableSpace π.carrier := borel π.carrier
  have : BorelSpace π.carrier := ⟨rfl⟩
  exact SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_lt_top κ α

theorem isBigClass_of_classVolume_pos (π : Modification (m + 1) X) [ConnectedSpace π.carrier]
    (κ : KahlerBackground (m + 1) π.carrier) {α : RealBottChern (m + 1) π.carrier}
    (h : 0 < Modification.classVolume π α) : IsBigClass α := by
  let _ : MeasurableSpace π.carrier := borel π.carrier
  have : BorelSpace π.carrier := ⟨rfl⟩
  exact (SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_pos_iff_isBigClass κ α).mp h

/-- `vol {θ} = ∫ θ_{V_θ}^n` on a model. -/
theorem classVolume_eq_minimalEnvelope_mass (π : Modification (m + 1) X) [ConnectedSpace π.carrier]
    (κ : KahlerBackground (m + 1) π.carrier)
    (θa : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) π.carrier))
    (hmin : SourceMinimalSingularities θa (sourceMinimalEnvelope θa))
    (hV : IsThetaPshPotential (atlasClosedFormToNative θa).val (sourceMinimalEnvelope θa)) :
    Modification.classVolume π (RealBottChern.ofRepresentative (atlasClosedFormToNative θa)) =
      @diagonalPotentialMass _ _ _ (borel π.carrier) _ _ _ (atlasClosedFormToNative θa)
        (sourceMinimalEnvelope θa) hV := by
  let _ : MeasurableSpace π.carrier := borel π.carrier
  have : BorelSpace π.carrier := ⟨rfl⟩
  exact sourceClassVolume_eq_minimalEnvelope_mass κ hmin.1

omit [ConnectedSpace X] in
theorem regPullClass_congr (π : Modification (m + 1) X)
    {T T' : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))} (h : T = T')
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T') :
    π.regPullClass T hT = π.regPullClass T' hT' := by
  subst h
  rfl

theorem currentPushforward_congr {Y Z : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [CompactSpace Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {f f' : Y → Z} (h : f = f')
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ f)
    (hf' : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ f')
    (T : GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))) :
    currentPushforward hf T = currentPushforward hf' T := by
  subst h
  rfl

end ModelVolume

/-! ### The realization -/

section Main

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- **`thm:bigandnefreal`, the core statement.** Let `𝔻` be a b-divisor over the book's models such
that every `𝔻_Y` is modified nef (with respect to every Kähler form of `Y`) and `vol 𝔻 > 0`. Then
there are a representative `θ` of `𝔻_X` and an `𝓘`-good `u ∈ PSH(X, θ)` with `𝔻(θ + ddᶜu) = 𝔻`. -/
theorem exists_iGood_currentBDivisor_eq (ωX : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m))
    (hmn : ∀ (π : (ModelSystem.blowup (m + 1) X).Model) (κ : KahlerBackground (m + 1) π.1.carrier),
      SGPT.Siu.ClassModifiedNefWithRespectTo κ (D.onModel π))
    (hbig : D.IsBig) :
    ∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)) (u : SourceThetaPotentialL1 θ),
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) = D.root ∧
      currentBDivisor (sourcePotentialCurrent θ u) = D ∧
      sourceIGoodWith θ u.val u.property := by
  classical
  have hK : Nonempty (KahlerBackground (m + 1) X) := ⟨ωX⟩
  -- `𝔻` is pseudo-effective with finite positive volume
  have hDpsef : D.IsPseudoeffective := by
    by_contra h
    have h0 := WeilBDivisorOn.vol_of_not_isPseudoeffective h
    rw [WeilBDivisorOn.IsBig, h0] at hbig
    exact lt_irrefl _ hbig
  have hpsefπ := (WeilBDivisorOn.isPseudoeffective_iff D).mp hDpsef
  have hconn : ∀ π : (ModelSystem.blowup (m + 1) X).Model, ConnectedSpace π.1.carrier :=
    fun π => Modification.IsBlowupModel.connectedSpace π.2
  have κ : ∀ π : (ModelSystem.blowup (m + 1) X).Model, KahlerBackground (m + 1) π.1.carrier :=
    fun π => Classical.choice (ModelSystem.blowup_nonempty_kahlerBackground hK π)
  have hvoltop : D.vol < ⊤ := by
    have := hconn ModelSystem.Model.root
    exact (D.vol_le_classVolume ModelSystem.Model.root).trans_lt
      (classVolume_lt_top _ (κ ModelSystem.Model.root) _)
  set δ : ℝ := D.vol.toReal with hδdef
  have hδ : 0 < δ := ENNReal.toReal_pos hbig.ne' hvoltop.ne
  have hδvol : ENNReal.ofReal δ = D.vol := ENNReal.ofReal_toReal hvoltop.ne
  -- per-model minimal currents
  have hdata : ∀ π : (ModelSystem.blowup (m + 1) X).Model,
      ∃ θπ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) π.1.carrier),
        RealBottChern.ofRepresentative (atlasClosedFormToNative θπ) = D.onModel π ∧
          SourceMinimalSingularities θπ (sourceMinimalEnvelope θπ) := by
    intro π
    have := hconn π
    exact exists_minimalSingularities_of_pseudoeffective (hpsefπ π)
  choose θπ hθπ using hdata
  have hVπ : ∀ π, IsThetaPshPotential (atlasClosedFormToNative (θπ π)).val
      (sourceMinimalEnvelope (θπ π)) :=
    fun π => (isThetaPSH_iff_nativeThetaPotential _ _).mp (hθπ π).2.1
  have hTπ : ∀ π, SGPT.Siu.IsClosedPositiveCurrent
      (thetaPotentialCurrent (atlasClosedFormToNative (θπ π)).val _ (hVπ π)) :=
    fun π => SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ (hVπ π)
  have hvolπ : ∀ π, D.vol ≤ Modification.classVolume π.1 (D.onModel π) :=
    fun π => D.vol_le_classVolume π
  have hbigπ : ∀ π, IsBigClass (D.onModel π) := by
    intro π
    have := hconn π
    exact isBigClass_of_classVolume_pos π.1 (κ π) (hbig.trans_le (hvolπ π))
  have hndπ : ∀ π, SGPT.Siu.IsNonDivisorial _ (hTπ π) := by
    intro π
    have := hconn π
    refine isNonDivisorial_minimalEnvelope (κ π) (θπ π) (hθπ π).2 (hVπ π) ?_ ?_
    · rw [(hθπ π).1]; exact hbigπ π
    · rw [(hθπ π).1]; exact hmn π (κ π)
  -- the push-forwards to `X`, in the class `𝔻_X`
  set θX : ClosedRealOneOneForm (m + 1) X := Quotient.out D.root with hθXdef
  have hθX : RealBottChern.ofRepresentative θX = D.root := Quotient.out_eq D.root
  have hSπ : ∀ π : (ModelSystem.blowup (m + 1) X).Model, SGPT.Siu.IsClosedPositiveCurrent
      (currentPushforward π.1.isAnalyticModification.1
        (thetaPotentialCurrent _ _ (hVπ π))) :=
    fun π => SGPT.Siu.isClosedPositiveCurrent_currentPushforward _ (hTπ π)
  have hpushD : ∀ {π ρ : (ModelSystem.blowup (m + 1) X).Model} (h : ρ ≤ π)
      {g : π.1.carrier → ρ.1.carrier}
      (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
      (hgc : ρ.1.map ∘ g = π.1.map),
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (closedCurrentPushforward hg (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (ThetaPotentialCurrentBottChernClass.thetaClosedCurrent _ _ (hVπ π))) =
        D.onModel ρ := by
    intro π ρ h g hg hgc
    rw [bottChernClass_closedCurrentPushforward,
      ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent, (hθπ π).1,
      ← D.pushforward_onModel h, Modification.classPushforwardOfLE_eq _ h hg hgc]
  have hclassS : ∀ π, bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨currentPushforward π.1.isAnalyticModification.1 (thetaPotentialCurrent _ _ (hVπ π)),
        (hSπ π).1, (hSπ π).2.1⟩ = RealBottChern.ofRepresentative θX := by
    intro π
    rw [hθX]
    exact hpushD (ModelSystem.Model.root_le π) π.1.isAnalyticModification.1 rfl
  have hrep : ∀ π : (ModelSystem.blowup (m + 1) X).Model, ∃ (φ : X → EReal)
      (hφ : IsThetaPshPotential θX.val φ),
      currentPushforward π.1.isAnalyticModification.1 (thetaPotentialCurrent _ _ (hVπ π)) =
        thetaPotentialCurrent θX.val φ hφ := by
    intro π
    obtain ⟨φ, hφ, hSeq, -⟩ :=
      PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
        ⟨_, (hSπ π).1, (hSπ π).2.1⟩ θX (hSπ π).2.2 (hclassS π)
    exact ⟨φ, hφ, hSeq⟩
  choose φ hφ hSeq using hrep
  set θXa := nativeClosedFormToAtlas θX with hθXa
  have hφa : ∀ π, (ofFixedModel (m + 1) X).IsThetaPSH θXa (φ π) :=
    fun π => (isThetaPSH_iff_nativeThetaPotential θXa _).mpr (hφ π)
  -- masses: `∫ (π_*T_Y)^n = ∫ T_Y^n = vol 𝔻_Y ≥ vol 𝔻`
  have hmassφ : ∀ π, D.vol ≤ diagonalPotentialMass θX (φ π) (hφ π) := by
    intro π
    have := hconn π
    let _ : MeasurableSpace π.1.carrier := borel π.1.carrier
    have : BorelSpace π.1.carrier := ⟨rfl⟩
    have h1 := SGPT.NPP.MassPushforward.globalMixedMeasure_univ_pushforward
      π.1.isAnalyticModification (fun _ => atlasClosedFormToNative (θπ π))
      (fun _ => sourceMinimalEnvelope (θπ π)) (fun _ => hVπ π) (fun _ => θX) (fun _ => φ π)
      (fun _ => hφ π) (fun _ => hSeq π)
    have h2 := classVolume_eq_minimalEnvelope_mass π.1 (κ π) (θπ π) (hθπ π).2 (hVπ π)
    rw [(hθπ π).1] at h2
    calc D.vol ≤ Modification.classVolume π.1 (D.onModel π) := hvolπ π
      _ = _ := h2
      _ = diagonalPotentialMass θX (φ π) (hφ π) := h1.symm
  -- the `𝓘`-envelopes
  let ψ : (ModelSystem.blowup (m + 1) X).Model → SourceThetaPotentialL1 θXa := fun π =>
    ⟨sourceIEnvelope θXa (φ π), isThetaPSH_sourceIEnvelope (hφa π)⟩
  have hstage : ∀ π, ENNReal.ofReal δ ≤
      sourcePotentialNonPluripolarMeasure θXa (ψ π).val (ψ π).property univ := by
    intro π
    rw [hδvol]
    exact le_trans (hmassφ π) (sourceMass_le_iVolume ωX (hφa π))
  -- the net `π ↦ ψ_π` decreases (`lma:pushIpo`)
  have hanti : Antitone fun π => (ψ π).val := by
    intro π π' h
    have hle : π.1 ≤ π'.1 := h
    have := hconn π
    let _ : MeasurableSpace π.1.carrier := borel π.1.carrier
    have : BorelSpace π.1.carrier := ⟨rfl⟩
    have hgm := Modification.Dominates.isAnalyticModification hle
    have hgc : π.1.map ∘ Modification.homOfLE hle = π'.1.map := Modification.map_comp_homOfLE hle
    set R := currentPushforward hgm.1 (thetaPotentialCurrent _ _ (hVπ π')) with hRdef
    have hR : SGPT.Siu.IsClosedPositiveCurrent R :=
      SGPT.Siu.isClosedPositiveCurrent_currentPushforward hgm.1 (hTπ π')
    have hRnd : SGPT.Siu.IsNonDivisorial R hR :=
      SGPT.Siu.isNonDivisorial_currentPushforward hgm (hTπ π') (hndπ π')
    have hRcl : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨R, hR.1, hR.2.1⟩ =
        RealBottChern.ofRepresentative (atlasClosedFormToNative (θπ π)) := by
      rw [(hθπ π).1]
      exact hpushD h hgm.1 hgc
    obtain ⟨w, hw, hReq, -⟩ :=
      PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
        ⟨R, hR.1, hR.2.1⟩ _ hR.2.2 hRcl
    have hwV : SGPT.PSH.SingularityLE w (sourceMinimalEnvelope (θπ π)) :=
      (hθπ π).2.2 w ((isThetaPSH_iff_nativeThetaPotential _ _).mpr hw)
    have hIO : IOrderOnManifold (n := m + 1) w (sourceMinimalEnvelope (θπ π)) :=
      GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SingularGlobalPOrder.sourcePOrder_of_moreSingularOn (κ π) _ _ hw (hVπ π) hwV)
    have hI : sourceCurrentIOrder R (thetaPotentialCurrent _ _ (hVπ π)) :=
      ⟨_, _, w, _, hw, hVπ π, hReq, rfl, hIO⟩
    have hRcl' : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨R, hR.1, hR.2.1⟩ =
        bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
          ⟨thetaPotentialCurrent _ _ (hVπ π), (hTπ π).1, (hTπ π).2.1⟩ :=
      hRcl.trans
        (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent _ _ (hVπ π)).symm
    have hpush := Exceptional.currentPushforward_sourceCurrentIOrder (κ π)
      π.1.isAnalyticModification hR (hTπ π) hRnd (hndπ π) hRcl' hI
    have hcomp : currentPushforward π.1.isAnalyticModification.1 R =
        currentPushforward π'.1.isAnalyticModification.1 (thetaPotentialCurrent _ _ (hVπ π')) := by
      rw [hRdef, ← currentPushforward_comp]
      exact currentPushforward_congr hgc _ _ _
    rw [hcomp, hSeq π', hSeq π] at hpush
    have hIX : IOrderOnManifold (n := m + 1) (φ π') (φ π) :=
      (sourceCurrentIOrder_iff_of_representation ωX (hφ π') (hφ π) rfl rfl).mp hpush
    have hQ : ∀ ρ, (ofFixedModel (m + 1) X).IsQPSH (φ ρ) := fun ρ => ⟨θXa, hφa ρ⟩
    exact (sourceIOrder_iff_sourceIEnvelope_le (hφa π') (hφa π)).mp
      ((sourceIOrder_iff_native (hQ π') (hQ π)).mpr hIX)
  -- The root of a big b-divisor is big, so completeness applies to this
  -- very same original background and to the original directed model net.
  have hatlas : atlasClosedFormToNative θXa = θX := by
    dsimp [θXa, nativeClosedFormToAtlas, atlasClosedFormToNative]
    rcases θX with ⟨θ, hθ⟩
    cases θ
    rfl
  have hbigX : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θXa)) := by
    rw [hatlas, hθX]
    exact hbigπ ModelSystem.Model.root
  obtain ⟨U, _hUmodel, hmassU, hUlim⟩ :=
    sourceSingularity_exists_model_limit_of_antitone ωX θXa hbigX ψ hanti hδ hstage
  have hconv := currentBDivisor_converges_of_dS ωX θXa hbigX atTop ψ U hUlim

  -- I-enveloping a source potential leaves its b-divisor unchanged.
  have hIbd (v : SourceThetaPotentialL1 θXa) :
      currentBDivisor (sourcePotentialCurrent θXa
          ⟨sourceIEnvelope θXa v.val, isThetaPSH_sourceIEnvelope v.property⟩) =
        currentBDivisor (sourcePotentialCurrent θXa v) := by
    have hv := (isThetaPSH_iff_nativeThetaPotential θXa v.val).mp v.property
    have heq := currentBDivisorOn_iEnvelope (ModelSystem.blowup (m + 1) X)
      (atlasClosedFormToNative θXa) v.val hv
    have hI := (isThetaPSH_iff_nativeThetaPotential θXa (sourceIEnvelope θXa v.val)).mp
      (isThetaPSH_sourceIEnvelope v.property)
    change currentBDivisorOn (ModelSystem.blowup (m + 1) X)
      (thetaPotentialCurrent (atlasClosedFormToNative θXa).val (sourceIEnvelope θXa v.val) hI)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hI) =
      currentBDivisorOn (ModelSystem.blowup (m + 1) X)
        (thetaPotentialCurrent (atlasClosedFormToNative θXa).val v.val hv)
        (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hv)
    simpa only [sourceIEnvelope_eq_native θXa v.val v.property] using heq

  -- Fix ρ. On every π ≥ ρ the model trace already equals D_ρ, using
  -- the actual pushforward of the non-divisorial current on π.
  have htrace : ∀ (ρ π : (ModelSystem.blowup (m + 1) X).Model), ρ ≤ π →
      (currentBDivisor (sourcePotentialCurrent θXa (ψ π))).onModel ρ = D.onModel ρ := by
    intro ρ π h
    have := hconn ρ
    have hgm := Modification.Dominates.isAnalyticModification h
    have hgc : ρ.1.map ∘ Modification.homOfLE h = π.1.map := Modification.map_comp_homOfLE h
    let R := currentPushforward hgm.1 (thetaPotentialCurrent _ _ (hVπ π))
    have hR : SGPT.Siu.IsClosedPositiveCurrent R :=
      SGPT.Siu.isClosedPositiveCurrent_currentPushforward hgm.1 (hTπ π)
    have hRnd : SGPT.Siu.IsNonDivisorial R hR :=
      SGPT.Siu.isNonDivisorial_currentPushforward hgm (hTπ π) (hndπ π)
    have hcomp : currentPushforward ρ.1.isAnalyticModification.1 R =
        currentPushforward π.1.isAnalyticModification.1 (thetaPotentialCurrent _ _ (hVπ π)) := by
      dsimp only [R]
      rw [← currentPushforward_comp]
      exact currentPushforward_congr hgc _ _ _
    have hclassR : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨R, hR.1, hR.2.1⟩ = D.onModel ρ := hpushD h hgm.1 hgc
    have henv := hIbd (⟨φ π, hφa π⟩ : SourceThetaPotentialL1 θXa)
    change (currentBDivisor (sourcePotentialCurrent θXa (ψ π))).onModel ρ = _
    rw [henv]
    change ρ.1.regPullClass
      (sourcePotentialCurrent θXa (⟨φ π, hφa π⟩ : SourceThetaPotentialL1 θXa)).current _ = _
    have hcur :
        (sourcePotentialCurrent θXa (⟨φ π, hφa π⟩ : SourceThetaPotentialL1 θXa)).current =
          thetaPotentialCurrent θX.val (φ π) (hφ π) := by
      change thetaPotentialCurrent (atlasClosedFormToNative θXa).val (φ π)
        ((isThetaPSH_iff_nativeThetaPotential θXa (φ π)).mp (hφa π)) = _
      subst θXa
      rcases θX with ⟨θX, hθX⟩
      cases θX
      rfl
    have hcurrent :
        (sourcePotentialCurrent θXa (⟨φ π, hφa π⟩ : SourceThetaPotentialL1 θXa)).current =
          currentPushforward ρ.1.isAnalyticModification.1 R :=
      hcur.trans ((hSeq π).symm.trans hcomp.symm)
    have hPS : SGPT.Siu.IsClosedPositiveCurrent (currentPushforward ρ.1.isAnalyticModification.1 R) :=
      SGPT.Siu.isClosedPositiveCurrent_currentPushforward ρ.1.isAnalyticModification.1 hR
    exact (regPullClass_congr ρ.1 hcurrent
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent
        (sourcePotentialCurrent θXa (⟨φ π, hφa π⟩ : SourceThetaPotentialL1 θXa))) hPS).trans
      ((regPullClass_currentPushforward_of_nonDivisorial ρ.1 hR hRnd hPS).trans hclassR)

  have hDU : currentBDivisor (sourcePotentialCurrent θXa U) = D := by
    apply WeilBDivisorOn.eq_of_converges_of_eventually_eq hconv
    intro ρ
    exact (eventually_ge_atTop ρ).mono fun π h => htrace ρ π h

  -- The I-envelope of U is I-model, has positive mass, and represents
  -- exactly the same b-divisor. No I-goodness assumption is supplied.
  let U' : SourceThetaPotentialL1 θXa :=
    ⟨sourceIEnvelope θXa U.val, isThetaPSH_sourceIEnvelope U.property⟩
  have hposU : 0 < sourcePotentialNonPluripolarMeasure θXa U.val U.property univ :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le hmassU
  have hposU' : 0 < sourcePotentialNonPluripolarMeasure θXa U'.val U'.property univ := by
    change 0 < sourceIVolume θXa U.val U.property
    exact hposU.trans_le (sourceMass_le_iVolume ωX U.property)
  have hgood : sourceIGoodWith θXa U'.val U'.property :=
    (sourceIModel_positive_iGood θXa U'.val (sourceIEnvelope_isIModel U.property) hposU').1
  refine ⟨θXa, U', ?_, ?_, hgood⟩
  · rw [hatlas, hθX]
  · exact (hIbd U).trans hDU

/-- The positive-dimensional blowup-model case of `thm:bigandnefreal`:
every big nef b-divisor is represented by an I-good current in its root class. -/
theorem exists_iGood_currentBDivisor_eq_of_big_nef (ωX : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m))
    (hbig : D.IsBig) (hnef : D.IsNef) :
    ∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)) (u : SourceThetaPotentialL1 θ),
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) = D.root ∧
      currentBDivisor (sourcePotentialCurrent θ u) = D ∧
      sourceIGoodWith θ u.val u.property := by
  apply exists_iGood_currentBDivisor_eq ωX D ?_ hbig
  intro π κ
  exact (WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup ⟨ωX⟩ hnef π).2 κ

end Main

end SGPT.Hodge.BDivChain
