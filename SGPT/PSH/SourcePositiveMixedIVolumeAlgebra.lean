import SGPT.PSH.SourcePositiveMixedIVolume
import SGPT.Envelopes.SourceIEnvelopeAlgebra
import SGPT.PSH.SourceIModelGood
import SGPT.PSH.SourceIGoodOperations
import SGPT.PSH.SourceMixedPOrderMonotonicity
import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence

/-! # Whole positive mixed I-volume laws in the original independent backgrounds -/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem sourceUpdatePSH
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n) {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {v : M → EReal} (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    ∀ i, (ofFixedModel n M).IsThetaPSH (Function.update θ a σ i)
      (Function.update u a v i) := by
  intro i
  by_cases hi : i = a
  · subst i; simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hi] using hu i

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem sourceAddKahlerPSH (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (ε : NNReal) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ε.property)

/-- The actual independent current family Tᵢ+εω, for every nonnegative real ε,
with each unchanged original potential and its genuine PSH domain produced. -/
def sourceMixedIVolumeKahlerPerturbation (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) (ε : NNReal) : ENNReal :=
  sourceEnvelopeMixedIVolume
    (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (ε : ℝ) • ω.form))
    u (fun i => sourceAddKahlerPSH ω (hu i) ε)

private theorem sourceIGood_PEquivalent_iEnvelope (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hg : sourceIGood (n := n) u) :
    GlobalPComparison.sourcePEquivalent (n := n) u (sourceIEnvelope θ u) := by
  have he := (sourceIGood_iff_PI_eq ω hu hpos).mp hg
  rw [← he, sourceSingularityEnvelope_eq_native]
  exact SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope ω
    (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem native_update
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (a : Fin n)
    (σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    (fun i => atlasClosedFormToNative (Function.update θ a σ i)) =
      Function.update (fun i => atlasClosedFormToNative (θ i)) a (atlasClosedFormToNative σ) := by
  classical
  funext i
  by_cases hi : i = a <;> simp [hi, Function.update_of_ne]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem envelope_update
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (a : Fin n) (σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (v : M → EReal) :
    (fun i => sourceIEnvelope (Function.update θ a σ i) (Function.update u a v i)) =
      Function.update (fun i => sourceIEnvelope (θ i) (u i)) a (sourceIEnvelope σ v) := by
  classical
  funext i
  by_cases hi : i = a <;> simp [hi, Function.update_of_ne]

omit [ConnectedSpace M] in
private theorem sourceIndependentSum_mass_pos (ω : KahlerBackground n M)
    {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    0 < sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
      (fun x => u x + v x) (sourceIndependentSum_thetaPSH hu hv) univ := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b =>
    if b then atlasClosedFormToNative σ else atlasClosedFormToNative θ
  let f : Bool → M → EReal := fun b => if b then v else u
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
  have hf b : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hun
    · exact hvn
  have hs := (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (sourceIndependentSum_thetaPSH hu hv)
  rw [sourceNativeAtlasForm_roundTrip] at hs
  have esθ : (fun _ : Fin n => GlobalMultilinearExpansion.sumForm
      Finset.univ (fun _ : Bool => (1 : ℝ)) α) =
      fun _ => atlasClosedFormToNative θ + atlasClosedFormToNative σ := by
    funext i
    simp [GlobalMultilinearExpansion.sumForm, α, add_comm]
  have esp : (fun _ : Fin n => GlobalMultilinearExpansion.sumPot
      Finset.univ (fun _ : Bool => (1 : ℝ)) f) = fun _ x => u x + v x := by
    funext i x
    simp [GlobalMultilinearExpansion.sumPot, f, add_comm]
  have he := MixedMassProductCalculus.globalMixedMeasure_sumPot_expand ω
    (c := fun (_ : Fin n) (_ : Bool) => (1 : ℝ)) (fun _ _ => zero_le_one) hf
  rw [GlobalDiagonalScaling.globalMixedMeasure_congr esθ esp _ (fun _ => hs.1)] at he
  have hexp := congrArg (fun μ : Measure M => μ univ) he
  rw [Measure.coe_finsetSum, Finset.sum_apply] at hexp
  have hp : 0 < MixedMass.globalMixedMass (fun _ : Fin n => atlasClosedFormToNative θ)
      (fun _ => u) (fun _ => hun.1) := by
    rw [← sourceMixedNonPluripolarMass_diagonal θ u hu,
      sourceMixedNonPluripolarMass_eq_native] at hpos
    exact hpos
  have hle : MixedMass.globalMixedMass (fun _ : Fin n => atlasClosedFormToNative θ)
      (fun _ => u) (fun _ => hun.1) ≤
      ∑ g : Fin n → Bool, (ENNReal.ofReal (∏ _ : Fin n, (1 : ℝ)) •
        GlobalNonPluripolar.globalMixedMeasure (fun k => α (g k))
          (fun k => f (g k)) (fun k => (hf (g k)).1)) univ := by
    simpa only [α, f, Bool.false_eq_true, if_false, MixedMass.globalMixedMass,
      Finset.prod_const_one, ENNReal.ofReal_one, one_smul] using
      (Finset.single_le_sum (fun (g : Fin n → Bool) _ =>
        (zero_le : 0 ≤ ((ENNReal.ofReal (∏ _ : Fin n, (1 : ℝ)) •
          GlobalNonPluripolar.globalMixedMeasure (fun k => α (g k))
            (fun k => f (g k)) (fun k => (hf (g k)).1)) univ)))
        (Finset.mem_univ (fun _ : Fin n => false)))
  rw [← hexp] at hle
  rw [← sourceMixedNonPluripolarMass_diagonal _ _ (sourceIndependentSum_thetaPSH hu hv),
    sourceMixedNonPluripolarMass_eq_native]
  simpa only [sourceNativeAtlasForm_roundTrip, MixedMass.globalMixedMass] using hp.trans_le hle

omit [ConnectedSpace M] in
private theorem sourceMixedMass_add_slot
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n) (σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourceMixedNonPluripolarMass
      (Function.update θ a (nativeClosedFormToAtlas
        (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ)))
      (Function.update u a (fun x => u a x + v x))
      (sourceUpdatePSH hu a (sourceIndependentSum_thetaPSH (hu a) hv)) =
      sourceMixedNonPluripolarMass θ u hu +
        sourceMixedNonPluripolarMass (Function.update θ a σ) (Function.update u a v)
          (sourceUpdatePSH hu a hv) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b =>
    if b then atlasClosedFormToNative σ else atlasClosedFormToNative (θ a)
  let f : Bool → M → EReal := fun b => if b then v else u a
  have hun i := (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)
  have hvn := (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
  have hf b : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hun a
    · exact hvn
  have hsum := (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (sourceIndependentSum_thetaPSH (hu a) hv)
  rw [sourceNativeAtlasForm_roundTrip] at hsum
  have esθ : GlobalMultilinearExpansion.sumForm Finset.univ (fun _ : Bool => (1 : ℝ)) α =
      atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ := by
    simp [GlobalMultilinearExpansion.sumForm, α, add_comm]
  have esp : GlobalMultilinearExpansion.sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f =
      fun x => u a x + v x := by
    funext x
    simp [GlobalMultilinearExpansion.sumPot, f, add_comm]
  have he := GlobalMultilinearExpansion.globalMixedMeasure_update_sum (ι := Bool) a
    (fun i _ => (hun i).1) (T := Finset.univ) Finset.univ_nonempty
    (w := fun _ => (1 : ℝ)) (fun _ => zero_lt_one) (fun b => (hf b).1)
    (fun b => ⟨(hf b).1.quasiPlurisubharmonic, (hf b).2⟩)
  simp only [esθ, esp, Fintype.sum_bool, α, f, Bool.false_eq_true, if_false, if_true,
    ENNReal.ofReal_one, one_smul, Function.update_eq_self] at he
  have eθ := native_update θ a (nativeClosedFormToAtlas
    (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ))
  rw [sourceNativeAtlasForm_roundTrip] at eθ
  simp only [sourceMixedNonPluripolarMass_eq_native, MixedMass.globalMixedMass]
  rw [GlobalDiagonalScaling.globalMixedMeasure_congr eθ rfl _
    (GlobalMultilinearExpansion.update_thetaPlurisubharmonic (fun i _ => (hun i).1) hsum.1),
    GlobalDiagonalScaling.globalMixedMeasure_congr (native_update θ a σ) rfl _
      (GlobalMultilinearExpansion.update_thetaPlurisubharmonic (fun i _ => (hun i).1) hvn.1)]
  have heval := congrArg (fun μ : Measure M => μ univ) he
  simpa only [Measure.add_apply, add_comm] using heval

omit [BorelSpace M] [ConnectedSpace M] in
private theorem sourceMixedMass_eq_of_potentials_eq
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u v : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i)) (h : u = v) :
    sourceMixedNonPluripolarMass θ u hu = sourceMixedNonPluripolarMass θ v hv := by
  subst v
  rfl

omit [BorelSpace M] in
private theorem sourceEnvelopeMixedIVolume_update
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n) (σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourceEnvelopeMixedIVolume (Function.update θ a σ) (Function.update u a v)
      (sourceUpdatePSH hu a hv) =
      sourceMixedNonPluripolarMass (Function.update θ a σ)
        (Function.update (fun i => sourceIEnvelope (θ i) (u i)) a (sourceIEnvelope σ v))
        (sourceUpdatePSH (fun i => isThetaPSH_sourceIEnvelope (hu i)) a
          (isThetaPSH_sourceIEnvelope hv)) :=
  sourceMixedMass_eq_of_potentials_eq _ _ _ _ _ (envelope_update θ u a σ v)

/-- Whole independent-current slot addition. All positivity and P-equivalence
needed for the actual sum are derived from the original positive I-volumes. -/
theorem sourceEnvelopeMixedIVolume_add_slot (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i))
    (a : Fin n) (σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH σ v)
    (hvpos : 0 < sourceIVolume σ v hv) :
    sourceEnvelopeMixedIVolume
      (Function.update θ a (nativeClosedFormToAtlas
        (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ)))
      (Function.update u a (fun x => u a x + v x))
      (sourceUpdatePSH hu a (sourceIndependentSum_thetaPSH (hu a) hv)) =
      sourceEnvelopeMixedIVolume θ u hu +
        sourceEnvelopeMixedIVolume (Function.update θ a σ) (Function.update u a v)
          (sourceUpdatePSH hu a hv) := by
  classical
  let U : Fin n → M → EReal := fun i => sourceIEnvelope (θ i) (u i)
  let W : M → EReal := sourceIEnvelope σ v
  let τ := nativeClosedFormToAtlas (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ)
  have hU i : (ofFixedModel n M).IsThetaPSH (θ i) (U i) :=
    isThetaPSH_sourceIEnvelope (hu i)
  have hW : (ofFixedModel n M).IsThetaPSH σ W := isThetaPSH_sourceIEnvelope hv
  have hsum := sourceIndependentSum_thetaPSH (hU a) hW
  have hsumpos := sourceIndependentSum_mass_pos ω (hU a) hW (hpos a)
  have hgoodU := (sourceIModel_positive_iGood (θ a) (U a)
    (sourceIEnvelope_isIModel (hu a)) (hpos a)).2
  have hgoodW := (sourceIModel_positive_iGood σ W
    (sourceIEnvelope_isIModel hv) hvpos).2
  have hPeq := sourceIGood_PEquivalent_iEnvelope ω hsum hsumpos
    (sourceIGood_add ω hgoodU hgoodW)
  have hI : sourceIEquivalent (ofFixedModel n M)
      (fun x => u a x + v x) (fun x => U a x + W x) :=
    sourceIEquivalent_trans (sourceIEquivalent_iEnvelope
      (sourceIndependentSum_thetaPSH (hu a) hv))
      (sourceIEnvelope_independent_add_equivalent (hu a) hv)
  have heq : sourceIEnvelope τ (fun x => U a x + W x) =
      sourceIEnvelope τ (fun x => u a x + v x) :=
    (sourceIEnvelope_eq_of_equivalent hI).symm
  rw [heq] at hPeq
  have hslot : ∀ i, GlobalPComparison.sourcePEquivalent (n := n)
      (Function.update U a (sourceIEnvelope τ (fun x => u a x + v x)) i)
      (Function.update U a (fun x => U a x + W x) i) := by
    intro i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self]
      exact ⟨hPeq.2, hPeq.1⟩
    · simp only [Function.update_of_ne hi]
      have hn := (isThetaPSH_iff_nativeThetaPotential (θ i) (U i)).mp (hU i)
      have hr := GlobalPComparison.sourcePOrder_refl ω
        ⟨hn.1.quasiPlurisubharmonic, hn.2⟩
      exact ⟨hr, hr⟩
  rw [sourceEnvelopeMixedIVolume_update θ u hu a τ (fun x => u a x + v x)
    (sourceIndependentSum_thetaPSH (hu a) hv),
    sourceEnvelopeMixedIVolume_update θ u hu a σ v hv]
  change sourceMixedNonPluripolarMass (Function.update θ a τ) _ _ = _
  rw [sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω
    (sourceUpdatePSH hU a (isThetaPSH_sourceIEnvelope
      (sourceIndependentSum_thetaPSH (hu a) hv))) (sourceUpdatePSH hU a hsum) hslot]
  exact sourceMixedMass_add_slot θ U hU a σ W hW

private def mixedBackgroundPolynomial (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) (ε : NNReal) : ℝ :=
  ∑ g : Fin n → Option (Fin n), (ε : ℝ) ^ CanonicalBackgroundPolynomial.backgroundDegree g *
    (if ∀ i, g i ∈ CanonicalBackgroundPolynomial.backgroundChoices i then
      (MixedMass.globalMixedMass (fun i => MixedMassBoundedDifference.optForm ω θ (g i))
        (fun i => MixedMassBoundedDifference.optPot u (g i))
        (fun i => MixedMassBoundedDifference.optPot_psh ω hu (g i))).toReal else 0)

omit [BorelSpace M] [ConnectedSpace M] in
private theorem mixedBackgroundPolynomial_zero (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) :
    mixedBackgroundPolynomial ω θ u hu 0 =
      (MixedMass.globalMixedMass θ u (fun i => (hu i).1)).toReal := by
  classical
  let d : (Fin n → Option (Fin n)) → ℝ := fun g =>
    (MixedMass.globalMixedMass (fun i => MixedMassBoundedDifference.optForm ω θ (g i))
      (fun i => MixedMassBoundedDifference.optPot u (g i))
      (fun i => MixedMassBoundedDifference.optPot_psh ω hu (g i))).toReal
  change (∑ g, (0 : ℝ) ^ CanonicalBackgroundPolynomial.backgroundDegree g *
    (if ∀ i, g i ∈ CanonicalBackgroundPolynomial.backgroundChoices i then d g else 0)) = _
  calc
    _ = ∑ g with CanonicalBackgroundPolynomial.backgroundDegree g = 0,
        if ∀ i, g i ∈ CanonicalBackgroundPolynomial.backgroundChoices i then d g else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hd : CanonicalBackgroundPolynomial.backgroundDegree g = 0 <;> simp [hd]
    _ = d (fun i => some i) := CanonicalBackgroundPolynomial.sum_zero_background_degree d
    _ = _ := rfl

omit [ConnectedSpace M] in
private theorem mixedBackgroundPolynomial_eq (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {ε : NNReal} (hε : 0 < (ε : ℝ)) :
    (MixedMass.globalMixedMass (fun i => θ i + (ε : ℝ) • ω.form) u
      (fun i => (CanonicalBackgroundPolynomial.isThetaPshPotential_add_background ω hu
        ε.property i).1)).toReal = mixedBackgroundPolynomial ω θ u hu ε := by
  classical
  have he := SingularPBackgroundMassPolynomial.globalMixedMass_add_background_toReal_eq_sum ω hu hε
  have es : Fintype.piFinset (CanonicalBackgroundPolynomial.backgroundChoices (n := n)) =
      Finset.univ.filter (fun g => ∀ i, g i ∈ CanonicalBackgroundPolynomial.backgroundChoices i) := by
    ext g
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [es, Finset.sum_filter] at he
  rw [he]
  unfold mixedBackgroundPolynomial
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ∀ i, g i ∈ CanonicalBackgroundPolynomial.backgroundChoices i <;> simp [hg]

private theorem sourcePerturbation_eq_mixedMass (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i))
    {ε : NNReal} (hε : 0 < (ε : ℝ)) :
    sourceMixedIVolumeKahlerPerturbation ω θ u hu ε =
      MixedMass.globalMixedMass
        (fun i => atlasClosedFormToNative (θ i) + (ε : ℝ) • ω.form)
        (fun i => sourceIEnvelope (θ i) (u i))
        (fun i => (CanonicalBackgroundPolynomial.isThetaPshPotential_add_background ω
          (fun j => (isThetaPSH_iff_nativeThetaPotential (θ j) _).mp
            (isThetaPSH_sourceIEnvelope (hu j))) ε.property i).1) := by
  let U : Fin n → M → EReal := fun i => sourceIEnvelope (θ i) (u i)
  let Γ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M) := fun i =>
    nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (ε : ℝ) • ω.form)
  have hU i : (ofFixedModel n M).IsThetaPSH (θ i) (U i) :=
    isThetaPSH_sourceIEnvelope (hu i)
  have hUΓ i : (ofFixedModel n M).IsThetaPSH (Γ i) (U i) :=
    sourceAddKahlerPSH ω (hU i) ε
  have hgood i := (sourceIModel_positive_iGood (θ i) (U i)
    (sourceIEnvelope_isIModel (hu i)) (hpos i)).2
  have hp i : 0 < sourcePotentialNonPluripolarMeasure (Γ i) (U i) (hUΓ i) univ := by
    have ht := SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω
      ((isThetaPSH_iff_nativeThetaPotential (θ i) (U i)).mp (hU i)) hε
    simpa only [sourcePotentialNonPluripolarMeasure, Γ, sourceNativeAtlasForm_roundTrip,
      DiagonalMass.HasPositivePotentialMass, DiagonalMass.diagonalPotentialMass] using ht
  have hPeq i : GlobalPComparison.sourcePEquivalent (n := n)
      (U i) (sourceIEnvelope (Γ i) (u i)) := by
    have ht := sourceIGood_PEquivalent_iEnvelope ω (hUΓ i) (hp i) (hgood i)
    have he : sourceIEnvelope (Γ i) (u i) = sourceIEnvelope (Γ i) (U i) :=
      sourceIEnvelope_eq_of_equivalent (sourceIEquivalent_iEnvelope (hu i))
    rw [← he] at ht
    exact ht
  have hm := sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω hUΓ
    (fun i => isThetaPSH_sourceIEnvelope (sourceAddKahlerPSH ω (hu i) ε)) hPeq
  change sourceMixedNonPluripolarMass Γ (fun i => sourceIEnvelope (Γ i) (u i)) _ = _
  rw [← hm, sourceMixedNonPluripolarMass_eq_native]
  simp only [Γ, sourceNativeAtlasForm_roundTrip]
  rfl

/-- The printed right Kähler limit, on the actual nonnegative real family.
Positive I-volumes, rather than positive masses of the original uᵢ, suffice. -/
theorem sourceEnvelopeMixedIVolume_tendsto_add_kahler (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i)) :
    Tendsto (sourceMixedIVolumeKahlerPerturbation ω θ u hu) (𝓝 (0 : NNReal))
      (𝓝 (sourceEnvelopeMixedIVolume θ u hu)) := by
  classical
  let U : Fin n → M → EReal := fun i => sourceIEnvelope (θ i) (u i)
  have hU i := (isThetaPSH_iff_nativeThetaPotential (θ i) (U i)).mp
    (isThetaPSH_sourceIEnvelope (hu i))
  let P : NNReal → ℝ := mixedBackgroundPolynomial ω (fun i => atlasClosedFormToNative (θ i)) U hU
  have hpzero : P 0 = (sourceEnvelopeMixedIVolume θ u hu).toReal :=
    mixedBackgroundPolynomial_zero ω _ U hU
  have hpcont : Continuous P := by
    change Continuous (fun ε : NNReal => P ε)
    unfold P mixedBackgroundPolynomial
    fun_prop
  have hzero : sourceMixedIVolumeKahlerPerturbation ω θ u hu 0 =
      sourceEnvelopeMixedIVolume θ u hu := by
    unfold sourceMixedIVolumeKahlerPerturbation
    congr 1
    funext i
    simp only [NNReal.coe_zero, zero_smul, add_zero]
    cases θ i
    rfl
  have hfinite ε : sourceMixedIVolumeKahlerPerturbation ω θ u hu ε ≠ ⊤ :=
    (sourceEnvelopeMixedIVolume_lt_top ω _ u (fun i => sourceAddKahlerPSH ω (hu i) ε)).ne
  have hreal (ε : NNReal) (hε : 0 < (ε : ℝ)) :
      (sourceMixedIVolumeKahlerPerturbation ω θ u hu ε).toReal = P ε := by
    rw [sourcePerturbation_eq_mixedMass ω θ u hu hpos hε]
    exact mixedBackgroundPolynomial_eq ω _ U hU hε
  have he : sourceMixedIVolumeKahlerPerturbation ω θ u hu =
      fun ε => ENNReal.ofReal (P ε) := by
    funext ε
    by_cases hε : ε = 0
    · subst ε
      rw [hzero, hpzero, ENNReal.ofReal_toReal (sourceEnvelopeMixedIVolume_lt_top ω θ u hu).ne]
    · have hεpos : 0 < (ε : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
      rw [← hreal ε hεpos, ENNReal.ofReal_toReal (hfinite ε)]
  rw [he]
  have ht := ENNReal.tendsto_ofReal (hpcont.tendsto 0)
  simpa only [hpzero, ENNReal.ofReal_toReal (sourceEnvelopeMixedIVolume_lt_top ω θ u hu).ne] using ht

/-- Whole slot homogeneity for an arbitrary positive REAL scalar, with actual
scaled backgrounds and potentials. It also holds when an original I-volume is zero. -/
theorem sourceEnvelopeMixedIVolume_positive_smul_slot
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (a : Fin n) {c : ℝ} (hc : 0 < c) :
    sourceEnvelopeMixedIVolume
      (Function.update θ a (nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ a))))
      (Function.update u a (fun x => (c : EReal) * u a x))
      (sourceUpdatePSH hu a (sourcePositiveScaling_thetaPSH (hu a) hc)) =
      ENNReal.ofReal c * sourceEnvelopeMixedIVolume θ u hu := by
  classical
  let U : Fin n → M → EReal := fun i => sourceIEnvelope (θ i) (u i)
  have hU i := (isThetaPSH_iff_nativeThetaPotential (θ i) (U i)).mp
    (isThetaPSH_sourceIEnvelope (hu i))
  have he := GlobalMultilinearExpansion.globalMixedMeasure_update_smul a
    (fun i _ => (hU i).1) hc (hU a).1 ⟨(hU a).1.quasiPlurisubharmonic, (hU a).2⟩
  have eθ := native_update θ a
    (nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ a)))
  rw [sourceNativeAtlasForm_roundTrip] at eθ
  have eu := envelope_update θ u a
    (nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ a)))
    (fun x => (c : EReal) * u a x)
  rw [sourceIEnvelope_positiveScaling (hu a) hc] at eu
  simp only [sourceEnvelopeMixedIVolume_eq_native, MixedMass.globalMixedMass]
  rw [GlobalDiagonalScaling.globalMixedMeasure_congr eθ eu _
    (GlobalMultilinearExpansion.update_thetaPlurisubharmonic (fun i _ => (hU i).1)
      (GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hc (hU a).1)), he]
  simp only [Function.update_eq_self, Measure.smul_apply, smul_eq_mul, U]

/-- All FIVE clauses of original `lma:vollinearlimit2`, retaining independent
forms, arbitrary positive real scalars and different cohomologous representatives. -/
theorem sourcePositiveMixedIVolume_laws (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i)) :
    (∀ π : Equiv.Perm (Fin n),
      sourceEnvelopeMixedIVolume (fun i => θ (π i)) (fun i => u (π i)) (fun i => hu (π i)) =
        sourceEnvelopeMixedIVolume θ u hu) ∧
    Tendsto (sourceMixedIVolumeKahlerPerturbation ω θ u hu) (𝓝 (0 : NNReal))
      (𝓝 (sourceEnvelopeMixedIVolume θ u hu)) ∧
    (∀ (a : Fin n) (σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
      (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH σ v),
      0 < sourceIVolume σ v hv →
      sourceEnvelopeMixedIVolume
        (Function.update θ a (nativeClosedFormToAtlas
          (atlasClosedFormToNative (θ a) + atlasClosedFormToNative σ)))
        (Function.update u a (fun x => u a x + v x))
        (sourceUpdatePSH hu a (sourceIndependentSum_thetaPSH (hu a) hv)) =
        sourceEnvelopeMixedIVolume θ u hu +
          sourceEnvelopeMixedIVolume (Function.update θ a σ) (Function.update u a v)
            (sourceUpdatePSH hu a hv)) ∧
    (∀ (a : Fin n) (c : ℝ) (hc : 0 < c),
      sourceEnvelopeMixedIVolume
        (Function.update θ a (nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ a))))
        (Function.update u a (fun x => (c : EReal) * u a x))
        (sourceUpdatePSH hu a (sourcePositiveScaling_thetaPSH (hu a) hc)) =
        ENNReal.ofReal c * sourceEnvelopeMixedIVolume θ u hu) ∧
    (∀ (η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (v : Fin n → M → EReal)
      (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i)),
      (∀ i, 0 < sourceIVolume (η i) (v i) (hv i)) →
      (∀ i, RealBottChern.ofRepresentative (atlasClosedFormToNative (θ i)) =
        RealBottChern.ofRepresentative (atlasClosedFormToNative (η i))) →
      (∀ i, sourceIOrder (ofFixedModel n M) (u i) (v i)) →
      sourceEnvelopeMixedIVolume θ u hu ≤ sourceEnvelopeMixedIVolume η v hv) := by
  refine ⟨sourceEnvelopeMixedIVolume_perm θ u hu,
    sourceEnvelopeMixedIVolume_tendsto_add_kahler ω θ u hu hpos, ?_, ?_, ?_⟩
  · intro a σ v hv hvpos
    exact sourceEnvelopeMixedIVolume_add_slot ω θ u hu hpos a σ v hv hvpos
  · intro a c hc
    exact sourceEnvelopeMixedIVolume_positive_smul_slot θ u hu a hc
  · intro η v hv _ hclass hI
    exact sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω θ η u v hu hv hclass hI

end SGPT.PSH.VariableComplexAtlas
