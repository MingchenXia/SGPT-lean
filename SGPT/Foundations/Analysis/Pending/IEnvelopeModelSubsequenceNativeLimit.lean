import SGPT.Foundations.Analysis.Pending.IEnvelopeMonotoneNativeLimits
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelSandwich
import SGPT.Foundations.Analysis.Pending.SingularDecreasingPEnvelopeNets
import SGPT.Foundations.Analysis.Pending.SingularNativeOrderSandwich
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

set_option autoImplicit false

/-! # Genuine native I-envelope subsequences of convergent model sequences -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeModelSubsequenceNativeLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  FirstPass.IEnvelope ThetaPshL1Topology SingularCanonicalSingularityDistance
  DiagonalMass MixedMass ActualDecreasingModelInfimum IncreasingMixedDirectedNets
  IEnvelopeMonotoneNativeLimits SingularCanonicalSingularityIncreasing
  SingularCanonicalSingularityModelSandwich SingularDecreasingPEnvelopeNets
  SingularNativeOrderSandwich SingularGlobalPOrder ActualIEnvelopeOrderInfimum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem iEnvelopeReader_eq_of_native_dist_eq_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    dist u v = 0 → iEnvelopeReader θ u = iEnvelopeReader θ v := by
  let := singularityPseudoMetricSpace omega θ hbig
  intro hd
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig
    u.property v.property
  have hmzero : m = 0 := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, hm,
      EReal.toReal_coe] using hd
  have hz : singularityDistance omega θ hbig u.val v.val = 0 := by
    rw [hm, hmzero, EReal.coe_zero]
  have he := (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      u.property v.property).mp hz
  apply Subtype.ext
  exact iSingularityEnvelope_eq_of_iEquivalent
    (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent he)

private theorem envelope_isModel_of_positive (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    IsModelPotential θ (singularityEnvelope θ.val u) := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hu.1.hasSmoothLocalPotentials u hu
  exact ⟨hP, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
    omega θ u hu hpos).symm,
    (singularityEnvelopeMassPreserving omega θ u hu hP).symm ▸ hpos⟩

/-- True model geometry internally produces a strict subsequence whose
literal I-envelope readers converge in the actual native topology. -/
theorem exists_strictMono_tendsto_iEnvelope_of_models
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val) {δ : ℝ}
    (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun i => iEnvelopeReader θ (ui (f i))) atTop
        (@nhds (ThetaPshL1 θ.val)
          (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
          (iEnvelopeReader θ u)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  obtain ⟨f, hf, η, ψ, _, _, hηmodel, hηmono, hψanti, hbetween, hηlim, hψlim⟩ :=
    exists_strictMono_monotone_sandwich_of_tendsto omega θ hbig ui u
      hmodels hδ hstage hlim
  have hη0 (i : ℕ) (x : M) : (η i).val x ≤ (0 : EReal) := by
    rw [(hηmodel i).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (η i).val x
  let S : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ i, (η i).val),
    isThetaPshPotential_regularized_of_uniformlyBounded (fun i => (η i).property) hη0⟩
  have hηS : (η 0).val ≤ S.val :=
    (le_iSup (fun i => (η i).val) 0).trans (le_uscRegularization _)
  have hSpos : HasPositivePotentialMass θ S.val S.property :=
    (hηmodel 0).positive_mass.trans_le (diagonalPotentialMass_mono_of_kahler
      omega (η 0).property S.property (MoreSingularOn.of_le fun x _ => hηS x))
  have hηSlim : Tendsto η atTop (𝓝 S) :=
    tendsto_native_of_monotone_uniformlyBounded omega θ hbig η hηmono hη0
  have hSu : dist S u = 0 := by
    have h := hηSlim.dist hηlim
    simp only [dist_self] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hISu := iEnvelopeReader_eq_of_native_dist_eq_zero omega θ hbig S u hSu
  have hIη : Tendsto (fun i => iEnvelopeReader θ (η i)) atTop
      (𝓝 (iEnvelopeReader θ u)) := by
    have h : Tendsto (fun i => iEnvelopeReader θ (η i)) atTop
        (𝓝 (iEnvelopeReader θ S)) :=
      tendsto_iEnvelope_of_monotone_uniformlyBounded omega θ hbig η hηmono hη0 hSpos
    rw [hISu] at h
    exact h
  have hψpos (i : ℕ) : HasPositivePotentialMass θ (ψ i).val (ψ i).property :=
    (hmodels (f i)).positive_mass.trans_le (diagonalPotentialMass_mono_of_kahler
      omega (ui (f i)).property (ψ i).property
        (MoreSingularOn.of_le fun x _ => (hbetween i).2 x))
  have hBmodel (i : ℕ) : IsModelPotential θ (singularityEnvelope θ.val (ψ i).val) :=
    envelope_isModel_of_positive omega (ψ i).property (hψpos i)
  let B : ℕ → ThetaPshL1 θ.val := fun i =>
    ⟨singularityEnvelope θ.val (ψ i).val, (hBmodel i).plurisubharmonic⟩
  have hBanti : Antitone fun i => (B i).val := by
    intro i j hij
    exact singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hψanti x hij)
  have hInfEq : (⨅ i, (B i).val) = singularityEnvelope θ.val u.val :=
    iInf_singularityEnvelope_eq_of_fixedPOrder_tendsto_native omega θ hbig ψ u
      (fun i j hij => pOrderWith_of_moreSingular
        (MoreSingularOn.of_le fun x _ => hψanti x hij)) hψlim hpos
  let T : ThetaPshL1 θ.val := ⟨⨅ i, (B i).val,
    isThetaPshPotential_iInf_of_antitone_model hBmodel hBanti⟩
  have hPupos : HasPositivePotentialMass θ (singularityEnvelope θ.val u.val)
      (envelope_isModel_of_positive omega u.property hpos).plurisubharmonic :=
    (envelope_isModel_of_positive omega u.property hpos).positive_mass
  have hTpos : HasPositivePotentialMass θ T.val T.property := by
    simpa only [HasPositivePotentialMass, T, hInfEq] using hPupos
  have hITu : iEnvelopeReader θ T = iEnvelopeReader θ u := by
    apply Subtype.ext
    change iSingularityEnvelope θ.val (⨅ i, (B i).val) = _
    rw [hInfEq]
    exact iSingularityEnvelope_singularityEnvelope θ.val θ.property.1 θ.property.2
      u.property.1.hasSmoothLocalPotentials u.val u.property
  have hIBψ : (fun i => iEnvelopeReader θ (B i)) =
      fun i => iEnvelopeReader θ (ψ i) := by
    funext i
    apply Subtype.ext
    exact iSingularityEnvelope_singularityEnvelope θ.val θ.property.1 θ.property.2
      (ψ i).property.1.hasSmoothLocalPotentials (ψ i).val (ψ i).property
  have hIψ : Tendsto (fun i => iEnvelopeReader θ (ψ i)) atTop
      (𝓝 (iEnvelopeReader θ u)) := by
    have h : Tendsto (fun i => iEnvelopeReader θ (B i)) atTop
        (𝓝 (iEnvelopeReader θ T)) :=
      tendsto_iEnvelope_of_antitone_models omega θ hbig B hBmodel hBanti hTpos
    simpa only [hITu, hIBψ] using h
  have hlow (i : ℕ) : (iEnvelopeReader θ (η i)).val ≤
      (iEnvelopeReader θ (ui (f i))).val :=
    iSingularityEnvelope_le_of_iOrderOnManifold θ (ui (f i)).property
      (iOrderOnManifold_of_le (ui (f i)).property.1.quasiPlurisubharmonic (hbetween i).1)
  have hupp (i : ℕ) : (iEnvelopeReader θ (ui (f i))).val ≤
      (iEnvelopeReader θ (ψ i)).val :=
    iSingularityEnvelope_le_of_iOrderOnManifold θ (ψ i).property
      (iOrderOnManifold_of_le (ψ i).property.1.quasiPlurisubharmonic (hbetween i).2)
  refine ⟨f, hf, tendsto_native_of_sourcePOrder_sandwich omega θ hbig atTop
    (fun i => iEnvelopeReader θ (η i)) (fun i => iEnvelopeReader θ (ui (f i)))
    (fun i => iEnvelopeReader θ (ψ i)) (iEnvelopeReader θ u) ?_ ?_ hIη hIψ⟩
  · intro i
    exact sourcePOrder_of_moreSingularOn omega θ θ
      (iEnvelopeReader θ (η i)).property (iEnvelopeReader θ (ui (f i))).property
      (MoreSingularOn.of_le fun x _ => hlow i x)
  · intro i
    exact sourcePOrder_of_moreSingularOn omega θ θ
      (iEnvelopeReader θ (ui (f i))).property (iEnvelopeReader θ (ψ i)).property
      (MoreSingularOn.of_le fun x _ => hupp i x)

end
end SGPT.Foundations.Analysis.Pending.IEnvelopeModelSubsequenceNativeLimit
