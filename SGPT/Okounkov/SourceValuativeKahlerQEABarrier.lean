import SGPT.Okounkov.SourceValuativeAffineAdmissibility
import SGPT.Okounkov.SourceValuativeIEnvelopeReader
import SGPT.IGood.LogVolume
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceValuativeClosure
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody

/-- Actual analytic Kähler currents have original I-volume equal to their
actual original mass. Analytic goodness and mass positivity are produced. -/
theorem iVolume_eq_mass_of_kahler_analytic {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hA : u ∈ analyticCurrents θ) (hK : IsKahlerCurrentPotential θ u) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    letI : Nonempty F.carrier := PartialBody.nonempty_carrier F
    iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) u hA.1 =
      diagonalPotentialMass θ u hA.1 := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  let Γ := nativeClosedFormToAtlas θ
  have hu : (ofFixedModel (m + 1) F.carrier).IsThetaPSH Γ u := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    simpa only [Γ, sourceNativeAtlasForm_roundTrip] using hA.1
  have hpos : 0 < sourcePotentialNonPluripolarMeasure Γ u hu univ := by
    simpa only [Γ, sourcePotentialNonPluripolarMeasure, sourceNativeAtlasForm_roundTrip,
      diagonalPotentialMass] using diagonalPotentialMass_pos_of_isKahlerCurrentPotential hK hA.1
  have hg := SGPT.IGood.LogVolume.sourceIGoodWith_of_analytic F.omega hu hA.2 hpos
  have h := SGPT.IGood.LogVolume.sourceIVolume_eq_mass_of_iGoodWith F.omega hu hg
  rw [sourceIVolume_eq_native _ _ _
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative Γ))] at h
  simpa only [Γ, sourcePotentialNonPluripolarMeasure, sourceNativeAtlasForm_roundTrip,
    diagonalPotentialMass] using h

/-- A genuine original Kähler QEA INTERNALLY supplies all actual masses,
their convergence, every fixed REAL coefficient's admissibility, and actual
positive-mass affine-envelope barriers in the SAME original background.
The whole source consumer chooses this actual QEA from hK itself. -/
theorem kahlerQEA_eventually_affine_barrier {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ) {U : ℕ → F.carrier → EReal}
    (hU : IsKahlerQEA θ φ U) {a : ℝ} (ha : 1 < a) :
    ∀ᶠ j in atTop, ∃ η : F.carrier → EReal, ∃ hη : IsThetaPshPotential θ.val η,
      (letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      HasPositivePotentialMass θ η hη) ∧
      convexComb a⁻¹ η (iSingularityEnvelope θ.val (U j)) ≤ iSingularityEnvelope θ.val φ := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hφ := isThetaPshPotential_of_isKahlerCurrentPotential hK
  let V := iSingularityEnvelope θ.val φ
  have hV : IsThetaPshPotential θ.val V :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ
  let W : ℕ → F.carrier → EReal := fun j => iSingularityEnvelope θ.val (U j)
  have hW (j : ℕ) : IsThetaPshPotential θ.val (W j) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) (U j) (hU.2 j).1.1
  let p := diagonalPotentialMass θ V hV
  let q : ℕ → ℝ≥0∞ := fun j => diagonalPotentialMass θ (W j) (hW j)
  have hp : 0 < p :=
    (diagonalPotentialMass_pos_of_isKahlerCurrentPotential hK hφ).trans_le
      (diagonalPotentialMass_le_iVolume F.omega hφ)
  have horder (j : ℕ) : V ≤ W j := by
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp
      (le_of_sourceQuasiEquisingularApproximation hU.1 j)
    have hI := iOrderOnManifold_of_le_add (hU.2 j).1.1.1.quasiPlurisubharmonic hC
    exact ActualIEnvelopeOrderInfimum.iSingularityEnvelope_le_of_iOrderOnManifold
      θ (hU.2 j).1.1 hI
  have hpq (j : ℕ) : p ≤ q j :=
    diagonalPotentialMass_mono_of_kahler F.omega hV (hW j)
      (MoreSingularOn.of_le fun x _ => horder j x)
  have hqfin (j : ℕ) : q j ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top F.omega (fun _ : Fin (m + 1) => (hW j).1)).ne
  have hpfin : p ≠ ⊤ := ne_top_of_le_ne_top (hqfin 0) (hpq 0)
  have hqeq (j : ℕ) : q j = diagonalPotentialMass θ (U j) (hU.2 j).1.1 :=
    iVolume_eq_mass_of_kahler_analytic F
      (globalAnalyticCurrents_subset_analyticCurrents θ (hU.2 j).1) (hU.2 j).2
  have hlim : Tendsto q atTop (𝓝 p) :=
    (tendsto_diagonalPotentialMass_of_isKahlerQEA hK hU).congr fun j => (hqeq j).symm
  filter_upwards [eventually_sourceAffineCoefficient_of_tendsto hp hpfin hpq hqfin hlim ha]
    with j hj
  have hadm := (sourceAffineCoefficient_iff hp (hpq j) (hqfin j)).mp hj
  have hmore : MoreSingularOn V (W j) univ := MoreSingularOn.of_le fun x _ => horder j x
  obtain ⟨hE, _hquant, hEpos, hbar⟩ := POrderAffineRooftop.xiaTheorem611 F.omega θ hV (hW j) hp
    (FirstPass.POrder.pOrderWith_of_moreSingular hmore) hadm
  exact ⟨_, hE, hEpos, hbar⟩

end SGPT.Okounkov.SourceValuativeClosure
