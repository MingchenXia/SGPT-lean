import SGPT.Foundations.Analysis.Pending.IEnvelopeVaryingBackgroundModelInfimum
import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

set_option autoImplicit false

/-! # Literal varying I-model infima preserve positive global reader classes -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.POrder DiagonalMass IEnvelopeVaryingBackgroundModelInfimum
  ActualIEnvelopeOrderInfimum IGoodPositiveBackgroundIndependence SingularGlobalPOrder

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] in
/-- Literal I-model identities in the varying input backgrounds internally
make the unchanged original infimum a genuine original I-model. -/
theorem isIModelPotential_iInf_varying_models
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j))
    (hI : ∀ j, IsIModelPotential (θ + ε j • omega.form).val (v j))
    (hanti : Antitone v) : IsIModelPotential θ.val (⨅ j, v j) := by
  let u : M → EReal := ⨅ j, v j
  have hu : IsThetaPshPotential θ.val u :=
    isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti
  let Q : M → EReal := iSingularityEnvelope θ.val u
  have hQ : IsThetaPshPotential θ.val Q :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hu0 : u ≤ 0 := (iInf_le v 0).trans (by
    rw [(hv 0).envelope_eq]
    exact singularityEnvelope_le_zero (θ + ε 0 • omega.form).val (v 0))
  have hIuQ : IEquivalentOnManifold (n := n) u Q :=
    iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hQv (j : ℕ) : Q ≤ v j := by
    have hQσ : IsThetaPshPotential (θ + ε j • omega.form).val Q :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hQ
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (hεpos j).le)
    have hlow : Q ≤ iSingularityEnvelope (θ + ε j • omega.form).val u :=
      le_iSingularityEnvelope hQσ (iSingularityEnvelope_le_zero θ.val u) hIuQ.symm
    have horder := iSingularityEnvelope_le_of_iOrderOnManifold
      (θ + ε j • omega.form) (hv j).plurisubharmonic
      (iOrderOnManifold_of_le (hv j).plurisubharmonic.1.quasiPlurisubharmonic (iInf_le v j))
    exact hlow.trans (horder.trans_eq (hI j).envelope_eq.symm)
  exact ⟨hu, le_antisymm
    (le_iSingularityEnvelope hu hu0 (IEquivalentOnManifold.refl u)) (le_iInf hQv)⟩

/-- Real positive original infimum mass, actual varying I-model fields and
a constant genuine global class produce the class of the literal infimum. -/
theorem sourcePEquivalent_iInf_of_varying_iModels
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j))
    (hI : ∀ j, IsIModelPotential (θ + ε j • omega.form).val (v j))
    (hanti : Antitone v)
    (hpos : HasPositivePotentialMass θ (⨅ j, v j)
      (isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti))
    (heq : ∀ j, SourcePEquivalent (n := n) (v j) (v 0)) :
    SourcePEquivalent (n := n) (⨅ j, v j) (v 0) := by
  let u : M → EReal := ⨅ j, v j
  have hu : IsThetaPshPotential θ.val u :=
    isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti
  have hIU : IsIModelPotential θ.val u :=
    isIModelPotential_iInf_varying_models omega θ hεpos hεanti hεlim hv hI hanti
  have hPU : singularityEnvelope θ.val u = u := by
    calc singularityEnvelope θ.val u
        = singularityEnvelope θ.val (iSingularityEnvelope θ.val u) :=
          congrArg (singularityEnvelope θ.val) hIU.envelope_eq
      _ = iSingularityEnvelope θ.val u :=
        singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
          hu.1.hasSmoothLocalPotentials u hu
      _ = u := hIU.envelope_eq.symm
  have hgood : IGoodWith θ u hu := ⟨hpos, hPU.trans hIU.envelope_eq⟩
  let γ : ClosedRealOneOneForm n M := θ + (ε 0 + 1) • omega.form
  have ht : 0 < ε 0 + 1 := by linarith [hεpos 0]
  have hGu : IsThetaPshPotential γ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  have hGup : HasPositivePotentialMass γ u hGu := hpos.trans_le
    (DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul omega ht hu hGu (le_refl u))
  have hGgood : IGoodWith γ u hGu :=
    (iGoodWith_iff_positive_common_potential omega θ γ hu hGu hpos hGup).mp hgood
  have hform : θ + ε 0 • omega.form + (1 : ℝ) • omega.form = γ := by
    dsimp only [γ]
    module
  have hGv : IsThetaPshPotential γ.val (v 0) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hv 0).plurisubharmonic
      (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
    rwa [hform] at h
  have hGvp : HasPositivePotentialMass γ (v 0) hGv := by
    change 0 < diagonalPotentialMass γ (v 0) hGv
    have hmass := DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
      omega zero_lt_one (hv 0).plurisubharmonic
      (LocalPotentials.isThetaPshPotential_add_of_semipositive (hv 0).plurisubharmonic
        (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)) (le_refl (v 0))
    simpa only [hform] using (hv 0).positive_mass.trans_le hmass
  have hgoodV : IGoodWith (θ + ε 0 • omega.form) (v 0) (hv 0).plurisubharmonic :=
    ⟨(hv 0).positive_mass, (hv 0).envelope_eq.symm.trans (hI 0).envelope_eq⟩
  have hGgoodV : IGoodWith γ (v 0) hGv :=
    (iGoodWith_iff_positive_common_potential omega (θ + ε 0 • omega.form) γ
      (hv 0).plurisubharmonic hGv (hv 0).positive_mass hGvp).mp hgoodV
  have hconst (j : ℕ) : iSingularityEnvelope γ.val (v j) =
      iSingularityEnvelope γ.val (v 0) :=
    iSingularityEnvelope_eq_of_iEquivalent
      (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent (heq j))
  have hcomm := iInf_iSingularityEnvelope_eq_in_fixed_enlargement
    omega θ hεpos hεanti hεlim hv hanti hpos
  change (⨅ j, iSingularityEnvelope γ.val (v j)) = iSingularityEnvelope γ.val u at hcomm
  have hIE : iSingularityEnvelope γ.val u = iSingularityEnvelope γ.val (v 0) := by
    rw [← hcomm]
    simp only [hconst, iInf_const]
  have hPE : singularityEnvelope γ.val u = singularityEnvelope γ.val (v 0) :=
    hGgood.envelope_eq.trans (hIE.trans hGgoodV.envelope_eq.symm)
  exact (sourcePEquivalent_iff_pEquivalentWith omega γ hGu hGv hGup hGvp).mpr
    (pEquivalentWith_iff_envelope_eq.mpr hPE)

end
end SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass
