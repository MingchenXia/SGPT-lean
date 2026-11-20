import SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass
import SGPT.Foundations.Analysis.Pending.IEnvelopeNativeContinuity
import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed

set_option autoImplicit false

/-! # A positive varying I-model infimum has the actual native stage limit's global class -/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.VaryingIModelNativeGlobalClass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  DiagonalMass MixedMass ThetaPshL1Topology SingularCanonicalSingularityDistance
  IEnvelopeVaryingBackgroundModelInfimum VaryingBackgroundIModelGlobalClass
  ActualIEnvelopeOrderInfimum IGoodPositiveBackgroundIndependence SingularGlobalPOrder
  IEnvelopeMonotoneNativeLimits SingularCanonicalSingularityDecreasingModels

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine native stage convergence to a positive I-good reader identifies
the global class of the literal varying I-model infimum. -/
theorem sourcePEquivalent_iInf_of_native_varying_iModels
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j))
    (hI : ∀ j, IsIModelPotential (θ + ε j • omega.form).val (v j))
    (hanti : Antitone v)
    (hpos : HasPositivePotentialMass θ (⨅ j, v j)
      (isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti))
    (hΓ : IsBigClass (RealBottChern.ofRepresentative (θ + (ε 0 + 1) • omega.form)))
    (hGv : ∀ j, IsThetaPshPotential (θ + (ε 0 + 1) • omega.form).val (v j))
    {τ : M → EReal} (hτ : IsThetaPshPotential (θ + (ε 0 + 1) • omega.form).val τ)
    (hgoodτ : IGoodWith (θ + (ε 0 + 1) • omega.form) τ hτ)
    (hlim : Tendsto (fun j => (⟨v j, hGv j⟩ : ThetaPshL1
        (θ + (ε 0 + 1) • omega.form).val)) atTop
      (@nhds (ThetaPshL1 (θ + (ε 0 + 1) • omega.form).val)
        (singularityPseudoMetricSpace omega (θ + (ε 0 + 1) • omega.form)
          hΓ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩)) :
    SourcePEquivalent (n := n) (⨅ j, v j) τ := by
  let u : M → EReal := ⨅ j, v j
  let Γ : ClosedRealOneOneForm n M := θ + (ε 0 + 1) • omega.form
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
  have hgoodU : IGoodWith θ u hu := ⟨hpos, hPU.trans hIU.envelope_eq⟩
  have ht : 0 < ε 0 + 1 := by linarith [hεpos 0]
  have hGu : IsThetaPshPotential Γ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  have hGup : HasPositivePotentialMass Γ u hGu := hpos.trans_le
    (DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
      omega ht hu hGu (le_refl u))
  have hGgoodU : IGoodWith Γ u hGu :=
    (iGoodWith_iff_positive_common_potential omega θ Γ hu hGu hpos hGup).mp hgoodU
  let W : ℕ → ThetaPshL1 Γ.val := fun j => ⟨v j, hGv j⟩
  let B : ℕ → ThetaPshL1 Γ.val := fun j => iEnvelopeReader Γ (W j)
  have hv0 (j : ℕ) : v j ≤ 0 := by
    rw [(hv j).envelope_eq]
    exact singularityEnvelope_le_zero (θ + ε j • omega.form).val (v j)
  have hvB (j : ℕ) : v j ≤ (B j).val :=
    le_iSingularityEnvelope (hGv j) (hv0 j) (IEquivalentOnManifold.refl (v j))
  have huB (j : ℕ) : u ≤ (B j).val := (iInf_le v j).trans (hvB j)
  have hBmodel (j : ℕ) : IsModelPotential Γ (B j).val :=
    ⟨(B j).property,
      (singularityEnvelope_iSingularityEnvelope Γ.val Γ.property.1 Γ.property.2
        (hGv j).1.hasSmoothLocalPotentials (v j) (hGv j)).symm,
      hGup.trans_le (diagonalPotentialMass_mono_of_kahler omega hGu (B j).property
        (MoreSingularOn.of_le fun x _ => huB j x))⟩
  have hBanti : Antitone fun j => (B j).val := by
    intro i j hij
    exact iSingularityEnvelope_le_of_iOrderOnManifold Γ (hGv i)
      (iOrderOnManifold_of_le (hGv i).1.quasiPlurisubharmonic (hanti hij))
  let L : ℝ≥0∞ := diagonalPotentialMass Γ u hGu
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega (fun _ : Fin n => hGu.1)).ne
  let δ : ℝ := L.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hGup.ne' hLtop
  have hbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass Γ (B j).val (hBmodel j).plurisubharmonic := by
    rw [ENNReal.ofReal_toReal hLtop]
    exact diagonalPotentialMass_mono_of_kahler omega hGu (B j).property
      (MoreSingularOn.of_le fun x _ => huB j x)
  let U : ThetaPshL1 Γ.val := iEnvelopeReader Γ ⟨u, hGu⟩
  have heq : (⨅ j, (B j).val) = U.val :=
    iInf_iSingularityEnvelope_eq_in_fixed_enlargement
      omega θ hεpos hεanti hεlim hv hanti hpos
  let := singularityPseudoMetricSpace omega Γ hΓ
  let : TopologicalSpace (ThetaPshL1 Γ.val) :=
    (singularityPseudoMetricSpace omega Γ hΓ).toUniformSpace.toTopologicalSpace
  have hBlow : Tendsto B atTop (𝓝 U) := by
    have hh := tendsto_native_iInf_of_uniform_positive_stage_mass
      omega Γ hΓ B hBmodel hBanti hδ hbound
    have hsub : (⟨⨅ j, (B j).val,
        ActualDecreasingModelInfimum.isThetaPshPotential_iInf_of_antitone_model
          hBmodel hBanti⟩ : ThetaPshL1 Γ.val) = U := Subtype.ext heq
    simpa only [hsub] using hh
  let T : ThetaPshL1 Γ.val := iEnvelopeReader Γ ⟨τ, hτ⟩
  have hBhigh : Tendsto B atTop (𝓝 T) :=
    IEnvelopeNativeContinuity.tendsto_iEnvelope_of_tendsto_positive_mass
      omega Γ hΓ atTop W ⟨τ, hτ⟩ hgoodτ.positiveMass hlim
  have horder : ∀ᶠ j in atTop, SourcePOrder (n := n) (B j).val (B j).val :=
    Eventually.of_forall fun j => sourcePOrder_refl_of_isThetaPshPotential omega (B j).property
  have hmiddle : SourcePEquivalent (n := n) U.val T.val :=
    ⟨SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
      omega Γ hΓ atTop B B U T hBlow hBhigh horder,
     SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
      omega Γ hΓ atTop B B T U hBhigh hBlow horder⟩
  have hUclass : SourcePEquivalent (n := n) u U.val := by
    change SourcePEquivalent (n := n) u (iSingularityEnvelope Γ.val u)
    rw [← hGgoodU.envelope_eq]
    exact SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega Γ hGu
  have hTclass : SourcePEquivalent (n := n) τ T.val := by
    change SourcePEquivalent (n := n) τ (iSingularityEnvelope Γ.val τ)
    change IGoodWith Γ τ hτ at hgoodτ
    rw [← hgoodτ.envelope_eq]
    exact SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega Γ hτ
  exact ⟨(hUclass.1.trans omega hmiddle.1).trans omega hTclass.2,
    (hTclass.1.trans omega hmiddle.2).trans omega hUclass.2⟩

end
end SGPT.Foundations.Analysis.Pending.VaryingIModelNativeGlobalClass
