import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.SourceIGoodBackground
import SGPT.Toric.ProjectiveLogLogNonPluripolarMass

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Full mass relative to the literal genuine minimal model gives BOTH entire
source envelope identities and goodness in the SAME original background. -/
theorem sourceFullMass_iGood (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : M → EReal)
    (hu : SourceRelativeFullMass θ (sourceMinimalEnvelope θ) u
      (sourceMinimalEnvelope_model omega θ hbig)) :
    sourceSingularityEnvelope θ u = sourceMinimalEnvelope θ ∧
    sourceMinimalEnvelope θ = sourceIEnvelope θ u ∧
    sourceIGoodWith θ u hu.choose ∧ sourceIGood (n := n) u := by
  have hV := sourceMinimalEnvelope_model omega θ hbig
  have huPSH := hu.choose
  have hP : sourceSingularityEnvelope θ u = sourceMinimalEnvelope θ :=
    (sourceRelativeFullMass_iff_envelope_eq omega huPSH).mp hu
  have hmass : 0 < sourcePotentialNonPluripolarMeasure θ u huPSH univ := by
    rw [hu.choose_spec.2]
    exact hV.choose_spec.2
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp huPSH
  have hPI : sourceSingularityEnvelope θ u ≤ sourceIEnvelope θ u := by
    rw [sourceSingularityEnvelope_eq_native,sourceIEnvelope_eq_native θ u huPSH]
    exact singularityEnvelope_le_iSingularityEnvelope (atlasClosedFormToNative θ).val
      θ.closed θ.typeOneOne hn.1.hasSmoothLocalPotentials u hn
  have hIV : sourceIEnvelope θ u ≤ sourceMinimalEnvelope θ := by
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hV.thetaPSH).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro v
    exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧ w ≤ 0} => w.1 x)
      ⟨v.1,v.2.1,v.2.2.1⟩
  have hI : sourceMinimalEnvelope θ = sourceIEnvelope θ u :=
    le_antisymm (by rw [← hP]; exact hPI) hIV
  have hg : sourceIGoodWith θ u huPSH := ⟨hmass,hP.trans hI⟩
  exact ⟨hP,hI,hg,θ,huPSH,hg⟩

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.Toric
open Set Filter
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- Genuine native competitors are manufactured one-way from the explicit
original candidates; the original two-chart atlas is never identified with
ofFixedModel, and no reverse competitor dictionary is assumed. -/
theorem projectiveLogLog_nativeEnvelope_eq_zero :
    singularityEnvelope projectiveNativeFSBackground.form.val projectiveLogLogPotential = 0 := by
  have hcandidate (k : ℕ) :
      projectiveLogLogModelCandidate (logLogModelScale k)
        (logLogModelScale_pos k) (logLogModelScale_le_one k) ≤
      singularityEnvelope projectiveNativeFSBackground.form.val projectiveLogLogPotential :=
    le_singularityEnvelope
      (isThetaPshPotential_projectiveNativeFS_of_source
        (isThetaPSH_projectiveLogLogModelCandidate (logLogModelScale_pos k) (logLogModelScale_le_one k)))
      (projectiveLogLogModelCandidate_le_zero (logLogModelScale_pos k) (logLogModelScale_le_one k))
      (projectiveLogLogModelCandidate_singularityLE (logLogModelScale_pos k) (logLogModelScale_le_one k))
  have hoff : ∀ p ∉ projectiveToricBoundary,
      0 ≤ singularityEnvelope projectiveNativeFSBackground.form.val projectiveLogLogPotential p := by
    intro p hp
    apply le_of_tendsto (tendsto_projectiveLogLogModelCandidate_off hp)
    exact Eventually.of_forall fun k => hcandidate k p
  have hd : Dense (projectiveToricBoundaryᶜ) :=
    interior_eq_empty_iff_dense_compl.mp interior_projectiveToricBoundary
  have hc : IsClosed {p | 0 ≤
      singularityEnvelope projectiveNativeFSBackground.form.val projectiveLogLogPotential p} :=
    (upperSemicontinuous_singularityEnvelope _ _).isClosed_preimage 0
  apply le_antisymm (singularityEnvelope_le_zero _ _)
  intro p
  exact closure_minimal (fun q hq => hoff q hq) hc (hd p)

/-- The literal original projective log-log example is I-good. Its actual
native diagonal measure, not a radial surrogate, supplies positive mass. -/
theorem projectiveLogLog_iGood : sourceIGood (n := 1) projectiveLogLogPotential := by
  have hn := isThetaPshPotential_projectiveLogLogPotential
  have hPI := singularityEnvelope_le_iSingularityEnvelope projectiveNativeFSBackground.form.val
    projectiveNativeFSBackground.form.property.1 projectiveNativeFSBackground.form.property.2
    hn.1.hasSmoothLocalPotentials projectiveLogLogPotential hn
  rw [projectiveLogLog_nativeEnvelope_eq_zero] at hPI
  have hI : IEnvelope.iSingularityEnvelope projectiveNativeFSBackground.form.val
      projectiveLogLogPotential = 0 :=
    le_antisymm (IEnvelope.iSingularityEnvelope_le_zero _ _) hPI
  have hmass : DiagonalMass.HasPositivePotentialMass projectiveNativeFSBackground.form
      projectiveLogLogPotential hn := by
    change 0 < projectiveLogLogNonPluripolarMeasure univ
    rw [projectiveLogLogNonPluripolarMeasure_univ]
    exact zero_lt_one
  apply (sourceIGood_iff_native _).mpr
  exact ⟨projectiveNativeFSBackground.form,hn,hmass,
    projectiveLogLog_nativeEnvelope_eq_zero.trans hI.symm⟩

end SGPT.Toric
