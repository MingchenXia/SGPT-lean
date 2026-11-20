import SGPT.Envelopes.SourceClassVolumeModification
import SGPT.Hodge.BDivChainDTVolume
import SGPT.BDivisor.ClassPullback
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-! The original class volume of an actual semipositive pullback on EVERY
analytic model. The model is never assumed to carry a Kahler background. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace SGPT.BDivisor.BaseHyperplaneNext

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff ENNReal

section Minimal
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Minimal singularities give the literal minimal I-envelope, without a
Kahler-background assumption or an incoming measure identity. -/
theorem sourceIEnvelope_eq_minimal_of_minimal
    {η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : SourceMinimalSingularities η v) :
    sourceIEnvelope η v = sourceMinimalEnvelope η := by
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hv.1
  have hminV := sourceMinimalEnvelope_minimalSingularities hv.1
  obtain ⟨A, hA⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp (hv.2 _ hV)
  obtain ⟨B, hB⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp (hminV.2 _ hv.1)
  have hI : sourceIEquivalent (ofFixedModel n M) (sourceMinimalEnvelope η) v := by
    apply (sourceIEquivalent_iff_native ⟨η, hV⟩ ⟨η, hv.1⟩).mpr
    exact ⟨iOrderOnManifold_of_le_add
      ((isThetaPSH_iff_nativeThetaPotential η v).mp hv.1).1.quasiPlurisubharmonic hA,
      iOrderOnManifold_of_le_add
        ((isThetaPSH_iff_nativeThetaPotential η _).mp hV).1.quasiPlurisubharmonic hB⟩
  apply le_antisymm
  · intro x
    exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH η w ∧ w ≤ 0} =>
      w.1 x) ⟨_, isThetaPSH_sourceIEnvelope hv.1, sourceIEnvelope_le_zero η v⟩
  · exact le_sourceIEnvelope hV (sourceMinimalEnvelope_le_zero η) hI

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- The chosen original minimally singular I-volume is its actual minimal
non-pluripolar mass, on any compact connected complex manifold. -/
theorem sourceIVolume_eq_minimal_mass_of_minimal
    {η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : SourceMinimalSingularities η v) :
    sourceIVolume η v hv.1 = sourcePotentialNonPluripolarMeasure η
      (sourceMinimalEnvelope η) (sourceMinimalEnvelope_thetaPSH_of_mem hv.1) univ := by
  unfold sourceIVolume
  exact congrArg (fun μ : Measure M => μ univ)
    (sourcePotentialNonPluripolarMeasure_congr
      (sourceIEnvelope_eq_minimal_of_minimal hv) _ _)

end Minimal

section AllModels
variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y] [ConnectedSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Genuine original class-volume invariance for an actual semipositive
pullback. Only the ORIGINAL BASE has a Kahler background; no positive-volume,
mass, model-Kahler, or desired volume certificate is supplied. -/
theorem sourceClassVolume_semipositive_pullback_all_models
    (κ : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    (hθ : θ.val.IsSemipositive) {ρ : Y → X}
    (hρ : IsAnalyticModification (n := m + 1) ρ) :
    sourceClassVolume (classPullback hρ.1 (RealBottChern.ofRepresentative θ)) =
      sourceClassVolume (RealBottChern.ofRepresentative θ) := by
  classical
  let θa := nativeClosedFormToAtlas θ
  let σ := θa.nativeHolomorphicPullback hρ.1
  have hθ0 : (ofFixedModel (m + 1) X).IsThetaPSH θa (fun _ => (0 : EReal)) := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [sourceNativeAtlasForm_roundTrip]
    exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr hθ
  have hσ0 : (ofFixedModel (m + 1) Y).IsThetaPSH σ (fun _ => (0 : EReal)) :=
    hθ0.comp_native_analyticModification hρ
  have hσclass : classPullback hρ.1 (RealBottChern.ofRepresentative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative σ) := by
    simp only [σ, θa, AtlasClosedRealOneOneForm.nativeHolomorphicPullback,
      sourceNativeAtlasForm_roundTrip, classPullback_ofRepresentative]
  have hex : ∃ η : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y),
      RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
        RealBottChern.ofRepresentative (atlasClosedFormToNative σ) ∧
        ∃ v : Y → EReal, SourceMinimalSingularities η v :=
    ⟨σ, rfl, sourceMinimalEnvelope σ, sourceMinimalEnvelope_minimalSingularities hσ0⟩
  let η := hex.choose
  let v := hex.choose_spec.2.choose
  have hv : SourceMinimalSingularities η v := hex.choose_spec.2.choose_spec
  have hread : sourceClassVolume (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)) =
      sourcePotentialNonPluripolarMeasure η (sourceMinimalEnvelope η)
        (sourceMinimalEnvelope_thetaPSH_of_mem hv.1) univ := by
    unfold sourceClassVolume
    rw [dif_pos hex]
    exact sourceIVolume_eq_minimal_mass_of_minimal hv
  obtain ⟨g, hg, hησ⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hex.choose_spec.1
  have hchange : SourceSmoothBackgroundChange η σ g :=
    (sourceSmoothBackgroundChange_iff_native _ _ _).mpr ⟨hg, hησ⟩
  have hreverse : SourceSmoothBackgroundChange σ η (fun y => -g y) := by
    apply (sourceSmoothBackgroundChange_iff_native _ _ _).mpr
    refine ⟨fun e => (hg e).neg, ?_⟩
    intro e z hz
    rw [smoothDDC_neg e.val.open_target (hg e) hz, hησ e z hz,
      add_neg_cancel_right]
  have hgpsh : (ofFixedModel (m + 1) Y).IsThetaPSH η (fun y => (g y : EReal)) := by
    have h := sourceThetaPSH_sub_smooth hreverse hσ0
    convert h using 1
    funext y
    simp only [zero_sub, EReal.coe_neg, neg_neg]
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hv.1
  let w : Y → EReal := fun y => sourceMinimalEnvelope η y - (g y : EReal)
  have hw : (ofFixedModel (m + 1) Y).IsThetaPSH σ w :=
    sourceThetaPSH_sub_smooth hchange hV
  let u := sourceModificationDescent hρ θa hw
  have hu := (sourceModificationDescent_spec hρ θa hw).1
  have hcomp : u ∘ ρ = w := (sourceModificationDescent_spec hρ θa hw).2
  obtain ⟨A, hA⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
    ((sourceMinimalEnvelope_minimalSingularities hv.1).2 _ hgpsh)
  have hwlow : ∀ y, ((-A : ℝ) : EReal) ≤ w y := by
    intro y
    have hh := add_le_add (hA y) (le_refl (((-g y - A : ℝ)) : EReal))
    have hleft : (g y : EReal) + (((-g y - A : ℝ)) : EReal) = ((-A : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      ring
    have hright : (sourceMinimalEnvelope η y + (A : EReal)) +
        (((-g y - A : ℝ)) : EReal) = w y := by
      dsimp only [w]
      simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
      congr 2
      ring
    rwa [hleft, hright] at hh
  have hulow : ∀ x, ((-A : ℝ) : EReal) ≤ u x := by
    intro x
    obtain ⟨y, rfl⟩ := surjective_of_isAnalyticModification hρ x
    rw [show u (ρ y) = w y from congrFun hcomp y]
    exact hwlow y
  have hun : IsThetaPshPotential θ.val u := by
    have h := (isThetaPSH_iff_nativeThetaPotential θa u).mp hu
    simpa only [θa, sourceNativeAtlasForm_roundTrip] using h
  obtain ⟨B, hB⟩ := hun.exists_global_upper_bound
  let C := max A B
  have hlow : ∀ x, ((-C : ℝ) : EReal) ≤ u x := fun x =>
    (EReal.coe_le_coe_iff.mpr (neg_le_neg (le_max_left A B))).trans (hulow x)
  have hup : ∀ x, u x ≤ (C : EReal) := fun x =>
    (hB x).trans (EReal.coe_le_coe_iff.mpr (le_max_right A B))
  have hbasemass := SGPT.Hodge.BDivChain.sourceClassVolume_eq_mass_of_bounded
    κ θ hun C hlow hup
  have hrep : sourcePotentialNonPluripolarMeasure σ w hw univ =
      sourcePotentialNonPluripolarMeasure η (sourceMinimalEnvelope η) hV univ := by
    change GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin (m + 1) => atlasClosedFormToNative σ) (fun _ => w)
        (fun _ => ((isThetaPSH_iff_nativeThetaPotential σ w).mp hw).1) univ =
      GlobalNonPluripolar.globalMixedMeasure
        (fun _ : Fin (m + 1) => atlasClosedFormToNative η)
          (fun _ => sourceMinimalEnvelope η)
          (fun _ => ((isThetaPSH_iff_nativeThetaPotential η _).mp hV).1) univ
    exact congrArg (fun μ : Measure Y => μ univ)
      (GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
        (fun _ : Fin (m + 1) => hg) (fun _ => hησ)
        (fun _ => ((isThetaPSH_iff_nativeThetaPotential η _).mp hV).1))
  have hpull : sourcePotentialNonPluripolarMeasure σ w hw univ =
      sourcePotentialNonPluripolarMeasure θa u hu univ := by
    have huc := hu.comp_native_analyticModification hρ
    calc
      _ = sourcePotentialNonPluripolarMeasure σ (u ∘ ρ) huc univ :=
        congrArg (fun μ : Measure Y => μ univ)
          (sourcePotentialNonPluripolarMeasure_congr hcomp.symm hw huc)
      _ = _ := sourcePotentialNonPluripolarMeasure_univ_modification_pullback hρ θa hu huc
  rw [hσclass, hread, ← hrep, hpull]
  change diagonalPotentialMass (atlasClosedFormToNative θa) u _ = _
  simpa only [θa, sourceNativeAtlasForm_roundTrip] using hbasemass.symm

end AllModels
end SGPT.BDivisor.BaseHyperplaneNext
