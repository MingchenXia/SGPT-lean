import SGPT.Foundations.Analysis.Pending.AnalyticModificationMinimalMixedPullback
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback
open AnalyticModificationMinimalMixedPullback SingularCanonicalSingularityDistance
open SingularCanonicalSingularityMassComparison ThetaPshL1Topology
open RelativeEnergy SingularMinimalCanonicalRay

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Y] [BorelSpace Y] in
private theorem connectedSpace_of_modification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) : ConnectedSpace Y := by
  apply connectedSpace_iff_univ.mpr
  have hc :=
    AnalyticModificationConnectedFibres.isConnected_preimage_of_isConnected
      hπ (⟨univ, isOpen_univ⟩ : TopologicalSpace.Opens X) isConnected_univ
  change IsConnected (π ⁻¹' (univ : Set X)) at hc
  simpa only [preimage_univ] using hc

/-- The actual big upstairs background follows from the true original
minimal positive mass; no upstairs bigness certificate is a premise. -/
theorem isBigClass_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    IsBigClass (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1 θ)) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := connectedSpace_of_modification hπ
  by_cases hn : n = 0
  · exact NonBigPotentialMass.isBigClass_of_dim_zero hn omegaY _
  let hV := (isModelPotential_thetaPshSupremum omegaX θ hbig).plurisubharmonic
  let hVp := isThetaPshPotential_comp_of_isAnalyticModification hπ θ hV
  have hpos := RestrictedApproximantMass.diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass
    omegaX θ hbig hV
  have hmass := AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification
    hπ θ hV
  apply BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos (Nat.pos_of_ne_zero hn)
    omegaY _ hVp
  simpa only [hmass] using hpos

/-- Genuine literal minimal-reference pullback identifies every actual
extended endpoint mass before any real projection. -/
theorem minimalEndpointMixedMass_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {a : X → EReal} (ha : IsThetaPshPotential θ.val a) (j : Fin (n + 1)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := connectedSpace_of_modification hπ
    let β := ClosedRealOneOneForm.pullback hπ.1 θ
    let hβ := isBigClass_modification_pullback hπ omegaX omegaY θ hbig
    endpointMixedMass β (thetaPshSupremum β.val) (a ∘ π)
      (isModelPotential_thetaPshSupremum omegaY β hβ).plurisubharmonic
      (isThetaPshPotential_comp_of_isAnalyticModification hπ θ ha) j =
    endpointMixedMass θ (thetaPshSupremum θ.val) a
      (isModelPotential_thetaPshSupremum omegaX θ hbig).plurisubharmonic ha j := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := connectedSpace_of_modification hπ
  let β := ClosedRealOneOneForm.pullback hπ.1 θ
  let hV := (isModelPotential_thetaPshSupremum omegaX θ hbig).plurisubharmonic
  have hreference : thetaPshSupremum β.val =
      (fun y => thetaPshSupremum θ.val (π y)) := by
    funext y
    exact thetaPshSupremum_pullback_eq hπ θ ⟨_, hV⟩ y
  dsimp only [β] at hreference
  have hmass := endpointMixedMass_pullback_of_isAnalyticModification hπ θ hV ha j
  simpa only [← hreference, Function.comp_def] using hmass

/-- The actual distance-generated native convergence is preserved and
reflected for every filter under a genuine general analytic modification. -/
theorem native_tendsto_modification_pullback_iff
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ι : Type*} (L : Filter ι) (w : ι → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := connectedSpace_of_modification hπ
    let β := ClosedRealOneOneForm.pullback hπ.1 θ
    let hβ := isBigClass_modification_pullback hπ omegaX omegaY θ hbig
    let wπ : ι → ThetaPshL1 β.val := fun i =>
      ⟨(w i).val ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ θ (w i).property⟩
    let vπ : ThetaPshL1 β.val :=
      ⟨v.val ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ θ v.property⟩
    Tendsto wπ L (@nhds (ThetaPshL1 β.val)
      (singularityPseudoMetricSpace omegaY β hβ).toUniformSpace.toTopologicalSpace vπ) ↔
    Tendsto w L (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omegaX θ hbig).toUniformSpace.toTopologicalSpace v) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := connectedSpace_of_modification hπ
  let β := ClosedRealOneOneForm.pullback hπ.1 θ
  let hβ := isBigClass_modification_pullback hπ omegaX omegaY θ hbig
  let wπ : ι → ThetaPshL1 β.val := fun i =>
    ⟨(w i).val ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ θ (w i).property⟩
  let vπ : ThetaPshL1 β.val :=
    ⟨v.val ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ θ v.property⟩
  have hX := tendsto_native_iff_endpointMixedMass omegaX θ hbig L w v
  have hY := tendsto_native_iff_endpointMixedMass omegaY β hβ L wπ vπ
  refine (hY.trans ?_).trans hX.symm
  apply forall_congr'
  intro j
  have hmember (i : ι) := minimalEndpointMixedMass_modification_pullback
    hπ omegaX omegaY θ hbig (w i).property j
  have hlimit := minimalEndpointMixedMass_modification_pullback
    hπ omegaX omegaY θ hbig v.property j
  have hmaximum (i : ι) := minimalEndpointMixedMass_modification_pullback
    hπ omegaX omegaY θ hbig (IsThetaPshPotential.max (w i).property v.property) j
  dsimp only at hmember hlimit hmaximum
  simp only [Function.comp_def] at hmember hlimit hmaximum
  dsimp only [β, wπ, vπ]
  simp only [Function.comp_def, hmember, hlimit, hmaximum]

end SGPT.Okounkov
