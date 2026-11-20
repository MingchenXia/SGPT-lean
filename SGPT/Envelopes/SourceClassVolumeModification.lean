import SGPT.Envelopes.SourceClassVolume
import SGPT.PSH.SourceTestCurveModificationPullback
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.DimZeroKahler

/-!
# Volumes of classes under proper bimeromorphic pull-back

Source: Chapter "The envelope operators", `prop:cones_modif2`, item 1: for a big class
`α`, `π^*α` is big and `vol π^*α = vol α`.

Let `π : Y → X` be a proper bimeromorphic morphism (`IsAnalyticModification`) between
connected compact complex manifolds with Kähler backgrounds, and `α = {θ}` a
pseudo-effective class (in particular a big class). The class `π^*α` is represented by
`π^*θ`. The proof is the source's: `π^*V_θ` is a current with minimal singularities in
`π^*α` (every `π^*θ`-psh function descends to `X`), it is its own `I`-envelope, and the
non-pluripolar mass is invariant under pull-back (`prop:nppmassinv`, through
`sourcePotentialNonPluripolarMeasure_univ_modification_pullback`). Bigness of `π^*α`
follows since `∫ (π^*θ)_{π^*V_θ}^n = ∫ θ_{V_θ}^n > 0` and a class containing a potential
of positive non-pluripolar mass is big (Boucksom's criterion,
`BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback

universe u

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  {π : Y → X} (hπ : IsAnalyticModification (n := n) π)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [ConnectedSpace Y] in
/-- `π^*V_θ` has minimal singularities in the class of `π^*θ`. -/
theorem sourceMinimalEnvelope_comp_minimalSingularities
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    SourceMinimalSingularities (θ.nativeHolomorphicPullback hπ.1)
      (sourceMinimalEnvelope θ ∘ π) := by
  refine ⟨(sourceMinimalEnvelope_thetaPSH_of_mem hu).comp_native_analyticModification hπ,
    fun w hw => ?_⟩
  obtain ⟨hv, hve⟩ := sourceModificationDescent_spec hπ θ hw
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
    (singularityLE_sourceMinimalEnvelope_of_thetaPSH hv)
  refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, fun y => ?_⟩
  rw [← hve]
  exact hC (π y)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- `π^*V_θ` is its own `I`-envelope in `PSH(Y, π^*θ)`. -/
theorem sourceIEnvelope_minimalEnvelope_comp
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    sourceIEnvelope (θ.nativeHolomorphicPullback hπ.1) (sourceMinimalEnvelope θ ∘ π) =
      sourceMinimalEnvelope θ ∘ π := by
  have hVY := (sourceMinimalEnvelope_comp_minimalSingularities hπ hu).1
  have hs := surjective_of_isAnalyticModification hπ
  apply le_antisymm
  · have hw := isThetaPSH_sourceIEnvelope hVY
    obtain ⟨hv, hve⟩ := sourceModificationDescent_spec hπ θ hw
    set v := sourceModificationDescent hπ θ hw
    have hv0 : v ≤ 0 := by
      intro x
      obtain ⟨y, rfl⟩ := hs x
      have h := sourceIEnvelope_le_zero (θ.nativeHolomorphicPullback hπ.1)
        (sourceMinimalEnvelope θ ∘ π) y
      rw [← hve] at h
      exact h
    intro y
    rw [← hve]
    exact le_iSup (fun w : {w : X → EReal // (ofFixedModel n X).IsThetaPSH θ w ∧ w ≤ 0} =>
      w.1 (π y)) ⟨v, hv, hv0⟩
  · exact le_sourceIEnvelope hVY (fun y => sourceMinimalEnvelope_le_zero θ (π y))
      (sourceIEquivalent_refl ⟨_, hVY⟩)

/-- Source `prop:cones_modif2`, item 1, volume identity: for every pseudo-effective (in
particular every big) class `α = {θ}` on `X`, `vol π^*α = vol α`, where `π^*α = {π^*θ}`. -/
theorem sourceClassVolume_modification_pullback (ωX : KahlerBackground n X)
    (ωY : KahlerBackground n Y) {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {u : X → EReal} (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    sourceClassVolume (RealBottChern.ofRepresentative
        (atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1))) =
      sourceClassVolume (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) := by
  have hmin := sourceMinimalEnvelope_comp_minimalSingularities hπ hu
  rw [sourceClassVolume_eq ωY hmin, sourceClassVolume_eq_minimalEnvelope_mass ωX hu]
  unfold sourceIVolume
  rw [sourcePotentialNonPluripolarMeasure_congr (sourceIEnvelope_minimalEnvelope_comp hπ hu) _
    hmin.1]
  exact sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ
    (sourceMinimalEnvelope_thetaPSH_of_mem hu) hmin.1

/-- Source `prop:cones_modif2`, item 1, bigness: the pull-back of a big class is big. -/
theorem isBigClass_modification_pullback (ωX : KahlerBackground n X)
    (ωY : KahlerBackground n Y) {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact DimZeroKahler.isBigClass_of_dim_zero hn ωY _
  -- a potential of `θ`
  obtain ⟨δ₀, hδ₀, u₀, hu₀⟩ :=
    DivisorialDomination.exists_isThetaPshPotential_sub_smul_of_isBigClass ωX _ hbig
  have hu₀' : IsThetaPshPotential (atlasClosedFormToNative θ).val u₀ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀
      (KahlerDomination.isSemipositive_smul ωX.isSemipositive hδ₀.le)
    rwa [sub_add_cancel] at h
  have hu : (ofFixedModel n X).IsThetaPSH θ u₀ :=
    (isThetaPSH_iff_nativeThetaPotential θ u₀).mpr hu₀'
  have hmin := sourceMinimalEnvelope_comp_minimalSingularities hπ hu
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hu
  have hVn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hV
  have hposX : 0 < sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ) hV univ := by
    have hEq := sourceMinimalEnvelope_eq_native θ
    have hV' : IsThetaPshPotential (atlasClosedFormToNative θ).val
        (thetaPshSupremum (atlasClosedFormToNative θ).val) := hEq ▸ hVn
    have h := RestrictedApproximantMass.diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass
      ωX (atlasClosedFormToNative θ) hbig hV'
    have hc := sourcePotentialNonPluripolarMeasure_congr hEq hV
      ((isThetaPSH_iff_nativeThetaPotential θ _).mpr hV')
    rw [hc]
    exact h
  have hposY : 0 < sourcePotentialNonPluripolarMeasure (θ.nativeHolomorphicPullback hπ.1)
      (sourceMinimalEnvelope θ ∘ π) hmin.1 univ := by
    rw [sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ hV hmin.1]
    exact hposX
  exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hn ωY _
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hmin.1) hposY

end SGPT.PSH.VariableComplexAtlas
