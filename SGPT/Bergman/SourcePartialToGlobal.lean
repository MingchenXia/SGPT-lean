import SGPT.Bergman.SourcePartialEnvelopes
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.SourceThetaPSHCompactness
import SGPT.Envelopes.SourceGlobalPRelativeEnvelope
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

/-! Exact frozen PK3 tail after namespace alpha-renaming only.
No inherited proof bodies copied. Canonical acceptance and actual private discovery pending. -/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace SGPT.Bergman.PartialToGlobal

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology Classical

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem partialObstacle_univ_trans {K : Set M} {f : K → EReal} {η H : M → EReal}
    (hη : partialObstacle (n := n) univ (fun x : (univ : Set M) => H x.val) η)
    (hH : partialObstacle (n := n) K f H) : partialObstacle (n := n) K f η := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  apply (quasiEverywhere_and ((sourceQuasiEverywhere_iff_native _).mp hη)
    ((sourceQuasiEverywhere_iff_native _).mp hH)).mono
  intro x hx hxK
  exact (hx.1 (mem_univ x)).trans (hx.2 hxK)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Original positive-mass data manufacture the SAME literal minimal envelope's
genuine membership/positive mass/global-P-order before partial monotonicity. -/
theorem partialEnvelope_le_minimal_reference (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x) :
    partialEnvelope θ φ K f ≤ partialEnvelope θ (sourceMinimalEnvelope θ) K f := by
  have hbig := sourcePositiveMass_isBig ω hφ hφpos
  have hV := sourceMinimalEnvelope_thetaPSH ω θ hbig
  let T := atlasClosedFormToNative θ
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hφV : SGPT.PSH.SingularityLE φ (sourceMinimalEnvelope θ) := by
    rw [sourceMinimalEnvelope_eq_native]
    exact FirstPass.thetaPshSupremum_minimalSingularities T.val T.property.1 T.property.2
      hφn.1.hasSmoothLocalPotentials ⟨φ, hφn⟩ φ hφn
  have hVpos : 0 < sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ) hV univ :=
    hφpos.trans_le (sourcePotentialNonPluripolarMass_mono ω hφ hV hφV)
  have hφVP : GlobalPComparison.sourcePOrder (n := n) φ (sourceMinimalEnvelope θ) :=
    GlobalPComparison.sourcePOrder_of_moreSingular ω hφn.quasiPshPotential
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hV).quasiPshPotential hφV
  exact partialEnvelope_mono_globalPOrder ω hφ hV hφpos hVpos hf hφVP

/-- WHOLE original cor:PKtoPX / eq:PthetaKvarphiveq, with the actual bounded
REAL subtype obstacle, genuine positive original reference, original V_theta
and literal whole-X partial operator. No target output certificate is supplied. -/
theorem partialEnvelope_partial_to_global (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    (f : K → ℝ) (hf : ∃ R : ℝ, ∀ x : K, |f x| ≤ R) :
    partialEnvelope θ φ K (fun x => (f x : EReal)) =
      partialEnvelope θ φ univ (fun x : (univ : Set M) =>
        partialEnvelope θ (sourceMinimalEnvelope θ) K (fun y => (f y : EReal)) x.val) := by
  obtain ⟨R, hR⟩ := hf
  let g : K → EReal := fun x => (f x : EReal)
  let H : M → EReal := partialEnvelope θ (sourceMinimalEnvelope θ) K g
  have hlo : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ g x :=
    ⟨-R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).1⟩
  have hup : ∃ B : ℝ, ∀ x : K, g x ≤ (B : EReal) :=
    ⟨R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).2⟩
  have hle : partialEnvelope θ φ K g ≤ H :=
    partialEnvelope_le_minimal_reference ω hφ hφpos hlo
  have hHK : partialObstacle (n := n) K g H :=
    partialEnvelope_obstacle θ (sourceMinimalEnvelope θ) hK hup
  change partialEnvelope θ φ K g = partialEnvelope θ φ univ (fun x => H x.val)
  apply le_antisymm
  · apply uscRegularization_le
      (upperSemicontinuous_partialEnvelope θ φ univ (fun x => H x.val))
    intro x
    apply iSup_le
    intro v
    have hvH : v.val ≤ H :=
      (le_partialEnvelope v.property.1 v.property.2.1 v.property.2.2).trans hle
    exact le_partialEnvelope v.property.1
      (partialObstacle_of_forall (fun y : (univ : Set M) => hvH y.val)) v.property.2.2 x
  · apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K g)
    intro x
    apply iSup_le
    intro v
    exact le_partialEnvelope v.property.1
      (partialObstacle_univ_trans v.property.2.1 hHK) v.property.2.2 x

end SGPT.Bergman.PartialToGlobal
