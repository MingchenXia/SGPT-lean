import SGPT.PSH.SourceIGoodBackground
import SGPT.PSH.SourceSingularityBackgroundChange
import SGPT.Hodge.BDivChainDS

/-! The full mathematical route was written first in blueprint.tex. Original θ need not be big. -/
set_option autoImplicit false
noncomputable section
universe u

open Filter Set
open scoped Topology

namespace SGPT.Hodge.BDivChain.SourceDSDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual original background plus an arbitrary actual Kähler form. -/
def enlargedBackground (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (κ : KahlerBackground n X) : AtlasClosedRealOneOneForm (ofFixedModel n X) :=
  θ.add (nativeClosedFormToAtlas κ.form)

/-- The same entire original extended-real function, including all its poles. -/
def enlargedPotential {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (κ : KahlerBackground n X) (u : SourceThetaPotentialL1 θ) :
    SourceThetaPotentialL1 (enlargedBackground θ κ) :=
  ⟨u.val, sourceThetaPSH_add_kahler κ u.property⟩

/-- A genuine Kähler-current witness is produced from the actual original PSH potential. -/
theorem enlargedBackground_isBig (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (κ : KahlerBackground n X) (v : SourceThetaPotentialL1 θ) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (enlargedBackground θ κ))) := by
  simpa only [enlargedBackground, sourceNativeClosedForm_add,
    sourceNativeAtlasForm_roundTrip, one_smul] using
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential κ
      (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property) zero_lt_one

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Convergence in a genuine big reference, with that bigness constructed internally. -/
def enlargedDSTendsto (ω : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {I : Type*}
    (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (κ : KahlerBackground n X) : Prop :=
  Tendsto (fun i => enlargedPotential κ (w i)) F
    (@nhds _ (sourceSingularityTopology ω (enlargedBackground θ κ)
      (enlargedBackground_isBig θ κ v)) (enlargedPotential κ v))

/-- The actual convergence in common big backgrounds does not depend on which enlargement is used. -/
theorem enlargedDSTendsto_iff (ω : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {I : Type*}
    (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (κ₁ κ₂ : KahlerBackground n X) :
    enlargedDSTendsto ω θ F w v κ₁ ↔ enlargedDSTendsto ω θ F w v κ₂ := by
  exact tendsto_sourceSingularityTopology_iff_common_backgrounds ω
    (enlargedBackground θ κ₁) (enlargedBackground θ κ₂)
    (enlargedBackground_isBig θ κ₁ v) (enlargedBackground_isBig θ κ₂ v)
    F (fun i => enlargedPotential κ₁ (w i)) (enlargedPotential κ₁ v)
    (fun i => (enlargedPotential κ₂ (w i)).property) (enlargedPotential κ₂ v).property

/-- Original unindexed convergence: existence of a genuine common big Kähler enlargement.
This does not define a radial pseudometric in a nonbig original class. -/
def unindexedDSTendsto (ω : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {I : Type*}
    (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) : Prop :=
  ∃ κ : KahlerBackground n X, enlargedDSTendsto ω θ F w v κ

/-- The existential notation is equivalent to convergence in every such actual reference. -/
theorem unindexedDSTendsto_iff_forall (ω : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {I : Type*}
    (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    unindexedDSTendsto ω θ F w v ↔
      ∀ κ : KahlerBackground n X, enlargedDSTendsto ω θ F w v κ := by
  constructor
  · rintro ⟨κ, hκ⟩ κ'
    exact (enlargedDSTendsto_iff ω θ F w v κ κ').mp hκ
  · intro h
    exact ⟨ω, h ω⟩

/-- On the entire original big-background domain, this is exactly the already defined source dS convergence. -/
theorem unindexedDSTendsto_iff_original (ω : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    unindexedDSTendsto ω θ F w v ↔
      Tendsto w F (@nhds _ (sourceSingularityTopology ω θ hbig) v) := by
  have hκ (κ : KahlerBackground n X) :
      Tendsto w F (@nhds _ (sourceSingularityTopology ω θ hbig) v) ↔
        enlargedDSTendsto ω θ F w v κ :=
    tendsto_sourceSingularityTopology_iff_common_backgrounds ω θ (enlargedBackground θ κ)
      hbig (enlargedBackground_isBig θ κ v) F w v
      (fun i => (enlargedPotential κ (w i)).property) (enlargedPotential κ v).property
  constructor
  · rintro ⟨κ, h⟩
    exact (hκ κ).mpr h
  · intro h
    exact ⟨ω, (hκ ω).mp h⟩

end SGPT.Hodge.BDivChain.SourceDSDraft
