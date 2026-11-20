import SGPT.Hodge.SourceCurrentNonDivisorial
import SGPT.Hodge.ExceptionalBDivisor
import SGPT.PSH.SourceCurrentMixedIVolumeAlgebra

set_option autoImplicit false
noncomputable section
universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original existential multiplier order of genuine presentations of the actual currents. -/
def currentIOrderAny (T S : ClosedPositive (n := n) (X := X)) : Prop :=
  ∃ (θ σ : ClosedRealOneOneForm n X) (u v : X → EReal),
    IsPresentationAny T θ u ∧ IsPresentationAny S σ v ∧ IOrderOnManifold (n := n) u v

/-- Exact positive-dimensional comparison with the already defined original current I-order. -/
theorem currentIOrderAny_iff_existing {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (T S : ClosedPositive (n := m + 1) (X := Y)) :
    currentIOrderAny T S ↔ sourceCurrentIOrder (toBookCurrent T).current (toBookCurrent S).current := by
  constructor
  · rintro ⟨θ, σ, u, v, hT, hS, hI⟩
    obtain ⟨hu, hTr⟩ := (isPresentationAny_iff_book T θ u).mp hT
    obtain ⟨hv, hSr⟩ := (isPresentationAny_iff_book S σ v).mp hS
    exact ⟨θ, σ, u, v, hu, hv, hTr, hSr, hI⟩
  · rintro ⟨θ, σ, u, v, hu, hv, hTr, hSr, hI⟩
    exact ⟨θ, σ, u, v, (isPresentationAny_iff_book T θ u).mpr ⟨hu, hTr⟩,
      (isPresentationAny_iff_book S σ v).mpr ⟨hv, hSr⟩, hI⟩

variable [CompactSpace X]

/-- The actual current has an actual source form/potential presentation, selected internally. -/
def currentPresentationBackground (T : ClosedPositive (n := n) (X := X)) :
    AtlasClosedRealOneOneForm (ofFixedModel n X) :=
  (DTUniformDraft.exists_source_presentation T).choose

def currentPresentationPotential (T : ClosedPositive (n := n) (X := X)) : X → EReal :=
  (DTUniformDraft.exists_source_presentation T).choose_spec.choose

theorem currentPresentation_isPresentation (T : ClosedPositive (n := n) (X := X)) :
    IsPresentationAny T (atlasClosedFormToNative (currentPresentationBackground T))
      (currentPresentationPotential T) :=
  (DTUniformDraft.exists_source_presentation T).choose_spec.choose_spec

/-- Reflexivity uses an internally produced genuine presentation in every dimension. -/
theorem currentIOrderAny_refl (T : ClosedPositive (n := n) (X := X)) : currentIOrderAny T T := by
  obtain ⟨θ, u, hp⟩ := DTUniformDraft.exists_native_presentation T
  exact ⟨θ, θ, u, u, hp, hp, iOrderOnManifold_refl u⟩

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- Original current volume is defined from the actual source I-envelope mass of an internally
produced presentation, not through the target b-divisor or a desired volume equality. -/
def currentIVolumeAny (T : ClosedPositive (n := n) (X := X)) : ℝ≥0∞ :=
  sourceIVolume (currentPresentationBackground T) (currentPresentationPotential T)
    ((isThetaPSH_iff_nativeThetaPotential _ _).mpr (currentPresentation_isPresentation T).choose)

/-- Every actual presentation computes this same original current volume. -/
theorem currentIVolumeAny_eq_of_presentation (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X))
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal)
    (hp : IsPresentationAny T (atlasClosedFormToNative θ) u) :
    currentIVolumeAny T =
      sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hp.choose) :=
  DTUniformDraft.sourceIVolume_eq_of_presentations ω T (currentPresentationBackground T)
    θ (currentPresentationPotential T) u (currentPresentation_isPresentation T) hp

/-- The genuine source DT identity is a theorem about the independently defined volume. -/
theorem currentIVolumeAny_eq_bdivisorVolume (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X)) :
    currentIVolumeAny T = volumeAny (currentBDivisorAnyOn (ModelSystem.blowup n X) T) :=
  (DTUniformDraft.currentBDivisorAnyOn_vol_eq_sourceIVolume ω T (currentPresentationBackground T)
    (currentPresentationPotential T) (currentPresentation_isPresentation T)).symm

/-- The exact source G(alpha), allowing all original nondivisorial positive-volume currents,
not only I-good currents or currents with supplied presentations. -/
def GCurrent (α : RealBottChern n X) :=
  {T : ClosedPositive (n := n) (X := X) //
    currentClassAny T = α ∧ T = regularCurrentAny T ∧ 0 < currentIVolumeAny T}

/-- Target families use the EXISTING original modelwise volume and genuine directed-net nefness. -/
def BigNefRoot (α : RealBottChern n X) :=
  {D : WeilFamilyAny (ModelSystem.blowup n X) //
    0 < volumeAny D ∧ IsNefAny D ∧ D.val ModelSystem.Model.root = α}

/-- Transitivity is read in genuine presentations in positive dimension. Zero-dimensional
currents are actually equal, so their genuine reflexive order suffices. -/
theorem currentIOrderAny_trans (ω : KahlerBackground n X)
    {T S U : ClosedPositive (n := n) (X := X)}
    (hTS : currentIOrderAny T S) (hSU : currentIOrderAny S U) : currentIOrderAny T U := by
  cases n with
  | zero =>
    have hTU : T = U := (closedPositive_eq_zeroDim T).trans (closedPositive_eq_zeroDim U).symm
    subst U
    exact currentIOrderAny_refl T
  | succ m =>
    apply (currentIOrderAny_iff_existing T U).mpr
    obtain ⟨θ, u, hu, hT⟩ := SGPT.PSH.BookCurrent.exists_presentation (toBookCurrent T)
    obtain ⟨σ, v, hv, hS⟩ := SGPT.PSH.BookCurrent.exists_presentation (toBookCurrent S)
    obtain ⟨τ, w, hw, hU⟩ := SGPT.PSH.BookCurrent.exists_presentation (toBookCurrent U)
    have hI := (sourceCurrentIOrder_iff_of_representation ω hu hv hT hS).mp
      ((currentIOrderAny_iff_existing T S).mp hTS)
    have hJ := (sourceCurrentIOrder_iff_of_representation ω hv hw hS hU).mp
      ((currentIOrderAny_iff_existing S U).mp hSU)
    exact (sourceCurrentIOrder_iff_of_representation ω hu hw hT hU).mpr (hI.trans hJ)

/-- The original two-way current multiplier order, on actual whole currents. -/
def currentISetoid (ω : KahlerBackground n X) : Setoid (ClosedPositive (n := n) (X := X)) where
  r T S := currentIOrderAny T S ∧ currentIOrderAny S T
  iseqv := ⟨fun T => ⟨currentIOrderAny_refl T, currentIOrderAny_refl T⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h h' => ⟨currentIOrderAny_trans ω h.1 h'.1, currentIOrderAny_trans ω h'.2 h.2⟩⟩

/-- Restrict precisely that source equivalence to the WHOLE original G(alpha). -/
def gCurrentISetoid (ω : KahlerBackground n X) (α : RealBottChern n X) : Setoid (GCurrent α) :=
  (currentISetoid ω).comap Subtype.val

end SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
