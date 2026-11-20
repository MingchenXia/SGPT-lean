import SGPT.PSH.BookCurrentSpace
import SGPT.Envelopes.SourceClassVolume

/-!
# Currents with minimal singularities and the non-nef locus

Source: `chapter_pshfunctions.tex`, `def:nnlocus`: for a big class `α`,
`nn(α) = {x ∈ X : ν(T_min, x) > 0}`, where `T_min` is a current with minimal singularities
in `α`.

* `sourceLelong_le_of_singularityLE`, `currentLelong_eq_of_sameSingularityType`: Lelong numbers
  only depend on the singularity type (`ν(φ, x) ≥ ν(ψ, x)` if `φ ⪯ ψ`).
* `IsMinimalSingularities α T`: `T ∈ 𝒵₊(X, α)` and `T' ⪯ T` for every `T' ∈ 𝒵₊(X, α)`.
* `exists_minimalSingularities`: every pseudo-effective class (in particular every big class)
  contains a current with minimal singularities (`θ + dd^c V_θ`, the project's
  `sourceMinimalEnvelope`).
* `nonNefLocus α`, `nonNefLocus_eq_of_isMinimalSingularities`: the definition does not depend on
  the choice of `T_min`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace SGPT.PSH.BookCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- Lelong numbers are antitone for the singularity preorder: `φ ⪯ ψ ⇒ ν(ψ, x) ≤ ν(φ, x)`. -/
theorem sourceLelong_le_of_singularityLE {u v : X → EReal} (h : SingularityLE u v) (x : X) :
    (ofFixedModel (m + 1) X).sourceLelong v x ≤ (ofFixedModel (m + 1) X).sourceLelong u x := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real u v).mp h
  let i : (ofFixedModel (m + 1) X).Index := complexChartAt (n := m + 1) x
  have hi : x ∈ ((ofFixedModel (m + 1) X).chart i).source := mem_complexChartAt_source x
  have hn : (ofFixedModel (m + 1) X).dimension i ≠ 0 := Nat.succ_ne_zero m
  rw [(ofFixedModel (m + 1) X).sourceLelong_eq_growth_sup v x i hi hn,
    (ofFixedModel (m + 1) X).sourceLelong_eq_growth_sup u x i hi hn]
  refine iSup₂_le fun γ hγ => le_iSup₂_of_le γ ?_ le_rfl
  obtain ⟨C', hC'⟩ := hγ
  refine ⟨C' + C, hC'.mono fun z hz => ?_⟩
  calc u (((ofFixedModel (m + 1) X).chart i).symm z)
      ≤ v (((ofFixedModel (m + 1) X).chart i).symm z) + (C : EReal) := hC _
    _ ≤ (((γ : ℝ) * Real.log (‖z - (ofFixedModel (m + 1) X).chart i x‖ ^ 2) + C' : ℝ) : EReal) +
          (C : EReal) := add_le_add_left hz _
    _ = (((γ : ℝ) * Real.log (‖z - (ofFixedModel (m + 1) X).chart i x‖ ^ 2) + (C' + C) : ℝ) :
          EReal) := by
      rw [← EReal.coe_add]
      congr 1
      ring

variable [CompactSpace X]

/-- Lelong numbers of currents only depend on the singularity type. -/
theorem currentLelong_eq_of_sameSingularityType {T T' : ClosedPositiveCurrent m X}
    (h : SameSingularityType T T') (x : X) : currentLelong T x = currentLelong T' x := by
  have hT := isPresentation_presentation T
  have hT' := isPresentation_presentation T'
  have he := (sameSingularityType_iff_of_isPresentation hT hT').mp h
  rw [currentLelong_eq_of_isPresentation hT, currentLelong_eq_of_isPresentation hT']
  exact le_antisymm (sourceLelong_le_of_singularityLE he.2 x)
    (sourceLelong_le_of_singularityLE he.1 x)

/-- **Currents with minimal singularities** in `α`: `T ∈ 𝒵₊(X, α)` with `T' ⪯ T` for all
`T' ∈ 𝒵₊(X, α)`. -/
def IsMinimalSingularities (α : RealBottChern (m + 1) X) (T : ClosedPositiveCurrent m X) : Prop :=
  currentClass T = α ∧ ∀ T' : ClosedPositiveCurrent m X, currentClass T' = α → MoreSingular T' T

/-- Two currents with minimal singularities in the same class have the same singularity type. -/
theorem IsMinimalSingularities.sameSingularityType {α : RealBottChern (m + 1) X}
    {T T' : ClosedPositiveCurrent m X} (hT : IsMinimalSingularities α T)
    (hT' : IsMinimalSingularities α T') : SameSingularityType T T' :=
  ⟨hT'.2 T hT.1, hT.2 T' hT'.1⟩

variable [ConnectedSpace X]

/-- **Every pseudo-effective class contains a current with minimal singularities**, namely
`θ + dd^c V_θ` for a representative `θ` (`V_θ` = `sourceMinimalEnvelope θ`). -/
theorem exists_minimalSingularities {α : RealBottChern (m + 1) X} (hα : IsPseudoeffective α) :
    ∃ T : ClosedPositiveCurrent m X, IsMinimalSingularities α T := by
  obtain ⟨θa, hθa, hmin⟩ := exists_minimalSingularities_of_pseudoeffective
    ((isPseudoeffective_iff_classPseudoeffectiveViaPotentials α).mp hα)
  set θ : ClosedRealOneOneForm (m + 1) X := atlasClosedFormToNative θa with hθdef
  have hV : IsThetaPshPotential θ.val (sourceMinimalEnvelope θa) :=
    (isThetaPSH_iff_nativeThetaPotential θa _).mp hmin.1
  refine ⟨thetaPositiveCurrent θ _ hV, ?_, ?_⟩
  · rw [currentClass_thetaPositiveCurrent, hθa]
  · intro T' hT'
    obtain ⟨θ', u', h'⟩ := exists_presentation T'
    rw [moreSingular_iff_of_isPresentation h' (isPresentation_thetaPositiveCurrent θ _ hV)]
    have hcl : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative θ := by
      rw [← h'.currentClass_eq, hT', hθa]
    obtain ⟨g, hg, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff θ' θ).mp hcl
    have hψ : IsThetaPshPotential θ.val (fun x => u' x - (g x : EReal)) :=
      thetaPshPotential_sub_smooth hg hrel h'.isThetaPsh
    have hψa : (ofFixedModel (m + 1) X).IsThetaPSH θa (fun x => u' x - (g x : EReal)) :=
      (isThetaPSH_iff_nativeThetaPotential θa _).mpr hψ
    exact singularityLE_trans (singularityLE_sub_chartSmooth hg u') (hmin.2 _ hψa)

/-- **The non-nef locus** (`def:nnlocus`): `nn(α) = {x : ν(T_min, x) > 0}`. -/
def nonNefLocus (α : RealBottChern (m + 1) X) : Set X :=
  {x | ∃ T : ClosedPositiveCurrent m X, IsMinimalSingularities α T ∧ 0 < currentLelong T x}

omit [ConnectedSpace X] in
/-- The non-nef locus does not depend on the current with minimal singularities. -/
theorem nonNefLocus_eq_of_isMinimalSingularities {α : RealBottChern (m + 1) X}
    {T : ClosedPositiveCurrent m X} (hT : IsMinimalSingularities α T) :
    nonNefLocus α = {x | 0 < currentLelong T x} := by
  ext x
  constructor
  · rintro ⟨T', hT', hx⟩
    show 0 < currentLelong T x
    rwa [currentLelong_eq_of_sameSingularityType (hT.sameSingularityType hT') x]
  · intro hx
    exact ⟨T, hT, hx⟩

end SGPT.PSH.BookCurrent
