import SGPT.PSH.SourcePositiveMixedIVolume
import SGPT.Envelopes.SourceEnvelopeContactSupport

/-!
# The volume of a pseudo-effective class

Source: Chapter "The envelope operators", `def:volcohclass`: for a pseudo-effective class
`α ∈ H^{1,1}(X, ℝ)`, `vol α = vol T_min` where `T_min` is a current with minimal
singularities in `α`, and `vol α` does not depend on the choice of `T_min`.

Classes are real Bott--Chern classes `RealBottChern n M` (quotients of closed real smooth
`(1,1)`-forms by `dd^c` of smooth functions). A current in `α` is `θ + dd^c φ` for a
representative `θ` and `φ ∈ PSH(X,θ)`; it has minimal singularities when every
`ψ ∈ PSH(X,θ)` satisfies `ψ ⪯ φ` (`SourceMinimalSingularities`). Its volume is
`vol(θ, φ) = ∫_X θ_{P_θ[φ]_I}^n` (`def:volqpsh`, `eq:volcurrdef`).

* `sourceIVolume_eq_of_minimalSingularities`: two currents with minimal singularities in the
  same class (for possibly different representatives) have the same volume;
* `sourceClassVolume`: the volume of a class, and `sourceClassVolume_eq` identifies it with
  `vol T_min` for every current with minimal singularities in the class;
* `exists_minimalSingularities_of_pseudoeffective`: pseudo-effective classes contain
  currents with minimal singularities (`V_θ`), and
  `sourceClassVolume_eq_minimalEnvelope_mass`: `vol α = ∫_X θ_{V_θ}^n`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `θ + dd^c φ` is a current with minimal singularities in the class of `θ`. -/
def SourceMinimalSingularities (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) : Prop :=
  (ofFixedModel n M).IsThetaPSH θ φ ∧
    ∀ ψ : M → EReal, (ofFixedModel n M).IsThetaPSH θ ψ → SGPT.PSH.SingularityLE ψ φ

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- A smooth function on a compact manifold is bounded, so `φ ⪯ φ - g`. -/
theorem singularityLE_sub_chartSmooth {g : M → ℝ} (hg : ChartSmooth (n := n) g)
    (φ : M → EReal) : SGPT.PSH.SingularityLE φ (fun x => φ x - (g x : EReal)) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨B, fun x => ?_⟩
  have hgx : g x ≤ B := by
    have h := hB x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have he : φ x - (g x : EReal) + (B : EReal) = φ x + ((B - g x : ℝ) : EReal) := by
    have := sub_coe_add_coe (φ x) (g x) (B - g x)
    rwa [sub_add_cancel] at this
  rw [he]
  exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (sub_nonneg.mpr hgx))

/-- The volume does not decrease from any current to a current with minimal singularities
in the same class, for arbitrary representatives of the class. -/
theorem sourceIVolume_le_of_minimalSingularities (ω : KahlerBackground n M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hclass : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {φ ψ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : SourceMinimalSingularities η ψ) :
    sourceIVolume θ φ hφ ≤ sourceIVolume η ψ hψ.1 := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hclass
  have hchange : SourceSmoothBackgroundChange θ η g :=
    (sourceSmoothBackgroundChange_iff_native _ _ _).mpr ⟨hg, hθη⟩
  have hφ' := sourceThetaPSH_sub_smooth hchange hφ
  have hle : SGPT.PSH.SingularityLE φ ψ :=
    SGPT.PSH.singularityLE_trans (singularityLE_sub_chartSmooth hg φ) (hψ.2 _ hφ')
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hle
  have hI : sourceIOrder (ofFixedModel n M) φ ψ :=
    (sourceIOrder_iff_native ⟨θ, hφ⟩ ⟨η, hψ.1⟩).mpr
      (iOrderOnManifold_of_le_add
        ((isThetaPSH_iff_nativeThetaPotential η ψ).mp hψ.1).1.quasiPlurisubharmonic hC)
  have h := sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω
    (fun _ : Fin n => θ) (fun _ => η) (fun _ => φ) (fun _ => ψ) (fun _ => hφ) (fun _ => hψ.1)
    (fun _ => hclass) (fun _ => hI)
  simpa only [sourceEnvelopeMixedIVolume_diagonal] using h

/-- Source `def:volcohclass`, independence of the choice of `T_min`: currents with minimal
singularities in the same class have the same volume (representatives may differ). -/
theorem sourceIVolume_eq_of_minimalSingularities (ω : KahlerBackground n M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hclass : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {φ ψ : M → EReal} (hφ : SourceMinimalSingularities θ φ)
    (hψ : SourceMinimalSingularities η ψ) :
    sourceIVolume θ φ hφ.1 = sourceIVolume η ψ hψ.1 :=
  le_antisymm (sourceIVolume_le_of_minimalSingularities ω hclass hφ.1 hψ)
    (sourceIVolume_le_of_minimalSingularities ω hclass.symm hψ.1 hφ)

/-- Source `def:volcohclass`: the volume `vol α` of a class, namely `vol T_min` for a current
`T_min` with minimal singularities in `α` (and `0` when `α` contains no such current, i.e.
when `α` is not pseudo-effective). -/
def sourceClassVolume (α : RealBottChern n M) : ℝ≥0∞ := by
  classical
  exact if h : ∃ θ : AtlasClosedRealOneOneForm (ofFixedModel n M),
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) = α ∧
        ∃ φ : M → EReal, SourceMinimalSingularities θ φ then
    sourceIVolume h.choose h.choose_spec.2.choose h.choose_spec.2.choose_spec.1 else 0

/-- Source `def:volcohclass`: `vol α = vol T_min` for EVERY current `T_min = θ + dd^c φ` with
minimal singularities in `α`. -/
theorem sourceClassVolume_eq (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceMinimalSingularities θ φ) :
    sourceClassVolume (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) =
      sourceIVolume θ φ hφ.1 := by
  classical
  have hex : ∃ η : AtlasClosedRealOneOneForm (ofFixedModel n M),
      RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
        RealBottChern.ofRepresentative (atlasClosedFormToNative θ) ∧
        ∃ ψ : M → EReal, SourceMinimalSingularities η ψ := ⟨θ, rfl, φ, hφ⟩
  unfold sourceClassVolume
  rw [dif_pos hex]
  exact sourceIVolume_eq_of_minimalSingularities ω hex.choose_spec.1
    hex.choose_spec.2.choose_spec hφ

omit [MeasurableSpace M] [BorelSpace M] in
/-- `V_θ` has minimal singularities as soon as `PSH(X,θ) ≠ ∅`. -/
theorem sourceMinimalEnvelope_minimalSingularities
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SourceMinimalSingularities θ (sourceMinimalEnvelope θ) :=
  ⟨sourceMinimalEnvelope_thetaPSH_of_mem hu,
    fun _ hψ => singularityLE_sourceMinimalEnvelope_of_thetaPSH hψ⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- Every pseudo-effective class contains a current with minimal singularities. -/
theorem exists_minimalSingularities_of_pseudoeffective {α : RealBottChern n M}
    (hα : ClassPseudoeffectiveViaPotentials α) :
    ∃ θ : AtlasClosedRealOneOneForm (ofFixedModel n M),
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) = α ∧
        SourceMinimalSingularities θ (sourceMinimalEnvelope θ) := by
  induction α using Quotient.inductionOn with
  | h T =>
    obtain ⟨u, hu⟩ := (classPseudoeffectiveViaPotentials_ofRepresentative T).mp hα
    refine ⟨nativeClosedFormToAtlas T, ?_, ?_⟩
    · rw [sourceNativeAtlasForm_roundTrip]
      rfl
    · apply sourceMinimalEnvelope_minimalSingularities (u := u)
      apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [sourceNativeAtlasForm_roundTrip]
      exact hu

/-- With the minimal envelope as `T_min`, `vol α = ∫_X θ_{V_θ}^n`: `V_θ` is its own
`I`-envelope. -/
theorem sourceClassVolume_eq_minimalEnvelope_mass (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceClassVolume (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) =
      sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
        (sourceMinimalEnvelope_thetaPSH_of_mem hu) univ := by
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hu
  rw [sourceClassVolume_eq ω (sourceMinimalEnvelope_minimalSingularities hu)]
  have hI : sourceIEnvelope θ (sourceMinimalEnvelope θ) = sourceMinimalEnvelope θ := by
    apply le_antisymm
    · intro x
      exact le_iSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧ v ≤ 0} =>
        v.1 x) ⟨_, isThetaPSH_sourceIEnvelope hV, sourceIEnvelope_le_zero θ _⟩
    · exact le_sourceIEnvelope hV (sourceMinimalEnvelope_le_zero θ)
        (sourceIEquivalent_refl ⟨θ, hV⟩)
  unfold sourceIVolume
  exact congrArg (fun μ : Measure M => μ univ)
    (sourcePotentialNonPluripolarMeasure_congr hI _ _)

end SGPT.PSH.VariableComplexAtlas
