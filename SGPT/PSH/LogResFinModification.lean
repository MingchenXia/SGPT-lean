import SGPT.PSH.SourceAnalyticLogResolution
import SGPT.Foundations.Analysis.Pending.BlowupRestrictOpen
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# Modifications in the sense of the book's conventions, and log resolutions

Source: `conventions.tex` ("A *modification* of a complex space `X` is a proper bimeromorphic
morphism `π : Y → X` that is locally obtained from a finite composition of blow-ups with smooth
centers"), `appendix_unibranch.tex`, `def:modif` (for a *compact* `X`: a finite composition of
blow-ups with smooth centres), and `chapter_pshfunctions.tex`, `def:logres` ("A log resolution of
`φ` is a modification `π : Y → X` such that `π^*φ` has log singularities along a simple normal
crossing effective `ℚ`-divisor. See `def:modif` for the notion of modifications").

On complex manifolds of pure dimension `n` (`ChartedSpace (ComplexModel n)`):

* `exists_restrict_of_isBlowupSequence`: a finite composition of blow-ups with smooth centres
  restricts, over every open subset `U` of the base, to a finite composition of blow-ups of `U`
  (TN's `isBlowupAlong_restrict`, by induction on the sequence).
* `IsBlowupSequenceOver n π U`: over the open set `U`, the map `π` is a finite composition of
  blow-ups with smooth centres of `U`, up to a biholomorphism of `π⁻¹ U`.
* `IsConventionModification n π` (`conventions.tex`): `π` is a proper bimeromorphic holomorphic
  map (TN's `IsAnalyticModification`) and every point of `X` has an open neighbourhood over which
  `π` is a finite composition of blow-ups with smooth centres.
* `IsSourceModification n π`: the notion of modification used by `def:logres`, namely `def:modif`
  (`IsBlowupSequence`) when `X` is compact and the conventions' notion otherwise.  It is
  equivalent to `IsBlowupSequence` for compact `X` (`isSourceModification_iff_of_compact`) and to
  `IsConventionModification` for non-compact `X`; a finite composition of blow-ups is always a
  modification in the conventions' sense (`isConventionModification_of_isBlowupSequence`).
* `IsSourceLogResolution n φ π` (`def:logres` for arbitrary, possibly non-compact `X`), with
  `isSourceLogResolution_iff_isLogResolution` identifying it, for compact `X`, with the compact
  notion `IsLogResolution` of `SGPT.PSH.LogResolution`.

Remark (not an erratum claim): for compact `X` the conventions' notion is strictly weaker than
`def:modif` (Hironaka's example of a proper modification of a projective threefold which is
locally, but not globally, a composition of two blow-ups along smooth curves); `def:logres`
refers to `def:modif`, which is what `IsSourceModification` records.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u

section Native

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **A finite composition of blow-ups restricts over open subsets.**  If `π : Y → X` is a finite
composition of blow-ups with smooth centres and `U ⊆ X` is open, then `π⁻¹ U → U` is a finite
composition of blow-ups with smooth centres of `U` (the centres are the traces of the original
ones). -/
theorem exists_restrict_of_isBlowupSequence {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    (U : Opens X) :
    ∃ (V : Opens Y) (σ : V → U), (V : Set Y) = π ⁻¹' U ∧ IsBlowupSequence n U V σ ∧
      ∀ v, (σ v : X) = π v := by
  induction hπ with
  | refl => exact ⟨U, id, rfl, IsBlowupSequence.refl, fun _ => rfl⟩
  | @step Y₀ Z _ _ _ _ _ _ f C g _ hg ih =>
    obtain ⟨V₀, σ₀, hV₀, hσ₀, hval₀⟩ := ih
    have hopen : IsOpen (g ⁻¹' (V₀ : Set Y₀)) := V₀.isOpen.preimage hg.contMDiff.continuous
    have hblow := BlowupRestrictOpen.isBlowupAlong_restrict hg V₀ hopen
    refine ⟨⟨g ⁻¹' (V₀ : Set Y₀), hopen⟩, σ₀ ∘ fun p => (⟨g p.1, p.2⟩ : V₀), ?_,
      IsBlowupSequence.step σ₀ _ _ hσ₀ hblow, ?_⟩
    · change g ⁻¹' (V₀ : Set Y₀) = (f ∘ g) ⁻¹' (U : Set X)
      rw [hV₀]
      rfl
    · intro v
      exact hval₀ _

variable (n) in
/-- `conventions.tex`, local clause: over the open set `U ⊆ X`, the map `π` is a finite
composition of blow-ups with smooth centres of `U`, up to a biholomorphism `ψ : W ≅ π⁻¹ U`:
`π ∘ ψ = σ` for a finite composition of blow-ups `σ : W → U`. -/
def IsBlowupSequenceOver (π : Y → X) (U : Opens X) : Prop :=
  ∃ V : Opens Y, (V : Set Y) = π ⁻¹' U ∧
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → U)
      (ψ : W ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V),
      IsBlowupSequence n U W σ ∧ ∀ w, π (ψ w : Y) = σ w

/-- A finite composition of blow-ups is, over every open subset of the base, a finite composition
of blow-ups (with `ψ` the identity of `π⁻¹ U`). -/
theorem isBlowupSequenceOver_of_isBlowupSequence {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    (U : Opens X) : IsBlowupSequenceOver n π U := by
  obtain ⟨V, σ, hV, hσ, hval⟩ := exists_restrict_of_isBlowupSequence hπ U
  exact ⟨V, hV, V, inferInstance, inferInstance, inferInstance, σ,
    Diffeomorph.refl 𝓘(ℂ, ComplexModel n) V ∞, hσ, fun v => (hval v).symm⟩

variable (n) in
/-- `conventions.tex`: a *modification* is a proper bimeromorphic morphism (TN's
`IsAnalyticModification`: holomorphic, proper, with a holomorphic inverse off closed nowhere dense
analytic subsets) which is locally (over a neighbourhood of every point of `X`) obtained from a
finite composition of blow-ups with smooth centres. -/
def IsConventionModification (π : Y → X) : Prop :=
  IsAnalyticModification (n := n) π ∧ ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsBlowupSequenceOver n π U

/-- `def:modif` implies the conventions' notion: a finite composition of blow-ups with smooth
centres is a proper bimeromorphic morphism which is (even globally) a finite composition of
blow-ups. -/
theorem isConventionModification_of_isBlowupSequence {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) : IsConventionModification n π :=
  ⟨HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ,
    fun _ => ⟨⊤, trivial, isBlowupSequenceOver_of_isBlowupSequence hπ ⊤⟩⟩

variable (n) in
/-- The notion of *modification* in `def:logres`: `def:modif` (a finite composition of blow-ups
with smooth centres) when `X` is compact, the conventions' notion when `X` is not compact. -/
def IsSourceModification (π : Y → X) : Prop :=
  (CompactSpace X → IsBlowupSequence n X Y π) ∧
    (¬ CompactSpace X → IsConventionModification n π)

/-- For compact `X`, the book's modifications are exactly the finite compositions of blow-ups with
smooth centres (`def:modif`). -/
theorem isSourceModification_iff_of_compact [CompactSpace X] {π : Y → X} :
    IsSourceModification n π ↔ IsBlowupSequence n X Y π :=
  ⟨fun h => h.1 inferInstance, fun h => ⟨fun _ => h, fun hc => absurd (inferInstance : CompactSpace X) hc⟩⟩

/-- For non-compact `X`, the book's modifications are those of `conventions.tex`. -/
theorem isSourceModification_iff_of_not_compact (hX : ¬ CompactSpace X) {π : Y → X} :
    IsSourceModification n π ↔ IsConventionModification n π :=
  ⟨fun h => h.2 hX, fun h => ⟨fun hc => absurd hc hX, fun _ => h⟩⟩

/-- Every modification of `def:logres` is a modification in the sense of `conventions.tex`. -/
theorem IsSourceModification.isConventionModification {π : Y → X}
    (h : IsSourceModification n π) : IsConventionModification n π := by
  by_cases hX : CompactSpace X
  · exact isConventionModification_of_isBlowupSequence (h.1 hX)
  · exact h.2 hX

/-- The book's modification is the conventions' notion, refined by `def:modif` on compact `X`. -/
theorem isSourceModification_iff {π : Y → X} :
    IsSourceModification n π ↔
      IsConventionModification n π ∧ (CompactSpace X → IsBlowupSequence n X Y π) :=
  ⟨fun h => ⟨h.isConventionModification, h.1⟩, fun h => ⟨h.2, fun _ => h.1⟩⟩

variable (n) in
/-- Source `def:logres` for an arbitrary (possibly non-compact) complex manifold `X` of pure
dimension `n`: `π : Y → X` is a modification (`IsSourceModification`) and `π^*φ = φ ∘ π` has log
singularities (`NativeHasLogSingularitiesAlongAnyDimension`, the native form of
`def:pshfunctions:L1393`) along a simple normal crossing effective `ℚ`-divisor. -/
def IsSourceLogResolution (φ : X → EReal) (π : Y → X) : Prop :=
  IsSourceModification n π ∧
    ∃ D : EffectiveGeometricQDivisor n Y, D.IsSNC ∧
      NativeHasLogSingularitiesAlongAnyDimension D (φ ∘ π)

variable (n) in
/-- The variant of `def:logres` with the conventions' notion of modification. -/
def IsConventionLogResolution (φ : X → EReal) (π : Y → X) : Prop :=
  IsConventionModification n π ∧
    ∃ D : EffectiveGeometricQDivisor n Y, D.IsSNC ∧
      NativeHasLogSingularitiesAlongAnyDimension D (φ ∘ π)

/-- For compact `X`, `def:logres` is the compact notion `IsLogResolution`
(`def:modif` + simple normal crossing log singularities). -/
theorem isSourceLogResolution_iff_isLogResolution [CompactSpace X] {φ : X → EReal}
    {π : Y → X} : IsSourceLogResolution n φ π ↔ IsLogResolution n φ π := by
  unfold IsSourceLogResolution IsLogResolution
  rw [isSourceModification_iff_of_compact]

/-- For non-compact `X`, `def:logres` uses the conventions' notion of modification. -/
theorem isSourceLogResolution_iff_of_not_compact (hX : ¬ CompactSpace X) {φ : X → EReal}
    {π : Y → X} : IsSourceLogResolution n φ π ↔ IsConventionLogResolution n φ π := by
  unfold IsSourceLogResolution IsConventionLogResolution
  rw [isSourceModification_iff_of_not_compact hX]

/-- A log resolution of `def:logres` is a log resolution with the conventions' modifications. -/
theorem IsSourceLogResolution.isConventionLogResolution {φ : X → EReal} {π : Y → X}
    (h : IsSourceLogResolution n φ π) : IsConventionLogResolution n φ π :=
  ⟨h.1.isConventionModification, h.2⟩

/-- The compact notion `IsLogResolution` is a log resolution in the conventions' sense. -/
theorem IsLogResolution.isConventionLogResolution {φ : X → EReal} {π : Y → X}
    (h : IsLogResolution n φ π) : IsConventionLogResolution n φ π :=
  ⟨isConventionModification_of_isBlowupSequence h.1, h.2⟩

/-- Source `thm:resolvelogsing` (pure dimension, `def:logres` as `IsSourceLogResolution`): on a
compact complex manifold, every quasi-psh `φ` with analytic singularities (the source's local
rational analytic type) has a log resolution, with `Y` compact. -/
theorem exists_isSourceLogResolution_of_hasRationalAnalyticType [CompactSpace X]
    {φ : X → EReal} (hφ : (VariableComplexAtlas.ofFixedModel n X).IsQPSH φ)
    (ha : (VariableComplexAtlas.ofFixedModel n X).HasRationalAnalyticType φ) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X), CompactSpace Y ∧ IsSourceLogResolution n φ π := by
  obtain ⟨Y, tY, cY, mY, π, hY, hlog⟩ := exists_isLogResolution_of_hasRationalAnalyticType hφ ha
  exact ⟨Y, tY, cY, mY, π, hY, isSourceLogResolution_iff_isLogResolution.mpr hlog⟩

end Native

end SGPT.PSH
