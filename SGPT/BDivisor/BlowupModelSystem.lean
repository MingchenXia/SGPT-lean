import SGPT.BDivisor.WeilBDivisor
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.BlowupConnected

/-!
# The book's model system: finite compositions of blow-ups with smooth centres

Source: `chap:bdiv` (the index set "all modifications `π : Y → X`" of `def:bdiv:L38`), with the
book's notion of modification: `def:modif` (appendix *Unibranch spaces*): "a modification of a
compact complex space `X` is a finite composition of blow-ups with smooth centres", and
`π' : Z → X` *dominates* `π : Y → X` if `π' = π ∘ g` for a morphism `g : Z → Y`; "the
modifications of `X` together with the domination relation form a directed set".

The b-divisor files of lanes S4–S36 (`SGPT.BDivisor.Modification`, `SGPT.BDivisor.WeilBDivisor`,
…) index b-divisors by **all** proper holomorphic bimeromorphic maps from complex manifolds
(`IsAnalyticModification`). Here we single out the book's models inside that system:

* `SGPT.BDivisor.ModelSystem n X` — a *system of models*: a class of modifications containing the
  root `id : X → X` and directed for domination. Everything about b-divisors that only uses the
  directed preorder of models is developed once for an arbitrary model system
  (`SGPT.BDivisor.WeilBDivisorOn`, files `BlowupModel*.lean`).
* `SGPT.BDivisor.Modification.IsBlowupModel π` — `π : Y → X` is a finite composition of blow-ups
  with smooth centres (TN's `IsBlowupSequence`, which is `def:modif`).
* `SGPT.BDivisor.ModelSystem.blowup` — **the book's model system** (`X` compact): directed by
  `SGPT.Foundations.Analysis.Pending.HironakaChowLemma.exists_common_isBlowupSequence` (two blow-up
  sequences of a compact manifold are dominated by a third).
* `SGPT.BDivisor.ModelSystem.all` — all modifications (`X` compact connected), the system of the
  earlier files.
* Every blow-up model of a compact Kähler manifold is compact Kähler
  (`Modification.IsBlowupModel.nonempty_kahlerBackground`, Blanchard's theorem, proved in TN as
  `BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong`) and every blow-up model of a connected
  manifold is connected.
* `SGPT.BDivisor.ModelSystem.IsCofinal` and `ModelSystem.blowup_isCofinal_of_chow`: the blow-up
  models are cofinal among all modifications **if** Hironaka's Chow lemma holds
  (`HironakaChowLemmaManifold`, a proposition of TN that is not proved; TN reduces it to
  `HironakaDominatingIdealManifold`, also unproved). This is the only place where the comparison
  with the earlier convention needs the Chow lemma.

Convention. `conventions.tex` describes a modification as a proper bimeromorphic morphism *locally*
obtained from finite compositions of blow-ups; for the compact `X` of `chap:bdiv` the appendix
definition `def:modif` (global finite compositions) is the one in force, and it is the one used
here.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (n X) in
/-- A **system of models** of `X`: a class of modifications of `X` containing the root
`id : X → X` and directed for the domination preorder. -/
structure ModelSystem where
  /-- The modifications belonging to the system. -/
  Mem : Modification n X → Prop
  root_mem : Mem Modification.root
  directed : ∀ π₁ π₂ : Modification n X, Mem π₁ → Mem π₂ →
    ∃ ρ : Modification n X, Mem ρ ∧ π₁ ≤ ρ ∧ π₂ ≤ ρ

namespace ModelSystem

/-- The models of a system, preordered by domination. -/
abbrev Model (S : ModelSystem n X) : Type (u + 1) := {π : Modification n X // S.Mem π}

variable {S : ModelSystem n X}

theorem Model.le_iff {π π' : S.Model} : π ≤ π' ↔ π.1 ≤ π'.1 := Iff.rfl

/-- The root `id : X → X` as a model of the system. -/
def Model.root : S.Model := ⟨Modification.root, S.root_mem⟩

theorem Model.root_le (π : S.Model) : Model.root ≤ π := Modification.root_le π.1

instance instNonempty : Nonempty S.Model := ⟨Model.root⟩

/-- **The models of a system form a directed set** (the book's "lim over `π : Y → X`" is taken
along it). -/
instance instIsDirected : IsDirected S.Model (· ≤ ·) where
  directed π₁ π₂ := by
    obtain ⟨ρ, hρ, h₁, h₂⟩ := S.directed π₁.1 π₂.1 π₁.2 π₂.2
    exact ⟨⟨ρ, hρ⟩, h₁, h₂⟩

theorem Model.exists_le_le (π₁ π₂ : S.Model) : ∃ ρ : S.Model, π₁ ≤ ρ ∧ π₂ ≤ ρ :=
  (instIsDirected (S := S)).directed π₁ π₂

/-- A model system is **cofinal** if every modification of `X` is dominated by one of its
models. -/
def IsCofinal (S : ModelSystem n X) : Prop :=
  ∀ π : Modification n X, ∃ σ : S.Model, π ≤ σ.1

variable (n X) in
/-- The system of **all** modifications (the convention of `SGPT.BDivisor.Modification`). -/
def all [CompactSpace X] [ConnectedSpace X] : ModelSystem n X where
  Mem _ := True
  root_mem := trivial
  directed π₁ π₂ _ _ := by
    obtain ⟨ρ, h₁, h₂⟩ := (Modification.instIsDirected (n := n) (X := X)).directed π₁ π₂
    exact ⟨ρ, trivial, h₁, h₂⟩

theorem all_isCofinal [CompactSpace X] [ConnectedSpace X] : (all n X).IsCofinal :=
  fun π => ⟨⟨π, trivial⟩, le_refl π⟩

end ModelSystem

namespace Modification

/-- `π : Y → X` is a **blow-up model** (`def:modif`): a finite composition of blow-ups with
smooth centres. -/
def IsBlowupModel (π : Modification n X) : Prop :=
  IsBlowupSequence n X π.carrier π.map

theorem isBlowupModel_root : (root : Modification n X).IsBlowupModel :=
  IsBlowupSequence.refl

/-- The modification defined by a blow-up sequence. -/
def ofIsBlowupSequence {W : Type u} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
    [IsComplexManifold n W] {σ : W → X} (hσ : IsBlowupSequence n X W σ) : Modification n X where
  carrier := W
  map := σ
  isAnalyticModification :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hσ

theorem isBlowupModel_ofIsBlowupSequence {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W] {σ : W → X}
    (hσ : IsBlowupSequence n X W σ) : (ofIsBlowupSequence hσ).IsBlowupModel := hσ

/-- **Directedness of blow-up models**: for `X` compact, two blow-up models are dominated by a
third (TN `exists_common_isBlowupSequence`). -/
theorem IsBlowupModel.exists_le_le [CompactSpace X] {π₁ π₂ : Modification n X}
    (h₁ : π₁.IsBlowupModel) (h₂ : π₂.IsBlowupModel) :
    ∃ ρ : Modification n X, ρ.IsBlowupModel ∧ π₁ ≤ ρ ∧ π₂ ≤ ρ := by
  obtain ⟨W, tW, chW, mW, σ, g₁, g₂, hσ, hg₁, hg₂, hc₁, hc₂⟩ :=
    HironakaChowLemma.exists_common_isBlowupSequence h₁ h₂
  exact ⟨ofIsBlowupSequence hσ, hσ, ⟨g₁, hg₁, hc₁⟩, ⟨g₂, hg₂, hc₂⟩⟩

/-- A blow-up sequence of a compact Kähler manifold is compact Kähler (Blanchard's theorem along
each blow-up, TN `BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong`). -/
theorem compactSpace_and_kahler_of_isBlowupSequence [CompactSpace X]
    (hK : Nonempty (KahlerBackground n X)) {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X}
    (hf : IsBlowupSequence n X Y f) : CompactSpace Y ∧ Nonempty (KahlerBackground n Y) := by
  induction hf with
  | refl => exact ⟨inferInstance, hK⟩
  | step f C g _ hg ih =>
      obtain ⟨hc, hk⟩ := ih
      have := hc
      exact BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong hk hg

/-- **Blow-up models of a compact Kähler manifold are Kähler.** -/
theorem IsBlowupModel.nonempty_kahlerBackground [CompactSpace X]
    (hK : Nonempty (KahlerBackground n X)) {π : Modification n X} (hπ : π.IsBlowupModel) :
    Nonempty (KahlerBackground n π.carrier) :=
  (compactSpace_and_kahler_of_isBlowupSequence hK hπ).2

/-- Blow-up models of a connected manifold are connected. -/
theorem IsBlowupModel.connectedSpace [ConnectedSpace X] {π : Modification n X}
    (hπ : π.IsBlowupModel) : ConnectedSpace π.carrier :=
  BlowupConnected.connectedSpace_of_isBlowupSequence π.map hπ

end Modification

namespace ModelSystem

variable (n X) in
/-- **The book's model system** (`def:modif`): the finite compositions of blow-ups with smooth
centres of the compact manifold `X`, directed by domination. -/
def blowup [CompactSpace X] : ModelSystem n X where
  Mem := Modification.IsBlowupModel
  root_mem := Modification.isBlowupModel_root
  directed _ _ h₁ h₂ := Modification.IsBlowupModel.exists_le_le h₁ h₂

theorem blowup_mem_iff [CompactSpace X] (π : Modification n X) :
    (blowup n X).Mem π ↔ π.IsBlowupModel := Iff.rfl

/-- Every model of the book's system of a compact Kähler manifold carries a Kähler form. -/
theorem blowup_nonempty_kahlerBackground [CompactSpace X] (hK : Nonempty (KahlerBackground n X))
    (π : (blowup n X).Model) : Nonempty (KahlerBackground n π.1.carrier) :=
  Modification.IsBlowupModel.nonempty_kahlerBackground hK π.2

/-- **The Chow lemma gives cofinality of blow-up models.** If Hironaka's Chow lemma for compact
complex manifolds holds (`HironakaChowLemmaManifold`, a proposition of TN, not proved), every
modification of `X` is dominated by a blow-up model. -/
theorem blowup_isCofinal_of_chow [CompactSpace X]
    (H : HironakaChowLemma.HironakaChowLemmaManifold.{u}) : (blowup n X).IsCofinal := by
  intro π
  obtain ⟨W, tW, chW, mW, σ, g, hσ, hg, hc⟩ :=
    H n X π.carrier π.map π.isAnalyticModification
  exact ⟨⟨Modification.ofIsBlowupSequence hσ, hσ⟩, ⟨g, hg, hc⟩⟩

end ModelSystem

end SGPT.BDivisor
