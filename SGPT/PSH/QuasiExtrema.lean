import SGPT.PSH.PlurifineQuasiPSH
import Mathlib.Topology.Order.IsLUB

namespace SGPT.PSH
open Set TopologicalSpace
open scoped Topology

/-- Actual open subsets inherit density of an original dense complement. -/
theorem dense_subtype_compl_of_isOpen {X : Type*} [TopologicalSpace X]
    {D Z : Set X} (hD : IsOpen D) (hZ : Dense Zᶜ) :
    Dense {x : D | x.val ∉ Z} :=
  hZ.preimage hD.isOpenEmbedding_subtypeVal.isOpenMap

/-- On the actual specified locus, at least one function is finite; hence
the original EReal difference is continuous and never has a double pole. -/
theorem continuous_ereal_sub_on_finite_locus {X : Type*} [TopologicalSpace X]
    {u w : X → EReal} (hu : Continuous u) (hw : Continuous w)
    (hut : ∀ x, u x ≠ ⊤) {D : Set X}
    (hD : ∀ x ∈ D, u x ≠ ⊥ ∨ w x ≠ ⊥) :
    Continuous (fun x : D ↦ u x.val - w x.val) := by
  have hc := hu.comp (continuous_subtype_val : Continuous (Subtype.val : D → X))
  have hg := hw.neg.comp (continuous_subtype_val : Continuous (Subtype.val : D → X))
  rw [continuous_iff_continuousAt]
  intro x
  have hp : u x.val ≠ ⊥ ∨ -w x.val ≠ ⊤ := by
    simpa only [ne_eq, EReal.neg_eq_top_iff] using hD x.val x.property
  simpa only [sub_eq_add_neg, Function.comp_def, Pi.neg_apply] using
    (EReal.continuousAt_add (Or.inl (hut x.val)) hp).comp
      (hc.continuousAt.prodMk hg.continuousAt)

/-- Actual dense-complement deletion preserves both extended-real extrema
on an original open subset; no boundedness or nonempty-locus premise is needed. -/
theorem extrema_eq_of_dense_compl_on_open {X : Type*} [TopologicalSpace X]
    {D Z : Set X} (hD : IsOpen D) (hZ : Dense Zᶜ) {f : D → EReal}
    (hf : Continuous f) :
    (⨆ x : {x : D | x.val ∉ Z}, f x.val) = (⨆ x : D, f x) ∧
    (⨅ x : {x : D | x.val ∉ Z}, f x.val) = (⨅ x : D, f x) := by
  have hd := dense_subtype_compl_of_isOpen hD hZ
  exact ⟨hd.ciSup' hf, hd.ciInf' hf⟩

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open scoped Topology
universe v
variable {X : Type v} [TopologicalSpace X]

/-- Exact source family of actual pluripolar deletions containing the original
exceptional set; all functions remain defined on the original complement. -/
def PluripolarDeletions (A : VariableComplexAtlas X) (Z : Set X) :=
  {W : Set X // A.LocallyPluripolar W ∧ Z ⊆ W}

/-- The original function restricted to one eligible deletion complement. -/
def restrictDeletion (A : VariableComplexAtlas X) {Z : Set X}
    (f : ↥(Zᶜ) → EReal) (W : A.PluripolarDeletions Z) : ↥(W.valᶜ) → EReal :=
  fun x ↦ f ⟨x.val, fun hx ↦ x.property (W.property.2 hx)⟩

/-- Exact source def:quasi_sup with the function's original complement domain. -/
noncomputable def quasiSup (A : VariableComplexAtlas X) {Z : Set X}
    (f : ↥(Zᶜ) → EReal) : EReal :=
  ⨅ W : A.PluripolarDeletions Z, ⨆ x : ↥(W.valᶜ), A.restrictDeletion f W x

/-- Exact source def:quasi_sup dual formula, retaining the original domain. -/
noncomputable def quasiInf (A : VariableComplexAtlas X) {Z : Set X}
    (f : ↥(Zᶜ) → EReal) : EReal :=
  ⨆ W : A.PluripolarDeletions Z, ⨅ x : ↥(W.valᶜ), A.restrictDeletion f W x

variable {A : VariableComplexAtlas X}

/-- The genuine original exceptional set is itself an eligible deletion. -/
theorem pluripolarDeletions_nonempty {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    Nonempty (A.PluripolarDeletions Z) := ⟨⟨Z, hZ, Subset.rfl⟩⟩

/-- Any actual eligible deletion bounds the source quasi-supremum. -/
theorem quasiSup_le_deleted_sup {Z : Set X} (f : ↥(Zᶜ) → EReal)
    (W : A.PluripolarDeletions Z) :
    A.quasiSup f ≤ ⨆ x : ↥(W.valᶜ), A.restrictDeletion f W x := iInf_le _ W

/-- Any actual eligible deletion bounds the source quasi-infimum. -/
theorem deleted_inf_le_quasiInf {Z : Set X} (f : ↥(Zᶜ) → EReal)
    (W : A.PluripolarDeletions Z) :
    (⨅ x : ↥(W.valᶜ), A.restrictDeletion f W x) ≤ A.quasiInf f :=
  le_iSup (fun U : A.PluripolarDeletions Z ↦
    ⨅ x : ↥(U.valᶜ), A.restrictDeletion f U x) W

/-- Original-domain supremum bounds the genuine source quasi-supremum. -/
theorem quasiSup_le_source_sup {Z : Set X} (hZ : A.LocallyPluripolar Z)
    (f : ↥(Zᶜ) → EReal) : A.quasiSup f ≤ ⨆ x : ↥(Zᶜ), f x :=
  quasiSup_le_deleted_sup f ⟨Z, hZ, Subset.rfl⟩

/-- Original-domain infimum bounds the genuine source quasi-infimum. -/
theorem source_inf_le_quasiInf {Z : Set X} (hZ : A.LocallyPluripolar Z)
    (f : ↥(Zᶜ) → EReal) : (⨅ x : ↥(Zᶜ), f x) ≤ A.quasiInf f :=
  deleted_inf_le_quasiInf f ⟨Z, hZ, Subset.rfl⟩

/-- Exact order preservation for genuine source functions on their original
complement domain. -/
theorem quasiSup_mono {Z : Set X} {f g : ↥(Zᶜ) → EReal} (hfg : ∀ x, f x ≤ g x) :
    A.quasiSup f ≤ A.quasiSup g := by
  apply iInf_mono
  intro W
  exact iSup_mono fun x ↦ hfg _

theorem quasiInf_mono {Z : Set X} {f g : ↥(Zᶜ) → EReal} (hfg : ∀ x, f x ≤ g x) :
    A.quasiInf f ≤ A.quasiInf g := by
  apply iSup_mono
  intro W
  exact iInf_mono fun x ↦ hfg _

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.PSH
open Set TopologicalSpace
open scoped Topology

/-- Mathlib's true dense-image extremum identities apply to the actual
extended-real function, including unbounded values and an empty original space. -/
theorem extrema_eq_of_dense_compl {X : Type*} [TopologicalSpace X]
    {Z : Set X} (hZ : Dense Zᶜ) {f : X → EReal} (hf : Continuous f) :
    (⨆ x : ↥(Zᶜ), f x.val) = (⨆ x : X, f x) ∧
    (⨅ x : ↥(Zᶜ), f x.val) = (⨅ x : X, f x) :=
  ⟨hZ.ciSup' hf, hZ.ciInf' hf⟩

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open scoped Topology
universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Genuine source pluripolar deletion preserves both actual extrema of
an original source PSH function; global quasi-PSH remains a separate bridge. -/
theorem IsPSH.extrema_eq_off_pluripolar {u : X → EReal} (hu : A.IsPSH u)
    {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    (⨆ x : ↥(Zᶜ), u x.val) = (⨆ x : X, u x) ∧
    (⨅ x : ↥(Zᶜ), u x.val) = (⨅ x : X, u x) :=
  @extrema_eq_of_dense_compl X A.plurifineTopology Z hZ.dense_plurifine_compl
    u hu.continuous_plurifine

/-- Exact source quasi-extrema of an actual globally fine-continuous function
agree with its true original extrema, by all eligible genuine dense deletions. -/
theorem quasiExtrema_eq_of_continuous {u : X → EReal}
    (hu : @Continuous X EReal A.plurifineTopology inferInstance u)
    {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    A.quasiSup (fun x : ↥(Zᶜ) ↦ u x.val) = (⨆ x : X, u x) ∧
    A.quasiInf (fun x : ↥(Zᶜ) ↦ u x.val) = (⨅ x : X, u x) := by
  let : Nonempty (A.PluripolarDeletions Z) := pluripolarDeletions_nonempty hZ
  constructor
  · change (⨅ W : A.PluripolarDeletions Z, ⨆ x : ↥(W.valᶜ), u x.val) = _
    have heq : ∀ W : A.PluripolarDeletions Z,
        (⨆ x : ↥(W.valᶜ), u x.val) = (⨆ x : X, u x) := fun W ↦
      (@extrema_eq_of_dense_compl X A.plurifineTopology W.val
        W.property.1.dense_plurifine_compl u hu).1
    simp_rw [heq]
    exact iInf_const
  · change (⨆ W : A.PluripolarDeletions Z, ⨅ x : ↥(W.valᶜ), u x.val) = _
    have heq : ∀ W : A.PluripolarDeletions Z,
        (⨅ x : ↥(W.valᶜ), u x.val) = (⨅ x : X, u x) := fun W ↦
      (@extrema_eq_of_dense_compl X A.plurifineTopology W.val
        W.property.1.dense_plurifine_compl u hu).2
    simp_rw [heq]
    exact iSup_const

/-- Genuine source PSH fine-continuity supplies, rather than assumes,
the continuity needed for its true original-domain quasi-extrema. -/
theorem IsPSH.quasiExtrema_eq {u : X → EReal} (hu : A.IsPSH u)
    {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    A.quasiSup (fun x : ↥(Zᶜ) ↦ u x.val) = (⨆ x : X, u x) ∧
    A.quasiInf (fun x : ↥(Zᶜ) ↦ u x.val) = (⨅ x : X, u x) :=
  quasiExtrema_eq_of_continuous hu.continuous_plurifine hZ

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.PSH
open Set TopologicalSpace
open scoped Topology

/-- Deleting a true dense complement preserves the original difference extrema
on any actual open locus avoiding simultaneous poles. -/
theorem extrema_difference_eq_on_open_finite_locus {X : Type*} [TopologicalSpace X]
    {u w : X → EReal} (hu : Continuous u) (hw : Continuous w)
    (hut : ∀ x, u x ≠ ⊤) {D Z : Set X} (hD : IsOpen D) (hZ : Dense Zᶜ)
    (hfinite : ∀ x ∈ D, u x ≠ ⊥ ∨ w x ≠ ⊥) :
    (⨆ x : {x : D | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨆ x : D, u x.val - w x.val) ∧
    (⨅ x : {x : D | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨅ x : D, u x.val - w x.val) :=
  extrema_eq_of_dense_compl_on_open hD hZ
    (continuous_ereal_sub_on_finite_locus hu hw hut hfinite)

/-- The actual non-pole locus of any continuous extended-real function is open. -/
theorem isOpen_finiteLocus_of_continuous {X : Type*} [TopologicalSpace X]
    {u : X → EReal} (hu : Continuous u) : IsOpen {x | u x ≠ ⊥} := by
  simpa only [bot_lt_iff_ne_bot] using isOpen_lt (continuous_const (y := (⊥ : EReal))) hu

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open scoped Topology
universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- True source PSH difference extrema on the first original non-pole locus
are unchanged after deleting an actual source pluripolar set. -/
theorem IsPSH.difference_extrema_eq_on_left_finite_locus {u w : X → EReal}
    (hu : A.IsPSH u) (hw : A.IsPSH w) {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    (⨆ x : {x : {y | u y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨆ x : {y | u y ≠ ⊥}, u x.val - w x.val) ∧
    (⨅ x : {x : {y | u y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨅ x : {y | u y ≠ ⊥}, u x.val - w x.val) :=
  @extrema_difference_eq_on_open_finite_locus X A.plurifineTopology u w
    hu.continuous_plurifine hw.continuous_plurifine hu.ne_top {x | u x ≠ ⊥} Z
    (@isOpen_finiteLocus_of_continuous X A.plurifineTopology u hu.continuous_plurifine)
    hZ.dense_plurifine_compl (fun _ hx ↦ Or.inl hx)

/-- The corresponding source PSH difference extrema retain the second
original non-pole locus and its potentially infinite difference values. -/
theorem IsPSH.difference_extrema_eq_on_right_finite_locus {u w : X → EReal}
    (hu : A.IsPSH u) (hw : A.IsPSH w) {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    (⨆ x : {x : {y | w y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨆ x : {y | w y ≠ ⊥}, u x.val - w x.val) ∧
    (⨅ x : {x : {y | w y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨅ x : {y | w y ≠ ⊥}, u x.val - w x.val) :=
  @extrema_difference_eq_on_open_finite_locus X A.plurifineTopology u w
    hu.continuous_plurifine hw.continuous_plurifine hu.ne_top {x | w x ≠ ⊥} Z
    (@isOpen_finiteLocus_of_continuous X A.plurifineTopology w hw.continuous_plurifine)
    hZ.dense_plurifine_compl (fun _ hx ↦ Or.inr hx)

end SGPT.PSH.VariableComplexAtlas
