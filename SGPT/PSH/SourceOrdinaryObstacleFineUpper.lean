import SGPT.PSH.GlobalQPSH
import SGPT.Envelopes.SourceObstacleConcentration

/-! # Whole ordinary-obstacle definition and its fine upper semicontinuity footnote

Original `def:Pthetaf`, author/chapter_npp.tex:639--646. The actual ordinary
source envelope is the existing relative envelope with top reference. Its
original quasi-everywhere competitor condition is replaced by everywhere
only for a genuinely plurifine upper semicontinuous obstacle. The ordinary
upper semicontinuous case follows from the actual topology refinement.
All extended-real values, empty families and original upper regularization
are retained. No output genuineness, noncollapse, compactness or mass premise
is used in the definition or the footnote.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set
open scoped Topology

/-- A continuous function below an upper semicontinuous function on an actual
dense complement is below it everywhere, including both infinite values. -/
theorem le_of_dense_compl_continuous_upperSemicontinuous
    {X : Type*} [TopologicalSpace X] {Z : Set X} {u f : X → EReal}
    (hZ : Dense Zᶜ) (hu : Continuous u) (hf : UpperSemicontinuous f)
    (hle : ∀ x, x ∉ Z → u x ≤ f x) : u ≤ f := by
  intro x
  by_contra hn
  obtain ⟨c, hfc, hcu⟩ := exists_between (lt_of_not_ge hn)
  have hO : IsOpen ({y | c < u y} ∩ {y | f y < c}) :=
    (isOpen_lt continuous_const hu).inter (hf.isOpen_preimage c)
  obtain ⟨y, hyO, hyZ⟩ := (dense_iff_inter_open.mp hZ) _ hO ⟨x, hcu, hfc⟩
  exact (not_lt_of_ge (hle y hyZ)) (hyO.2.trans hyO.1)

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Genuine source QPSH fine continuity and actual pluripolar-complement density
remove every exception against a fine upper semicontinuous obstacle. -/
theorem IsQPSH.le_of_plurifine_upperSemicontinuous_off_pluripolar
    {u f : X → EReal} (hu : A.IsQPSH u)
    (hf : @UpperSemicontinuous X EReal A.plurifineTopology inferInstance f)
    {Z : Set X} (hZ : A.LocallyPluripolar Z)
    (hle : ∀ x, x ∉ Z → u x ≤ f x) : u ≤ f :=
  @SGPT.PSH.le_of_dense_compl_continuous_upperSemicontinuous X A.plurifineTopology
    Z u f hZ.dense_plurifine_compl hu.continuous_plurifine hf hle

section FixedDimension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The exact original fine-USC obstacle footnote at the level of every genuine
source theta-PSH competitor, without any assumption on the envelope. -/
theorem sourceQuasiEverywhere_le_iff_of_plurifine_upperSemicontinuous
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u f : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hf : @UpperSemicontinuous M EReal (ofFixedModel n M).plurifineTopology
      inferInstance f) :
    SourceQuasiEverywhere (n := n) (fun x => u x ≤ f x) ↔ u ≤ f := by
  constructor
  · intro hqe
    exact IsQPSH.le_of_plurifine_upperSemicontinuous_off_pluripolar
      ⟨θ, hu⟩ hf hqe (fun x hx => Classical.not_not.mp hx)
  · exact sourceQuasiEverywhere_of_forall

/-- Ordinary upper semicontinuity is the literal special case of the source
fine-USC obstacle footnote, by the actual fine/ordinary topology comparison. -/
theorem sourceQuasiEverywhere_le_iff_of_upperSemicontinuous
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u f : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hf : UpperSemicontinuous f) :
    SourceQuasiEverywhere (n := n) (fun x => u x ≤ f x) ↔ u ≤ f := by
  have hfFine : @UpperSemicontinuous M EReal (ofFixedModel n M).plurifineTopology
      inferInstance f := by
    intro x a ha
    exact (nhds_mono (a := x) (ofFixedModel n M).plurifine_le_euclidean) (hf x a ha)
  exact sourceQuasiEverywhere_le_iff_of_plurifine_upperSemicontinuous hu hfFine

/-- The literal original ordinary-obstacle supremum uses ALL original genuine
quasi-everywhere competitors. The top-reference comparison is automatic. -/
theorem sourceObstacleEnvelope_eq_uscSup_qeCompetitors
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (f : M → EReal) :
    sourceRelativeEnvelope θ (fun _ => ⊤) f =
      uscSup (fun a : {a : M → EReal // (ofFixedModel n M).IsThetaPSH θ a ∧
        SourceQuasiEverywhere (n := n) (fun x => a x ≤ f x)} => a.1) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup (fun b : {b : M → EReal // (ofFixedModel n M).IsThetaPSH θ b ∧
      SourceQuasiEverywhere (n := n) (fun y => b y ≤ f y)} => b.1 x)
      ⟨a.1, a.2.1, a.2.2.1⟩
  · apply iSup_le
    intro a
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ (fun _ => ⊤) f => b.1 x)
      ⟨a.1, a.2.1, a.2.2, sourceObstacle_topReference a.1⟩

/-- Whole original fine upper semicontinuity footnote: the actual QE-envelope
is the upper regularized supremum of all pointwise original competitors.
The proof identifies the whole families before applying upper regularization. -/
theorem sourceObstacleEnvelope_eq_pointwise_of_plurifine_upperSemicontinuous
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (f : M → EReal)
    (hf : @UpperSemicontinuous M EReal (ofFixedModel n M).plurifineTopology
      inferInstance f) :
    sourceRelativeEnvelope θ (fun _ => ⊤) f =
      uscSup (fun a : {a : M → EReal // (ofFixedModel n M).IsThetaPSH θ a ∧ a ≤ f} => a.1) := by
  rw [sourceObstacleEnvelope_eq_uscSup_qeCompetitors]
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup (fun b : {b : M → EReal // (ofFixedModel n M).IsThetaPSH θ b ∧ b ≤ f} => b.1 x)
      ⟨a.1, a.2.1,
        (sourceQuasiEverywhere_le_iff_of_plurifine_upperSemicontinuous a.2.1 hf).mp a.2.2⟩
  · apply iSup_le
    intro a
    exact le_iSup (fun b : {b : M → EReal // (ofFixedModel n M).IsThetaPSH θ b ∧
      SourceQuasiEverywhere (n := n) (fun y => b y ≤ f y)} => b.1 x)
      ⟨a.1, a.2.1, sourceQuasiEverywhere_of_forall a.2.2⟩

/-- The original ordinary-USC special case, with unchanged source functions,
background and regularization, retaining empty families and both infinities. -/
theorem sourceObstacleEnvelope_eq_pointwise_of_upperSemicontinuous
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (f : M → EReal)
    (hf : UpperSemicontinuous f) :
    sourceRelativeEnvelope θ (fun _ => ⊤) f =
      uscSup (fun a : {a : M → EReal // (ofFixedModel n M).IsThetaPSH θ a ∧ a ≤ f} => a.1) := by
  have hfFine : @UpperSemicontinuous M EReal (ofFixedModel n M).plurifineTopology
      inferInstance f := by
    intro x a ha
    exact (nhds_mono (a := x) (ofFixedModel n M).plurifine_le_euclidean) (hf x a ha)
  exact sourceObstacleEnvelope_eq_pointwise_of_plurifine_upperSemicontinuous θ f hfFine

end FixedDimension
end SGPT.PSH.VariableComplexAtlas
