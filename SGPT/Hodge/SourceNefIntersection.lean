import SGPT.Hodge.SourceNefIntersectionPerturbation
import Mathlib.Topology.Order.AtTopBotIxx

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]
local notation "Sys" => ModelSystem.blowup n X

/-- The exact original one-sided positive REAL parameter filter. -/
theorem source_positiveParameter_filter :
    Filter.map (fun ε : Ioi (0 : ℝ) => ε.val) atBot=𝓝[>] (0 : ℝ) :=
  map_coe_Ioi_atBot 0

theorem source_positiveParameter_tendsto :
    Tendsto (fun ε : Ioi (0 : ℝ) => ε.val) atBot (𝓝 (0 : ℝ)) := by
  apply le_trans (show Filter.map (fun ε : Ioi (0 : ℝ) => ε.val) atBot≤𝓝[>] (0 : ℝ) by
    rw [source_positiveParameter_filter])
  exact nhdsWithin_le_nhds

/-- The finite ENNReal reading of the proved nonnegative real intersection. -/
def nefIntersection (D : Fin n → WeilFamilyAny Sys) : ENNReal :=
  ENNReal.ofReal (nefIntersectionReal D)

theorem nefIntersection_lt_top (D : Fin n → WeilFamilyAny Sys) : nefIntersection D<⊤ :=
  ENNReal.ofReal_lt_top

variable [MeasurableSpace X] [BorelSpace X]

/-- The new all-nef reading extends EXACTLY the existing original big-nef
definition, not merely a chosen current presentation or an ordinary mass. -/
theorem nefIntersection_eq_bigNefIntersection (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    nefIntersection (fun i => (D i).val)=bigNefIntersection ω D := by
  rw [nefIntersection,←bigNefIntersection_eq_nefIntersectionReal ω D]
  exact ENNReal.ofReal_toReal (bigNefIntersection_lt_top ω D).ne

/-- Exact ORIGINAL def:DF_ext limit: every actual Kähler form, every nef
family tuple, all n and the literal positive-real parameter approaching0. -/
theorem source_DFext_limit (ω κ : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i)) :
    Tendsto (fun ε : Ioi (0 : ℝ) => bigNefIntersection ω
      (fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) ε.val ε.property))
      atBot (𝓝 (nefIntersection D)) := by
  have ht := nefIntersectionReal_add_smul_tendsto ω D hD
    (rootCartierAny (RealBottChern.ofRepresentative κ.form))
    (rootKahler_pseudoeffective κ) (fun ε : Ioi (0 : ℝ) => ε.val)
    (fun ε => ε.property.le) source_positiveParameter_tendsto
  have he (ε : Ioi (0 : ℝ)) : ENNReal.ofReal (nefIntersectionReal
      (fun i => D i+ε.val • rootCartierAny (RealBottChern.ofRepresentative κ.form)))=
      bigNefIntersection ω (fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) ε.val ε.property) := by
    exact nefIntersection_eq_bigNefIntersection ω
      (fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) ε.val ε.property)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  exact h.congr' (Eventually.of_forall he)

/-- The WHOLE source definition: a unique finite nonnegative value, every
original Kähler reference, the genuine one-sided limit and decreasing
perturbation values. No reader/positivity/limit certificate is an input. -/
theorem source_DFext_whole (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i)) :
    ∃! I : ENNReal,I<⊤ ∧
      ∀ κ : KahlerBackground n X,
        Tendsto (fun ε : Ioi (0 : ℝ) => bigNefIntersection ω
          (fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) ε.val ε.property)) atBot (𝓝 I) ∧
        Monotone (fun ε : Ioi (0 : ℝ) => bigNefIntersection ω
          (fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) ε.val ε.property)) := by
  refine ⟨nefIntersection D,⟨nefIntersection_lt_top D,fun κ =>
    ⟨source_DFext_limit ω κ D hD,bigNefIntersection_kahlerPerturbation_monotone ω κ D hD⟩⟩,?_⟩
  intro I hI
  exact tendsto_nhds_unique (hI.2 ω).1 (source_DFext_limit ω ω D hD)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Limits of arbitrary original nef nets are themselves in the original
nef domain, produced by its actual closed-cone theorem. -/
theorem isNefAny_of_converges {J : Type*} [Preorder J] [IsDirected J (·≤·)] [Nonempty J]
    (D : J → WeilFamilyAny Sys) (E : WeilFamilyAny Sys)
    (hD : ∀ j,IsNefAny (D j)) (hc : ConvergesAny atTop D E) : IsNefAny E := by
  cases n with
  | zero => exact isNefAny_zero E
  | succ m =>
    apply (isNefAny_iff_existing (Nat.succ_pos m) E).mpr
    exact WeilBDivisorOn.IsNef.of_converges
      (fun j => (isNefAny_iff_existing (Nat.succ_pos m) (D j)).mp (hD j))
      ((convergesAny_iff_existing (Nat.succ_pos m) atTop D E).mp hc)

omit [MeasurableSpace X] [BorelSpace X] in
/-- WHOLE original prop:DFdecnet: every decreasing directed net, arbitrary
original nef tuples and the exact original modelwise topology, all n. -/
theorem source_DFdecnet (ω : KahlerBackground n X)
    {J : Type*} [Preorder J] [IsDirected J (·≤·)] [Nonempty J]
    (D : Fin n → J → WeilFamilyAny Sys) (E : Fin n → WeilFamilyAny Sys)
    (hD : ∀ i j,IsNefAny (D i j))
    (ha : ∀ i j k,j≤k → LEAny (D i k) (D i j))
    (hc : ∀ i,ConvergesAny atTop (D i) (E i)) :
    (∀ i,IsNefAny (E i)) ∧
      Tendsto (fun j => nefIntersection (fun i => D i j)) atTop (𝓝 (nefIntersection E)) := by
  refine ⟨fun i => isNefAny_of_converges (D i) (E i) (hD i) (hc i),?_⟩
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (nefIntersectionReal_tendsto_of_antitone ω D E hD ha hc)

/-- The existing big-nef intersection diagonal is the independent ORIGINAL
pure family volume, via actual whole-current DT. -/
theorem bigNefIntersection_diagonal (ω : KahlerBackground n X)
    (D : BigNefFamily (n := n) (X := X)) :
    bigNefIntersection ω (fun _ : Fin n => D)=volumeAny D.val := by
  have hd : bigNefIntersection ω (fun _ : Fin n => D)=
      currentIVolumeAny (realizingCurrent ω D).val :=
    sourceGeneralMixedIVolume_diagonal ω (presentationPSH (realizingCurrent ω D).val)
  rw [hd,currentIVolumeAny_eq_bdivisorVolume ω,realizingCurrent_family]

/-- WHOLE original prop:bdiv:L678: every nef family's diagonal intersection
is its independently defined original volume, including the actual n0 value1. -/
theorem source_nefIntersection_diagonal (ω : KahlerBackground n X)
    (D : WeilFamilyAny Sys) (hD : IsNefAny D) :
    nefIntersection (fun _ : Fin n => D)=volumeAny D := by
  have hm := source_DFext_limit ω ω (fun _ : Fin n => D) (fun _ => hD)
  have hv := volumeAny_add_smul_tendsto ω D
    (rootCartierAny (RealBottChern.ofRepresentative ω.form))
    (isPseudoeffectiveAny_of_isNef ω D hD) (rootKahler_pseudoeffective ω)
    (fun ε : Ioi (0 : ℝ) => ε.val) (fun ε => ε.property.le) source_positiveParameter_tendsto
  have he (ε : Ioi (0 : ℝ)) : bigNefIntersection ω
      (fun _ : Fin n => kahlerPerturbedBigNef ω ω D hD ε.val ε.property)=
      volumeAny (D+ε.val • rootCartierAny (RealBottChern.ofRepresentative ω.form)) :=
    bigNefIntersection_diagonal ω _
  exact tendsto_nhds_unique (hm.congr' (Eventually.of_forall he)) hv

theorem source_nefIntersection_dim_zero {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (D : Fin 0 → WeilFamilyAny (ModelSystem.blowup 0 Y)) : nefIntersection D=1 := by
  rw [nefIntersection,nefIntersectionReal_zero]
  norm_num

end SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
