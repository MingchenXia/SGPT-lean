import SGPT.Okounkov.ResolvedNextFlagRestriction
import SGPT.Okounkov.FlagLiftingTail
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

def univCarrierHomeomorph (X : Type u) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x, mem_univ x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem contMDiff_univCarrierHomeomorph
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (hU : ∀ x ∈ (univ : Set X), RegularAtDim (n := n) univ x n) :
    letI := SubmanifoldChartedSpace.chartedSpace le_rfl hU
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (univCarrierHomeomorph X) :=
  SubmanifoldChartedSpace.contMDiff_val le_rfl hU

theorem contMDiff_univCarrierHomeomorph_symm
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (hU : ∀ x ∈ (univ : Set X), RegularAtDim (n := n) univ x n) :
    letI := SubmanifoldChartedSpace.chartedSpace le_rfl hU
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (univCarrierHomeomorph X).symm :=
  SubmanifoldCodRestrict.contMDiff_codRestrict le_rfl hU contMDiff_id (fun x => mem_univ x)

theorem isAnalyticModification_of_finiteBlowupSequence
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {p : Y → X} (hp : IsBlowupSequence n X Y p) : IsAnalyticModification (n := n) p := by
  induction hp with
  | refl => exact isAnalyticModification_identity
  | step p C b _ hb ih =>
      exact AnalyticModificationComposition.isAnalyticModification_comp ih
        (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hb)

theorem isBlowupSequence_comp_nativeFlag
    {n : ℕ} {X Y Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {p : Y → X} {q : Z → Y} (hp : IsBlowupSequence n X Y p)
    (hq : IsBlowupSequence n Y Z q) : IsBlowupSequence n X Z (p ∘ q) := by
  induction hq with
  | refl => exact hp
  | step q C b _ hb ih => exact IsBlowupSequence.step (p ∘ q) C b ih hb

theorem connectedSpace_source_of_isAnalyticModification
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ConnectedSpace X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {p : Y → X} (hp : IsAnalyticModification (n := n) p) : ConnectedSpace Y := by
  have h := AnalyticModificationConnectedFibres.isConnected_preimage_of_isConnected hp
    (⟨univ, isOpen_univ⟩ : TopologicalSpace.Opens X) isConnected_univ
  change IsConnected (p ⁻¹' (univ : Set X)) at h
  rw [preimage_univ] at h
  exact connectedSpace_iff_univ.mpr h

theorem isAnalyticModification_wholeCarrierRestriction
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] {p : Y → X} (hp : IsAnalyticModification (n := n) p)
    (hX : ∀ x ∈ (univ : Set X), RegularAtDim (n := n) univ x n)
    (hY : ∀ y ∈ (univ : Set Y), RegularAtDim (n := n) univ y n) :
    letI := SubmanifoldChartedSpace.chartedSpace le_rfl hX
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hX
    letI := SubmanifoldChartedSpace.chartedSpace le_rfl hY
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hY
    IsAnalyticModification (n := n)
      (fun y : (univ : Set Y) => (⟨p y.1, mem_univ _⟩ : (univ : Set X))) := by
  let := SubmanifoldChartedSpace.chartedSpace le_rfl hX
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hX
  let := SubmanifoldChartedSpace.chartedSpace le_rfl hY
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hY
  let : CompactSpace (univ : Set Y) := isCompact_iff_compactSpace.mp isCompact_univ
  exact isAnalyticModification_biholomorphic_transport
    (univCarrierHomeomorph X) (univCarrierHomeomorph Y)
    (contMDiff_univCarrierHomeomorph hX) (contMDiff_univCarrierHomeomorph_symm hX)
    (contMDiff_univCarrierHomeomorph hY) (contMDiff_univCarrierHomeomorph_symm hY) hp

theorem isAnalyticModification_wholeSetRestriction
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] {p : Y → X} (hp : IsAnalyticModification (n := n) p)
    {U : Set X} {V : Set Y} (hU : U = univ) (hV : V = univ)
    (hX : ∀ x ∈ U, RegularAtDim (n := n) U x n)
    (hY : ∀ y ∈ V, RegularAtDim (n := n) V y n) :
    ∃ hi : MapsTo p V U,
      letI := SubmanifoldChartedSpace.chartedSpace le_rfl hX
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hX
      letI := SubmanifoldChartedSpace.chartedSpace le_rfl hY
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hY
      IsAnalyticModification (n := n) (fun y : V => (⟨p y.1, hi y.2⟩ : U)) := by
  subst U
  subst V
  exact ⟨fun _ _ => mem_univ _, isAnalyticModification_wholeCarrierRestriction hp hX hY⟩

/-- The actual original first flag divisor is resolved internally, and the
literal original projection has a genuine analytic-modification restriction. -/
theorem exists_resolvedFirstFlagMember
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] [CompactSpace Z]
    (omegaZ : KahlerBackground (m + 1) Z) (pi : Z → F.carrier)
    (hpi : IsAnalyticModification (n := m + 1) pi) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (_ : CompactSpace Y) (_ : KahlerBackground (m + 1) Y)
      (p : Y → Z), IsBlowupSequence (m + 1) Z Y p ∧
      ∃ (D : Set Y) (hD : IsClosedConnectedSubmanifold (m + 1) D m),
        ∃ hi : ∀ y ∈ D, pi (p y) ∈ F.flag (1 : Fin (m + 2)),
          letI : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
          letI : IsComplexManifold m (F.flag (1 : Fin (m + 2))) := F.tail.complex
          letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hD.2.2
          letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hD.2.2
          IsAnalyticModification (n := m)
            (fun y : D => (⟨pi (p y.1), hi y.1 y.2⟩ : F.tail.carrier)) := by
  classical
  let hU : ∀ z ∈ (univ : Set Z), RegularAtDim (n := m + 1) univ z (m + 1) :=
    fun z _ => AnalyticIrreducibleComponents.regularAtDim_univ z
  let := SubmanifoldChartedSpace.chartedSpace le_rfl hU
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace le_rfl hU
  let : CompactSpace (univ : Set Z) := isCompact_iff_compactSpace.mp isCompact_univ
  have hval : IsAnalyticModification (n := m + 1) (Subtype.val : ↥(univ : Set Z) → Z) :=
    isAnalyticModification_biholomorphic_transport
      (Homeomorph.refl Z) (univCarrierHomeomorph Z) contMDiff_id contMDiff_id
      (contMDiff_univCarrierHomeomorph hU) (contMDiff_univCarrierHomeomorph_symm hU)
      isAnalyticModification_identity
  have hg := AnalyticModificationComposition.isAnalyticModification_comp hpi hval
  obtain ⟨x, hx⟩ := F.firstDivisor.2.1.nonempty
  let H : ClosedIrreducibleAnalyticSubvariety (m + 1) F.carrier := {
    carrier := F.flag (1 : Fin (m + 2))
    isClosed_carrier := F.firstDivisor.1
    irreducible_carrier :=
      SourceGenericSubmanifoldMinimum.isComplexAnalyticallyIrreducible_of_submanifold F.firstDivisor
    dim := m
    dim_le := Nat.le_succ m
    regularLocus_nonempty := ⟨x, F.firstDivisor.2.2 x hx⟩ }
  obtain ⟨V, _hV, _hdim, Nt, _topNt, _chartsNt, _complexNt, q, _hq, _hres,
    Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS,
    hp, _hSc, _hSstrict, _hA', _hMods, e, f, _he, _hf, _hfe, _hef, _hcomm,
    D, hD, _hDeq, _hpD, _hDS, _hPN, hi, hmod⟩ :=
    exists_ambientAncestorTower_resolving_nextFlagMember omegaZ le_rfl isClosed_univ hU
      (fun i : Empty => nomatch i) (fun i : Empty => nomatch i)
      (fun i => nomatch i) (fun i => nomatch i) (fun i => nomatch i) (fun i => nomatch i)
      (pi ∘ Subtype.val) hg H F.firstDivisor rfl
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  exact ⟨Y, topY, chartsY, complexY, compactY, omegaY, p, hp, D, hD,
    fun y hy => hi ⟨y, hy⟩, hmod⟩

end SGPT.Okounkov
