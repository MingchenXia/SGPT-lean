import SGPT.Hodge.SourceCartierRealizationNef

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]

/-- The arbitrary-model class conclusion in every natural dimension, with
dimension zero using the actual vanishing Bott--Chern class. -/
theorem source_nefbCequiv_every_realization (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D)
    (π : (ModelSystem.blowup n X).Model) (α : RealBottChern n π.1.carrier)
    (hr : IsRealizationAny D π α) (κ : KahlerBackground n π.1.carrier) :
    ClassNefWithRespectTo κ α := by
  cases n with
  | zero => exact classNefWithRespectTo_of_dim_zero κ α
  | succ m => exact classNef_of_nef_cartier_realization ω D hD π α hr κ

/-- WHOLE original cor:nefbCequiv, chapter_bdiv502--504, including all natural
dimensions. The input is precisely an actual Cartier realization, and nefness
is precisely the original directed-net predicate. All realization classes,
currents, regularizations and point-blowup consequences are proved internally. -/
theorem source_nefbCequiv_whole (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X))
    (hCartier : ∃ π α,IsRealizationAny D π α) :
    IsNefAny D ↔ IsNefCartierAny D := by
  constructor
  · intro hD
    obtain ⟨π,α,hr⟩ := hCartier
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    exact ⟨π,α,hr,κ,source_nefbCequiv_every_realization ω D hD π α hr κ⟩
  · exact isNefAny_of_isNefCartierAny

/-- The original positive-dimensional book objects and the original source
Cartier/net-nef/nef-Cartier predicates, without a replacement object domain. -/
theorem source_nefbCequiv_existing {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]
    [CompactSpace Y] [ConnectedSpace Y] (ω : KahlerBackground (m+1) Y)
    (D : WeilBDivisorOn (ModelSystem.blowup (m+1) Y) (Nat.succ_pos m))
    (hCartier : D.IsCartier) : D.IsNef ↔ D.IsNefCartier := by
  let F := fromExisting (ModelSystem.blowup (m+1) Y) (Nat.succ_pos m) D
  have hF : ∃ π α,IsRealizationAny F π α := by
    obtain ⟨π,α,hr⟩ := hCartier
    exact ⟨π,α,hr⟩
  have h := source_nefbCequiv_whole ω F hF
  rw [isNefAny_iff_existing (Nat.succ_pos m),
    isNefCartierAny_iff_existing (Nat.succ_pos m),toExisting_fromExisting] at h
  exact h

end SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
