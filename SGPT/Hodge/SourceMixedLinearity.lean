import SGPT.Hodge.SourceNefMixedAlgebra
import SGPT.Hodge.SourceNefMixedOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceIntersection

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup n X

theorem source_nefIntersectionReal_perm (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (σ : Equiv.Perm (Fin n)) : nefIntersectionReal (fun i => D (σ i))=nefIntersectionReal D := by
  cases n with
  | zero => simp only [nefIntersectionReal_zero]
  | succ m => exact nefIntersectionReal_perm_pos ω D hD σ

theorem source_nefIntersectionReal_update_add (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (j : Fin n) (U V : WeilFamilyAny Sys) (hU : IsNefAny U) (hV : IsNefAny V) :
    nefIntersectionReal (Function.update D j (U+V))=
      nefIntersectionReal (Function.update D j U)+nefIntersectionReal (Function.update D j V) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m => exact nefIntersectionReal_update_add_pos ω D hD j U V hU hV

theorem source_nefIntersectionReal_update_smul (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (j : Fin n) (U : WeilFamilyAny Sys) (hU : IsNefAny U) (c : ℝ) (hc : 0≤c) :
    nefIntersectionReal (Function.update D j (c • U))=
      c * nefIntersectionReal (Function.update D j U) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m => exact nefIntersectionReal_update_smul_pos ω D hD j U hU c hc

theorem source_nefIntersection_perm (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (σ : Equiv.Perm (Fin n)) : nefIntersection (fun i => D (σ i))=nefIntersection D := by
  unfold nefIntersection
  rw [source_nefIntersectionReal_perm ω D hD σ]

theorem source_nefIntersection_update_add (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (j : Fin n) (U V : WeilFamilyAny Sys) (hU : IsNefAny U) (hV : IsNefAny V) :
    nefIntersection (Function.update D j (U+V))=
      nefIntersection (Function.update D j U)+nefIntersection (Function.update D j V) := by
  have hp (W : WeilFamilyAny Sys) (hW : IsNefAny W) :
      ∀ i,IsNefAny (Function.update D j W i) := by
    classical
    intro i
    by_cases hij : i=j
    · subst i
      simpa only [Function.update_self] using hW
    · simpa only [Function.update_of_ne hij] using hD i
  unfold nefIntersection
  rw [source_nefIntersectionReal_update_add ω D hD j U V hU hV]
  exact ENNReal.ofReal_add
    (nefIntersectionReal_nonneg ω _ (hp U hU)) (nefIntersectionReal_nonneg ω _ (hp V hV))

/-- Actual homogeneity at scalar0 uses the proved all-nef extension of the
original big-nef reader; it does not assert that a zero family is big. -/
theorem source_nefIntersection_update_smul (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (j : Fin n) (U : WeilFamilyAny Sys) (hU : IsNefAny U) (c : ℝ) (hc : 0≤c) :
    nefIntersection (Function.update D j (c • U))=
      ENNReal.ofReal c * nefIntersection (Function.update D j U) := by
  unfold nefIntersection
  rw [source_nefIntersectionReal_update_smul ω D hD j U hU c hc]
  exact ENNReal.ofReal_mul hc

/-- Exact actual big-nef readback for EVERY original realizing choice,
so the all-nef statements specialize to the original def:DF_ext2 reader. -/
theorem source_DFlinear_bigNef_read (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    nefIntersection (fun i => (D i).val)=bigNefIntersection ω D :=
  nefIntersection_eq_bigNefIntersection ω D

/-- All FOUR clauses of the original mixed-intersection lemma, strengthened
to the actual complete nef domain. This covers original arbitrary big-nef
tuples via source_DFlinear_bigNef_read, with the scalar0 convention explicitly
read in the genuine all-nef extension. All n and original model families. -/
theorem source_DFlinear_whole (ω : KahlerBackground n X) :
    (∀ (D : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      ∀ σ : Equiv.Perm (Fin n),nefIntersection (fun i => D (σ i))=nefIntersection D) ∧
    (∀ (D : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      ∀ (j : Fin n) (U V : WeilFamilyAny Sys), IsNefAny U → IsNefAny V →
        nefIntersection (Function.update D j (U+V))=
          nefIntersection (Function.update D j U)+nefIntersection (Function.update D j V)) ∧
    (∀ (D : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      ∀ (j : Fin n) (U : WeilFamilyAny Sys), IsNefAny U → ∀ c : ℝ,0≤c →
        nefIntersection (Function.update D j (c • U))=
          ENNReal.ofReal c * nefIntersection (Function.update D j U)) ∧
    (∀ (D E : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      (∀ i,IsNefAny (E i)) → (∀ i,LEAny (D i) (E i)) → nefIntersection D≤nefIntersection E) :=
  ⟨source_nefIntersection_perm ω,source_nefIntersection_update_add ω,
    source_nefIntersection_update_smul ω,source_nefIntersection_mono ω⟩

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
