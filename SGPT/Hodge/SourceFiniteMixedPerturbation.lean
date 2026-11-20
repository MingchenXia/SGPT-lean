import SGPT.Hodge.SourceMixedLinearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceMixedOrderDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup n X

/-- Exact real reading of the accepted original finite mixed intersection. -/
theorem nefIntersection_toReal_eq (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i)) :
    (nefIntersection D).toReal=nefIntersectionReal D :=
  ENNReal.toReal_ofReal (nefIntersectionReal_nonneg ω D hD)

theorem nefIntersectionReal_mono (ω : KahlerBackground n X)
    (D E : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (hE : ∀ i,IsNefAny (E i)) (hDE : ∀ i,LEAny (D i) (E i)) :
    nefIntersectionReal D≤nefIntersectionReal E := by
  have h := ENNReal.toReal_mono (nefIntersection_lt_top E).ne
    (source_nefIntersection_mono ω D E hD hE hDE)
  simpa only [nefIntersection_toReal_eq ω D hD,nefIntersection_toReal_eq ω E hE] using h

/-- Finite original slot telescoping. Bounds are consumed only in this algebra
helper; the whole compact-root theorem produces all of them internally. -/
theorem finite_mixed_perturbation_bound (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (C U : WeilFamilyAny Sys)
    (hD : ∀ i,IsNefAny (D i)) (hC : IsNefAny C) (hU : IsNefAny U)
    (ε : ℝ) (hε : 0≤ε) (hεC : IsNefAny (ε • C))
    (hplus : ∀ i,IsNefAny (D i+ε • C))
    (hDplus : ∀ i,LEAny (D i) (D i+ε • C))
    (hDU : ∀ i,LEAny (D i) U) (hCU : LEAny C U)
    (hplusU : ∀ i,LEAny (D i+ε • C) U) :
    0≤nefIntersectionReal (fun i => D i+ε • C)-nefIntersectionReal D ∧
      nefIntersectionReal (fun i => D i+ε • C)-nefIntersectionReal D≤
        (n : ℝ)*nefIntersectionReal (fun _ : Fin n => U)*ε := by
  classical
  let H (F : Finset (Fin n)) (i : Fin n) := if i∈F then D i+ε • C else D i
  let M := nefIntersectionReal (fun _ : Fin n => U)
  have hH (F) (i) : IsNefAny (H F i) := by
    dsimp only [H]
    split_ifs
    · exact hplus i
    · exact hD i
  have hHU (F) (i) : LEAny (H F i) U := by
    dsimp only [H]
    split_ifs
    · exact hplusU i
    · exact hDU i
  have hUupdate (F : Finset (Fin n)) (j : Fin n) :
      nefIntersectionReal (Function.update (H F) j C)≤M := by
    apply nefIntersectionReal_mono ω _ _
    · intro i
      by_cases hi : i=j
      · subst i; simpa using hC
      · simpa only [Function.update_of_ne hi] using hH F i
    · intro _; exact hU
    · intro i
      by_cases hi : i=j
      · subst i; simpa using hCU
      · simpa only [Function.update_of_ne hi] using hHU F i
  have hsum (F : Finset (Fin n)) :
      nefIntersectionReal (H F)-nefIntersectionReal D≤(F.card : ℝ)*M*ε := by
    induction F using Finset.induction_on with
    | empty =>
      have he : H ∅=D := by funext i; simp [H]
      rw [he]
      simp
    | @insert j F hj ih =>
      have hins : H (insert j F)=Function.update (H F) j (D j+ε • C) := by
        funext i
        by_cases hi : i=j
        · subst i; simp [H]
        · simp [H,hi]
      have hold : Function.update (H F) j (D j)=H F := by
        funext i
        by_cases hi : i=j
        · subst i; simp [H,hj]
        · simp [hi]
      have hadd := source_nefIntersectionReal_update_add ω (H F) (hH F) j (D j) (ε • C) (hD j) hεC
      have hsmul := source_nefIntersectionReal_update_smul ω (H F) (hH F) j C hC ε hε
      have hstep : nefIntersectionReal (H (insert j F))=
          nefIntersectionReal (H F)+ε*nefIntersectionReal (Function.update (H F) j C) := by
        rw [hins,hadd,hold,hsmul]
      rw [hstep]
      have hm := mul_le_mul_of_nonneg_left (hUupdate F j) hε
      have hc : ((insert j F).card : ℝ)=(F.card : ℝ)+1 := by
        rw [Finset.card_insert_of_notMem hj,Nat.cast_add,Nat.cast_one]
      rw [hc]
      nlinarith
  have hfull : H Finset.univ=(fun i => D i+ε • C) := by funext i; simp [H]
  refine ⟨sub_nonneg.mpr (nefIntersectionReal_mono ω D _ hD hplus hDplus),?_⟩
  have h := hsum Finset.univ
  simpa only [hfull,Finset.card_univ,Fintype.card_fin,M] using h

end SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
