import SGPT.PSH.OriginalSourceGlobalLocalPositivity
import SGPT.PSH.OriginalNativeRealCurrentDictionary

/-! Literal source-global complex positivity and the actual native positive
current predicate, through genuine entire LF maps and realness producers. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests
open SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (m : ℕ) (k : CurrentDegree n) (hk : k.val=2*m)

/-- Actual real source currents have precisely the native positivity after
true complementary-degree transport and genuine complexification. -/
theorem source_complexification_positive_iff_native
    (S : OriginalRealCurrent (ofFixedModel n M) (2*(n-m))) :
    OriginalSourceComplexPositive (ofFixedModel n M) (n-m)
      (originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m)) S 0) ↔
      IsPositiveCurrent m hk (nativeRealCurrentOfOriginal k (testDegree_eq hk) S) := by
  rw [source_global_positive_iff_local]
  constructor
  · intro hS
    refine Or.inr ?_
    intro e beta hbeta phi hphi alpha halpha
    let a : TestForm (chartTarget e) (2*(n-m)) := castTestDegree (testDegree_eq hk).symm alpha
    have ha : ∀ z,a z=phi z • betaProduct (fun j => beta j z) := by
      intro z
      dsimp only [a]
      rw [castTestDegree_apply',halpha z,map_smul,castForm_castForm]
      rw [castForm_self]
    have h := (hS e beta hbeta phi hphi a ha).2
    have hread := congrArg (fun R : OriginalRealCurrent (ofFixedModel n M) (2*(n-m)) => R.val e a)
      (originalCurrentRe_extend (ofFixedModel n M) (2*(n-m)) S 0)
    change ((originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m)) S 0).val e
      (testOfRealCLM (chartTarget e) a)).re = S.val e a at hread
    have hnonneg : 0≤S.val e a := hread ▸ h
    rw [nativeRealCurrentOfOriginal_inChart]
    exact hnonneg
  · intro hS
    rcases hS with hbad|hS
    · have hb := k.isLt
      rw [hk,complexModel_real_finrank] at hb
      omega
    intro e beta hbeta phi hphi alpha halpha
    have ha : ∀ z,castTestDegree (testDegree_eq hk) alpha z=
        phi z • castForm (testDegree_eq hk) (betaProduct (fun j => beta j z)) := by
      intro z
      rw [castTestDegree_apply',halpha z,map_smul]
    have h := hS e beta hbeta phi hphi (castTestDegree (testDegree_eq hk) alpha) ha
    have hreadNative := nativeRealCurrentOfOriginal_inChart k (testDegree_eq hk) S e
      (castTestDegree (testDegree_eq hk) alpha)
    have hcast : 0≤S.val e (castTestDegree (testDegree_eq hk).symm
        (castTestDegree (testDegree_eq hk) alpha)) := hreadNative ▸ h
    have hcancel := congrArg (S.val e)
      (castTestDegree_castTestDegree (testDegree_eq hk) (testDegree_eq hk).symm alpha)
    have hnonneg : 0≤S.val e alpha := hcancel ▸ hcast
    have hRe := congrArg (fun R : OriginalRealCurrent (ofFixedModel n M) (2*(n-m)) => R.val e alpha)
      (originalCurrentRe_extend (ofFixedModel n M) (2*(n-m)) S 0)
    have hIm := congrArg (fun R : OriginalRealCurrent (ofFixedModel n M) (2*(n-m)) => R.val e alpha)
      (originalCurrentIm_extend (ofFixedModel n M) (2*(n-m)) S 0)
    change ((originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m)) S 0).val e
      (testOfRealCLM (originalCurrentTarget (ofFixedModel n M) e) alpha)).re = S.val e alpha at hRe
    exact ⟨hIm,hRe.symm ▸ hnonneg⟩

end SGPT.PSH.ComplexCurrentBridge
