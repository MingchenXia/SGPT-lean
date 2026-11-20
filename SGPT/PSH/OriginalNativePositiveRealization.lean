import SGPT.PSH.OriginalNativeComplexPositivity

/-! Positive original pure complex currents are exactly the genuine original
complexifications of positive native currents, with a unique entire LF model. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft SGPT.PSH.BookCurrent
open scoped Distributions
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (m : ℕ) (k : CurrentDegree n) (hk : k.val=2*m)

/-- The actual native current is mapped back to the same original compatible
real LF current and then genuinely complexified on every complex test. -/
def nativeCurrentComplexification (S : GlobalCurrent n M k) :
    OriginalComplexCurrent (ofFixedModel n M) (2*(n-m)) :=
  originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m))
    ((originalNativeRealCurrentEquiv k (testDegree_eq hk)).symm S) 0

/-- The forward current map is the proved bijection, including full degrees. -/
theorem nativeRealCurrentOfOriginal_eq_equiv
    (S : OriginalRealCurrent (ofFixedModel n M) (2*(n-m))) :
    nativeRealCurrentOfOriginal k (testDegree_eq hk) S=
      originalNativeRealCurrentEquiv k (testDegree_eq hk) S := rfl

/-- Literal source-global positivity of the genuine complexification is
precisely the actual existing BookCurrent predicate, without extra geometry. -/
theorem nativeCurrentComplexification_positive_iff (S : GlobalCurrent n M k) :
    OriginalSourceComplexPositive (ofFixedModel n M) (n-m)
      (nativeCurrentComplexification m k hk S) ↔ IsPositiveCurrent m hk S := by
  have h := source_complexification_positive_iff_native m k hk
    ((originalNativeRealCurrentEquiv k (testDegree_eq hk)).symm S)
  rw [nativeRealCurrentOfOriginal_eq_equiv m k hk,Equiv.apply_symm_apply] at h
  exact h

/-- Every original pure complex current is source positive exactly when it
has a UNIQUE positive native LF realization through the actual entire-test
complexification. Source realness is proved, never a hypothesis. -/
theorem source_pure_positive_iff_unique_native_realization
    (T : OriginalComplexCurrent (ofFixedModel n M) (2*(n-m)))
    (htype : OriginalComplexHasPureType (ofFixedModel n M) (n-m) T) :
    OriginalSourceComplexPositive (ofFixedModel n M) (n-m) T ↔
      ∃! S : GlobalCurrent n M k,IsPositiveCurrent m hk S ∧
        nativeCurrentComplexification m k hk S=T := by
  constructor
  · intro hT
    let R := originalCurrentRe (ofFixedModel n M) (2*(n-m)) T
    let E : OriginalRealCurrent (ofFixedModel n M) (2*(n-m)) ≃ GlobalCurrent n M k :=
      originalNativeRealCurrentEquiv k (testDegree_eq hk)
    have hext : originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m)) R 0=T :=
      original_source_positive_complex_real_extension (ofFixedModel n M) (n-m) T htype hT
    have hcomp : nativeCurrentComplexification m k hk (E R)=T := by
      dsimp only [nativeCurrentComplexification,E]
      rw [Equiv.symm_apply_apply]
      exact hext
    refine ⟨E R,⟨?_,hcomp⟩,?_⟩
    · apply (nativeCurrentComplexification_positive_iff m k hk (E R)).mp
      rwa [hcomp]
    · intro S hS
      apply E.symm.injective
      have h := congrArg (originalCurrentRe (ofFixedModel n M) (2*(n-m)))
        (hS.2.trans hext.symm)
      change originalCurrentRe (ofFixedModel n M) (2*(n-m))
        (originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m)) (E.symm S) 0)=
        originalCurrentRe (ofFixedModel n M) (2*(n-m))
          (originalExtendComplexCurrent (ofFixedModel n M) (2*(n-m)) R 0) at h
      rw [originalCurrentRe_extend,originalCurrentRe_extend] at h
      simpa only [Equiv.symm_apply_apply] using h
  · rintro ⟨S,hS,_⟩
    rw [← hS.2]
    exact (nativeCurrentComplexification_positive_iff m k hk S).mpr hS.1

end SGPT.PSH.ComplexCurrentBridge
