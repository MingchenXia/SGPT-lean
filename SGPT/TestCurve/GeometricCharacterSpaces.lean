import SGPT.TestCurve.TCLinVandermonde

/-! Actual pointwise character spaces are forced by genuine spanning eigenvectors. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.TestCurve.GeometricCharacterSpaces
open Set
open SGPT.TestCurve.TCLin

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A spanning family of actual character vectors is exactly the actual geometric eigenspaces. -/
theorem mem_iff_character (R : ℂˣ → Module.End ℂ M) (P : ℤ → Submodule ℂ M)
    (hspan : (⨆ lam, P lam) = ⊤)
    (hweight : ∀ lam, ∀ v ∈ P lam, ∀ c : ℂˣ, R c v = ((c ^ lam : ℂˣ) : ℂ) • v)
    (lam : ℤ) (v : M) : v ∈ P lam ↔ ∀ c : ℂˣ, R c v = ((c ^ lam : ℂˣ) : ℂ) • v := by
  classical
  constructor
  · exact fun hv => hweight lam v hv
  · intro hv
    have hmem : v ∈ ⨆ mu, P mu := by rw [hspan]; trivial
    obtain ⟨q, hq, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hmem
    let S := insert lam q.support
    obtain ⟨C, b, hb⟩ := exists_interpolation S lam
    have hproj : (∑ c ∈ C, b c • R c v) = v := by
      simp_rw [hv, smul_smul]
      rw [← Finset.sum_smul, hb lam (by simp [S])]
      simp
    have hRsum (c : ℂˣ) : R c v =
        ∑ mu ∈ q.support, ((c ^ mu : ℂˣ) : ℂ) • q mu := by
      rw [← hsum, Finsupp.sum, map_sum]
      exact Finset.sum_congr rfl fun mu _ => hweight mu (q mu) (hq mu) c
    have hcomponent : (∑ c ∈ C, b c • R c v) = q lam := by
      simp_rw [hRsum, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      calc
        _ = ∑ mu ∈ q.support, if mu = lam then q mu else 0 := by
          refine Finset.sum_congr rfl fun mu hmu => ?_
          rw [← Finset.sum_smul, hb mu (Finset.mem_insert_of_mem hmu)]
          split_ifs <;> simp
        _ = q lam := by
          by_cases hl : lam ∈ q.support
          · simp [hl]
          · simp [hl, Finsupp.notMem_support_iff.mp hl]
    have heq : v = q lam := hproj.symm.trans hcomponent
    rw [heq]
    exact hq lam

end SGPT.TestCurve.GeometricCharacterSpaces
