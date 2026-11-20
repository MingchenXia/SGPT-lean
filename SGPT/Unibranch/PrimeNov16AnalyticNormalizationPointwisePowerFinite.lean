import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedAlgebra

/-! Per-element powers become one whole-algebra power at each actual original stalk.
Blueprint: prime-nov16-analytic-normalization-pointwise-power-finite.tex. -/
set_option autoImplicit false
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationPointwisePowerFinite
open PrimeNov16AnalyticNormalizationReducedAlgebra

theorem exists_whole_power_of_elementwise {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (q : A)
    (he : ∀ b : B,∃ N : ℕ,∃ a : A,algebraMap A B (q^N)*b=algebraMap A B a) :
    ∃ N : ℕ,∀ b : B,∃ a : A,algebraMap A B (q^N)*b=algebraMap A B a := by
  classical
  obtain ⟨k,s,hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  choose m a ha using fun i : Fin k => he (s i)
  let N : ℕ := ∑ i,m i
  have hm (i : Fin k) : m i ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let S : Submodule A B := {
    carrier := fun b => ∃ a : A,algebraMap A B (q^N)*b=algebraMap A B a
    zero_mem' := ⟨0,by rw [mul_zero,map_zero]⟩
    add_mem' := by
      rintro b c ⟨a,ha⟩ ⟨d,hd⟩
      exact ⟨a+d,by rw [mul_add,ha,hd,map_add]⟩
    smul_mem' := by
      rintro a b ⟨c,hc⟩
      refine ⟨a*c,?_⟩
      rw [Algebra.smul_def]
      rw [map_mul,← mul_assoc,mul_comm (algebraMap A B (q^N)) (algebraMap A B a),mul_assoc,hc] }
  have hsS : Submodule.span A (Set.range s) ≤ S := by
    apply Submodule.span_le.mpr
    rintro b ⟨i,rfl⟩
    refine ⟨q^(N-m i)*a i,?_⟩
    calc
      algebraMap A B (q^N)*s i =
          algebraMap A B (q^(N-m i))*(algebraMap A B (q^(m i))*s i) := by
        rw [← mul_assoc,← map_mul,← pow_add,Nat.sub_add_cancel (hm i)]
      _ = algebraMap A B (q^(N-m i)*a i) := by rw [ha i,map_mul]
  rw [hs] at hsS
  exact ⟨N,fun b => hsS (show b ∈ (⊤ : Submodule A B) from trivial)⟩

theorem original_whole_branch_power_of_elementwise (X : SourceReducedComplexSpace)
    (x : X.obj.left) (q : (X.obj.left.presheaf.stalk x).carrier)
    (he : ∀ b : NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier,
      ∃ N : ℕ,∃ a : (X.obj.left.presheaf.stalk x).carrier,
        normalBranchMap (X.obj.left.presheaf.stalk x).carrier (q^N)*b =
          normalBranchMap (X.obj.left.presheaf.stalk x).carrier a) :
    ∃ N : ℕ,∀ b : NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier,
      ∃ a : (X.obj.left.presheaf.stalk x).carrier,
        normalBranchMap (X.obj.left.presheaf.stalk x).carrier (q^N)*b =
          normalBranchMap (X.obj.left.presheaf.stalk x).carrier a := by
  have := original_normal_branch_algebra_finite X x
  exact exists_whole_power_of_elementwise q he

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationPointwisePowerFinite
