import SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalkCalculus
import SGPT.Foundations.Analysis.Pending.GermParametrizationData

/-! Native ordinary equations manufacture actual translated germ relations.
Blueprint: prime-nov16-analytic-normalization-native-monic.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Polynomial
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization GermParametrizationData RegularLocusDense
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationNativeMonic

theorem exists_monic_germ_of_native_equation {d n k : ℕ}
    (C : Set (ComplexModel n)) (p : ComplexModel n) (hk : k < n)
    (q : ℕ) (a : ℕ → ComplexModel d → ℂ)
    (ha : ∀ j,∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (a j) z)
    (heq : ∀ᶠ v in 𝓝 (0 : ComplexModel n),v+p ∈ C →
      monicEval q a (coordinateProjection n d v) (v ⟨k,hk⟩+p ⟨k,hk⟩) = 0) :
    ∃ P : (HolGerm (ComplexModel d))[X], P.Monic ∧
      evalGerm n P (coordGerm n k hk) ∈
        AnalyticGermDecomposition.vanishingIdeal {v : ComplexModel n | v+p ∈ C} := by
  let c : ℕ → HolGerm (ComplexModel d) := fun j => HolGerm.mk (a j) (ha j)
  let P₀ : (HolGerm (ComplexModel d))[X] := X^q+∑ j ∈ Finset.range q,Polynomial.C (c j)*X^j
  have hP₀ : P₀.Monic := (AnalyticProjectionWeierstrass.monic_X_pow_add_sum q c).1
  let centerValue := p ⟨k,hk⟩
  let P := P₀.comp (X+Polynomial.C (HolGerm.constHom centerValue))
  refine ⟨P,hP₀.comp (monic_X_add_C _) (by simp),?_⟩
  let y : ComplexModel n → ℂ := fun v => v ⟨k,hk⟩+centerValue
  have hy : ∀ᶠ v in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ y v :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (𝕜 := ℂ) (⟨k,hk⟩ : Fin n)).differentiableAt.add_const centerValue
  have hcoeff : ∀ j,∀ᶠ v in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun v => a j (coordinateProjection n d v)) v :=
    fun j => eventually_differentiableAt_comp_clm (coordinateProjection n d) (ha j)
  have hterm : ∀ j,∀ᶠ v in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun v => a j (coordinateProjection n d v)*y v^j) v :=
    fun j => eventually_differentiableAt_mul (hcoeff j) (eventually_differentiableAt_pow hy j)
  have hyG : coordGerm n k hk + HolGerm.constHom centerValue = HolGerm.mk y hy := by
    rw [← HolGerm.mk_const]
    exact (HolGerm.mk_add _ _ _ _).symm
  have hconst : projGerm n d (HolGerm.constHom centerValue) = HolGerm.constHom centerValue := rfl
  have hev : evalGerm n P (coordGerm n k hk) =
      HolGerm.mk (fun v => monicEval q a (coordinateProjection n d v) (y v))
        (eventually_differentiableAt_add (eventually_differentiableAt_pow hy q)
          (eventually_differentiableAt_sum (Finset.range q) hterm)) := by
    change Polynomial.eval₂ (projGerm n d) _ (P₀.comp _) = _
    rw [Polynomial.eval₂_comp]
    simp only [eval₂_add,eval₂_X,eval₂_C,hconst,hyG]
    simp only [P₀,eval₂_add,eval₂_pow,eval₂_X,eval₂_finsetSum,eval₂_mul,eval₂_C]
    symm
    change HolGerm.mk (fun v => y v^q + ∑ j ∈ Finset.range q,
      a j (coordinateProjection n d v)*y v^j) _ = _
    rw [HolGerm.mk_add _ _ (eventually_differentiableAt_pow hy q)
      (eventually_differentiableAt_sum (Finset.range q) hterm),HolGerm.mk_pow y hy q,
      HolGerm.mk_sum _ _ hterm]
    congr 1
  rw [hev]
  exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr heq

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationNativeMonic
