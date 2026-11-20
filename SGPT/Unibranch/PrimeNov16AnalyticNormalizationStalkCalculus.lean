import SGPT.Unibranch.PrimeNov16AnalyticNormalizationPolynomialCalculus
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceLocalFunctions

/-! Whole original stalk dictionary and actual analytic calculus.
Blueprint: prime-nov16-analytic-normalization-stalk-calculus.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Polynomial
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open HolGerm GermAlgebraicParametrization
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalkCalculus

theorem wholeChart_vanishing_eq_translated {n : ℕ}
    (C : Set (ComplexModel n)) (p : ComplexModel n) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) C) p p (mem_chart_source (ComplexModel n) p) =
      AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p ∈ C} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hfC,rfl⟩
    change HolGerm.mk (fun z => f (z+p))
      (translated_holomorphic p (hf.mono fun _ h => h.differentiableAt)) ∈ _
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    have ht : Tendsto (fun z : ComplexModel n => z+p) (𝓝 0) (𝓝 p) := by
      simpa only [zero_add] using
        (show Continuous (fun z : ComplexModel n => z+p) from
          continuous_id.add continuous_const).tendsto (0 : ComplexModel n)
    exact ht.eventually hfC.2
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    have hv := AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg
    let F : ComplexModel n → ℂ := fun w => f (w-p)
    have hT : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (fun w : ComplexModel n => w-p) := contMDiff_id.sub contMDiff_const
    have hf' : HolomorphicAt n f ((fun w : ComplexModel n => w-p) p) := by
      simpa only [sub_self] using
        (show HolomorphicAt n f (0 : ComplexModel n) from hf.mono fun _ h => h.mdifferentiableAt)
    have hF : HolomorphicAt n F p := HolomorphicAt.comp_contMDiff
      (m := n) (n := n) (b := f) (f := fun w : ComplexModel n => w-p) (y := p)
        hf' (Eventually.of_forall fun w => hT w)
    have hFC : (vanishingIdeal (n := n) C).mem p F := by
      refine ⟨hF,?_⟩
      have ht : Tendsto (fun w : ComplexModel n => w-p) (𝓝 p) (𝓝 0) := by
        simpa only [sub_self] using
          (show Continuous (fun w : ComplexModel n => w-p) from
            continuous_id.sub continuous_const).tendsto p
      filter_upwards [ht.eventually hv] with w hw hwC
      exact hw (by simpa only [sub_add_cancel] using hwC)
    have he : chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p) F hF =
        HolGerm.mk f hf := by
      simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => by
        change f ((z+p)-p) = f z
        rw [add_sub_cancel_right]
    exact Ideal.subset_span ⟨F,hF,hFC,he.symm⟩

/-- Actual whole intrinsic stalk; no selected generators or desired comparison. -/
def translatedStalkEquiv {n : ℕ} (C : Set (ComplexModel n)) (p : C) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier ≃+*
      HolGerm (ComplexModel n) ⧸
        AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p.val ∈ C} :=
  (actualSubspaceStalkChartEquiv (n := n) C p).trans
    (Ideal.quotEquivOfEq (wholeChart_vanishing_eq_translated C p.val))

def stalkStructureMap {n : ℕ} (C : Set (ComplexModel n)) (p : C) (d : ℕ) :
    HolGerm (ComplexModel d) →+*
      ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier :=
  (translatedStalkEquiv C p).symm.toRingHom.comp
    (quotientStructureMap
      (AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p.val ∈ C}) d)

theorem stalkStructureMap_finite {d n : ℕ} (hdn : d ≤ n)
    (C : Set (ComplexModel n)) (p : C)
    (hmonic : ∀ k (hk : k < n), d ≤ k →
      ∃ P : (HolGerm (ComplexModel d))[X], P.Monic ∧
        evalGerm n P (coordGerm n k hk) ∈
          AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p.val ∈ C}) :
    (stalkStructureMap C p d).Finite := by
  exact (RingHom.Finite.of_surjective (translatedStalkEquiv C p).symm.toRingHom
    (translatedStalkEquiv C p).symm.surjective).comp
      (PrimeNov16AnalyticNormalizationFiniteCalculus.quotientStructureMap_finite_of_monic
        hdn _ hmonic)

theorem actual_stalk_polynomial_surjective {d n : ℕ} (hdn : d ≤ n)
    (C : Set (ComplexModel n)) (p : C)
    (hmonic : ∀ k (hk : k < n), d ≤ k →
      ∃ P : (HolGerm (ComplexModel d))[X], P.Monic ∧
        evalGerm n P (coordGerm n k hk) ∈
          AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p.val ∈ C}) :
    Function.Surjective (fun R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)) =>
      (translatedStalkEquiv C p).symm
        (Ideal.Quotient.mk
          (AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p.val ∈ C})
            (MvPolynomial.eval₂ (projGerm n d) coord R))) :=
  (translatedStalkEquiv C p).symm.surjective.comp
    (PrimeNov16AnalyticNormalizationPolynomialCalculus.polynomial_evaluation_surjective
      hdn _ hmonic)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalkCalculus
