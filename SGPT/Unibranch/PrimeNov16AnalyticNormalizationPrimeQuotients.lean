import SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranches

/-! EVERY actual original prime stalk quotient has finite canonical closure.
All germ maps are produced from actual original sheaf/embedding maps.
Blueprint: prime-nov16-analytic-normalization-prime-quotients.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationPrimeQuotients

/-- The original space itself produces the actual germ-ring surjection onto
its SAME intrinsic structure-sheaf stalk. No presentation supplier is input. -/
theorem exists_original_stalk_germ_surjection (X : SourceReducedComplexSpace) (x : X.obj.left) :
    ∃ n : ℕ, ∃ f : HolGerm (ComplexModel n) →+* (X.obj.left.presheaf.stalk x).carrier,
      Function.Surjective f := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c,hcx⟩ := LocalEmbedding.mem_range_ofPoint X x
  change e.toPoint c = x at hcx
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let E := ((asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv).trans
    (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c)
  let I := wholeChartStalkIdeal (vanishingIdeal (n := e.dim) e.carrier) c.val c.val
    (mem_chart_source (ComplexModel e.dim) c.val)
  have H : ∃ n : ℕ,
      ∃ f : HolGerm (ComplexModel n) →+* (X.obj.left.presheaf.stalk (e.toPoint c)).carrier,
        Function.Surjective f := by
    refine ⟨e.dim,E.symm.toRingHom.comp (Ideal.Quotient.mk I),?_⟩
    exact E.symm.surjective.comp Ideal.Quotient.mk_surjective
  exact Eq.mp (congrArg (fun t : X.obj.left => ∃ n : ℕ,
    ∃ f : HolGerm (ComplexModel n) →+* (X.obj.left.presheaf.stalk t).carrier,
      Function.Surjective f) hcx) H

/-- An actual analytic domain quotient, not a finite-type polynomial algebra. -/
theorem finite_closure_of_germ_surjection {n : ℕ} {A : Type*} [CommRing A] [IsDomain A]
    (f : HolGerm (ComplexModel n) →+* A) (hf : Function.Surjective f) :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have := PrimeNov16AnalyticIntegralClosure.finite_analytic_germ_integralClosure (RingHom.ker f)
  exact PrimeNov16AnalyticNormalizationStalk.finite_closure_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective hf)

/-- Every actual prime branch of an arbitrary original reduced stalk, including
multibranch singular points, internally has finite canonical integral closure. -/
theorem finite_original_prime_quotient_closure (X : SourceReducedComplexSpace)
    (x : X.obj.left) (p : Ideal (X.obj.left.presheaf.stalk x).carrier) [p.IsPrime] :
    Module.Finite ((X.obj.left.presheaf.stalk x).carrier ⧸ p)
      (integralClosure ((X.obj.left.presheaf.stalk x).carrier ⧸ p)
        (FractionRing ((X.obj.left.presheaf.stalk x).carrier ⧸ p))) := by
  obtain ⟨n,f,hf⟩ := exists_original_stalk_germ_surjection X x
  exact finite_closure_of_germ_surjection ((Ideal.Quotient.mk p).comp f)
    (Ideal.Quotient.mk_surjective.comp hf)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationPrimeQuotients
