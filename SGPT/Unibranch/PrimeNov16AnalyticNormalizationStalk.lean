import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGenerators
import SGPT.Unibranch.ComplexSpaceUnibranchGerm

/-! Canonical finite normal algebra on the SAME original structure-sheaf domain
stalk, internally using genuine original analytic quotient/stalk equivalences.
Multibranch reduced stalks remain outside this local domain-stalk theorem.
Blueprint: prime-nov16-analytic-normalization-stalk.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalk
open PrimeNov16AnalyticNormalizationTransitions

/-- Canonical coefficient squares give finite-map transport by actual ring
composition. No normalization equivalence is a caller input. -/
theorem finite_closure_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) [Module.Finite A (integralClosure A (FractionRing A))] :
    Module.Finite B (integralClosure B (FractionRing B)) := by
  have hfin : (algebraMap A (integralClosure A (FractionRing A))).Finite := by
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hf := ((RingHom.Finite.of_surjective (closureEquiv e).toRingHom
    (closureEquiv e).surjective).comp hfin).comp
    (RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective)
  have heq : ((closureEquiv e).toRingHom.comp
      (algebraMap A (integralClosure A (FractionRing A)))).comp e.symm.toRingHom =
      algebraMap B (integralClosure B (FractionRing B)) := by
    apply RingHom.ext
    intro b
    change closureEquiv e (algebraMap A _ (e.symm b)) = _
    rw [closureEquiv_algebraMap,e.apply_symm_apply]
  rw [heq] at hf
  exact RingHom.finite_algebraMap.mp hf

/-- Actual ORIGINAL stalk, no supplied chart/normalization/finite-map supplier.
Domain is an explicit local branch scope, not inferred from global irreducibility. -/
theorem finite_original_domain_stalk_closure (X : SourceReducedComplexSpace)
    (x : X.obj.left) [IsDomain (X.obj.left.presheaf.stalk x).carrier] :
    Module.Finite (X.obj.left.presheaf.stalk x).carrier
      (integralClosure (X.obj.left.presheaf.stalk x).carrier
        (FractionRing (X.obj.left.presheaf.stalk x).carrier)) := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c,hcx⟩ := LocalEmbedding.mem_range_ofPoint X x
  change e.toPoint c = x at hcx
  have : IsDomain (X.obj.left.presheaf.stalk (e.map.base c)).carrier := by
    change IsDomain (X.obj.left.presheaf.stalk (e.toPoint c)).carrier
    rw [hcx]
    infer_instance
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let E := ((asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv).trans
    (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c)
  let I := wholeChartStalkIdeal (vanishingIdeal (n := e.dim) e.carrier) c.val c.val
    (mem_chart_source (ComplexModel e.dim) c.val)
  have : IsDomain (HolGerm (ComplexModel e.dim) ⧸ I) :=
    Function.Injective.isDomain E.symm E.symm.injective
  have : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have := PrimeNov16AnalyticIntegralClosure.finite_analytic_germ_integralClosure I
  have ht := finite_closure_of_ringEquiv E.symm
  change Module.Finite (X.obj.left.presheaf.stalk (e.toPoint c)).carrier
    (integralClosure (X.obj.left.presheaf.stalk (e.toPoint c)).carrier
      (FractionRing (X.obj.left.presheaf.stalk (e.toPoint c)).carrier)) at ht
  exact Eq.mp (congrArg (fun t : X.obj.left =>
    Module.Finite (X.obj.left.presheaf.stalk t).carrier
      (integralClosure (X.obj.left.presheaf.stalk t).carrier
        (FractionRing (X.obj.left.presheaf.stalk t).carrier))) hcx) ht

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalk
