import SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalk
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! Actual finite minimal-prime branch quotient algebra for EVERY original
reduced complex-space stalk. Not a normalization space or supplied branch data.
Blueprint: prime-nov16-analytic-normalization-branches.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranches

/-- Genuine original full stalk quotient proves Noetherianity, no domain input. -/
theorem original_stalk_noetherian (X : SourceReducedComplexSpace) (x : X.obj.left) :
    IsNoetherianRing (X.obj.left.presheaf.stalk x).carrier := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c,hcx⟩ := LocalEmbedding.mem_range_ofPoint X x
  change e.toPoint c = x at hcx
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let E := ((asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv).trans
    (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c)
  have : IsNoetherianRing (HolGerm (ComplexModel e.dim)) := isNoetherianRing_holGerm_euclidean e.dim
  have ht := isNoetherianRing_of_ringEquiv _ E.symm
  change IsNoetherianRing (X.obj.left.presheaf.stalk (e.toPoint c)).carrier at ht
  exact Eq.mp (congrArg (fun t : X.obj.left =>
    IsNoetherianRing (X.obj.left.presheaf.stalk t).carrier) hcx) ht

/-- Literal actual minimal-prime quotient product, with no chosen branch supplier. -/
abbrev BranchProduct (A : Type*) [CommRing A] := ∀ p : minimalPrimes A, A ⧸ p.val

def branchMap (A : Type*) [CommRing A] : A →+* BranchProduct A :=
  RingHom.pi fun p => Ideal.Quotient.mk p.val

theorem branch_isDomain (A : Type*) [CommRing A] (p : minimalPrimes A) :
    IsDomain (A ⧸ p.val) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr p.property.isPrime

theorem branchMap_injective (A : Type*) [CommRing A] [IsReduced A] :
    Function.Injective (branchMap A) := by
  intro a b hab
  have hmem : a-b ∈ sInf (minimalPrimes A) := by
    apply Submodule.mem_sInf.mpr
    intro p hp
    exact Ideal.Quotient.eq.mp (congrFun hab ⟨p,hp⟩)
  rw [Ideal.sInf_minimalPrimes,Ideal.radical_bot_of_isReduced] at hmem
  exact sub_eq_zero.mp hmem

theorem branch_product_finite (A : Type*) [CommRing A] [IsNoetherianRing A] :
    Module.Finite A (BranchProduct A) := by
  let := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  infer_instance

/-- EVERY original stalk, including multibranch singular points, has this actual
finite branch index. Not inferred from global irreducibility. -/
theorem original_minimal_primes_finite (X : SourceReducedComplexSpace) (x : X.obj.left) :
    (minimalPrimes (X.obj.left.presheaf.stalk x).carrier).Finite := by
  have := original_stalk_noetherian X x
  exact minimalPrimes.finite_of_isNoetherianRing _

theorem original_branchMap_injective (X : SourceReducedComplexSpace) (x : X.obj.left) :
    Function.Injective (branchMap (X.obj.left.presheaf.stalk x).carrier) := by
  have := X.isReduced_stalk x
  exact branchMap_injective _

theorem original_branch_product_finite (X : SourceReducedComplexSpace) (x : X.obj.left) :
    Module.Finite (X.obj.left.presheaf.stalk x).carrier
      (BranchProduct (X.obj.left.presheaf.stalk x).carrier) := by
  have := original_stalk_noetherian X x
  exact branch_product_finite _

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranches
