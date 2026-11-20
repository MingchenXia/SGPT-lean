import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDenominatorIdentities
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationTranslatedCanonicalReadback

/-! Full canonical normal algebra readback on EVERY actual central graph stalk.
Blueprint: prime-nov16-analytic-normalization-central-canonical-stalk.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization RegularLocusDense
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralCanonicalStalk
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationGraphOriginalStalk
open PrimeNov16AnalyticNormalizationGraphStalkCoordinates
open PrimeNov16AnalyticNormalizationCentralStalkInjective
open PrimeNov16AnalyticNormalizationGraphStalkFunctions
open PrimeNov16AnalyticNormalizationGraphDenominatorIdentities

theorem exists_actual_central_canonical_equiv {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (hH0 : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ H x)
    (hG0 : ∀ i,∀ᶠ x in 𝓝 0,DifferentiableAt ℂ (G i) x)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : {x : U | x.val ∈ Z},H x.val.val ≠ 0 → ∀ i,
      GermParametrizationData.monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    (h : HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)
    (hh : h ≠ 0)
    (s : Fin k → integralClosure (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)
      (FractionRing (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)))
    (hs : Submodule.span (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z) (range s) = ⊤)
    (hHclass : Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal Z) (HolGerm.mk H hH0) = h)
    (hden : ∀ i,algebraMap _ (FractionRing (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)) h *
      (s i : FractionRing (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)) =
      algebraMap _ _ (Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal Z) (HolGerm.mk (G i) (hG0 i)))) :
    ∃ e : ((actualSubspaceSheaf (n := n+k) (graphClosure U {x : U | x.val ∈ Z} H G)).presheaf.stalk p).carrier ≃+*
        integralClosure (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)
          (FractionRing (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z)),
      ∀ b,e (centralBaseMap hZ U hC H G hH hG p hp b) = algebraMap _ _ b := by
  let : (AnalyticGermDecomposition.vanishingIdeal Z).IsPrime :=
    (AnalyticGermDecomposition.isIrreducibleGerm_iff_isPrime hZ.1).mp hZ
  let A := HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z
  let R := ((actualSubspaceSheaf (n := n+k) (graphClosure U {x : U | x.val ∈ Z} H G)).presheaf.stalk p).carrier
  let q : HolGerm (ComplexModel n) →+* A := Ideal.Quotient.mk _
  let f : A →+* R := centralBaseMap hZ U hC H G hH hG p hp
  let := f.toAlgebra
  have hf : Function.Injective (algebraMap A R) := centralBaseMap_injective hZ U hC H G hH hG p hp
  have hfin : (algebraMap A R).Finite := centralBaseMap_finite hZ U hC H G hH hG p hp d a ha hmonic
  let : Module.Finite A R := RingHom.finite_algebraMap.mp hfin
  let c : Fin k → A := fun i => q (HolGerm.constHom (p.val.val (Fin.natAdd n i)))
  let b : Fin n → A := fun i => q (coord i)
  let g : Fin k → A := fun i => q (HolGerm.mk (G i) (hG0 i))
  let x : Fin (n+k) → R := graphCoordinate U {x : U | x.val ∈ Z} H G p
  have hHmap : algebraMap A R h = graphStalkStructureMap U {x : U | x.val ∈ Z} H G p (HolGerm.mk H hH0) := by
    rw [← hHclass]
    rfl
  have hbase : ∀ j,algebraMap A R (b j) = x (Fin.castAdd k j) := by
    intro j
    change graphStalkStructureMap U {x : U | x.val ∈ Z} H G p (coord j) = _
    rw [← graphGermMap_base_square,projGerm_coordGerm j.isLt (Nat.le_add_right n k)]
    rfl
  have htail : ∀ j,algebraMap A R h*(x (Fin.natAdd n j)+algebraMap A R (c j)) = algebraMap A R (g j) := by
    intro j
    have he := graph_fibre_denominator_identity U hC H G hH hG hH0 hG0 p hp j
    rw [← hHmap] at he
    exact he
  have hreg : algebraMap A R h ∈ nonZeroDivisors R := by
    rw [hHmap]
    exact graph_denominator_regular U _ H G hH p hp hH0
  exact PrimeNov16AnalyticNormalizationTranslatedCanonicalReadback.exists_translated_canonical_equiv
    (n := n) (k := k) hf h hh x b g c hbase htail
    (central_graph_polynomial_surjective hZ U hC H G hH hG p hp d a ha hmonic) hreg s hs hden

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralCanonicalStalk
