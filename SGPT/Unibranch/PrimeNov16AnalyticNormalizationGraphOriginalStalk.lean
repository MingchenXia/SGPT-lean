import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkFinite
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction

/-! SAME actual original graph stalks, without a supplied comparison.
Blueprint: prime-nov16-analytic-normalization-graph-original-stalk.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphOriginalStalk
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationStalkCalculus

theorem nativeCarrier_preimage {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) :
    (Subtype.val : wideDomain k U → ComplexModel (n+k)) ⁻¹' nativeCarrier U C H G =
      graphClosure U C H G := by
  ext z
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Subtype.ext he : w=z) ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

def stalkEquiv_of_carrier_eq {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    (S T : Set M) (h : S=T) (p : S) :
    ((actualSubspaceSheaf (n := m) S).presheaf.stalk p).carrier ≃+*
      ((actualSubspaceSheaf (n := m) T).presheaf.stalk
        (⟨p.val,h ▸ p.property⟩ : T)).carrier := by
  subst T
  exact RingEquiv.refl _

def nativeOriginalStalkEquiv {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) :
    ((actualSubspaceSheaf (n := n+k) (nativeCarrier U C H G)).presheaf.stalk
      (nativePoint U C H G p)).carrier ≃+*
    ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier := by
  let T := (Subtype.val : wideDomain k U → ComplexModel (n+k)) ⁻¹' nativeCarrier U C H G
  let pT : T := ⟨p.val,⟨p.val,p.property,rfl⟩⟩
  exact (actualOpenSubspaceStalkEquiv (n := n+k) (nativeCarrier U C H G) (wideDomain k U) pT).trans
    (stalkEquiv_of_carrier_eq T (graphClosure U C H G) (nativeCarrier_preimage U C H G) pT)

def graphStalkStructureMap {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) : HolGerm (ComplexModel n) →+*
      ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier :=
  (nativeOriginalStalkEquiv U C H G p).toRingHom.comp
    (stalkStructureMap (nativeCarrier U C H G) (nativePoint U C H G p) n)

theorem graphStalkStructureMap_finite {n k : ℕ}
    (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      GermParametrizationData.monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    (p : graphClosure U C H G) : (graphStalkStructureMap U C H G p).Finite :=
  (RingHom.Finite.of_surjective (nativeOriginalStalkEquiv U C H G p).toRingHom
    (nativeOriginalStalkEquiv U C H G p).surjective).comp
      (graph_native_stalkStructureMap_finite U C H G d a ha hmonic p)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphOriginalStalk
