import SGPT.GAGA.ChowBlLift
import SGPT.GAGA.ChowBlImage

/-! Actual Segre graph of the ORIGINAL projective embedding and a native
positive-bundle embedding; genuine full Chow ideal before algebraization.
Blueprint: original-chow-segre-graph.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open Set Filter SGPT.GAGA.H0S SGPT.GAGA.ChowBl
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {n N r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {Ψ : M → ComplexProjectiveSpace N} {Φ : M → ComplexProjectiveSpace r}

omit [IsComplexManifold n M] in
/-- SAME actual source and actual Segre graph: injectivity and differential
are manufactured from genuine local homogeneous lifts, not supplied. -/
theorem originalSegreGraph_isHolomorphicEmbedding
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hΦ : IsHolomorphicEmbedding (n := n) Φ) :
    IsHolomorphicEmbedding (n := n) (fun x => segreMap (Ψ x) (Φ x)) := by
  apply isHolomorphicEmbedding_of_lifts
  · intro x y h
    have hpair : (Ψ x, Φ x) = (Ψ y, Φ y) := segreMap_injective h
    exact hΨ.injective (congrArg Prod.fst hpair)
  · intro p
    let i := chartIndex (Ψ p)
    let j := chartIndex (Φ p)
    let F := fun z => affineLift i (chartMap (n := n) Ψ p i z)
    let G := fun z => affineLift j (chartMap (n := n) Φ p j z)
    have hF := exists_lift_of_isHolomorphicEmbedding hΨ p (mem_affineChart_chartIndex (Ψ p))
    have hG := exists_lift_of_isHolomorphicEmbedding hΦ p (mem_affineChart_chartIndex (Φ p))
    refine ⟨fun z => segreVec (F z) (G z), ?_, ?_⟩
    · filter_upwards [hF.1,hG.1] with z hzF hzG
      refine ⟨?_,segreVec_ne_zero hzF.2.1 hzG.2.1,?_⟩
      · apply differentiableAt_pi.mpr
        intro k
        exact ((differentiableAt_pi.mp hzF.1) (segreIdx N r k).1).mul
          ((differentiableAt_pi.mp hzG.1) (segreIdx N r k).2)
      · exact (congrArg₂ segreMap hzF.2.2 hzG.2.2).trans
          (segreMap_pmk hzF.2.1 hzG.2.1)
    · exact isProjImmersionAt_segreVec hF.1.self_of_nhds.1 hG.1.self_of_nhds.1
        hF.1.self_of_nhds.2.1 hG.1.self_of_nhds.2.1 (fun v hv _ => hF.2 v hv)

variable [CompactSpace M]

/-- Genuine Chow produces finite homogeneous generators of the FULL
analytic cone ideal of this SAME actual graph, not only its point set.
No algebraic graph, ideal-generation or algebraization certificate input. -/
theorem exists_originalSegreGraph_fullChowIdeal
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hΦ : IsHolomorphicEmbedding (n := n) Φ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ (μ : Type) (_ : Fintype μ)
      (P : μ → MvPolynomial (Fin (segreDim N r + 1)) ℂ),
      (∀ k, (P k).IsHomogeneous m) ∧
      (coneIdeal (range (fun x => segreMap (Ψ x) (Φ x)))).GeneratedOn
        (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace (segreDim N r)))
        (fun k => SGPT.GAGA.PN.polyTuple (P k)) ∧
      range (fun x => segreMap (Ψ x) (Φ x)) =
        {z | ∀ k, MvPolynomial.eval z.rep (P k) = 0} := by
  simpa only [image_univ] using chow_image (originalSegreGraph_isHolomorphicEmbedding hΨ hΦ)
    (isComplexAnalyticSubset_univ (n := n) (M := M))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
