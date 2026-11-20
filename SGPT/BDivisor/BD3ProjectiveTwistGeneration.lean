import SGPT.Projective.OriginalAffineGeneratedSections
import SGPT.BDivisor.BD3ClopenGeneratedSection
import SGPT.Okounkov.AlgebraicBodyOperations
import SGPT.Foundations.Schemes.OriginalPowerCommonDegreeGenerators
import SGPT.Foundations.Schemes.NativePolynomialPullbackTwistComparison

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalProjectiveTwistGeneration`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalProjectiveTwistGeneration`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Literal original projective-twist global generators, no pole-sheaf substitution.
Blueprint: original-projective-twist-generation.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open SGPT.Okounkov

/-- Actual SAME original projective twist has finite global generators for EVERY sufficiently large degree. -/
theorem exists_originalProjectiveTwist_generators_bd3 {X : Scheme.{0}} {N : ℕ}
    (i : X ⟶ polynomialProj ℂ N) [IsClosedImmersion i]
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ B : ℕ, ∀ D : ℕ, B ≤ D →
      ∃ G : (bundleTensor (bundleTensorPower
        ((Scheme.Modules.pullback i).obj (polynomialProjTwistingLine ℂ N).sheaf) D) L).GeneratingSections,
        G.IsFiniteType := by
  classical
  obtain ⟨m, B, hB⟩ := closedPolynomialProjPushforward_exists_commonDegree_chart_generators ℂ N i a
  refine ⟨B, fun D hD => ?_⟩
  obtain ⟨t, ht⟩ := hB D hD
  let P := (Scheme.Modules.pullback i).obj (polynomialProjTwistingLine ℂ N).sheaf
  let Q := bundleTensor (bundleTensorPower P D) L
  let I := Σ j : Fin (N + 1), Fin (m j)
  let U (j : Fin (N + 1)) := i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j
  let R := nativePolynomialPullbackTwistIso ℂ N i L D
  let s (b : I) : Γ(Q, ⊤) := R.hom.val.app (op ⊤) (t b)
  have hspan (j : Fin (N + 1)) : Submodule.span Γ(X, U j)
      (Set.range (fun b => Q.val.map (U j).leTop.op (s b))) = ⊤ := by
    let J := (((nativePolynomialPullbackAtlas ℂ N i).frame j).tensorPower D).tensorModuleCoefficients L (𝟙 (U j))
    let c (b : I) : bundleSections L (U j) :=
      atlasTwistedGlobalCoefficients (polynomialProjTwistingLine ℂ N).atlas
        ((Scheme.Modules.pushforward i).obj L) D j (t b)
    have hc (b : I) : J (Q.val.map (U j).leTop.op (s b)) = c b :=
      nativePolynomialPullbackTwistIso_globalCoefficients ℂ N i L D j (t b)
    have hres : Submodule.span Γ(X, U j) (Set.range c) = ⊤ :=
      polynomialProjTwistedCoefficient_span_originalRing ℂ N i L D t j (ht j)
    have hsp := span_range_eq_top_of_semilinear_surjective (RingHom.id Γ(X, U j))
      J.symm.toLinearMap.toAddMonoidHom J.symm.surjective (fun r x => J.symm.map_smul r x) c hres
    have he : (fun b => J.symm (c b)) = (fun b : I => Q.val.map (U j).leTop.op (s b)) := by
      funext b
      exact (congrArg J.symm (hc b)).symm.trans (J.symm_apply_apply _)
    change Submodule.span Γ(X, U j) (Set.range (fun b => J.symm (c b))) = ⊤ at hsp
    rw [he] at hsp
    exact hsp
  let bQ := pairwiseTensorAtlas ((nativePolynomialPullbackAtlas ℂ N i).tensorPower D) a
  let : Q.IsQuasicoherent := bQ.isQuasicoherent
  have hU (j : Fin (N + 1)) : IsAffineOpen (U j) :=
    (polynomialProjCoordinateOpen_isAffine ℂ N j).preimage i
  have hcover (x : X) : ∃ j, x ∈ U j :=
    (show IsOpenCover U from actualPolynomialProjectivePullbackCoordinateOpens_covers i).exists_mem x
  exact ⟨originalGeneratingSectionsOfAffineCoverSpan Q s U hU hcover hspan, inferInstance⟩

end SGPT.Projective.NumEq.AlgebraicCurveDegree
