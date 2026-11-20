import SGPT.Projective.OriginalNormalizedCurveZero
import SGPT.Projective.OriginalNormalizationPrincipalColength

/-! LITERAL ordinary-section zero affine rings and their actual ORIGINAL
normalization colength, with true structural constants. Blueprint:
original-section-zero-affine-colength.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Projective.NumEq.AlgebraicCurveDegree

/-- The actual original affine zero quotient preserves the SAME original
complex structural constants, not merely an abstract ring isomorphism. -/
def originalSectionZeroAffineQuotientAlgEquiv
    {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) {L : Y.Modules}
    (a : LineBundleAtlas L) (s : Γ(L,⊤)) {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := affineChartAlgebra g U
    letI := affineChartAlgebra (sectionZeroι a s ≫ g) (sectionZeroι a s ⁻¹ᵁ U)
    Γ(sectionZeroSubscheme a s,sectionZeroι a s ⁻¹ᵁ U) ≃ₐ[ℂ]
      Γ(Y,U) ⧸ sectionZeroIdeal L s U := by
  let := affineChartAlgebra g U
  let := affineChartAlgebra (sectionZeroι a s ≫ g) (sectionZeroι a s ⁻¹ᵁ U)
  let := (((sectionZeroι a s).app U).hom).toAlgebra
  let := originalMorphism_affineChartScalarTower g (sectionZeroι a s) U
  let e := (sectionZeroAffineQuotientIso a s ⟨U,hU⟩).commRingCatIsoToRingEquiv
  let eR : Γ(sectionZeroSubscheme a s,sectionZeroι a s ⁻¹ᵁ U) ≃ₐ[Γ(Y,U)]
      Γ(Y,U) ⧸ sectionZeroIdeal L s U := by
    refine { e with commutes' := ?_ }
    intro r
    change e ((sectionZeroι a s).app U r) = Ideal.Quotient.mk _ r
    rw [sectionZeroι_app a s ⟨U,hU⟩]
    exact e.apply_symm_apply _
  exact eR.restrictScalars ℂ

/-- The SAME actual coefficient in ANY actual original frame identifies
the ENTIRE actual affine zero ring with its principal quotient, preserving
original complex scalars and every nilpotent. -/
def originalSectionZeroAffinePrincipalAlgEquiv
    {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) {L : Y.Modules}
    (a : LineBundleAtlas L) (s : Γ(L,⊤)) {U V : Y.Opens}
    (hU : IsAffineOpen U) (e : LocalBundleFrame L V) (j : U ⟶ V) :
    letI := affineChartAlgebra g U
    letI := affineChartAlgebra (sectionZeroι a s ≫ g) (sectionZeroι a s ⁻¹ᵁ U)
    Γ(sectionZeroSubscheme a s,sectionZeroι a s ⁻¹ᵁ U) ≃ₐ[ℂ]
      Γ(Y,U) ⧸ Ideal.span {e.coefficients j (L.val.map U.leTop.op s)} := by
  let := affineChartAlgebra g U
  let := affineChartAlgebra (sectionZeroι a s ≫ g) (sectionZeroι a s ⁻¹ᵁ U)
  exact (originalSectionZeroAffineQuotientAlgEquiv g a s hU).trans
    (Ideal.quotientEquivAlgOfEq ℂ (sectionZeroIdeal_eq_span_frame s e j))

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include E hcurve in
/-- LITERAL actual ordinary-section zero rings on ANY framed original
nonempty affine have equal TRUE complex colength before/after the SAME
normalization. All coefficients/readers/finiteness are manufactured; there
is no desired zero-length/branch/degree/period comparison premise. -/
theorem originalNormalizationSectionZero_affineColength
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0)
    {U V : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (e : LocalBundleFrame L V) (j : U ⟶ V) :
    letI := affineChartAlgebra (sectionZeroι a s ≫ f) (sectionZeroι a s ⁻¹ᵁ U)
    letI := affineChartAlgebra
      (sectionZeroι (matePullbackAtlas (originalNormalizationMap X) a)
        (originalPulledSection (originalNormalizationMap X) s) ≫ (originalNormalizationMap X ≫ f))
      (sectionZeroι (matePullbackAtlas (originalNormalizationMap X) a)
        (originalPulledSection (originalNormalizationMap X) s) ⁻¹ᵁ (originalNormalizationMap X ⁻¹ᵁ U))
    Module.finrank ℂ Γ(sectionZeroSubscheme a s,sectionZeroι a s ⁻¹ᵁ U) =
      Module.finrank ℂ Γ(sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
        (originalPulledSection (originalNormalizationMap X) s),
        sectionZeroι (matePullbackAtlas (originalNormalizationMap X) a)
          (originalPulledSection (originalNormalizationMap X) s) ⁻¹ᵁ (originalNormalizationMap X ⁻¹ᵁ U)) := by
  let := originalNormalizationMap_finite X f E
  let ν := originalNormalizationMap X
  let aN := matePullbackAtlas ν a
  let sN := originalPulledSection ν s
  let := affineChartAlgebra f U
  let := affineChartAlgebra (ν ≫ f) (ν ⁻¹ᵁ U)
  let := affineChartAlgebra (sectionZeroι a s ≫ f) (sectionZeroι a s ⁻¹ᵁ U)
  let := affineChartAlgebra (sectionZeroι aN sN ≫ (ν ≫ f))
    (sectionZeroι aN sN ⁻¹ᵁ (ν ⁻¹ᵁ U))
  let r : Γ(X,U) := e.coefficients j (L.val.map U.leTop.op s)
  have hr : r ≠ 0 := sectionCoefficient_ne_zero a s hs e j
  have h := originalNormalizationAffinePrincipalQuotient_colength f E hcurve hU r hr
  let qR := originalSectionZeroAffinePrincipalAlgEquiv f a s hU e j
  let qS := originalSectionZeroAffinePrincipalAlgEquiv (ν ≫ f) aN sN (hU.preimage ν)
    (matePullbackFrame ν e) ((Opens.map ν.base).map j)
  have hcoeff := originalPulledSection_coefficients ν s e j
  have hqS := qS.toLinearEquiv.finrank_eq
  rw [hcoeff] at hqS
  exact qR.toLinearEquiv.finrank_eq.trans (h.2.2.trans hqS.symm)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
