import SGPT.Projective.OriginalArtinianOpenStalks
import SGPT.Projective.OriginalFiniteClosedPointSums
import SGPT.Projective.OriginalSectionZeroAffineColength

/-! ENTIRE actual normalized ordinary zero preserves the full original
stalk-dimension sum, from genuine local coefficient colength; no desired
global degree/Euler/period comparison input. Blueprint:
original-normalization-zero-global.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

/-- The FULL genuine original zero stalk dimension sum is preserved by
SAME actual ordinary-section normalization, retaining every actual point,
branch, nilpotent multiplicity and empty zero. No global comparison premise. -/
theorem originalNormalizationSectionZero_stalkDimensionSum
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) :
    letI := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
    letI := originalNormalizedCurveSectionZero_isArtinian f E hcurve a s hs
    letI : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
    letI : Fintype (sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
      (originalPulledSection (originalNormalizationMap X) s)) := Fintype.ofFinite _
    letI : ∀ z : sectionZeroSubscheme a s, Algebra ℂ ((sectionZeroSubscheme a s).presheaf.stalk z) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants (sectionZeroι a s ≫ f)) z
    letI : ∀ z : sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
      (originalPulledSection (originalNormalizationMap X) s), Algebra ℂ
        ((sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
          (originalPulledSection (originalNormalizationMap X) s)).presheaf.stalk z) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants
        (sectionZeroι (matePullbackAtlas (originalNormalizationMap X) a)
          (originalPulledSection (originalNormalizationMap X) s) ≫ (originalNormalizationMap X ≫ f))) z
    (∑ z : sectionZeroSubscheme a s, Module.finrank ℂ ((sectionZeroSubscheme a s).presheaf.stalk z)) =
      ∑ z : sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
        (originalPulledSection (originalNormalizationMap X) s),
        Module.finrank ℂ ((sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
          (originalPulledSection (originalNormalizationMap X) s)).presheaf.stalk z) := by
  classical
  let := originalNormalizationMap_finite X f E
  let := E.locallyOfFiniteType
  let ν := originalNormalizationMap X
  let aN := matePullbackAtlas ν a
  let sN := originalPulledSection ν s
  let Z := sectionZeroSubscheme a s
  let ZN := sectionZeroSubscheme aN sN
  let i := sectionZeroι a s
  let j := sectionZeroι aN sN
  let := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
  let := originalNormalizedCurveSectionZero_isArtinian f E hcurve a s hs
  let : Fintype Z := Fintype.ofFinite Z
  let : Fintype ZN := Fintype.ofFinite ZN
  let : ∀ z : Z, Algebra ℂ (Z.presheaf.stalk z) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants (i ≫ f)) z
  let : ∀ z : ZN, Algebra ℂ (ZN.presheaf.stalk z) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants (j ≫ (ν ≫ f))) z
  let A (z : Z) := i z
  let B (z : ZN) := ν (j z)
  let w (z : Z) := Module.finrank ℂ (Z.presheaf.stalk z)
  let v (z : ZN) := Module.finrank ℂ (ZN.presheaf.stalk z)
  have hA (z : Z) : IsClosed ({A z}:Set X) := by
    have h := i.isClosedMap _ (isClosed_singleton : IsClosed ({z}:Set Z))
    simpa only [Set.image_singleton] using h
  have hB (z : ZN) : IsClosed ({B z}:Set X) := by
    have h := (j ≫ ν).isClosedMap _ (isClosed_singleton : IsClosed ({z}:Set ZN))
    simpa only [Set.image_singleton,Scheme.Hom.comp_apply,B] using h
  let Basis : Set X.Opens := {U | IsAffineOpen U ∧ ∃ k : a.I,U≤a.opens k}
  have hBasis : ∀ x (O : X.Opens), x∈O → ∃ U∈Basis,x∈U ∧ U≤O := by
    intro x O hx
    obtain ⟨k,hk⟩ := a.covers x
    obtain ⟨U,hU,hxU,hUi⟩ := exists_isAffineOpen_mem_and_subset
      (show x∈O ⊓ a.opens k from ⟨hx,hk⟩)
    exact ⟨U,⟨hU,k,hUi.trans inf_le_right⟩,hxU,hUi.trans inf_le_left⟩
  have hlocal : ∀ U∈Basis,
      (∑ z : Z,if A z∈U then w z else 0) = ∑ z : ZN,if B z∈U then v z else 0 := by
    intro U hUB
    obtain ⟨hU,k,hUk⟩ := hUB
    by_cases hne : Nonempty U
    · let := hne
      have hc := originalNormalizationSectionZero_affineColength f E hcurve a s hs hU
        (a.frame k) (homOfLE hUk)
      have hR := originalArtinianOpen_finrank_eq_filteredStalkSum (i ≫ f) (i ⁻¹ᵁ U)
      have hS := originalArtinianOpen_finrank_eq_filteredStalkSum (j ≫ (ν ≫ f)) (j ⁻¹ᵁ (ν ⁻¹ᵁ U))
      exact hR.symm.trans (hc.trans hS)
    · have hbot : U=⊥ := by
        apply bot_unique
        intro x hx
        exact (hne ⟨⟨x,hx⟩⟩).elim
      subst U
      simp
  exact originalFiniteClosedPointSums_eq_of_basis A B w v hA hB Basis hBasis hlocal

/-- The FULL actual original zero-stalk length sum is preserved by SAME
normalization, including every nilpotent/branch and empty scheme. -/
theorem originalNormalizationSectionZero_fullLengthSum
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) :
    letI := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
    letI := originalNormalizedCurveSectionZero_isArtinian f E hcurve a s hs
    originalArtinianStalkLengthSum (sectionZeroSubscheme a s) =
      originalArtinianStalkLengthSum (sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
        (originalPulledSection (originalNormalizationMap X) s)) := by
  classical
  let := originalNormalizationMap_finite X f E
  let := E.locallyOfFiniteType
  let ν := originalNormalizationMap X
  let aN := matePullbackAtlas ν a
  let sN := originalPulledSection ν s
  let Z := sectionZeroSubscheme a s
  let ZN := sectionZeroSubscheme aN sN
  let i := sectionZeroι a s
  let j := sectionZeroι aN sN
  let := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
  let := originalNormalizedCurveSectionZero_isArtinian f E hcurve a s hs
  let : Fintype Z := Fintype.ofFinite Z
  let : Fintype ZN := Fintype.ofFinite ZN
  let : ∀ z : Z, Algebra ℂ (Z.presheaf.stalk z) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants (i ≫ f)) z
  let : ∀ z : ZN, Algebra ℂ (ZN.presheaf.stalk z) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants (j ≫ (ν ≫ f))) z
  have h := originalNormalizationSectionZero_stalkDimensionSum f E hcurve a s hs
  change (∑ z : Z,Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z)) =
    ∑ z : ZN,Module.length (ZN.presheaf.stalk z) (ZN.presheaf.stalk z)
  have hR := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun z (_hz : z ∈ (Finset.univ : Finset Z)) => originalArtinianStalk_length_eq_finrank (i ≫ f) z)
  have hS := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun z (_hz : z ∈ (Finset.univ : Finset ZN)) => originalArtinianStalk_length_eq_finrank (j ≫ (ν ≫ f)) z)
  refine hR.trans (Eq.trans ?_ hS.symm)
  simpa only [Nat.cast_sum] using congrArg (fun d : ℕ => (d:ℕ∞)) h

/-- INDEPENDENT original structural section-zero cycle degree equals
FULL SAME actual normalized zero lengths; no normalized embedding or period. -/
theorem originalIntegralCurveSectionZeroDegree_eq_normalizedFullLength
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) (p : Spec (.of ℂ)) :
    letI := originalNormalizedCurveSectionZero_isArtinian f E hcurve a s hs
    originalIntegralCurveSectionZeroDegree f E hcurve a s hs p =
      ((originalArtinianStalkLengthSum (sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
        (originalPulledSection (originalNormalizationMap X) s))).toNat : ℤ) := by
  let := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
  let := originalNormalizedCurveSectionZero_isArtinian f E hcurve a s hs
  exact (originalIntegralCurveSectionZeroDegree_eq_fullLength f E hcurve a s hs p).trans
    (congrArg (fun d : ℕ∞ => (d.toNat:ℤ))
      (originalNormalizationSectionZero_fullLengthSum f E hcurve a s hs))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
