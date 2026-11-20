import SGPT.Foundations.Schemes.RegularSectionCechEuler
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Actual affine zero-subscheme restriction lowers extended ring Krull
dimension whenever the actual original coefficient is regular. -/
theorem sectionZeroAffine_ringKrullDim_succ_le_of_regular {X : Scheme.{u}}
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (U : X.affineOpens)
    {V : X.Opens} (e : LocalBundleFrame L V) (i : U.val ⟶ V)
    (hr : e.coefficients i (L.presheaf.map U.val.leTop.op s) ∈ nonZeroDivisors Γ(X, U)) :
    ringKrullDim Γ(sectionZeroSubscheme a s, sectionZeroι a s ⁻¹ᵁ U) + 1 ≤ ringKrullDim Γ(X, U) := by
  apply ringKrullDim_succ_le_of_surjective ((sectionZeroι a s).app U).hom
    (sectionZeroι_app_surjective a s U) hr
  change e.coefficients i (L.presheaf.map U.val.leTop.op s) ∈
    RingHom.ker ((sectionZeroι a s).app U).hom
  rw [sectionZeroι_app_ker, sectionZeroIdeal_eq_span_frame s e i]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Genuine regularity lowers dimension on the ACTUAL divisor inverse-image
coordinate intersections, retaining actual source/target affine rings. -/
theorem nativePositiveProjectiveSectionZero_chart_dimension_drop_of_regular
    (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (f : X ⟶ polynomialProj K N) [IsAffineHom f] (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
    (s : bundlePowerGlobalSections L.sheaf q)
    (hr : nativePositiveProjectiveSectionRegular K N f L q e s)
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    let W := actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S
    ringKrullDim Γ(sectionZeroSubscheme (L.atlas.tensorPower q) s,
      sectionZeroι (L.atlas.tensorPower q) s ⁻¹ᵁ W) + 1 ≤ ringKrullDim Γ(X, W) := by
  let W := actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S
  let U : X.affineOpens :=
    ⟨W, actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f S hS⟩
  exact sectionZeroAffine_ringKrullDim_succ_le_of_regular (L.atlas.tensorPower q) s U
    (nativePositiveProjectiveCoordinateFrame K N f L q e hS.choose)
    (homOfLE (Finset.inf_le hS.choose_spec)) (hr S hS)

/-- One ACTUAL section, produced from original projective coordinates, gives
all-twist short exact/Euler identities AND genuine chart dimension drops. -/
theorem ClosedProjectiveEmbedding.exists_regular_positive_section_euler_dimension_drop
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf) :
    ∃ s : bundlePowerGlobalSections L.sheaf q,
      (∀ m : ℕ,
        (nativePositiveProjectiveSectionZeroCechShortComplex ℂ P.ambientDimension P.map L q e s
          (schemeGlobalConstants p) m).ShortExact ∧
        (nativePositiveProjectiveSectionZeroCechShortComplex ℂ P.ambientDimension P.map L q e s
          (schemeGlobalConstants p) m).X₂.homologyEulerChar =
        (nativePositiveProjectiveSectionZeroCechShortComplex ℂ P.ambientDimension P.map L q e s
          (schemeGlobalConstants p) m).X₁.homologyEulerChar +
        (nativePositiveSectionZeroRestrictedCechComplex ℂ P.ambientDimension P.map L q s p
          (m + 1)).homologyEulerChar) ∧
      (∀ (S : Finset (Fin (P.ambientDimension + 1))) (_hS : S.Nonempty),
        let W := actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens P.map) S
        ringKrullDim Γ(sectionZeroSubscheme (L.atlas.tensorPower q) s,
          sectionZeroι (L.atlas.tensorPower q) s ⁻¹ᵁ W) + 1 ≤ ringKrullDim Γ(X, W)) := by
  obtain ⟨s, hs⟩ := P.exists_regular_positive_section L q e
  refine ⟨s, ?_, ?_⟩
  · intro m
    constructor
    · exact nativePositiveProjectiveSectionZeroCechShortComplex_shortExact_of_regular ℂ
        P.ambientDimension P.map L q e s hs (schemeGlobalConstants p) m
    · exact nativePositiveProjectiveSectionZeroCechEulerOnDivisor_of_regular ℂ
        P.ambientDimension P.map L q e s hs p P.over_base m
  · intro S hS
    exact nativePositiveProjectiveSectionZero_chart_dimension_drop_of_regular ℂ
      P.ambientDimension P.map L q e s hs S hS

end
end SGPT.Foundations.Schemes
