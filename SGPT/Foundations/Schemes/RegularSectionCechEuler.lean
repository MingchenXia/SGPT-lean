import SGPT.Foundations.Schemes.ProjectiveRegularSection
import SGPT.Foundations.Schemes.NativeDivisorCoverCechEuler

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Genuine regularity of the original coefficient injects the ACTUAL tensor
multiplication component, without integrality or nonzero-section premises. -/
theorem sectionTensorRightMap_injective_of_regular {X : Scheme.{u}}
    {L B : X.Modules} (s : Γ(L, ⊤)) {U V : X.Opens}
    (eB : LocalBundleFrame B U) (e : LocalBundleFrame L U) (i : V ⟶ U)
    (hr : e.coefficients i (L.presheaf.map V.leTop.op s) ∈ nonZeroDivisors Γ(X, V)) :
    Function.Injective ((sectionTensorRightMap B L s).app V) := by
  intro x y h
  have hc := congrArg ((eB.tensor e).coefficients i) h
  change (eB.tensor e).coefficients i
    (tensorSection B L V x (L.presheaf.map V.leTop.op s)) =
      (eB.tensor e).coefficients i
        (tensorSection B L V y (L.presheaf.map V.leTop.op s)) at hc
  rw [LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensor_coefficients] at hc
  apply (eB.coefficients i).injective
  exact (mul_cancel_right_mem_nonZeroDivisors hr).mp hc


/-- Actual regular coefficients produce original short exact complexes on
possibly nonintegral strata; all right-map and affine quotient data is actual. -/
theorem nativePositiveProjectiveSectionZeroCechShortComplex_shortExact_of_regular
    (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (f : X ⟶ polynomialProj K N) [IsAffineHom f] (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
    (s : bundlePowerGlobalSections L.sheaf q)
    (hr : nativePositiveProjectiveSectionRegular K N f L q e s)
    (c : K →+* Γ(X, ⊤)) (m : ℕ) :
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s c m).ShortExact := by
  unfold nativePositiveProjectiveSectionZeroCechShortComplex sectionZeroPowerCechShortComplex
  apply actualNonemptySubsetCechShortComplex_shortExact
  · intro S
    let j := S.property.choose
    let W := actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S.val
    let h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K N j :=
      homOfLE (Finset.inf_le S.property.choose_spec)
    let a := nativePositiveProjectiveCoordinateFrame K N f L q e j
    change Function.Injective ((sectionTensorRightMap
      (bundleTensorPower (bundleTensorPower L.sheaf q) m) (bundleTensorPower L.sheaf q) s).app W)
    exact sectionTensorRightMap_injective_of_regular s (a.tensorPower m) a h (hr S.val S.property)
  · intro S
    change Function.Surjective
      ((sectionZeroTensorRestriction (L.atlas.tensorPower q) s
        (bundleTensorPower (bundleTensorPower L.sheaf q) (m + 1))).app
          (actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S.val))
    exact sectionZeroAffineTensorRestriction_surjective (L.atlas.tensorPower q) s
      ⟨_, actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f S.val S.property⟩
      ((nativePositiveProjectiveSubsetFrame K N f L q e S).tensorPower (m + 1)) (𝟙 _)

/-- Genuine regularity, actual closed projective geometry and canonical
restriction give the actual divisor Euler identity without integral strata. -/
theorem nativePositiveProjectiveSectionZeroCechEulerOnDivisor_of_regular
    (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (f : X ⟶ polynomialProj K N) [IsClosedImmersion f] (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
    (s : bundlePowerGlobalSections L.sheaf q)
    (hr : nativePositiveProjectiveSectionRegular K N f L q e s)
    (p : X ⟶ Spec (.of K)) (hp : actualPolynomialProjectivePullbackStructureMap f = p)
    (m : ℕ) :
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₂.homologyEulerChar =
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
      (schemeGlobalConstants p) m).X₁.homologyEulerChar +
    (nativePositiveSectionZeroRestrictedCechComplex K N f L q s p (m + 1)).homologyEulerChar := by
  let C := nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s
    (schemeGlobalConstants p) m
  have hC : C.ShortExact :=
    nativePositiveProjectiveSectionZeroCechShortComplex_shortExact_of_regular K N f L q e s hr
      (schemeGlobalConstants p) m
  let : ∀ j, Module.Finite K (C.X₁.homology j) := fun j ↦
    closedPolynomialProjLineCech_homology_finite K N f
      ((L.atlas.tensorPower q).tensorPower m) p hp j
  let : ∀ j, Module.Finite K (C.X₂.homology j) := fun j ↦
    closedPolynomialProjLineCech_homology_finite K N f
      ((L.atlas.tensorPower q).tensorPower (m + 1)) p hp j
  let : ∀ j, Module.Finite K (C.X₃.homology j) := fun j ↦
    nativePositiveSectionZeroQuotientCech_homology_finite K N f L q s p e hp (m + 1) j
  have hEuler : C.X₂.homologyEulerChar = C.X₁.homologyEulerChar + C.X₃.homologyEulerChar := by
    apply boundedCochain_homologyEulerChar_additive C hC (Fintype.card (Fin (N + 1)))
    all_goals
      intro j hj
      change IsZero ((subsetCechComplex _).homology j)
      exact subsetCechComplex_homology_isZero_of_card_le _ j hj
  exact hEuler.trans (congrArg (fun z : ℤ ↦ C.X₁.homologyEulerChar + z)
    (nativePositiveSectionZeroCechEuler_eq_restricted K N f L q s p e (m + 1)))

/-- The actual regular-section producer discharges every regularity input of
the genuine divisor Euler identity on ANY closed complex projective stratum. -/
theorem ClosedProjectiveEmbedding.exists_regular_positive_section_euler
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf) :
    ∃ s : bundlePowerGlobalSections L.sheaf q, ∀ m : ℕ,
      (nativePositiveProjectiveSectionZeroCechShortComplex ℂ P.ambientDimension P.map L q e s
        (schemeGlobalConstants p) m).ShortExact ∧
      (nativePositiveProjectiveSectionZeroCechShortComplex ℂ P.ambientDimension P.map L q e s
        (schemeGlobalConstants p) m).X₂.homologyEulerChar =
      (nativePositiveProjectiveSectionZeroCechShortComplex ℂ P.ambientDimension P.map L q e s
        (schemeGlobalConstants p) m).X₁.homologyEulerChar +
      (nativePositiveSectionZeroRestrictedCechComplex ℂ P.ambientDimension P.map L q s p
        (m + 1)).homologyEulerChar := by
  obtain ⟨s, hs⟩ := P.exists_regular_positive_section L q e
  refine ⟨s, fun m ↦ ⟨?_, ?_⟩⟩
  · exact nativePositiveProjectiveSectionZeroCechShortComplex_shortExact_of_regular ℂ
      P.ambientDimension P.map L q e s hs (schemeGlobalConstants p) m
  · exact nativePositiveProjectiveSectionZeroCechEulerOnDivisor_of_regular ℂ
      P.ambientDimension P.map L q e s hs p P.over_base m



end
end SGPT.Foundations.Schemes
