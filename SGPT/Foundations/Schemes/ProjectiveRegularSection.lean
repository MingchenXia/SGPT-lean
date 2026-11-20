import SGPT.Foundations.Schemes.FiniteAssociatedPrimeAvoidance
import SGPT.Foundations.Schemes.PositiveProjectiveCechInputs
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- The ORIGINAL global coefficient map is linear for the actual structural
constants on global and local sections. -/
def actualGlobalFrameCoefficientLinear {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (h : W ⟶ U) :
    letI : Module K Γ(L, ⊤) := schemeGlobalSectionModule p L
    letI : Algebra K Γ(X, W) :=
      ((X.presheaf.map W.leTop.op).hom.comp (schemeGlobalConstants p)).toAlgebra
    Γ(L, ⊤) →ₗ[K] Γ(X, W) := by
  letI : Module K Γ(L, ⊤) := schemeGlobalSectionModule p L
  letI : Algebra K Γ(X, W) :=
    ((X.presheaf.map W.leTop.op).hom.comp (schemeGlobalConstants p)).toAlgebra
  exact {
    toFun := fun s ↦ e.coefficients h (L.val.map W.leTop.op s)
    map_add' := by intro a b; simp only [map_add]
    map_smul' := by
      intro r s
      change e.coefficients h (L.val.map W.leTop.op (schemeGlobalConstants p r • s)) =
        (show Γ(X, W) from X.presheaf.map W.leTop.op (schemeGlobalConstants p r)) *
          (show Γ(X, W) from e.coefficients h (L.val.map W.leTop.op s))
      rw [PresheafOfModules.map_smul]
      exact (e.coefficients h).map_smul
        (show X.sheaf.obj.obj (op W) from
          X.presheaf.map W.leTop.op (schemeGlobalConstants p r)) _ }


/-- Actual nonzerodivisor coefficients on the ORIGINAL coordinate intersections. -/
def nativePositiveProjectiveSectionRegular (K : Type) [Field K] (N : ℕ)
    {X : Scheme} (f : X ⟶ polynomialProj K N) (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
    (s : bundlePowerGlobalSections L.sheaf q) : Prop :=
      ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
        let j := hS.choose
        let W := actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S
        let h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K N j :=
          homOfLE (Finset.inf_le hS.choose_spec)
        (nativePositiveProjectiveCoordinateFrame K N f L q e j).coefficients h
          ((bundleTensorPower L.sheaf q).val.map W.leTop.op s) ∈ nonZeroDivisors Γ(X, W)

/-- Genuine coordinates give an actual regular positive section on every
actual nonempty-index affine intersection of any closed complex projective
scheme. No reducedness, integrality, nonemptiness or CM certificate is used. -/
theorem ClosedProjectiveEmbedding.exists_regular_positive_section
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf) :
    ∃ s : bundlePowerGlobalSections L.sheaf q,
      nativePositiveProjectiveSectionRegular ℂ P.ambientDimension P.map L q e s := by
  classical
  let J := Fin (P.ambientDimension + 1)
  let I := {S : Finset J // S.Nonempty}
  let U := actualPolynomialProjectivePullbackCoordinateOpens P.map
  let W (S : I) := actualSchemeSubsetOpen U S.val
  let R (S : I) : Type := Γ(X, W S)
  let A := bundleTensorPower L.sheaf q
  let : Module ℂ Γ(A, ⊤) := schemeGlobalSectionModule p A
  let : ∀ S : I, Algebra ℂ (R S) := fun S ↦
    ((X.presheaf.map (W S).leTop.op).hom.comp (schemeGlobalConstants p)).toAlgebra
  let : ∀ S : I, IsNoetherianRing (R S) := fun S ↦
    P.affineSections_isNoetherian
      (actualPolynomialProjectivePullbackSubsetOpen_isAffine ℂ P.ambientDimension P.map S.val S.property)
  let σ (j : J) : Γ(A, ⊤) := nativePositiveProjectiveCoordinateSection ℂ P.ambientDimension P.map L q e j
  let F : (J → ℂ) →ₗ[ℂ] Γ(A, ⊤) :=
    ∑ j, (LinearMap.proj j).smulRight (σ j)
  let c (S : I) : Γ(A, ⊤) →ₗ[ℂ] R S :=
    actualGlobalFrameCoefficientLinear p
      (nativePositiveProjectiveCoordinateFrame ℂ P.ambientDimension P.map L q e S.property.choose)
      (homOfLE (Finset.inf_le S.property.choose_spec))
  have hF (S : I) : ∃ v : J → ℂ, (c S).comp F v = 1 := by
    refine ⟨Pi.single S.property.choose 1, ?_⟩
    change c S (F (Pi.single S.property.choose 1)) = 1
    have hsingle : F (Pi.single S.property.choose 1) = σ S.property.choose := by
      simp [F, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    rw [hsingle]
    have hc := nativePositiveProjectiveCoordinateSection_coefficients ℂ P.ambientDimension P.map L q e
      S.property.choose (W := W S)
      (homOfLE (show W S ≤ P.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ P.ambientDimension
        S.property.choose from Finset.inf_le S.property.choose_spec))
    convert hc using 1 <;> rfl
  let d : ∀ S : I, (J → ℂ) →ₗ[ℂ] R S := fun S ↦ (c S).comp F
  have hd : ∀ S : I, ∃ v, d S v = 1 := hF
  obtain ⟨v, hv⟩ := finite_linear_maps_exists_nonZeroDivisors ℂ (I := I) R (J → ℂ) d hd
  refine ⟨F v, ?_⟩
  intro S hS
  exact hv ⟨S, hS⟩


end
end SGPT.Foundations.Schemes
