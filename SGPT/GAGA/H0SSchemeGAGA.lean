import SGPT.GAGA.H0SSchemeJacobian

/-!
# GAGA for the sections of `𝒪_X(j)` on a smooth projective complex scheme


* `isJacobianPresentation_chartEquations`: the equations `chartEquations f E` of the affine
  pieces `X ∩ D₊(xᵢ)` (generators of `ker(ℂ[t] → Γ(X, Uᵢ))`) satisfy the Jacobian criterion
  for the embedding `X(ℂ) → ℙᴺ` (`IsJacobianPresentation`).
* **`eventually_hyperplaneSectionsPolynomial'`**: for `j ≫ 0`, every holomorphic section of
  `((𝒪_X(1), h_FS)^an)^{⊗ j}` is `P(x/xᵢ) xᵢ^j` for a homogeneous polynomial `P` of degree `j`
  (the `HyperplaneSectionsPolynomial`); more generally for every smooth metric `H`
  on `𝒪_X(1)` (`eventually_sectionsPolynomial'`).
* **`eventually_schemeSectionsAlgebraic'`**: GAGA for these sections (lane GAGAMULT2's
  `SchemeSectionsAlgebraic`), and **`multiplierIdealAlgebraic`**: lane GAGAMULT's
  `MultiplierIdealAlgebraic` holds for every smooth projective complex scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0S

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult SGPT.Projective
  SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0sGagaTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0sGagaCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0sGagaManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **The equations of the affine pieces of `X` satisfy the Jacobian criterion.** -/
theorem isJacobianPresentation_chartEquations :
    IsJacobianPresentation (n := n) (projectivePoint f E n) (chartEquations f E) where
  vanish i j y hy := by
    obtain ⟨p, hp⟩ := hy
    obtain ⟨hi, hc⟩ := affineCoords_of_mem_range f E n i hp
    have h := eval_eq_zero_of_mem_ker f E n i (chartEquations_mem f E i j) hi
    rwa [hc] at h
  zero i y hy := by
    have hker : RingHom.ker (affinePresentation f E i) ≤
        RingHom.ker (MvPolynomial.eval (fun a => y a)) :=
      ker_le_of_chartEquations f E i fun j => RingHom.mem_ker.mpr (hy j)
    obtain ⟨p, hi, hc⟩ := exists_point_of_eval_eq_zero f E n i y fun P hP =>
      RingHom.mem_ker.mp (hker hP)
    exact ⟨p, by rw [projectivePoint_eq_affinePoint f E n i hi, hc]⟩
  jacobian p i hsrc w hw := by
    have hpi := (projectivePoint_mem_source_iff f E n i p).mp hsrc
    rw [affineChart_projectivePoint f E n i hpi] at hw
    obtain ⟨v, hv⟩ := exists_fderiv_eq_of_jacobian f E n p i hpi w hw
    refine ⟨v, ?_⟩
    set e := complexChartAt (n := n) p
    have hp : p ∈ e.val.source := mem_complexChartAt_source p
    have hdom : e.val p ∈ coordChartDomain f E n i e :=
      ⟨e.val.map_source hp, by
        show schemeComplexPointImage f (e.val.symm (e.val p)) ∈ coordOpen E i
        rw [e.val.left_inv hp]; exact hpi⟩
    have hev : chartMap (n := n) (projectivePoint f E n) p i =ᶠ[𝓝 (e.val p)]
        affineCoordMap f E n i e := by
      filter_upwards [(isOpen_coordChartDomain f E n i e).mem_nhds hdom] with z hz
      exact chartMap_eq_affineCoordMap f E n p i hz
    rw [hev.fderiv_eq]
    exact hv

variable [CompactSpace (SchemeComplexPoint f)]

/-- **Holomorphic sections of `𝒪_X(j)` are polynomials, `j ≫ 0`**, for every smooth metric `H`
on `𝒪_X(1)`: every holomorphic section `s` of `((𝒪_X(1), H)^an)^{⊗ j}` is `P(x/xᵢ) xᵢ^j` for a
homogeneous polynomial `P` of degree `j`. -/
theorem eventually_sectionsPolynomial' (H : SchemeLineBundleMetric f n E (hyperplaneBundle E)) :
    ∀ᶠ j in atTop, ∀ s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j,
      ∃ P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ, P.IsHomogeneous j ∧
        ∀ (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
          schemeComplexPointImage f p ∈ coordOpen E i →
            coef f E n H s i p = MvPolynomial.eval (fun k => schemeOpenRegularFunction f n E
              (coordOpen E i) (ratio E i k) p) P :=
  eventually_sectionsPolynomial f E n H (isJacobianPresentation_chartEquations f E n)

/-- **FS-POS's `HyperplaneSectionsPolynomial` holds for `j ≫ 0`.** -/
theorem eventually_hyperplaneSectionsPolynomial' :
    ∀ᶠ j in atTop, HyperplaneSectionsPolynomial f n E j :=
  eventually_hyperplaneSectionsPolynomial f E n (isJacobianPresentation_chartEquations f E n)

/-- **GAGA for the sections of `𝒪_X(j)`, `j ≫ 0`** (the `SchemeSectionsAlgebraic`
for `𝒪_X(1)` with the Fubini–Study metric). -/
theorem eventually_schemeSectionsAlgebraic' :
    ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n) j :=
  eventually_schemeSectionsAlgebraic f E n (isJacobianPresentation_chartEquations f E n)

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- **Multiplier ideals are algebraic** (the `MultiplierIdealAlgebraic`): for every
smooth projective complex scheme `X` (relative dimension `n`, closed projective embedding `E`),
every quasi-psh `φ` on `X(ℂ)` and `c > 0`, `𝓘(cφ) ⊆ alg(𝓘(cφ))^an`. -/
theorem multiplierIdealAlgebraic : SGPT.NAPotential.Berkovich.MultiplierIdealAlgebraic f n E := by
  let := E.isSeparated
  let := E.quasiCompact
  exact multiplierIdealAlgebraic_of_jacobianPresentation f E n
    (isJacobianPresentation_chartEquations f E n)

/-! ### Unconditional consequences for non-Archimedean potentials -/

section Consequences

open SGPT.NAPotential.Berkovich

variable {f} [IsProper f]

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- **`def:NApotential:L975`, existence of the limit**: for `φ ∈ PSH(X, θ)` and `v ∈ X^An`,
`k⁻¹ v(𝓘(kφ)) → v(φ)`. -/
theorem tendsto_potentialVal {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => v.multiplierIdealVal n E φ k / k) atTop (𝓝 (v.potentialVal n E φ)) :=
  BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic f E n) hφ v

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- `v(φ) = sup_{k ≥ 1} k⁻¹ v(𝓘(kφ))`. -/
theorem potentialVal_eq_iSup {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ k : ℕ, ⨆ (_ : 0 < k), v.multiplierIdealVal n E φ k / k :=
  BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic f E n) hφ v

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- **`eq:varphiAnalt`**: `v(φ) = sup_j 2^{-j} v(𝓘(2^j φ))`. -/
theorem potentialVal_eq_iSup_dyadic {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ j : ℕ, v.multiplierIdealVal n E φ (2 ^ j) / (2 ^ j : ℕ) :=
  BerkovichPoint.potentialVal_eq_iSup_dyadic_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic f E n) hφ v

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- Monotonicity: `φ ≤ ψ ⟹ φ^An ≤ ψ^An` on `X^An`. -/
theorem potentialAn_mono {φ ψ : SchemeComplexPoint f → EReal}
    {θ θ' : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ' ψ)
    (hle : ∀ x, φ x ≤ ψ x) (v : BerkovichPoint f) :
    potentialAn n E φ v ≤ potentialAn n E ψ v :=
  BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic f E n) hφ hψ hle v

end Consequences

end SGPT.GAGA.H0S
