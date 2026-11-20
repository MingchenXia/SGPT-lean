import SGPT.NAPotential.FSPosAlgebraic

/-!
# Homogeneous polynomials as algebraic sections of `𝒪_X(j)`

Blueprint `claude-fs-pos:poly-sections`.

Let `X` be smooth projective over `ℂ` with closed projective embedding `E.map : X ⟶ ℙᴺ` and
`𝒪_X(1) = E.map^* 𝒪(1)`.

* `polySection E P hP`: a homogeneous polynomial `P ∈ ℂ[x₀, …, x_N]` of degree `j` gives a
  global algebraic section `P|_X ∈ H⁰(X, 𝒪_X(j))`, glued from its coefficients
  `P(x₀/xᵢ, …, x_N/xᵢ)` in the frames `xᵢ^j` (`algCoef_polySection`).
* `HyperplaneSectionsPolynomial j` (statement only): every holomorphic section of
  `𝒪_X(j)^an` is given, in every frame `xᵢ^j`, by `P(x₀/xᵢ, …, x_N/xᵢ)` for a homogeneous
  polynomial `P` of degree `j` (surjectivity of `ℂ[x]_j → H⁰(X(ℂ), 𝒪(j)^an)`; this is the form in
  which the cone theorem `SGPT.GAGA.H0.exists_isHomogeneous_eq_of_isLocallyHolomorphicOn`
  produces sections).
* `hyperplaneSectionsAlgebraic_of_polynomial`: it implies `HyperplaneSectionsAlgebraic j`, hence
  (`multiplierIdealAlgebraic_of_hyperplaneSectionsPolynomial`) `MultiplierIdealAlgebraic` as soon
  as it holds for `j ≫ 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.FSPos

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Opposite
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of a homogeneous polynomial at scaled arguments. -/
theorem eval₂_mul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (c : R →+* S) (y : σ → S) (u : S) {P : MvPolynomial σ R} {j : ℕ}
    (hP : P.IsHomogeneous j) :
    MvPolynomial.eval₂ c (fun k => u * y k) P = u ^ j * MvPolynomial.eval₂ c y P := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hP.degree_eq_sum_deg_support hd]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

section PolySec

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-! ### Polynomial sections -/

/-- The structural constants on `Uᵢ`. -/
def constMap (i : Fin (E.ambientDimension + 1)) : ℂ →+* X.sheaf.obj.obj (op (coordOpen E i)) :=
  (X.sheaf.obj.map (homOfLE (le_top : coordOpen E i ≤ ⊤)).op).hom.comp (schemeGlobalConstants f)

/-- `P(x₀/xᵢ, …, x_N/xᵢ) ∈ Γ(X, Uᵢ)`. -/
def polyCoef (i : Fin (E.ambientDimension + 1))
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) : X.sheaf.obj.obj (op (coordOpen E i)) :=
  MvPolynomial.eval₂ (constMap E i) (fun k => ratio E i k) P

/-- The transition `xᵢ / x_l` of the atlas frames on `Uᵢ ∩ U_l`. -/
def frameTr (i l : Fin (E.ambientDimension + 1)) :
    X.sheaf.obj.obj (op (coordOpen E i ⊓ coordOpen E l)) :=
  (localBundleFrameTransition ((hyperplaneAtlas E).frame i) ((hyperplaneAtlas E).frame l)
    (homOfLE inf_le_left) (homOfLE inf_le_right) :)

/-- `x_k/x_l = (x_i/x_l) · (x_k/x_i)` on `Uᵢ ∩ U_l`, the transition of the frames being
`x_i/x_l`. -/
theorem ratio_transition (i l k : Fin (E.ambientDimension + 1)) :
    X.sheaf.obj.map (homOfLE (inf_le_right : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E l)).op
        (ratio E l k) =
      frameTr E i l *
        X.sheaf.obj.map (homOfLE (inf_le_left : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E i)).op
          (ratio E i k) := by
  have h := localBundleFrameTransition_coefficients ((hyperplaneAtlas E).frame i)
    ((hyperplaneAtlas E).frame l) (homOfLE inf_le_left) (homOfLE inf_le_right)
    (coordSection E k (coordOpen E i ⊓ coordOpen E l))
  rw [coordCoef_restrict, coordCoef_restrict, coordCoef_atlas, coordCoef_atlas] at h
  exact h

theorem constMap_restrict (i l : Fin (E.ambientDimension + 1)) (b : ℂ) :
    X.sheaf.obj.map (homOfLE (inf_le_right : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E l)).op
        (constMap E l b) =
      X.sheaf.obj.map (homOfLE (inf_le_left : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E i)).op
        (constMap E i b) := by
  simp only [constMap, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  rfl

/-- The coefficients `P(x/xᵢ)` obey the transition law of the frames `xᵢ^j`. -/
theorem polyCoef_transition (i l : Fin (E.ambientDimension + 1))
    {P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ} {j : ℕ} (hP : P.IsHomogeneous j) :
    X.sheaf.obj.map (homOfLE (inf_le_right : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E l)).op
        (polyCoef E l P) =
      frameTr E i l ^ j *
        X.sheaf.obj.map (homOfLE (inf_le_left : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E i)).op
          (polyCoef E i P) := by
  unfold polyCoef
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  have hc : (X.sheaf.obj.map (homOfLE (inf_le_right :
      coordOpen E i ⊓ coordOpen E l ≤ coordOpen E l)).op).hom.comp (constMap E l) =
      (X.sheaf.obj.map (homOfLE (inf_le_left :
        coordOpen E i ⊓ coordOpen E l ≤ coordOpen E i)).op).hom.comp (constMap E i) := by
    ext b
    exact constMap_restrict E i l b
  have hr : ((X.sheaf.obj.map (homOfLE (inf_le_right :
      coordOpen E i ⊓ coordOpen E l ≤ coordOpen E l)).op).hom ∘ fun k => ratio E l k) =
      fun k => frameTr E i l *
        ((X.sheaf.obj.map (homOfLE (inf_le_left :
          coordOpen E i ⊓ coordOpen E l ≤ coordOpen E i)).op).hom ∘ fun k => ratio E i k) k := by
    funext k
    exact ratio_transition E i l k
  rw [hc, hr, eval₂_mul_of_isHomogeneous _ _ _ hP]

/-- The local section `P(x/xᵢ) xᵢ^j` of `𝒪_X(j)` on `Uᵢ`. -/
def polyLocal (j : ℕ) (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    (i : (hyperplaneAtlas E).I) :
    bundleSections (bundleTensorPower (hyperplaneBundle E) j) ((hyperplaneAtlas E).opens i) :=
  ((((hyperplaneAtlas E).frame i).tensorPower j).coefficients (𝟙 _)).symm (polyCoef E i P)

theorem polyLocal_coefficients_restrict (j : ℕ)
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) (i : (hyperplaneAtlas E).I)
    {W : X.Opens} (h : W ⟶ (hyperplaneAtlas E).opens i) :
    (((hyperplaneAtlas E).frame i).tensorPower j).coefficients h
        ((bundleTensorPower (hyperplaneBundle E) j).val.map h.op (polyLocal E j P i)) =
      X.sheaf.obj.map h.op (polyCoef E i P) := by
  have h' := (((hyperplaneAtlas E).frame i).tensorPower j).coefficients_restrict (𝟙 _) h
    (polyLocal E j P i)
  simpa only [Category.comp_id, polyLocal, LinearEquiv.apply_symm_apply] using h'

theorem polyLocal_compatible {j : ℕ} {P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ}
    (hP : P.IsHomogeneous j) :
    TopCat.Presheaf.IsCompatible (bundleTensorPower (hyperplaneBundle E) j).val.presheaf
      (hyperplaneAtlas E).opens (polyLocal E j P) := by
  intro i l
  let lft : (hyperplaneAtlas E).opens i ⊓ (hyperplaneAtlas E).opens l ⟶
    (hyperplaneAtlas E).opens i := homOfLE inf_le_left
  let rgt : (hyperplaneAtlas E).opens i ⊓ (hyperplaneAtlas E).opens l ⟶
    (hyperplaneAtlas E).opens l := homOfLE inf_le_right
  apply ((((hyperplaneAtlas E).frame l).tensorPower j).coefficients rgt).injective
  calc
    (((hyperplaneAtlas E).frame l).tensorPower j).coefficients rgt
        ((bundleTensorPower (hyperplaneBundle E) j).val.map lft.op (polyLocal E j P i)) =
        frameTr E i l ^ j *
          (((hyperplaneAtlas E).frame i).tensorPower j).coefficients lft
            ((bundleTensorPower (hyperplaneBundle E) j).val.map lft.op (polyLocal E j P i)) :=
      LocalBundleFrame.tensorPower_coefficients_transition _ _ lft rgt _ _
    _ = frameTr E i l ^ j *
          X.sheaf.obj.map lft.op (polyCoef E i P) := by
      rw [polyLocal_coefficients_restrict]
    _ = X.sheaf.obj.map rgt.op (polyCoef E l P) := (polyCoef_transition E i l hP).symm
    _ = (((hyperplaneAtlas E).frame l).tensorPower j).coefficients rgt
          ((bundleTensorPower (hyperplaneBundle E) j).val.map rgt.op (polyLocal E j P l)) :=
      (polyLocal_coefficients_restrict E j P l rgt).symm

theorem polySection_existsUnique {j : ℕ} {P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ}
    (hP : P.IsHomogeneous j) :
    ∃! z : bundlePowerGlobalSections (hyperplaneBundle E) j, ∀ i,
      (bundleTensorPower (hyperplaneBundle E) j).val.map (homOfLE le_top).op z =
        polyLocal E j P i := by
  have hcover : (⊤ : X.Opens) ≤ iSup (hyperplaneAtlas E).opens := by
    intro x _
    obtain ⟨i, hi⟩ := (hyperplaneAtlas E).covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let S : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(bundleTensorPower (hyperplaneBundle E) j).val.presheaf,
      (bundleTensorPower (hyperplaneBundle E) j).isSheaf⟩
  exact TopCat.Sheaf.existsUnique_gluing' S (hyperplaneAtlas E).opens ⊤
    (fun _ => homOfLE le_top) hcover (polyLocal E j P) (polyLocal_compatible E hP)

/-- **The algebraic section `P|_X ∈ H⁰(X, 𝒪_X(j))` of a homogeneous polynomial `P` of degree
`j`.** -/
def polySection {j : ℕ} (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    (hP : P.IsHomogeneous j) : bundlePowerGlobalSections (hyperplaneBundle E) j :=
  Classical.choose (polySection_existsUnique E hP).exists

/-- In the frame `xᵢ^j`, the coefficient of `P|_X` is `P(x₀/xᵢ, …, x_N/xᵢ)`. -/
theorem algCoef_polySection {j : ℕ} (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    (hP : P.IsHomogeneous j) (i : Fin (E.ambientDimension + 1)) :
    algCoef ((hyperplaneAtlas E).frame i) j (polySection E P hP) = polyCoef E i P := by
  have h := Classical.choose_spec (polySection_existsUnique E hP).exists i
  unfold algCoef
  change (((hyperplaneAtlas E).frame i).tensorPower j).coefficients (𝟙 _)
    ((bundleTensorPower (hyperplaneBundle E) j).val.map (homOfLE le_top).op
      (polySection E P hP)) = _
  unfold polySection
  rw [h, polyLocal, LinearEquiv.apply_symm_apply]

/-! ### Analytic values -/

end PolySec

section Analytic

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsSeparated f] [QuasiCompact f]

local instance fsPosSecTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fsPosSecCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance fsPosSecManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- Structural constants have constant analytic functions. -/
theorem schemeOpenRegularFunction_constMap (i : Fin (E.ambientDimension + 1)) (b : ℂ)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    schemeOpenRegularFunction f n E (coordOpen E i) (constMap E i b) p = b := by
  have h1 := schemeOpenRegularFunction_restrict f n E (coordOpen E i) ⊤ le_top
    (schemeGlobalConstants f b) hp
  change schemeOpenRegularFunction f n E (coordOpen E i)
    (X.presheaf.map (homOfLE (le_top : coordOpen E i ≤ ⊤)).op (schemeGlobalConstants f b)) p = b
  rw [h1, schemeOpenRegularFunction_apply f n E ⊤ _ p trivial, ← NativeHolGerm.eval_chartEquiv]
  have h2 := stalkToModel_constants f n p b
  change HolGerm.eval (stalkToModel f n p _) = b
  rw [h2]
  rfl

/-- The analytic function of `P(x/xᵢ)` is `P` evaluated at the analytic ratios. -/
theorem schemeOpenRegularFunction_polyCoef (i : Fin (E.ambientDimension + 1))
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    schemeOpenRegularFunction f n E (coordOpen E i) (polyCoef E i P) p =
      MvPolynomial.eval (fun k => schemeOpenRegularFunction f n E (coordOpen E i)
        (ratio E i k) p) P := by
  induction P using MvPolynomial.induction_on with
  | C b =>
    simp only [polyCoef, MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact schemeOpenRegularFunction_constMap f n E i b p hp
  | add P Q hP hQ =>
    simp only [polyCoef, MvPolynomial.eval₂_add, map_add] at hP hQ ⊢
    rw [schemeOpenRegularFunction_add f n E (coordOpen E i) _ _ hp]
    beta_reduce
    rw [hP, hQ]
  | mul_X P k hP =>
    simp only [polyCoef, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul,
      MvPolynomial.eval_X] at hP ⊢
    rw [schemeOpenRegularFunction_mul f n E (coordOpen E i) _ _ hp]
    beta_reduce
    rw [hP]

/-! ### Reduction of GAGA for sections to polynomial sections -/

/-- **Polynomiality of the holomorphic sections of `𝒪_X(j)`** (statement only): every
holomorphic section `s` of `((𝒪_X(1), h_FS)^an)^{⊗ j}` is given by a homogeneous polynomial `P` of
degree `j`: in every frame `xᵢ^j`, `s = P(x₀/xᵢ, …, x_N/xᵢ) · xᵢ^j` on `Uᵢ(ℂ)`. -/
def HyperplaneSectionsPolynomial (j : ℕ) : Prop :=
  ∀ s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E)
      (fubiniStudyMetric f E n)) unit j,
    ∃ P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ, P.IsHomogeneous j ∧
      ∀ (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
        schemeComplexPointImage f p ∈ coordOpen E i →
          (twistedFrame f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n)
              ((hyperplaneAtlas E).frame i) j).val.continuousLinearMapAt ℂ p (s p) =
            MvPolynomial.eval (fun k => schemeOpenRegularFunction f n E (coordOpen E i)
              (ratio E i k) p) P

/-- Polynomial sections are analytifications of algebraic sections: `HyperplaneSectionsPolynomial`
implies GAGA for the sections of `𝒪_X(j)`. -/
theorem schemeSectionsAlgebraic_of_polynomial {j : ℕ}
    (h : HyperplaneSectionsPolynomial f n E j) :
    SchemeSectionsAlgebraic f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n) j := by
  intro s
  obtain ⟨P, hP, hs⟩ := h s
  refine ⟨polySection E P hP, fun i p hp => ?_⟩
  rw [hs i p hp, algCoef_polySection E P hP i]
  exact (schemeOpenRegularFunction_polyCoef f n E i P p hp).symm

omit [IsSeparated f] [QuasiCompact f] in
/-- `HyperplaneSectionsPolynomial j ⟹ HyperplaneSectionsAlgebraic j`. -/
theorem hyperplaneSectionsAlgebraic_of_polynomial {j : ℕ}
    (h : letI := E.isSeparated; letI := E.quasiCompact; HyperplaneSectionsPolynomial f n E j) :
    HyperplaneSectionsAlgebraic f n E j := by
  let := E.isSeparated
  let := E.quasiCompact
  exact schemeSectionsAlgebraic_of_polynomial f n E h

omit [IsSeparated f] [QuasiCompact f] in
/-- **`MultiplierIdealAlgebraic` from the polynomiality of the sections of `𝒪_X(j)`, `j ≫ 0`.** -/
theorem multiplierIdealAlgebraic_of_hyperplaneSectionsPolynomial
    (h : ∀ᶠ j in atTop,
      letI := E.isSeparated; letI := E.quasiCompact; HyperplaneSectionsPolynomial f n E j) :
    MultiplierIdealAlgebraic f n E :=
  multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic f n E
    (h.mono fun _ hj => hyperplaneSectionsAlgebraic_of_polynomial f n E hj)

end Analytic

end SGPT.NAPotential.FSPos
