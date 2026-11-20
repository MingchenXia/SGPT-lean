import SGPT.Okounkov.SchemeComplexPointStalkEvaluation
import SGPT.Foundations.Schemes.PolynomialProjectiveAnalyticCompactness
import SGPT.Foundations.Schemes.CotangentSheaf

/-!
# chart maps to `ℙʳ` given by regular functions

Source: `rmk:bdiv:L749` (GAGA on the algebraized models of the book's blow-up system).

For an open `U` of a complex scheme `X` and regular functions `c_k ∈ Γ(X, U)` with `c_j = 1`,
`chartMap f U j c : U → D₊(y_j) ⊆ ℙʳ` is `U → Spec Γ(X, U) → Spec ℂ[y/y_j]`, `y_k/y_j ↦ c_k`.
It lies over `ℂ` (`chartMap_structure`) and sends a complex point `q` of `U` to the point
`[c₀(q) : ⋯ : c_r(q)]` (`comp_chartMap`); the value of a regular function at a complex point is
read through `U → Spec Γ(X, U)` (`stalkEval_germ_eq_specPreimage`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD6

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov

/-- The stalk isomorphism of `Spec ℂ` at its point. -/
def specStalkIso : (Spec (.of ℂ)).presheaf.stalk (default : Spec (.of ℂ)) ≅ CommRingCat.of ℂ :=
  (Spec (.of ℂ)).presheaf.stalkCongr
    (.of_eq (Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ))) ≪≫
      stalkClosedPointIso (.of ℂ)

theorem specStalkIso_germ :
    (Spec (.of ℂ)).presheaf.germ ⊤ default trivial ≫ specStalkIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).hom := by
  dsimp only [specStalkIso, Iso.trans_hom]
  rw [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes]
  exact germ_stalkClosedPointIso_hom (.of ℂ)

theorem stalkEval_def {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) :
    schemeComplexPointStalkEval f p = (p.val.stalkMap default ≫ specStalkIso.hom).hom := rfl

/-- The ring map of a complex point of `U` read through `U ⟶ Spec Γ(X, U)`. -/
theorem specPreimage_toSpecΓ {X : Scheme} (U : X.Opens) (q : Spec (.of ℂ) ⟶ U.toScheme) :
    Spec.preimage (q ≫ U.toSpecΓ) = U.topIso.inv ≫ q.appTop ≫ (Scheme.ΓSpecIso (.of ℂ)).hom := by
  apply Spec.map_injective
  rw [Spec.map_preimage, Scheme.Opens.toSpecΓ, ← Category.assoc, Scheme.toSpecΓ_naturality,
    ← SpecMap_ΓSpecIso_hom]
  simp only [Spec.map_comp, Category.assoc]

/-- The value of a global section at a complex point, read on the point's stalk. -/
theorem germ_top_stalkMap_specStalkIso {Y : Scheme} (q : Spec (.of ℂ) ⟶ Y) :
    Y.presheaf.germ ⊤ (q default) trivial ≫ q.stalkMap default ≫ specStalkIso.hom =
      q.appTop ≫ (Scheme.ΓSpecIso (.of ℂ)).hom := by
  have h := Scheme.Hom.germ_stalkMap q ⊤ default trivial
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc]
  erw [specStalkIso_germ]

theorem germ_stalkMap_ι {X : Scheme} (U : X.Opens) (y : U.toScheme) (hy : U.ι y ∈ U) :
    X.presheaf.germ U (U.ι y) hy ≫ U.ι.stalkMap y =
      U.topIso.inv ≫ U.toScheme.presheaf.germ ⊤ y trivial := by
  have h1 := Scheme.Opens.stalkIso_inv U y
  have h2 := Scheme.Opens.germ_stalkIso_inv U ⊤ y trivial
  erw [← h1, ← h2, ← Category.assoc]
  congr 1
  rw [Scheme.Opens.topIso_inv]
  exact (X.presheaf.germ_res _ _ _).symm

/-- **Evaluation at a complex point through `U ⟶ Spec Γ(X, U)`.** -/
theorem stalkEval_germ_eq_specPreimage {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (U : X.Opens)
    (q : Spec (.of ℂ) ⟶ U.toScheme) (hq : (q ≫ U.ι) ≫ f = 𝟙 _) (hU : U.ι (q default) ∈ U)
    (r : Γ(X, U)) :
    schemeComplexPointStalkEval f ⟨q ≫ U.ι, hq⟩ (X.presheaf.germ U (U.ι (q default)) hU r) =
      Spec.preimage (q ≫ U.toSpecΓ) r := by
  have h : X.presheaf.germ U (U.ι (q default)) hU ≫
      (q ≫ U.ι).stalkMap default ≫ specStalkIso.hom =
        U.topIso.inv ≫ q.appTop ≫ (Scheme.ΓSpecIso (.of ℂ)).hom := by
    rw [Scheme.Hom.stalkMap_comp, Category.assoc, ← Category.assoc _ (U.ι.stalkMap _)]
    erw [germ_stalkMap_ι U (q default) hU]
    rw [Category.assoc, germ_top_stalkMap_specStalkIso]
  have h' := congrArg (fun k => k r) (congrArg CommRingCat.Hom.hom h)
  rw [specPreimage_toSpecΓ]
  exact h'

/-! ### Chart maps to `ℙʳ` given by regular functions -/

section ChartMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (U : X.Opens) {r : ℕ}

/-- The constants `ℂ → Γ(X, U)` of a complex scheme. -/
def constRingHom : ℂ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ f.appTop ≫ X.presheaf.map U.leTop.op).hom

/-- The ring map of the chart `D₊(y_j) = Spec ℂ[y/y_j] → Γ(X, U)`, `y_k/y_j ↦ c_k`. -/
def chartRingHom (j : Fin (r + 1)) (c : Fin (r + 1) → Γ(X, U)) :
    polynomialProjCoordinateRing ℂ r j →+* Γ(X, U) :=
  (MvPolynomial.eval₂Hom (constRingHom f U) (fun a => c (j.succAbove a))).comp
    (polynomialProjCoordinateEquiv ℂ r j).toRingEquiv.toRingHom

/-- **The chart map** `U → D₊(y_j) ⊆ ℙʳ` given by the regular functions `c_k` (`c_j = 1`). -/
def chartMap (j : Fin (r + 1)) (c : Fin (r + 1) → Γ(X, U)) :
    U.toScheme ⟶ polynomialProj ℂ r :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRingHom f U j c)) ≫
    polynomialProjCoordinateImmersion ℂ r j

theorem toSpecΓ_SpecMap_constRingHom :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (constRingHom f U)) = U.ι ≫ f := by
  have h : CommRingCat.ofHom (constRingHom f U) =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ f.appTop ≫ X.presheaf.map U.leTop.op := rfl
  have h2 := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top U
  rw [h, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc]
  erw [h2]
  rw [Category.assoc,
    ← Category.assoc X.toSpecΓ, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem chartRingHom_algebraMap (j : Fin (r + 1)) (c : Fin (r + 1) → Γ(X, U)) (a : ℂ) :
    chartRingHom f U j c (algebraMap ℂ (polynomialProjCoordinateRing ℂ r j) a) =
      constRingHom f U a := by
  simp [chartRingHom]

/-- The chart map lies over `ℂ`. -/
theorem chartMap_structure (j : Fin (r + 1)) (c : Fin (r + 1) → Γ(X, U)) :
    chartMap f U j c ≫ polynomialProjStructureMap ℂ r = U.ι ≫ f := by
  rw [chartMap, Category.assoc, Category.assoc, polynomialProjCoordinateImmersion_structure]
  have h : affineBaseRingMap ℂ (.of (polynomialProjCoordinateRing ℂ r j)) ≫
      CommRingCat.ofHom (chartRingHom f U j c) = CommRingCat.ofHom (constRingHom f U) := by
    ext a
    exact chartRingHom_algebraMap f U j c a
  rw [affineStructuralMap, ← Spec.map_comp, h, toSpecΓ_SpecMap_constRingHom]

/-- The ring map of a complex point of `U` is `ℂ`-linear on the constants. -/
theorem specPreimage_constRingHom (q : Spec (.of ℂ) ⟶ U.toScheme) (hq : (q ≫ U.ι) ≫ f = 𝟙 _)
    (a : ℂ) : Spec.preimage (q ≫ U.toSpecΓ) (constRingHom f U a) = a := by
  have h : CommRingCat.ofHom (constRingHom f U) ≫ Spec.preimage (q ≫ U.toSpecΓ) = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc,
      toSpecΓ_SpecMap_constRingHom, ← Category.assoc, hq]
  exact congrArg (fun k => k a) (congrArg CommRingCat.Hom.hom h)

/-- **The complex points of a chart map**: a complex point `q` of `U` goes to the point of `ℙʳ`
with homogeneous coordinates `(c_k(q))_k`. -/
theorem comp_chartMap (j : Fin (r + 1)) (c : Fin (r + 1) → Γ(X, U)) (hc : c j = 1)
    (q : Spec (.of ℂ) ⟶ U.toScheme) (hq : (q ≫ U.ι) ≫ f = 𝟙 _) :
    q ≫ chartMap f U j c = (polynomialProjVectorChartPoint r j
      (fun k => Spec.preimage (q ≫ U.toSpecΓ) (c k))).val := by
  rw [polynomialProjVectorChartPoint_val, chartMap, ← Category.assoc,
    ← Spec.map_preimage (q ≫ U.toSpecΓ), ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  change Spec.preimage (q ≫ U.toSpecΓ) (chartRingHom f U j c x) = _
  obtain ⟨p, rfl⟩ := (polynomialProjCoordinateEquiv ℂ r j).symm.surjective x
  simp only [chartRingHom, RingHom.comp_apply]
  change Spec.preimage (q ≫ U.toSpecΓ) (MvPolynomial.eval₂Hom (constRingHom f U)
      (fun a => c (j.succAbove a)) ((polynomialProjCoordinateEquiv ℂ r j)
        ((polynomialProjCoordinateEquiv ℂ r j).symm p))) =
    polynomialProjVectorChartAlgebraPoint r j _ ((polynomialProjCoordinateEquiv ℂ r j).symm p)
  rw [AlgEquiv.apply_symm_apply]
  change _ = MvPolynomial.aeval (polynomialProjVectorRatios r j _)
    ((polynomialProjCoordinateEquiv ℂ r j) ((polynomialProjCoordinateEquiv ℂ r j).symm p))
  rw [AlgEquiv.apply_symm_apply]
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
      rw [specPreimage_constRingHom f U q hq]
      rfl
  | add p₁ p₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | mul_X p a h =>
      simp only [Spec.preimage_map] at h ⊢
      simp only [map_mul, h, MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X,
        polynomialProjVectorRatios, hc, map_one, div_one]

end ChartMap

end SGPT.BDivisor.BD6