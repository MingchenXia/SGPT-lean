import SGPT.Checks.Comparison.BJModel2GaussFlag

/-!
# `σ(v)(t) = 1`: the Gauss point on the ideal of the central fibre (lane BJ-MODEL2, step R1(e))

Source: `chapter_NApotential.tex`, `eq:Gext` (`σ(v)(t) = 1`), and [BJ22]
(`references/bj22-trivval`), §1.3, §2.1. Blueprint: `claude-bj-model2.tex`.

The value of the Gauss point `σ(v) ∈ (X × ℙ¹)^An` on the ideal `𝓘` of the central fibre is the
value on the ideal `𝓘₀` of `0 ∈ ℙ¹` of the point of `ℙ¹` given by `Spec K(t) → D₊(x₀) ⊆ ℙ¹` with the
Gauss valuation (`idealVal_comap_fieldBerkovichPoint` for `pr₂`). On the chart
`D₊(x₀) = Spec ℂ[t]` this point is `ord₀` on `ℂ(t)`:

* `valuation_stalk_chartZero`: an element of `𝒪_{ℙ¹,0} ≅ ℂ[t]_{(t)}` is `a/b` with `b(0) ≠ 0`,
  and its value is the Gauss value of `a`, which is `≥ 0`, and `≥ 1` iff `a(0) = 0`;
* `lineGaussPoint_isCenter`: hence `0` is the centre;
* `idealVal_lineGaussPoint_zeroIdeal`: the stalk of `𝓘₀` at `0` lies in the maximal ideal (value
  `≥ 1`) and contains the germ of `t` (value `1`), so the value is `1`.

Consequently (`idealVal_gaussPoint_centralIdeal`) `σ(v)(𝓘) = 1`, and the formulas of
`BJModel2GaussFlag` hold without hypothesis: `σ(v)(t^b 𝔞 · 𝒪_𝒳) = b - φ_𝔞(v)` on the blow-up model
(`idealVal_gaussModelPoint_flagSheaf_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology IsLocalRing
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel FlagIdealBound
open SGPT.NAPotential.Berkovich.BerkovichPoint (specializationMap)
open scoped Polynomial ENNReal

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Chart polynomials and their Gauss values -/

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{0}) (r : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom r) = r :=
  congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso R).inv_hom_id

/-- The coordinate ring `ℂ[x₁/x₀]` of the chart `D₊(x₀)` as polynomials in `t`. -/
def chartPoly : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2) →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X)

theorem chartPoly_eval_zero (a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) :
    (chartPoly a).eval 0 = evalZero ℂ a := by
  have h : (Polynomial.evalRingHom (0 : ℂ)).comp chartPoly = evalZero ℂ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chartPoly, evalZero]
    · intro i
      simp [chartPoly, evalZero]
  exact RingHom.congr_fun h a

theorem chartPoly_X :
    chartPoly (MvPolynomial.X ⟨1, by decide⟩ : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) =
      Polynomial.X := by
  simp [chartPoly]

section values

variable {K : Type} [Field K] [Algebra ℂ K] (v₀ : SourceRealValuation K)

theorem gaussChartHom_eq (a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) :
    gaussChartHom K a =
      algebraMap K[X] (FractionRing K[X]) ((chartPoly a).map (algebraMap ℂ K)) := by
  have h : gaussChartHom K = (algebraMap K[X] (FractionRing K[X])).comp
      ((Polynomial.mapRingHom (algebraMap ℂ K)).comp chartPoly) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [gaussChartHom, chartPoly, IsScalarTower.algebraMap_apply ℂ K[X] (FractionRing K[X]),
        Polynomial.algebraMap_apply]
    · intro i
      simp [gaussChartHom, chartPoly]
  exact RingHom.congr_fun h a

theorem gaussExtension_gaussChartHom (a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) :
    gaussExtension v₀ (gaussChartHom K a) = gaussVal v₀ ((chartPoly a).map (algebraMap ℂ K)) := by
  rw [gaussChartHom_eq]
  exact gaussExtension_algebraMap v₀ _

theorem valuation_algebraMap_nonneg (c : ℂ) : 0 ≤ v₀ (algebraMap ℂ K c) := by
  by_cases hc : c = 0
  · rw [hc, map_zero, v₀.map_zero]
    exact le_top
  · rw [v₀.map_complex' c hc]

theorem natCast_withTop_nonneg (i : ℕ) : (0 : WithTop ℝ) ≤ ((i : ℝ) : WithTop ℝ) :=
  WithTop.coe_nonneg.mpr (Nat.cast_nonneg i)

theorem gaussVal_chart_nonneg (a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) :
    0 ≤ gaussVal v₀ ((chartPoly a).map (algebraMap ℂ K)) := by
  rw [le_gaussVal_iff]
  intro i
  rw [Polynomial.coeff_map]
  exact add_nonneg (valuation_algebraMap_nonneg v₀ _) (natCast_withTop_nonneg i)

theorem one_le_gaussVal_chart {a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)}
    (ha : evalZero ℂ a = 0) : 1 ≤ gaussVal v₀ ((chartPoly a).map (algebraMap ℂ K)) := by
  rw [le_gaussVal_iff]
  intro i
  rw [Polynomial.coeff_map]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [Polynomial.coeff_zero_eq_eval_zero, chartPoly_eval_zero, ha, map_zero, v₀.map_zero,
      WithTop.top_add]
    exact le_top
  · have h1 : (1 : WithTop ℝ) ≤ ((i : ℝ) : WithTop ℝ) := by
      have : (1 : ℝ) ≤ i := by exact_mod_cast hi
      exact_mod_cast this
    exact h1.trans (le_add_of_nonneg_left (valuation_algebraMap_nonneg v₀ _))

theorem gaussVal_chart_eq_zero {b : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)}
    (hb : evalZero ℂ b ≠ 0) : gaussVal v₀ ((chartPoly b).map (algebraMap ℂ K)) = 0 := by
  refine le_antisymm ?_ (gaussVal_chart_nonneg v₀ b)
  have h := gaussVal_le v₀ ((chartPoly b).map (algebraMap ℂ K)) 0
  rwa [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, chartPoly_eval_zero,
    v₀.map_complex' _ hb, Nat.cast_zero, WithTop.coe_zero, add_zero] at h

theorem gaussVal_chart_X :
    gaussVal v₀ ((chartPoly (MvPolynomial.X ⟨1, by decide⟩ :
      ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))).map (algebraMap ℂ K)) = 1 := by
  rw [chartPoly_X, Polynomial.map_X]
  exact gaussVal_X v₀

end values

/-! ### The chart point `t = 0` and the Gauss point of the chart -/

section chart

variable {K : Type} [Field K] [Algebra ℂ K] (v₀ : SourceRealValuation K)

/-- The point `t = 0` of the chart `Spec ℂ[t]`. -/
abbrev chartZero : Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))) :=
  Spec.map (CommRingCat.ofHom (evalZero ℂ)) (closedPoint ℂ)

theorem mem_chartZero_iff (a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) :
    a ∈ chartZero.asIdeal ↔ evalZero ℂ a = 0 := by
  change evalZero ℂ a ∈ maximalIdeal ℂ ↔ _
  rw [maximalIdeal_eq_bot, Submodule.mem_bot]

variable (K) in
/-- The morphism `Spec K(t) ⟶ Spec ℂ[t]` of `t ↦ t`. -/
abbrev chartGauss :
    Spec (.of (FractionRing K[X])) ⟶ Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))) :=
  Spec.map (CommRingCat.ofHom (gaussChartHom K))

theorem fieldPt_chartGauss_specializes : fieldPt (chartGauss K) ⤳ chartZero := by
  refine (PrimeSpectrum.le_iff_specializes _ _).mp ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp ?_)
  intro a ha
  have h1 : gaussChartHom K a = 0 := by
    have : gaussChartHom K a ∈ maximalIdeal (FractionRing K[X]) := ha
    rwa [maximalIdeal_eq_bot, Submodule.mem_bot] at this
  rw [gaussChartHom_eq, map_eq_zero_iff _ (IsFractionRing.injective K[X] _),
    Polynomial.map_eq_zero_iff (algebraMap ℂ K).injective] at h1
  rw [mem_chartZero_iff, ← chartPoly_eval_zero, h1, Polynomial.eval_zero]

/-- The map `𝒪_{ℂ[t],c} → K(t)` of the Gauss point on germs of global sections. -/
theorem fieldEmb_chartGauss_germ {c : Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))}
    (hs : fieldPt (chartGauss K) ⤳ c)
    (r : Γ(Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))), ⊤)) :
    (fieldEmb (chartGauss K)).hom ((specializationMap hs).hom
      ((Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))).presheaf.germ ⊤ c trivial r)) =
      gaussChartHom K ((Scheme.ΓSpecIso _).hom r) := by
  have key : (Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))).presheaf.germ ⊤ c trivial ≫
      specializationMap hs ≫ fieldEmb (chartGauss K) =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (gaussChartHom K) := by
    unfold specializationMap
    dsimp only [fieldEmb]
    rw [← Category.assoc, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Category.assoc,
      Scheme.residue_descResidueField, Scheme.germ_stalkClosedPointTo_Spec]
  exact congrArg (fun φ => φ.hom r) key

/-- **Values on `𝒪_{ℙ¹,0} ≅ ℂ[t]_{(t)}`**: every element is `a/b` with `b(0) ≠ 0`; its value is the
Gauss value of `a`, and it lies in the maximal ideal iff `a(0) = 0`. -/
theorem valuation_stalk_chartZero
    (s : (Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))).presheaf.stalk chartZero) :
    ∃ a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2),
      gaussExtension v₀ ((fieldEmb (chartGauss K)).hom
        ((specializationMap fieldPt_chartGauss_specializes).hom s)) =
        gaussVal v₀ ((chartPoly a).map (algebraMap ℂ K)) ∧
      (s ∈ maximalIdeal _ ↔ evalZero ℂ a = 0) := by
  let e := Spec.stalkIso (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))) chartZero
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective chartZero.asIdeal.primeCompl
    (show Localization.AtPrime chartZero.asIdeal from e.hom.hom s)
  let θ := (specializationMap (fieldPt_chartGauss_specializes (K := K)) ≫
    fieldEmb (chartGauss K)).hom
  have hθ : ∀ r, θ (e.inv.hom (algebraMap _ (Localization.AtPrime chartZero.asIdeal) r)) =
      gaussChartHom K r := by
    intro r
    have h1 := congrArg (fun φ : CommRingCat.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) ⟶
        (Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))).presheaf.stalk chartZero => φ.hom r)
      (Spec.algebraMap_stalkIso_inv (R := .of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))
        chartZero)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    change θ (e.inv.hom _) = _
    rw [h1]
    change (fieldEmb (chartGauss K)).hom ((specializationMap _).hom _) = _
    rw [fieldEmb_chartGauss_germ, ΓSpecIso_hom_inv_apply]
  have hab' : IsLocalization.mk' (Localization.AtPrime chartZero.asIdeal) a b = e.hom.hom s := hab
  have hs : s = e.inv.hom (IsLocalization.mk' (Localization.AtPrime chartZero.asIdeal) a b) := by
    rw [hab']
    exact (congrArg (fun φ => φ.hom s) e.hom_inv_id).symm
  have hmul : θ s * gaussChartHom K b = gaussChartHom K a := by
    rw [← hθ, ← hθ, hs, ← map_mul, ← map_mul, IsLocalization.mk'_spec]
  have hb : evalZero ℂ b ≠ 0 := fun h => b.2 ((mem_chartZero_iff (b : _)).mpr h)
  refine ⟨a, ?_, ?_⟩
  · have h2 := congrArg (gaussExtension v₀) hmul
    rw [(gaussExtension v₀).map_mul', gaussExtension_gaussChartHom,
      gaussExtension_gaussChartHom, gaussVal_chart_eq_zero v₀ hb, add_zero] at h2
    exact h2
  · have key : ∀ y : Localization.AtPrime chartZero.asIdeal, IsUnit (e.inv.hom y) ↔ IsUnit y :=
      fun y => ⟨fun h => by
        have h' := h.map e.hom.hom
        rwa [show e.hom.hom (e.inv.hom y) = y from congrArg (fun φ => φ.hom y) e.inv_hom_id] at h',
        fun h => h.map e.inv.hom⟩
    rw [hs, mem_maximalIdeal, mem_nonunits_iff, key, ← mem_nonunits_iff, ← mem_maximalIdeal,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (S := Localization.AtPrime chartZero.asIdeal)
        (I := chartZero.asIdeal),
      mem_chartZero_iff]

end chart

/-! ### The Gauss point of `ℙ¹` and its value on the ideal of `0` -/

section line

variable {K : Type} [Field K] [Algebra ℂ K] (v₀ : SourceRealValuation K)

theorem toENNReal_one : toENNReal (1 : WithTop ℝ) = 1 := by
  change toENNReal ((1 : ℝ) : WithTop ℝ) = 1
  rw [toENNReal_coe, ENNReal.ofReal_one]

/-- The Gauss point of `ℙ¹`: the point of `Spec K(t) → D₊(x₀) ⊆ ℙ¹` with the Gauss valuation. -/
abbrev lineGaussPoint : BerkovichPoint (projectiveSpaceStructure ℂ 1) :=
  fieldBerkovichPoint (projectiveSpaceStructure ℂ 1) (gaussLineMap K) (gaussLineMap_structure K)
    (gaussExtension v₀)

theorem lineGaussPoint_support_specializes :
    (lineGaussPoint v₀).support ⤳ lineChart ℂ chartZero :=
  (fieldPt_chartGauss_specializes (K := K)).map (lineChart ℂ).continuous

/-- The values of the Gauss point of `ℙ¹` on the stalk at `0`. -/
theorem lineGaussPoint_valAt (s : (projectiveSpace ℂ 1).presheaf.stalk (lineChart ℂ chartZero)) :
    ∃ a : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2),
      (lineGaussPoint v₀).valAt
        ((specializationMap (lineGaussPoint_support_specializes v₀)).hom s) =
        gaussVal v₀ ((chartPoly a).map (algebraMap ℂ K)) ∧
      (s ∈ maximalIdeal _ → evalZero ℂ a = 0) := by
  obtain ⟨a, ha, hm⟩ := valuation_stalk_chartZero v₀ (((lineChart ℂ).stalkMap chartZero).hom s)
  refine ⟨a, ?_, fun hs => hm.mp ?_⟩
  · change gaussExtension v₀ ((fieldEmb (gaussLineMap K)).hom ((specializationMap _).hom s)) = _
    have := fieldEmb_comp_specializationMap (chartGauss K) (lineChart ℂ)
      (fieldPt_chartGauss_specializes (K := K)) s
    exact (congrArg (gaussExtension v₀) this).trans ha
  · rw [mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu => hs (isUnit_of_map_unit _ s hu)

/-- **The centre of the Gauss point of `ℙ¹` is `0`.** -/
theorem lineGaussPoint_isCenter : (lineGaussPoint v₀).IsCenter (lineChart ℂ chartZero) := by
  refine ⟨lineGaussPoint_support_specializes v₀, fun s => ?_, fun s hs => ?_⟩
  · obtain ⟨a, ha, -⟩ := lineGaussPoint_valAt v₀ s
    rw [ha]
    exact gaussVal_chart_nonneg v₀ a
  · obtain ⟨a, ha, hm⟩ := lineGaussPoint_valAt v₀ s
    rw [ha]
    exact lt_of_lt_of_le zero_lt_one (one_le_gaussVal_chart v₀ (hm hs))

/-- The stalk of the ideal of `0` lies in the maximal ideal of `𝒪_{ℙ¹,0}`. -/
theorem stalkIdeal_zeroIdeal_le :
    stalkIdeal (zeroIdeal ℂ) (lineChart ℂ chartZero) ≤
      maximalIdeal ((projectiveSpace ℂ 1).presheaf.stalk (lineChart ℂ chartZero)) := by
  obtain ⟨U, hU⟩ := exists_affineOpen_mem (lineChart ℂ chartZero)
  rw [stalkIdeal_eq_map (zeroIdeal ℂ) U hU, Ideal.map_le_iff_le_comap]
  intro σ hσ
  have hsupp : lineChart ℂ chartZero ∈ (zeroIdeal ℂ).support := by
    change lineChart ℂ chartZero ∈ ((zeroIdeal ℂ).support : Set (projectiveSpace ℂ 1))
    rw [support_zeroIdeal]
    exact ⟨closedPoint ℂ, by rw [zeroPoint, Scheme.Hom.comp_apply]⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff] at hsupp
  have h := hsupp σ hσ
  rw [Scheme.mem_basicOpen _ σ _ hU] at h
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  exact h

/-- The germ of `t` lies in the stalk of the ideal of `0` (via the chart). -/
theorem exists_mem_stalkIdeal_zeroIdeal_stalkMap :
    ∃ s ∈ stalkIdeal (zeroIdeal ℂ) (lineChart ℂ chartZero),
      ((lineChart ℂ).stalkMap chartZero).hom s =
        (Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))).presheaf.germ ⊤ chartZero
          trivial ((Scheme.ΓSpecIso _).inv (MvPolynomial.X ⟨1, by decide⟩)) := by
  let j := lineChart ℂ
  let k : Spec (.of ℂ) ⟶ Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))) :=
    Spec.map (CommRingCat.ofHom (evalZero ℂ))
  have hfst : pullback.fst j (zeroPoint ℂ) = pullback.snd j (zeroPoint ℂ) ≫ k := by
    rw [← cancel_mono j, Category.assoc, pullback.condition]
    rfl
  have hker : ((zeroIdeal ℂ).comap j).ideal ⟨⊤, isAffineOpen_top _⟩ =
      RingHom.ker ((pullback.snd j (zeroPoint ℂ) ≫ k).app ⊤).hom := by
    rw [zeroIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.Hom.ker_apply, hfst]
  have hmem : (Scheme.ΓSpecIso _).inv (MvPolynomial.X ⟨1, by decide⟩) ∈
      ((zeroIdeal ℂ).comap j).ideal ⟨⊤, isAffineOpen_top _⟩ := by
    rw [hker, RingHom.mem_ker, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
    have h1 : k.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (MvPolynomial.X ⟨1, by decide⟩ :
        ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))) = 0 := by
      have h2 := congrArg (fun φ => φ.hom (MvPolynomial.X ⟨1, by decide⟩ :
        ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2))) (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (evalZero ℂ)))
      have h0 : evalZero ℂ (MvPolynomial.X ⟨1, by decide⟩ :
          ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) = 0 := by
        simp [evalZero]
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, h0,
        map_zero] at h2
      exact h2.symm
    calc _ = ((pullback.snd j (zeroPoint ℂ)).app (k ⁻¹ᵁ ⊤)).hom 0 := congrArg _ h1
      _ = 0 := map_zero _
  have hgerm := germ_mem_stalkIdeal ((zeroIdeal ℂ).comap j) ⟨⊤, isAffineOpen_top _⟩
    (c := chartZero) trivial hmem
  rw [stalkIdeal_comap, Ideal.mem_map_iff_of_surjective _
    (ConcreteCategory.bijective_of_isIso (j.stalkMap chartZero)).2] at hgerm
  exact hgerm

/-- **The Gauss point of `ℙ¹` has value `1` on the ideal of `0`.** -/
theorem idealVal_lineGaussPoint_zeroIdeal : (lineGaussPoint v₀).idealVal (zeroIdeal ℂ) = 1 := by
  rw [idealVal_eq_of_isCenter _ (lineGaussPoint_isCenter v₀)]
  apply le_antisymm
  · obtain ⟨s, hs, hsg⟩ := exists_mem_stalkIdeal_zeroIdeal_stalkMap
    refine (iInf₂_le s hs).trans (le_of_eq ?_)
    have hval : (lineGaussPoint v₀).valAt
        ((specializationMap (lineGaussPoint_isCenter v₀).choose).hom s) = 1 := by
      change gaussExtension v₀ ((fieldEmb (gaussLineMap K)).hom ((specializationMap _).hom s)) = 1
      have := fieldEmb_comp_specializationMap (chartGauss K) (lineChart ℂ)
        (fieldPt_chartGauss_specializes (K := K)) s
      refine (congrArg (gaussExtension v₀) this).trans ?_
      rw [hsg, fieldEmb_chartGauss_germ, ΓSpecIso_hom_inv_apply, gaussExtension_gaussChartHom,
        gaussVal_chart_X]
    rw [hval]
    exact toENNReal_one
  · refine le_iInf₂ fun s hs => ?_
    obtain ⟨a, ha, hm⟩ := lineGaussPoint_valAt v₀ s
    have h1 : (1 : WithTop ℝ) ≤ (lineGaussPoint v₀).valAt
        ((specializationMap (lineGaussPoint_isCenter v₀).choose).hom s) := by
      have : (lineGaussPoint v₀).valAt
          ((specializationMap (lineGaussPoint_isCenter v₀).choose).hom s) =
          (lineGaussPoint v₀).valAt
            ((specializationMap (lineGaussPoint_support_specializes v₀)).hom s) := rfl
      rw [this, ha]
      exact one_le_gaussVal_chart v₀ (hm (stalkIdeal_zeroIdeal_le hs))
    have h2 := toENNReal_mono h1
    rwa [toENNReal_one] at h2

end line

/-! ### `σ(v)(𝓘) = 1` and the unconditional formulas -/

section gauss

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **`σ(v)(t) = 1`**: the Gauss point of `X × ℙ¹` has value `1` on the ideal of the central
fibre. -/
theorem idealVal_gaussPoint_centralIdeal (v : BerkovichPoint p) :
    (gaussPoint v).idealVal (centralIdeal p) = 1 := by
  let := residueComplexAlgebra p v.support
  unfold gaussPoint centralIdeal
  rw [idealVal_comap_fieldBerkovichPoint (productSnd p) (productSnd_structure p),
    fieldBerkovichPoint_congr (gaussMap_snd (K := X.residueField v.support) p _
      (fromSpecResidueField_structure v)) _ (gaussLineMap_structure _)]
  exact idealVal_lineGaussPoint_zeroIdeal v.val

/-- **`σ(v)(t^b 𝔞) = b - φ_𝔞(v)`** at the Gauss point of `X × ℙ¹` ([BJ22, §2.1]). -/
theorem idealVal_gaussPoint_flagSheaf_eq' (v : BerkovichPoint p) (𝔞 : FlagIdeal X) {b : ℤ}
    (hb : IsWeightBound 𝔞 b) :
    (gaussPoint v).idealVal (flagSheaf p 𝔞 b) = ENNReal.ofReal (b - 𝔞.phi v) :=
  idealVal_gaussPoint_flagSheaf_eq v 𝔞 hb (idealVal_gaussPoint_centralIdeal v)

/-- **The Gauss point of the model computes `φ_𝔞`** ([BJ22, §2.1, proof of `thm:VCarPL`]): on the
blow-up model `𝒳` of `t^b 𝔞`, `σ(v)((t^b 𝔞) · 𝒪_𝒳) = b - φ_𝔞(v)`. -/
theorem idealVal_gaussModelPoint_flagSheaf_eq (v : BerkovichPoint p) (𝔞 : FlagIdeal X) {b : ℤ}
    (hb : IsWeightBound 𝔞 b) :
    (gaussModelPoint v 𝔞 b).idealVal ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔞 b)) =
      ENNReal.ofReal (b - 𝔞.phi v) :=
  idealVal_gaussModelPoint_flagSheaf v 𝔞 hb (idealVal_gaussPoint_centralIdeal v)

/-- `φ_𝔞(v) = b - σ(v)((t^b 𝔞) · 𝒪_𝒳)` as real numbers: the PL function `φ_𝔞` is read off the
vertical Cartier divisor `(t^b 𝔞) · 𝒪_𝒳` at the Gauss points of the model. -/
theorem phi_eq_sub_idealVal_gaussModelPoint (v : BerkovichPoint p) (𝔞 : FlagIdeal X) {b : ℤ}
    (hb : IsWeightBound 𝔞 b) :
    𝔞.phi v = b - ((gaussModelPoint v 𝔞 b).idealVal
      ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔞 b))).toReal := by
  rw [idealVal_gaussModelPoint_flagSheaf_eq v 𝔞 hb,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (𝔞.phi_le v hb))]
  ring

end gauss

/-! ### Gauss points and domination maps between models -/

section domination

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))

/-- The Gauss point of a dominating model maps to the Gauss point of the dominated model. -/
theorem gaussModelMap_comp {K : Type} [Field K] [Algebra ℂ K] (ι : Spec (.of K) ⟶ X)
    (hι : ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) {𝔞 𝔠 : FlagIdeal X} {b c : ℤ}
    (g : flagModel p 𝔠 c ⟶ flagModel p 𝔞 b) (hg : g ≫ flagModelπ p 𝔞 b = flagModelπ p 𝔠 c) :
    gaussModelMap p ι hι 𝔠 c ≫ g = gaussModelMap p ι hι 𝔞 b :=
  Scheme.IdealSheafData.blowUp.hom_ext _ _
    (by rw [comap_gaussMap_flagSheaf]; exact Scheme.IdealSheafData.isInvertible_top) _ _
    (by rw [Category.assoc, hg, gaussModelMap_π]) (gaussModelMap_π p ι hι 𝔞 b)

variable [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable {p}

/-- **Values at Gauss points are compatible with domination maps** (towards the model independence
of `φ_D`, [BJ22, §2.1]): for a morphism `g : 𝒳_𝔠 ⟶ 𝒳_𝔞` over `X × ℙ¹` and an ideal sheaf `D` on
`𝒳_𝔞`, `σ(v)(D · 𝒪_{𝒳_𝔠}) = σ(v)(D)`. -/
theorem idealVal_gaussModelPoint_comap_map (v : BerkovichPoint p) {𝔞 𝔠 : FlagIdeal X} {b c : ℤ}
    (g : flagModel p 𝔠 c ⟶ flagModel p 𝔞 b) (hg : g ≫ flagModelπ p 𝔞 b = flagModelπ p 𝔠 c)
    (D : (flagModel p 𝔞 b).IdealSheafData) :
    (gaussModelPoint v 𝔠 c).idealVal (D.comap g) = (gaussModelPoint v 𝔞 b).idealVal D := by
  let := residueComplexAlgebra p v.support
  have hh : g ≫ flagModelStructure p 𝔞 b = flagModelStructure p 𝔠 c := by
    rw [flagModelStructure, ← Category.assoc, hg]
  unfold gaussModelPoint
  rw [idealVal_comap_fieldBerkovichPoint g hh,
    fieldBerkovichPoint_congr (gaussModelMap_comp (K := X.residueField v.support) p _
      (fromSpecResidueField_structure v) g hg)]

/-- **Every `φ_𝔞` is read off any model**: on the model `𝒳_𝔠` of any flag ideal `𝔠`, for every flag
ideal `𝔞` with weight bound `b`, `φ_𝔞(v) = b - σ(v)((t^b 𝔞) · 𝒪_{𝒳_𝔠})`. Together with
`exists_common_flagModel` (on which all `(t^{b_i} 𝔞_i) · 𝒪` are invertible) this puts finitely many
PL functions `φ_{𝔞_i}` on one model as vertical Cartier divisors ([BJ22, §2.1]). -/
theorem phi_eq_sub_idealVal_gaussModelPoint_of_model (v : BerkovichPoint p) (𝔠 : FlagIdeal X)
    (c : ℤ) (𝔞 : FlagIdeal X) {b : ℤ} (hb : IsWeightBound 𝔞 b) :
    𝔞.phi v = b - ((gaussModelPoint v 𝔠 c).idealVal
      ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔠 c))).toReal := by
  rw [idealVal_gaussModelPoint_comap, idealVal_gaussPoint_flagSheaf_eq' v 𝔞 hb,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (𝔞.phi_le v hb))]
  ring

end domination

end SGPT.NAPotential.BJ
