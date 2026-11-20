import SGPT.Checks.Comparison.BJModel2TestConfig
import SGPT.Checks.Comparison.BJModel2BerkovichMap
import SGPT.NAPotential.BJModelGaussFlag
import SGPT.Support.Principalization.Scheme.BlowUp.InvertibleSheaf

/-!
# Gauss points on `X × ℙ¹` and on the blow-up models (lane BJ-MODEL2, step R1(e))

Source: `chapter_NApotential.tex`, equation `eq:Gext` (the Gauss extension `σ(v)` of a point
`v ∈ X^An`, a semi-valuation on `X × 𝔸¹`), and [BJ22] (`references/bj22-trivval`), §1.3 and §2.1:
`σ(v)` is the semi-valuation of `X × ℙ¹` given on `κ(y)(t)` by `eq:Gext`; it has a centre on every
test configuration, and `σ(v)(𝔞) = min_λ (v(𝔞_λ) - λ) = -φ_𝔞(v)` (`equ:gaussflag`).
Blueprint: `claude-bj-model2.tex`.

For `v ∈ X^An` with support `y`, `K = κ(y)` and `L = K(t) = FractionRing K[t]`:

* `gaussMap : Spec L ⟶ X × ℙ¹` is the `ℂ`-morphism given by `Spec L → Spec K → X` and
  `t = x₁/x₀ ↦ t` on the chart `D₊(x₀) ⊆ ℙ¹`; it avoids the central fibre
  (`fieldPt_gaussMap_not_mem_central`), hence lifts to every blow-up model `gaussModelMap`
  (universal property of the blow-up, `t^b 𝔞` being trivial off the central fibre);
* `gaussPoint v ∈ (X × ℙ¹)^An` and `gaussModelPoint v 𝔞 b ∈ (𝒳_𝔞)^An` are the semi-valuations of
  these field-valued points with the Gauss valuation `σ(v)` of `eq:Gext` on `L`
  (`berkovichGaussExtension`).

## Main results

* `idealVal_gaussPoint_comap_fst`: `σ(v)(pr₁^* 𝔟) = v(𝔟)` for ideal sheaves `𝔟` on `X`;
* `idealVal_gaussModelPoint_comap`: `σ(v)(𝔠 · 𝒪_𝒳) = σ(v)(𝔠)` on the model for ideal sheaves
  `𝔠` on `X × ℙ¹` — the Gauss point of the model is the lift of the Gauss point of `X × ℙ¹`;
* `idealVal_gaussPoint_flagSheaf`: `σ(v)(t^b 𝔞) = inf_j (v(𝔞_{b-j}) + j σ(v)(𝓘))`, `𝓘` the ideal of
  the central fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology IsLocalRing
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel FlagIdealBound
open scoped Polynomial ENNReal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))

/-! ### The field-valued Gauss point -/

section gaussMap

variable (K : Type) [Field K] [Algebra ℂ K]

/-- The chart coordinate `t = x₁/x₀ ↦ t ∈ K(t)`. -/
def gaussChartHom :
    ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2) →+* FractionRing K[X] :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (FractionRing K[X]))
    (fun _ => algebraMap K[X] (FractionRing K[X]) Polynomial.X)

/-- The morphism `Spec K(t) ⟶ ℙ¹` of the coordinate `t`. -/
def gaussLineMap : Spec (.of (FractionRing K[X])) ⟶ projectiveSpace ℂ 1 :=
  Spec.map (CommRingCat.ofHom (gaussChartHom K)) ≫ lineChart ℂ

theorem gaussLineMap_structure : gaussLineMap K ≫ projectiveSpaceStructure ℂ 1 =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing K[X]))) := by
  rw [gaussLineMap, Category.assoc, Segre.coordinateChartInclusion_structure, ← Spec.map_comp]
  congr 1
  ext c
  simp [gaussChartHom, MvPolynomial.algebraMap_eq]

variable {K} (ι : Spec (.of K) ⟶ X)
  (hι : ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))

/-- The morphism `Spec K(t) ⟶ Spec K ⟶ X`. -/
def gaussBaseMap : Spec (.of (FractionRing K[X])) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap K (FractionRing K[X]))) ≫ ι

include hι in
theorem gaussBaseMap_structure : gaussBaseMap ι ≫ p =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing K[X]))) := by
  rw [gaussBaseMap, Category.assoc, hι, ← Spec.map_comp]
  congr 1

/-- **The Gauss point as a field-valued point** `Spec K(t) ⟶ X × ℙ¹`. -/
def gaussMap : Spec (.of (FractionRing K[X])) ⟶ productLine p :=
  pullback.lift (gaussBaseMap ι) (gaussLineMap K)
    (by rw [gaussBaseMap_structure p ι hι, gaussLineMap_structure])

@[reassoc (attr := simp)]
theorem gaussMap_fst : gaussMap p ι hι ≫ productFst p = gaussBaseMap ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem gaussMap_snd : gaussMap p ι hι ≫ productSnd p = gaussLineMap K := pullback.lift_snd _ _ _

theorem gaussMap_structure : gaussMap p ι hι ≫ productStructure p =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing K[X]))) := by
  rw [← Category.assoc, gaussMap_fst, gaussBaseMap_structure p ι hι]

/-- **The Gauss point is not on the central fibre**: its second coordinate is the generic point of
the chart `Spec ℂ[t]`. -/
theorem fieldPt_gaussMap_not_mem_central :
    fieldPt (gaussMap p ι hι) ∉ ((centralIdeal p).support : Set (productLine p)) := by
  rw [support_centralIdeal]
  rintro ⟨z, hz⟩
  have h1 : productSnd p (fieldPt (gaussMap p ι hι)) = fieldPt (gaussLineMap K) := by
    rw [← Scheme.Hom.comp_apply, gaussMap_snd]
  rw [h1] at hz
  change lineChart ℂ (Spec.map (CommRingCat.ofHom (evalZero ℂ)) z) =
    lineChart ℂ (Spec.map (CommRingCat.ofHom (gaussChartHom K)) (closedPoint _)) at hz
  have hz' := (lineChart ℂ).isOpenEmbedding.injective hz
  have hX : (MvPolynomial.X ⟨1, by decide⟩ : ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)) ∈
      (Spec.map (CommRingCat.ofHom (evalZero ℂ)) z).asIdeal := by
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
    simp only [Ideal.mem_comap, CommRingCat.hom_ofHom, evalZero, MvPolynomial.eval_X]
    exact Ideal.zero_mem _
  rw [hz', Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hX
  have h0 : ((closedPoint (FractionRing K[X])).asIdeal : Ideal (FractionRing K[X])) = ⊥ := by
    change maximalIdeal (FractionRing K[X]) = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  simp only [CommRingCat.hom_ofHom, gaussChartHom, MvPolynomial.eval₂Hom_X'] at hX
  rw [h0, Submodule.mem_bot] at hX
  exact Polynomial.X_ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective K[X] _)).mp hX)

/-- `t^b 𝔞` is trivial along the Gauss point. -/
theorem comap_gaussMap_flagSheaf (𝔞 : FlagIdeal X) (b : ℤ) :
    (flagSheaf p 𝔞 b).comap (gaussMap p ι hι) = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext z
  simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hz
  rw [Scheme.IdealSheafData.support_comap] at hz
  have hz' : gaussMap p ι hι z ∈ ((flagSheaf p 𝔞 b).support : Set (productLine p)) := hz
  have hpt : z = closedPoint (FractionRing K[X]) := Subsingleton.elim _ _
  rw [hpt] at hz'
  exact fieldPt_gaussMap_not_mem_central p ι hι (support_flagSheaf_le p 𝔞 b hz')

/-- **The Gauss point of the blow-up model**: the lift of `gaussMap` to `𝒳_𝔞`. -/
def gaussModelMap (𝔞 : FlagIdeal X) (b : ℤ) :
    Spec (.of (FractionRing K[X])) ⟶ flagModel p 𝔞 b :=
  Scheme.IdealSheafData.blowUp.lift _ (gaussMap p ι hι)
    (by rw [comap_gaussMap_flagSheaf]; exact Scheme.IdealSheafData.isInvertible_top)

@[reassoc (attr := simp)]
theorem gaussModelMap_π (𝔞 : FlagIdeal X) (b : ℤ) :
    gaussModelMap p ι hι 𝔞 b ≫ flagModelπ p 𝔞 b = gaussMap p ι hι :=
  Scheme.IdealSheafData.blowUp.lift_π _ _ _

theorem gaussModelMap_structure (𝔞 : FlagIdeal X) (b : ℤ) :
    gaussModelMap p ι hι 𝔞 b ≫ flagModelStructure p 𝔞 b =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing K[X]))) := by
  rw [flagModelStructure, gaussModelMap_π_assoc, gaussMap_structure]

end gaussMap

/-! ### The Gauss points of `v ∈ X^An` -/

section gaussPoint

variable {p}

theorem fromSpecResidueField_structure (v : BerkovichPoint p) :
    letI := residueComplexAlgebra p v.support
    X.fromSpecResidueField v.support ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (X.residueField v.support))) :=
  (spec_map_residueComplexHom p v.support).symm

variable [IsProjective p]

local instance : IsProper p := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **The Gauss extension `σ(v)` as a point of `(X × ℙ¹)^An`** (`eq:Gext`, [BJ22, §1.3]). -/
def gaussPoint (v : BerkovichPoint p) : BerkovichPoint (productStructure p) :=
  letI := residueComplexAlgebra p v.support
  fieldBerkovichPoint (productStructure p)
    (gaussMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
      (fromSpecResidueField_structure v))
    (gaussMap_structure (K := X.residueField v.support) p _ (fromSpecResidueField_structure v))
    (berkovichGaussExtension v)

/-- **The Gauss extension `σ(v)` as a point of the blow-up model `𝒳_𝔞`** ([BJ22, §2.1]). -/
def gaussModelPoint (v : BerkovichPoint p) (𝔞 : FlagIdeal X) (b : ℤ) :
    BerkovichPoint (flagModelStructure p 𝔞 b) :=
  letI := residueComplexAlgebra p v.support
  fieldBerkovichPoint (flagModelStructure p 𝔞 b)
    (gaussModelMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
      (fromSpecResidueField_structure v) 𝔞 b)
    (gaussModelMap_structure (K := X.residueField v.support) p _
      (fromSpecResidueField_structure v) 𝔞 b)
    (berkovichGaussExtension v)

/-- **`σ(v)(pr₁^* 𝔟) = v(𝔟)`**: the Gauss extension extends `v`. -/
theorem idealVal_gaussPoint_comap_fst (v : BerkovichPoint p) (J : X.IdealSheafData) :
    (gaussPoint v).idealVal (J.comap (productFst p)) = v.idealVal J := by
  let := residueComplexAlgebra p v.support
  unfold gaussPoint
  rw [idealVal_comap_fieldBerkovichPoint (productFst p) rfl,
    fieldBerkovichPoint_congr (gaussMap_fst (K := X.residueField v.support) p _
      (fromSpecResidueField_structure v)) _
      (gaussBaseMap_structure (K := X.residueField v.support) p _ (fromSpecResidueField_structure v))]
  exact idealVal_fieldBerkovichPoint_fromSpecResidueField v _ _ _ (fun a => by
    change berkovichGaussExtension v (algebraMap _ (FractionRing (X.residueField v.support)[X]) a) =
      v.valAt a
    rw [IsScalarTower.algebraMap_apply (X.residueField v.support)
      (X.residueField v.support)[X] (FractionRing (X.residueField v.support)[X]),
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact gaussExtension_C v.val a) J

/-- **The Gauss point of the model lifts the Gauss point of `X × ℙ¹`**: `σ(v)(𝔠 · 𝒪_𝒳) = σ(v)(𝔠)`
for ideal sheaves `𝔠` on `X × ℙ¹`. -/
theorem idealVal_gaussModelPoint_comap (v : BerkovichPoint p) (𝔞 : FlagIdeal X) (b : ℤ)
    (J : (productLine p).IdealSheafData) :
    (gaussModelPoint v 𝔞 b).idealVal (J.comap (flagModelπ p 𝔞 b)) = (gaussPoint v).idealVal J := by
  let := residueComplexAlgebra p v.support
  unfold gaussModelPoint gaussPoint
  rw [idealVal_comap_fieldBerkovichPoint (flagModelπ p 𝔞 b) rfl,
    fieldBerkovichPoint_congr (gaussModelMap_π (K := X.residueField v.support) p _
      (fromSpecResidueField_structure v) 𝔞 b)]

/-- The value of a power of an ideal sheaf. -/
theorem idealVal_pow {Y : Scheme.{0}} {fY : Y ⟶ Spec (.of ℂ)} [IsProper fY]
    [IsLocallyNoetherian Y] (w : BerkovichPoint fY) (J : Y.IdealSheafData) (j : ℕ) :
    w.idealVal (J ^ j) = j * w.idealVal J := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, BerkovichPoint.idealVal_mul, ih]; push_cast; ring

/-- **`σ(v)(t^b 𝔞) = inf_j (v(𝔞_{b-j}) + j σ(v)(𝓘))`**, `𝓘` the ideal of the central fibre. -/
theorem idealVal_gaussPoint_flagSheaf (v : BerkovichPoint p) (𝔞 : FlagIdeal X) (b : ℤ) :
    (gaussPoint v).idealVal (flagSheaf p 𝔞 b) =
      ⨅ j : ℕ, (v.idealVal (𝔞.ideal (b - j)) + j * (gaussPoint v).idealVal (centralIdeal p)) := by
  let := productLine_isLocallyNoetherian p
  rw [flagSheaf, idealVal_iSup]
  refine iInf_congr fun j => ?_
  rw [BerkovichPoint.idealVal_mul, idealVal_gaussPoint_comap_fst, idealVal_pow]

end gaussPoint

end SGPT.NAPotential.BJ
