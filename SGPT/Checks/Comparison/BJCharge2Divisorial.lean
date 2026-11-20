import SGPT.Checks.Comparison.BJChargeCenter
import SGPT.Checks.Comparison.BJModel2Dimension
import SGPT.NAPotential.BerkovichDivisorial


/-!
# Divisorial points are Abhyankar valuations (lane BJ-CHARGE, step R8(a))

Source: [BJ22] (`references/bj22-trivval`), Lemma `lem:tcdiv` and its proof via [BHJ17, Theorem 4.6]:
a divisorial valuation `v = s · ord_E` has residue field of transcendence degree `dim X - 1` and
rational values. Towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint:
`claude-bj-charge2.tex`.

* `residueFieldAlgEquiv`, `exists_algebraicIndependent_of_coheight_eq_one`: at a point of
  codimension one of an integral scheme of finite type over `ℂ` whose function field has
  transcendence degree `d`, the residue field contains `d - 1` algebraically independent elements
  (dimension formula);
* `spec_map_algebraMap_stalkAlgebra`, `residueComplexHom_eq_stalkAlgebra`,
  `residueComplexHom_comp`: the `ℂ`-structures of stalks (Hironaka's `stalkAlgebra`) and of residue
  fields (SGPT's `residueComplexHom`) agree;
* `ord_algebraMap_of_isUnit`, `ord_algebraMap_of_irreducible`: `ord_z` of units and uniformizers;
* `exists_specializationMap_div`: rational functions are fractions of germs at any point;
* `exists_residuallyIndependent_of_primeDivisor`: for a prime divisor `E` over `X`,
  `s · ord_E` has `dim X - 1` residually independent elements;
* `exists_reesData_of_primeDivisor`: **the data of step R8(a)**: ratios `a_i / b_i` of germs at
  the centre of `v = s · ord_E` with equal integral values, residually independent for `v`, and a
  germ `f` of positive integral value.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order
open SGPT.NAPotential.Berkovich

section residue

variable {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType q]

/-- The residue field of the stalk at a point of an affine open is the residue field of the
corresponding prime, as `ℂ`-algebras. -/
def residueFieldAlgEquiv {U : Y.Opens} (hU : IsAffineOpen U) {z : Y} (hz : z ∈ U) :
    letI := q.stalkAlgebra z
    letI := q.sectionsAlgebra U
    IsLocalRing.ResidueField (Y.presheaf.stalk z) ≃ₐ[ℂ]
      (hU.primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField :=
  letI := q.stalkAlgebra z
  letI := q.sectionsAlgebra U
  letI := Y.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)
  haveI : IsScalarTower ℂ Γ(Y, U) (Y.presheaf.stalk z) := q.isScalarTower_sectionsAlgebra_stalk U hz
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk z) (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hz⟩
  let e : Y.presheaf.stalk z ≃ₐ[ℂ] Localization.AtPrime (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl (Y.presheaf.stalk z)
      (Localization.AtPrime (hU.primeIdealOf ⟨z, hz⟩).asIdeal)).restrictScalars ℂ
  { IsLocalRing.ResidueField.mapEquiv e.toRingEquiv with
    commutes' := fun a => by
      change IsLocalRing.ResidueField.mapEquiv e.toRingEquiv
        (IsLocalRing.residue _ (algebraMap ℂ _ a)) = _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      change IsLocalRing.residue _ (e (algebraMap ℂ _ a)) = _
      rw [e.commutes]
      rfl }

/-- **A point of codimension one has a residue field of transcendence degree `dim - 1`**: if
`ℂ(Y)` has transcendence degree `d` over `ℂ`, the residue field at a point of codimension one
contains `d - 1` elements algebraically independent over `ℂ` (dimension formula). -/
theorem exists_algebraicIndependent_of_coheight_eq_one {d : ℕ}
    (htr : letI := q.stalkAlgebra (genericPoint Y); Algebra.trdeg ℂ Y.functionField = d)
    {z : Y} (hz : coheight z = 1) :
    ∃ x : Fin (d - 1) → IsLocalRing.ResidueField (Y.presheaf.stalk z),
      letI := q.stalkAlgebra z; AlgebraicIndependent ℂ x := by
  let := q.stalkAlgebra z
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show z ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  let := q.sectionsAlgebra U
  let := Y.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  have : Algebra.FiniteType ℂ Γ(Y, U) := q.finiteType_sectionsAlgebra hU
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  set P := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
  have : IsLocalization.AtPrime (Y.presheaf.stalk z) P := hU.isLocalization_stalk ⟨z, hzU⟩
  have hdimA : ringKrullDim Γ(Y, U) = d :=
    SGPT.Foundations.Envelope.SchemeFunctionFieldDimension.affineSections_dimension_eq q ⟨U, hU⟩ d htr
  have hP : P.height = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Y.presheaf.stalk z), hz] at h1
    exact_mod_cast h1
  have hform := SGPT.Support.Alterations.Algebra.AffinePrimeDimension.height_add_quotient_dimension ℂ
    Γ(Y, U) P
  let : Algebra.FiniteType ℂ (Γ(Y, U) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) Ideal.Quotient.mk_surjective
  have hfin : Algebra.trdeg ℂ (Γ(Y, U) ⧸ P) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  let : FaithfulSMul (Γ(Y, U) ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  let : FaithfulSMul ℂ (Γ(Y, U) ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap ℂ (Γ(Y, U) ⧸ P)).injective
  let : Algebra.IsAlgebraic (Γ(Y, U) ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic P.ResidueField (nonZeroDivisors (Γ(Y, U) ⧸ P))
  have heq : Algebra.trdeg ℂ (Γ(Y, U) ⧸ P) = Algebra.trdeg ℂ P.ResidueField := by
    have h := trdeg_add_eq ℂ (Γ(Y, U) ⧸ P) (A := P.ResidueField)
    rwa [trdeg_eq_zero (R := Γ(Y, U) ⧸ P), add_zero] at h
  obtain ⟨d', hd'⟩ := Cardinal.lt_aleph0.mp (heq ▸ hfin)
  have hdimQ := SGPT.Foundations.Envelope.SchemeFunctionFieldDimension.affine_dimension_eq ℂ (Γ(Y, U) ⧸ P)
    P.ResidueField d' hd'
  have hdd : d' = d - 1 := by
    rw [hP, hdimQ, hdimA] at hform
    have : (1 : WithBot ℕ∞) + (d' : WithBot ℕ∞) = (d : WithBot ℕ∞) := by exact_mod_cast hform
    have h2 : 1 + d' = d := by exact_mod_cast this
    omega
  let : FaithfulSMul ℂ P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap ℂ P.ResidueField).injective
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis'.{0} ℂ P.ResidueField
  have hcard : Cardinal.mk ι = (d - 1 : ℕ) := by
    rw [hx.cardinalMk_eq_trdeg, hd', hdd]
  obtain ⟨φ⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  let r := (residueFieldAlgEquiv q hU hzU).symm
  refine ⟨fun i => r (x (φ.symm i)), ?_⟩
  exact (hx.1.comp _ φ.symm.injective).map' (f := r.toAlgHom) r.injective

end residue

section bridge

variable {Y : Scheme.{0}} (q : Y ⟶ Spec (.of ℂ))

/-- The `ℂ`-structure of a stalk (Hironaka's `stalkAlgebra`) is the one of the morphism
`Spec 𝒪_{Y,y} ⟶ Y ⟶ Spec ℂ`. -/
theorem spec_map_algebraMap_stalkAlgebra (y : Y) :
    letI := q.stalkAlgebra y
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Y.presheaf.stalk y))) = Y.fromSpecStalk y ≫ q := by
  let := q.stalkAlgebra y
  have h2 := Scheme.toSpecΓ_naturality q
  rw [← SpecMap_ΓSpecIso_hom] at h2
  have hq : q = Y.toSpecΓ ≫ Spec.map q.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv := by
    rw [← Category.assoc, ← h2, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  rw [Scheme.Hom.algebraMap_stalkAlgebra]
  conv_rhs => rw [hq]
  rw [Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- **The two `ℂ`-structures agree on residue fields**: SGPT's `residueComplexHom` is the
`ℂ`-structure of the stalk followed by the residue map. -/
theorem residueComplexHom_eq_stalkAlgebra (y : Y) :
    letI := q.stalkAlgebra y
    residueComplexHom q y =
      CommRingCat.ofHom (algebraMap ℂ (Y.presheaf.stalk y)) ≫ Y.residue y := by
  let := q.stalkAlgebra y
  apply Spec.map_injective
  rw [spec_map_residueComplexHom, Spec.map_comp, spec_map_algebraMap_stalkAlgebra,
    Scheme.fromSpecResidueField, Category.assoc]

/-- `residueComplexHom` is compatible with residue field maps. -/
theorem residueComplexHom_comp {Z : Scheme.{0}} (fZ : Z ⟶ Spec (.of ℂ)) (h : Y ⟶ Z) (y : Y) :
    residueComplexHom (h ≫ fZ) y = residueComplexHom fZ (h y) ≫ h.residueFieldMap y := by
  apply Spec.map_injective
  symm
  rw [spec_map_residueComplexHom, Spec.map_comp, spec_map_residueComplexHom, ← Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]

end bridge

section ordUnit

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- `ord_z` of the image of a unit of `𝒪_{Y,z}` is `0`. -/
theorem ord_algebraMap_of_isUnit {z : Y} (hz : coheight z = 1) {r : Y.presheaf.stalk z}
    (hr : IsUnit r) : Scheme.ord (algebraMap _ Y.functionField r) z = 0 := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap _ Y.functionField r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hr.ne_zero
  rw [Scheme.ord_eq_iff hz hne]
  change Ring.ordFrac _ _ = _
  rw [Ring.ordFrac_eq_ord _ hr.ne_zero,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hr.ne_zero) (n := 0)
      (by rw [Ring.ord_of_isUnit hr]; rfl)]
  rfl

/-- `ord_z` of the image of a uniformizer of the DVR `𝒪_{Y,z}` is `1`. -/
theorem ord_algebraMap_of_irreducible {z : Y} (hz : coheight z = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk z)] {ϖ : Y.presheaf.stalk z} (hϖ : Irreducible ϖ) :
    Scheme.ord (algebraMap _ Y.functionField ϖ) z = 1 := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap _ Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  rw [Scheme.ord_eq_iff hz hne]
  change Ring.ordFrac _ _ = _
  rw [Ring.ordFrac_eq_ord _ hϖ.ne_zero,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) (n := 1)
      (by rw [Ring.ord_of_irreducible hϖ]; rfl)]
  rfl

end ordUnit

section generic

/-- The residue map at the generic point of an integral scheme is bijective. -/
theorem residue_bijective_of_eq_genericPoint {X : Scheme.{0}} [IsIntegral X] (y : X)
    (hy : y = genericPoint X) : Function.Bijective (X.residue y).hom := by
  subst hy
  exact ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩

/-- **Fractions at the generic point**: every element of `κ(η)` is `g(a)/g(b)` for germs
`a, b ∈ 𝒪_{X,c}` with `g(b) ≠ 0`, `g` the specialization map. -/
theorem exists_specializationMap_div {X : Scheme.{0}} [IsIntegral X] {y c : X}
    (hy : y = genericPoint X) (h : y ⤳ c) (w : X.residueField y) :
    ∃ a b : X.presheaf.stalk c, (BerkovichPoint.specializationMap h).hom b ≠ 0 ∧
      w = (BerkovichPoint.specializationMap h).hom a / (BerkovichPoint.specializationMap h).hom b := by
  subst hy
  let e : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      (residue_bijective_of_eq_genericPoint _ rfl)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk c) (e.symm w)
  have hspec : ∀ t : X.presheaf.stalk c, (BerkovichPoint.specializationMap h).hom t =
      e (algebraMap _ X.functionField t) := fun t => rfl
  refine ⟨a, b, ?_, ?_⟩
  · rw [hspec, map_ne_zero_iff _ e.injective]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hb)
  · rw [hspec, hspec, ← map_div₀, hab, RingEquiv.apply_symm_apply]

end generic

section divisorial

open SGPT.NAPotential.BJCharge

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]
  (E : PrimeDivisorOver X)

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- `π : Y → X` maps the generic point to the generic point with bijective stalk map. -/
theorem stalkMap_genericPoint_bijective_of_primeDivisor :
    Function.Bijective (E.π.stalkMap (genericPoint E.Y)).hom := by
  have h := congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap E.π (genericPoint E.Y))
  have hl : Function.Bijective ((X.residue (E.π (genericPoint E.Y)) ≫
      E.π.residueFieldMap (genericPoint E.Y)).hom) := by
    rw [CommRingCat.hom_comp]
    exact E.birational.comp (residue_bijective_of_eq_genericPoint _ E.isGenericPoint_image)
  rw [h, CommRingCat.hom_comp] at hl
  exact (Function.Bijective.of_comp_iff' (residue_bijective_of_eq_genericPoint _ rfl) _).mp hl

omit [IsIntegral X] in
theorem pullback_bijective_of_primeDivisor : Function.Bijective E.pullback := by
  refine ⟨E.pullback_injective, ?_⟩
  intro z
  obtain ⟨y, hy⟩ := E.birational.2 (E.residueEquiv z)
  exact ⟨y, by simp [PrimeDivisorOver.pullback, hy]⟩

omit [IsIntegral X] [IsProjective p] in
/-- The pull-back of rational functions is `ℂ`-linear. -/
theorem pullback_algebraMap_of_primeDivisor (a : ℂ) :
    E.pullback ((residueComplexHom p (E.π (genericPoint E.Y))).hom a) =
      (letI := (E.π ≫ p).stalkAlgebra (genericPoint E.Y)
       algebraMap ℂ E.Y.functionField a) := by
  let := (E.π ≫ p).stalkAlgebra (genericPoint E.Y)
  have h1 := congrArg (fun φ => φ.hom a) (residueComplexHom_comp p E.π (genericPoint E.Y))
  have h2 := congrArg (fun φ => φ.hom a)
    (residueComplexHom_eq_stalkAlgebra (E.π ≫ p) (genericPoint E.Y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  change E.residueEquiv.symm ((E.π.residueFieldMap (genericPoint E.Y)).hom
    ((residueComplexHom p (E.π (genericPoint E.Y))).hom a)) = _
  rw [← h1, h2]
  exact E.residueEquiv.symm_apply_apply _

/-- **Divisorial valuations are Abhyankar** (step R8(a)): for `v = s · ord_E`, the residue field
of `v` contains `dim X - 1` elements algebraically independent over `ℂ`, i.e. there are
`m ≥ dim X - 1` elements of `ℂ(X)` that are residually independent for `v`. -/
theorem exists_residuallyIndependent_of_primeDivisor (s : ℝ) (hs : 0 < s) :
    ∃ (m : ℕ) (w : Fin m → X.residueField (E.π (genericPoint E.Y))),
      topologicalKrullDim X ≤ (m + 1 : ℕ) ∧
      (letI := residueComplexAlgebra p (E.ordVal p s hs).support
       ResiduallyIndependent (E.ordVal p s hs).val w) := by
  let fY := E.π ≫ p
  obtain ⟨d, htr, hd⟩ := exists_trdeg_eq_and_dim_eq fY
  have hdimX : topologicalKrullDim X = d := by
    rw [← hd]
    exact (topologicalKrullDim_eq_of_stalkMap_genericPoint fY p E.π rfl E.isGenericPoint_image
      (stalkMap_genericPoint_bijective_of_primeDivisor E)).symm
  obtain ⟨x, hx⟩ := exists_algebraicIndependent_of_coheight_eq_one fY htr E.coheight_point
  let := fY.stalkAlgebra E.point
  let := fY.stalkAlgebra (genericPoint E.Y)
  let := residueComplexAlgebra p (E.π (genericPoint E.Y))
  choose r hr using fun i => IsLocalRing.residue_surjective (x i)
  let pb := RingEquiv.ofBijective E.pullback (pullback_bijective_of_primeDivisor E)
  let φ : X.residueField (E.π (genericPoint E.Y)) →ₐ[ℂ] E.Y.functionField :=
    { E.pullback with commutes' := fun a => pullback_algebraMap_of_primeDivisor E a }
  let ψ := stalkToFunctionField fY E.point
  refine ⟨d - 1, fun i => pb.symm (algebraMap _ E.Y.functionField (r i)), ?_, ?_⟩
  · rw [hdimX]
    exact_mod_cast (by omega : d ≤ d - 1 + 1)
  · intro P hP
    have h1 : E.pullback (MvPolynomial.aeval (fun i => pb.symm (algebraMap _ E.Y.functionField
        (r i))) P) = algebraMap _ E.Y.functionField (MvPolynomial.aeval r P) := by
      change φ _ = ψ _
      rw [MvPolynomial.comp_aeval_apply, MvPolynomial.comp_aeval_apply]
      congr 2
      funext i
      exact pb.apply_symm_apply _
    have hunit : IsUnit (MvPolynomial.aeval r P) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      have e4 : (IsScalarTower.toAlgHom ℂ (E.Y.presheaf.stalk E.point)
          (IsLocalRing.ResidueField (E.Y.presheaf.stalk E.point))) (MvPolynomial.aeval r P) =
          IsLocalRing.residue _ (MvPolynomial.aeval r P) := rfl
      rw [← e4, MvPolynomial.comp_aeval_apply]
      have : (fun i => (IsScalarTower.toAlgHom ℂ (E.Y.presheaf.stalk E.point)
          (IsLocalRing.ResidueField (E.Y.presheaf.stalk E.point))) (r i)) = x := by
        funext i
        exact hr i
      rw [this]
      intro h0
      exact hP ((algebraicIndependent_iff.mp hx) P h0)
    have hne : MvPolynomial.aeval (fun i => pb.symm (algebraMap _ E.Y.functionField (r i))) P ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hunit.ne_zero h1.symm
    have hord : E.ord (MvPolynomial.aeval (fun i => pb.symm (algebraMap _ E.Y.functionField
        (r i))) P) = 0 := by
      unfold PrimeDivisorOver.ord
      rw [h1]
      exact ord_algebraMap_of_isUnit E.coheight_point hunit
    refine (PrimeDivisorOver.ordVal_valAt E (f := p) s hs hne).trans ?_
    rw [hord]
    simp

end divisorial

section reesData

open SGPT.NAPotential.BJCharge BerkovichPoint

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

omit [IsProjective p] in
/-- The specialization map from a stalk to the generic residue field is injective. -/
theorem specializationMap_injective_of_eq_genericPoint {y c : X} (hy : y = genericPoint X)
    (h : y ⤳ c) : Function.Injective (specializationMap h).hom := by
  subst hy
  intro a b hab
  have e : ∀ t : X.presheaf.stalk c, (specializationMap h).hom t =
      (X.residue (genericPoint X)).hom (algebraMap _ X.functionField t) := fun t => rfl
  rw [e, e] at hab
  exact IsFractionRing.injective _ X.functionField ((X.residue (genericPoint X)).hom.injective hab)

omit [IsIntegral X] [IsProjective p] in
theorem valAt_pow (v : BerkovichPoint p) (g : X.residueField v.support) (n : ℕ) :
    v.valAt (g ^ n) = n • v.valAt g := by
  induction n with
  | zero => simp [valAt_one]
  | succ n ih => rw [pow_succ, valAt_mul, ih, succ_nsmul]

omit [IsIntegral X] [IsProjective p] in
/-- The value of `s · ord_E` on an integral power: `v(g^{den s}) = num(s) · ord_E(g)`. -/
theorem ordVal_valAt_pow_den (E : PrimeDivisorOver X) (s : ℚ) (hs : (0 : ℝ) < s)
    {g : X.residueField (E.ordVal p s hs).support} (hg : g ≠ 0) :
    (E.ordVal p s hs).valAt (g ^ s.den) = (((s.num * E.ord g : ℤ) : ℝ) : WithTop ℝ) := by
  rw [valAt_pow]
  rw [show (E.ordVal p s hs).valAt g = (((s : ℝ) * E.ord g : ℝ) : WithTop ℝ) from
    PrimeDivisorOver.ordVal_valAt E (f := p) s hs hg, ← WithTop.coe_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  have h := Rat.mul_den_eq_num s
  have h' : (s : ℝ) * (s.den : ℝ) = (s.num : ℝ) := by exact_mod_cast h
  push_cast
  rw [← h']
  ring

/-- **The data of step R8(a) for a divisorial point** `v = s · ord_E`: `m ≥ dim X - 1` ratios
`a_i / b_i` of germs at the centre `c(v)`, with equal integral values `v(a_i) = v(b_i) = μ_i`,
residually independent for `v`, and a germ `f` of positive integral value. -/
theorem exists_reesData_of_primeDivisor (E : PrimeDivisorOver X) (s : ℚ) (hs : (0 : ℝ) < s) :
    ∃ (m : ℕ) (a b : Fin m → X.presheaf.stalk (E.ordVal p s hs).center) (μ : Fin m → ℕ)
      (f : X.presheaf.stalk (E.ordVal p s hs).center) (l : ℕ),
      topologicalKrullDim X ≤ (m + 1 : ℕ) ∧
      (∀ i, (E.ordVal p s hs).centerVal (a i) = ((μ i : ℝ) : WithTop ℝ) ∧
        (E.ordVal p s hs).centerVal (b i) = ((μ i : ℝ) : WithTop ℝ)) ∧
      0 < l ∧ (E.ordVal p s hs).centerVal f = ((l : ℝ) : WithTop ℝ) ∧
      (letI := residueComplexAlgebra p (E.ordVal p s hs).support
       ResiduallyIndependent (E.ordVal p s hs).val (fun i =>
        (specializationMap (E.ordVal p s hs).support_specializes_center).hom (a i) /
          (specializationMap (E.ordVal p s hs).support_specializes_center).hom (b i))) := by
  set v := E.ordVal p s hs with hv
  let := residueComplexAlgebra p v.support
  obtain ⟨m, w, hdim, hind⟩ := exists_residuallyIndependent_of_primeDivisor (p := p) E (s : ℝ) hs
  have hy : v.support = genericPoint X := E.isGenericPoint_image
  let sp : X.presheaf.stalk v.center →+* X.residueField (E.π (genericPoint E.Y)) :=
    (specializationMap v.support_specializes_center).hom
  have hsp : Function.Injective sp :=
    specializationMap_injective_of_eq_genericPoint hy v.support_specializes_center
  have hcv : ∀ g, v.centerVal g = v.valAt (sp g) := fun g => rfl
  have hs' : (0 : ℝ) < s := hs
  have hnum : 0 < s.num := Rat.num_pos.mpr (by exact_mod_cast hs)
  -- the ratios
  choose a₀ b₀ hb₀' hab₀' using fun i => exists_specializationMap_div hy
    v.support_specializes_center (w i)
  have hb₀ : ∀ i, sp (b₀ i) ≠ 0 := hb₀'
  have hab₀ : ∀ i, w i = sp (a₀ i) / sp (b₀ i) := hab₀'
  have hw0 : ∀ i, v.valAt (w i) = 0 := hind.val_eq_zero
  have hspa : ∀ i, sp (a₀ i) = w i * sp (b₀ i) := fun i => by
    rw [hab₀ i, div_mul_cancel₀ _ (hb₀ i)]
  have hval_b : ∀ i, v.valAt (sp (b₀ i) ^ s.den) = (((s.num * E.ord (sp (b₀ i)) : ℤ) : ℝ) :
      WithTop ℝ) := fun i => ordVal_valAt_pow_den E s hs (hb₀ i)
  have hk : ∀ i, 0 ≤ s.num * E.ord (sp (b₀ i)) := by
    intro i
    have h1 := v.centerVal_nonneg (b₀ i ^ s.den)
    rw [hcv, map_pow, hval_b] at h1
    exact_mod_cast h1
  refine ⟨m, fun i => a₀ i * b₀ i ^ (s.den - 1), fun i => b₀ i ^ s.den,
    fun i => (s.num * E.ord (sp (b₀ i))).toNat, ?_⟩
  -- the element of positive value
  let pb := RingEquiv.ofBijective E.pullback (pullback_bijective_of_primeDivisor E)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (E.Y.presheaf.stalk E.point)
  let wϖ : X.residueField (E.π (genericPoint E.Y)) := pb.symm (algebraMap _ E.Y.functionField ϖ)
  have hwϖ : E.ord wϖ = 1 := by
    unfold PrimeDivisorOver.ord
    rw [show E.pullback wϖ = algebraMap _ E.Y.functionField ϖ from pb.apply_symm_apply _]
    exact ord_algebraMap_of_irreducible E.coheight_point hϖ
  have hwϖ0 : wϖ ≠ 0 := by
    intro h0
    have : E.pullback wϖ = 0 := by rw [h0]; exact map_zero _
    rw [show E.pullback wϖ = algebraMap _ E.Y.functionField ϖ from pb.apply_symm_apply _] at this
    exact hϖ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp this)
  obtain ⟨a₁, b₁, hb₁', hab₁'⟩ := exists_specializationMap_div hy v.support_specializes_center wϖ
  have hb₁ : sp b₁ ≠ 0 := hb₁'
  have hab₁ : wϖ = sp a₁ / sp b₁ := hab₁'
  have hspa₁ : sp a₁ = wϖ * sp b₁ := by rw [hab₁, div_mul_cancel₀ _ hb₁]
  have hsa₁ : sp a₁ ≠ 0 := by rw [hspa₁]; exact mul_ne_zero hwϖ0 hb₁
  have hordb₁ : 0 ≤ E.ord (sp b₁) := by
    have h1 := v.centerVal_nonneg b₁
    rw [hcv, show v.valAt (sp b₁) = (((s : ℝ) * E.ord (sp b₁) : ℝ) : WithTop ℝ) from
      PrimeDivisorOver.ordVal_valAt E (f := p) s hs hb₁] at h1
    have h2 : (0 : ℝ) ≤ (s : ℝ) * E.ord (sp b₁) := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ E.ord (sp b₁) := nonneg_of_mul_nonneg_right
      (by linarith) hs' |> fun h => by nlinarith [h2]
    exact_mod_cast h3
  have horda₁ : E.ord (sp a₁) = 1 + E.ord (sp b₁) := by
    rw [hspa₁, E.ord_mul hwϖ0 hb₁, hwϖ]
  refine ⟨a₁ ^ s.den, (s.num * E.ord (sp a₁)).toNat, hdim, ?_, ?_, ?_, ?_⟩
  · intro i
    have hb : v.centerVal (b₀ i ^ s.den) =
        (((s.num * E.ord (sp (b₀ i))).toNat : ℝ) : WithTop ℝ) := by
      rw [hcv, map_pow, hval_b]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg (hk i)).symm
    refine ⟨?_, hb⟩
    rw [← hb]
    show v.valAt (sp (a₀ i * b₀ i ^ (s.den - 1))) = v.valAt (sp (b₀ i ^ s.den))
    rw [map_mul, map_pow, map_pow]
    erw [valAt_mul, hspa i, valAt_mul, hw0, zero_add, valAt_pow, valAt_pow]
    rw [add_comm, ← succ_nsmul, Nat.sub_add_cancel s.den_pos]
  · have : 0 < s.num * E.ord (sp a₁) := mul_pos hnum (by rw [horda₁]; omega)
    omega
  · rw [hcv, map_pow]
    erw [ordVal_valAt_pow_den E s hs hsa₁]
    congr 1
    have : 0 ≤ s.num * E.ord (sp a₁) := le_of_lt (mul_pos hnum (by rw [horda₁]; omega))
    rw [show ((s.num * E.ord (sp a₁)).toNat : ℝ) = ((s.num * E.ord (sp a₁) : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg this]
  · intro P hP
    convert hind P hP using 3
    congr 1
    funext i
    change sp (a₀ i * b₀ i ^ (s.den - 1)) / sp (b₀ i ^ s.den) = w i
    rw [map_mul, map_pow, map_pow, hab₀ i]
    have hb0 := hb₀ i
    obtain ⟨k, hk'⟩ : ∃ k, s.den = k + 1 := ⟨s.den - 1, (Nat.sub_add_cancel s.den_pos).symm⟩
    rw [hk', Nat.add_sub_cancel, pow_succ]
    field_simp

end reesData

end SGPT.NAPotential.BJ
