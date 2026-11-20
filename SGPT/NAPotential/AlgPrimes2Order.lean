import SGPT.NAPotential.AlgPrimes2Point
import SGPT.NAPotential.AlgPrimesValuation

/-!
# The algebraic order along a prime divisor centred on a divisor


Let `D` be an algebraic prime divisor over the integral scheme `X` whose valuation `ord_D` has
centre `z`, a point of codimension one with `𝒪_{X,z}` a discrete valuation ring.  Let `u` be a
local equation of `{z}‾` on an affine open `V` (`u ∈ 𝔮`, `s 𝔮 ⊆ (u)`, `s ∉ 𝔮`, the germ of `u` at
`z` a uniformizer) and `y ∈ V` a point of `{z}‾` with `s ∉ 𝔪_y`.  Then for every nonzero
`g ∈ 𝒪_{X,y}`, `ord_D(g)` is the multiplicity of the germ of `u` in `g`
(`ord_eq_emultiplicity`): writing `g = uᵏ h` with `u ∤ h`, the image of `h` in `𝒪_{X,z}` is a
unit, so `ord_D(h) = 0` (`ord_D ≥ 0` on `𝒪_{X,z}`, the centre), and `ord_D(u) = 1` because
`ord_D` takes the value `1` (a uniformizer of `𝒪_{Y,D}`) on a quotient of elements of
`𝒪_{X,y}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes2

open AlgebraicGeometry CategoryTheory Topology IsLocalRing Opposite
open SGPT.NAPotential.Berkovich SGPT.NAPotential.AlgPrimes

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsIntegral X]

/-- The specialization map from a stalk to the residue field of the generic point is
injective. -/
theorem specializationMap_injective {w c : X} (hw : w = genericPoint X) (h : w ⤳ c) :
    Function.Injective (BerkovichPoint.specializationMap h).hom := by
  subst hw
  intro g g' hgg
  have h1 : algebraMap (X.presheaf.stalk c) X.functionField g =
      algebraMap (X.presheaf.stalk c) X.functionField g' :=
    (X.residue (genericPoint X)).hom.injective hgg
  exact IsFractionRing.injective (X.presheaf.stalk c) X.functionField h1

/-- Every element of the residue field of the generic point is a quotient of images of germs at
`c`. -/
theorem exists_specializationMap_mul_eq' {w c : X} (hw : w = genericPoint X) (h : w ⤳ c)
    (x : X.residueField w) :
    ∃ a b : X.presheaf.stalk c, b ≠ 0 ∧
      x * (BerkovichPoint.specializationMap h).hom b = (BerkovichPoint.specializationMap h).hom a := by
  subst hw
  exact exists_specializationMap_mul_eq c h x

omit [IsIntegral X] in
/-- Specialization maps compose with the specialization of stalks. -/
theorem specializationMap_stalkSpecializes {w z y : X} (hwz : w ⤳ z) (hzy : z ⤳ y)
    (g : X.presheaf.stalk y) :
    (BerkovichPoint.specializationMap (hwz.trans hzy)).hom g =
      (BerkovichPoint.specializationMap hwz).hom (X.presheaf.stalkSpecializes hzy g) := by
  change (X.presheaf.stalkSpecializes _ ≫ X.residue w).hom g =
    (X.presheaf.stalkSpecializes hwz ≫ X.residue w).hom ((X.presheaf.stalkSpecializes hzy).hom g)
  rw [← X.presheaf.stalkSpecializes_comp hwz hzy, Category.assoc]
  rfl

namespace PrimeDivisorOver'

variable (D : PrimeDivisorOver X)

omit [IsIntegral X] in
/-- **`ord_D` takes the value `1`**: a uniformizer of `𝒪_{Y,D}` is the pull-back of a rational
function on `X`. -/
theorem exists_ord_eq_one : ∃ x : X.residueField (D.π (genericPoint D.Y)), D.ord x = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (D.Y.presheaf.stalk D.point)
  set w : D.Y.functionField := algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField ϖ
  have hsurj : Function.Surjective D.pullback := by
    intro y
    obtain ⟨x, hx⟩ := D.birational.2 (D.residueEquiv y)
    exact ⟨x, by simp [PrimeDivisorOver.pullback, hx]⟩
  obtain ⟨x, hx⟩ := hsurj w
  refine ⟨x, ?_⟩
  have hw0 : w ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact hϖ.ne_zero
  rw [PrimeDivisorOver.ord, hx, Scheme.ord_eq_iff D.coheight_point hw0]
  have : Ring.KrullDimLE 1 (D.Y.presheaf.stalk D.point) :=
    krullDimLE_of_coheight_le (le_of_eq D.coheight_point)
  change Ring.ordFrac (D.Y.presheaf.stalk D.point) w = _
  rw [Ring.ordFrac_irreducible hϖ]
  rfl

variable [IsLocallyNoetherian X]

/-- **The algebraic order along a prime divisor centred on a divisor.**  If the centre `z` of
`ord_D` has codimension one, `u` is a local equation of `{z}‾` on the affine open `V`
(`u ∈ 𝔮`, `s 𝔮 ⊆ (u)` with `s ∉ 𝔮`, `𝔮` the prime of `z`, the germ of `u` at `z` irreducible)
and `y ∈ V ∩ {z}‾` with `s ∉ 𝔪_y`, then `ord_D(g)` is the multiplicity of the germ of `u` in `g`
for every nonzero `g ∈ 𝒪_{X,y}`. -/
theorem ord_eq_emultiplicity {z : X} [IsDiscreteValuationRing (X.presheaf.stalk z)]
    (hc : (D.ordVal f 1 one_pos).IsCenter z) {V : X.Opens} (hV : IsAffineOpen V) (hzV : z ∈ V)
    {u s : Γ(X, V)} (hu : u ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
    (hsq : ∀ a ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal, s * a ∈ Ideal.span {u})
    (hirr : Irreducible (X.presheaf.germ V z hzV u)) {y : X} (hyV : y ∈ V) (hzy : z ⤳ y)
    (hsy : s ∉ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal) {g : X.presheaf.stalk y} (hg : g ≠ 0) :
    (D.ord ((BerkovichPoint.specializationMap (ordVal_support_specializes f D y)).hom g) : ℤ) =
      ((emultiplicity (X.presheaf.germ V y hyV u) g).toNat : ℤ) := by
  classical
  set 𝔮 := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with h𝔮
  set 𝔪 := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal with h𝔪
  set π := X.presheaf.germ V y hyV u with hπ
  have hηgen : (D.ordVal f 1 one_pos).support = genericPoint X :=
    D.ordVal_support_eq_genericPoint 1 one_pos
  obtain ⟨hηz, hnonneg, hpos⟩ := hc
  have hηy : (D.ordVal f 1 one_pos).support ⤳ y := ordVal_support_specializes f D y
  have h𝔮𝔪 : 𝔮 ≤ 𝔪 := (specializes_iff_primeIdealOf_le hV hyV hzV).mp hzy
  -- the localizations
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyV⟩
  have hlocy : IsLocalization.AtPrime (X.presheaf.stalk y) 𝔪 := hV.isLocalization_stalk ⟨y, hyV⟩
  have hgermy : ∀ a, X.presheaf.germ V y hyV a ∈ maximalIdeal (X.presheaf.stalk y) ↔ a ∈ 𝔪 :=
    fun a => IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk y) 𝔪 a
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
  have hlocz : IsLocalization.AtPrime (X.presheaf.stalk z) 𝔮 := hV.isLocalization_stalk ⟨z, hzV⟩
  have hgermz : ∀ a, X.presheaf.germ V z hzV a ∈ maximalIdeal (X.presheaf.stalk z) ↔ a ∈ 𝔮 :=
    fun a => IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) 𝔮 a
  have hspec_germ : ∀ a, X.presheaf.stalkSpecializes hzy (X.presheaf.germ V y hyV a) =
      X.presheaf.germ V z hzV a := fun a => by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  -- the specialization maps
  set sp := (BerkovichPoint.specializationMap hηy).hom with hsp
  set spz := (BerkovichPoint.specializationMap hηz).hom with hspz
  have hsp_eq : ∀ g, sp g = spz (X.presheaf.stalkSpecializes hzy g) := fun g =>
    specializationMap_stalkSpecializes hηz hzy g
  have hinj : Function.Injective sp := specializationMap_injective hηgen hηy
  have hinjz : Function.Injective spz := specializationMap_injective hηgen hηz
  -- `ord_D ≥ 0` on `𝒪_{X,z}`, `= 0` on units, `> 0` on the maximal ideal
  have hord_nonneg : ∀ r : X.presheaf.stalk z, r ≠ 0 → 0 ≤ D.ord (spz r) := by
    intro r hr
    have h0 := hnonneg r
    have hr' : spz r ≠ 0 := fun h => hr (hinjz (h.trans (map_zero _).symm))
    rw [D.ordVal_valAt 1 one_pos hr', one_mul] at h0
    exact_mod_cast WithTop.coe_le_coe.mp h0
  have hord_unit : ∀ r : X.presheaf.stalk z, IsUnit r → D.ord (spz r) = 0 := by
    intro r hr
    obtain ⟨w, rfl⟩ := hr
    have h1 : spz (w : X.presheaf.stalk z) * spz ↑w⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hne : ∀ r : (X.presheaf.stalk z)ˣ, spz (r : X.presheaf.stalk z) ≠ 0 := fun r h =>
      r.ne_zero (hinjz (h.trans (map_zero _).symm))
    have hsum := D.ord_mul (hne w) (hne w⁻¹)
    rw [h1] at hsum
    have hone : D.ord (1 : X.residueField (D.π (genericPoint D.Y))) = 0 := by
      have := D.ord_pow (g := (1 : X.residueField (D.π (genericPoint D.Y)))) one_ne_zero 0
      simpa using this
    have h2 := hord_nonneg _ w.ne_zero
    have h3 := hord_nonneg _ w⁻¹.ne_zero
    omega
  have hord_pos : ∀ r ∈ maximalIdeal (X.presheaf.stalk z), r ≠ 0 → 0 < D.ord (spz r) := by
    intro r hr hr0
    have h0 := hpos r hr
    have hr' : spz r ≠ 0 := fun h => hr0 (hinjz (h.trans (map_zero _).symm))
    rw [D.ordVal_valAt 1 one_pos hr', one_mul] at h0
    exact_mod_cast WithTop.coe_lt_coe.mp h0
  -- `u` generates `𝔮` near `y`
  have hsunit : IsUnit (X.presheaf.germ V y hyV s) := by
    by_contra h
    exact hsy ((hgermy s).mp h)
  have hπmem : π ∈ maximalIdeal (X.presheaf.stalk y) := (hgermy u).mpr (h𝔮𝔪 hu)
  have hπ0 : π ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    rw [← hspec_germ, ← hπ, h0, map_zero]
  -- the image in `𝒪_{X,z}` of a germ not divisible by `π` is a unit
  have hunit_of : ∀ h : X.presheaf.stalk y, ¬π ∣ h → IsUnit (X.presheaf.stalkSpecializes hzy h) := by
    intro h hndvd
    by_contra hnu
    apply hndvd
    obtain ⟨a, t, ht, hht⟩ := exists_germ_mul_eq hV (hV.primeIdealOf ⟨y, hyV⟩) hyV
      (hV.fromSpec_primeIdealOf ⟨y, hyV⟩) h
    have htz : t ∉ 𝔮 := fun h' => ht (h𝔮𝔪 h')
    have htunit : IsUnit (X.presheaf.germ V y hyV t) := by
      by_contra h'
      exact ht ((hgermy t).mp h')
    have hgz : X.presheaf.germ V z hzV a ∈ maximalIdeal (X.presheaf.stalk z) := by
      rw [← hspec_germ, ← hht, map_mul]
      exact Ideal.mul_mem_right _ _ hnu
    have ha : a ∈ 𝔮 := (hgermz a).mp hgz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsq a ha)
    have h1 : X.presheaf.germ V y hyV s * X.presheaf.germ V y hyV a =
        π * X.presheaf.germ V y hyV c := by
      rw [← map_mul, ← map_mul, ← hc, mul_comm]
    obtain ⟨σs, hσs⟩ := hsunit
    obtain ⟨σt, hσt⟩ := htunit
    refine ⟨X.presheaf.germ V y hyV c * ↑σs⁻¹ * ↑σt⁻¹, ?_⟩
    calc h = h * X.presheaf.germ V y hyV t * ↑σt⁻¹ := by
          rw [← hσt, mul_assoc, Units.mul_inv, mul_one]
      _ = ↑σs * ↑σs⁻¹ * (X.presheaf.germ V y hyV a * ↑σt⁻¹) := by
          rw [hht, Units.mul_inv, one_mul]
      _ = (X.presheaf.germ V y hyV s * X.presheaf.germ V y hyV a) * ↑σs⁻¹ * ↑σt⁻¹ := by
          rw [hσs]; ring
      _ = _ := by rw [h1]; ring
  -- `d = ord_D(π) ≥ 1`
  set d := D.ord (sp π) with hd
  have hd_pos : 0 < d := by
    rw [hd, hsp_eq, hspec_germ]
    exact hord_pos _ ((hgermz u).mpr hu) hirr.ne_zero
  -- `ord_D(g) = d · mult_π(g)` for every nonzero `g`
  have hwf : WfDvdMonoid (X.presheaf.stalk y) := IsNoetherianRing.wfDvdMonoid
  have hπnu : ¬IsUnit π := fun h => (IsLocalRing.mem_maximalIdeal _).mp hπmem h
  have hformula : ∀ g : X.presheaf.stalk y, g ≠ 0 →
      D.ord (sp g) = d * ((emultiplicity π g).toNat : ℤ) := by
    intro g hg
    have hfin : FiniteMultiplicity π g := FiniteMultiplicity.of_not_isUnit hπnu hg
    obtain ⟨h, hgh, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hndvd (dvd_zero _)
    have hspπ : sp π ≠ 0 := fun e => hπ0 (hinj (e.trans (map_zero _).symm))
    have hsph : sp h ≠ 0 := fun e => hh0 (hinj (e.trans (map_zero _).symm))
    have hordh : D.ord (sp h) = 0 := by
      rw [hsp_eq]
      exact hord_unit _ (hunit_of h hndvd)
    rw [hfin.emultiplicity_eq_multiplicity, ENat.toNat_natCast]
    conv_lhs => rw [hgh, map_mul, map_pow]
    rw [D.ord_mul (pow_ne_zero _ hspπ) hsph, D.ord_pow hspπ, hordh, add_zero, ← hd, mul_comm]
  -- `d = 1`
  have hd1 : d = 1 := by
    obtain ⟨x, hx⟩ := PrimeDivisorOver'.exists_ord_eq_one D
    obtain ⟨a, b, hb, hab⟩ := exists_specializationMap_mul_eq' hηgen hηy x
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [PrimeDivisorOver.ord, map_zero, Scheme.ord_zero] at hx
      exact absurd hx (by norm_num)
    have hspb : sp b ≠ 0 := fun e => hb (hinj (e.trans (map_zero _).symm))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hab
      exact mul_ne_zero hx0 hspb hab
    have h1 := D.ord_mul hx0 hspb
    rw [hab, hx, hformula a ha0, hformula b hb] at h1
    have hdvd : d ∣ 1 := ⟨((emultiplicity π a).toNat : ℤ) - ((emultiplicity π b).toNat : ℤ),
      by linarith⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega
  rw [hformula g hg, hd1, one_mul]

end PrimeDivisorOver'

end SGPT.NAPotential.AlgPrimes2

end
