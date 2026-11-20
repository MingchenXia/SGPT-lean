import SGPT.Checks.Comparison.BJModel2BerkovichMap
import SGPT.Foundations.Envelope.Algebra.NormalDVR
import SGPT.Support.Principalization.Scheme.IdealSheaf.StalkLe
import SGPT.Support.Principalization.Scheme.IdealSheaf.Invertible
import SGPT.Support.Principalization.Scheme.IdealSheaf.Order.Basic
import SGPT.Support.Principalization.Scheme.BlowUp.Transform
import SGPT.Support.Principalization.Scheme.BlowUp.InvertibleSheaf

/-!
# Divisorial points of normal schemes and effectivity of Cartier divisors (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), §2.2 (on a normal test configuration a vertical
`ℚ`-Cartier divisor `D` is determined by the values `ord_E(D)` at the components `E` of the
central fibre) and §3.2 (`defi:intpairing`, well-definedness of the energy pairing). Towards
`thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

Let `Y` be an integral locally Noetherian scheme all of whose local rings are integrally closed
(a normal scheme), e.g. the normalized test configurations `normModel` of lane BJ-MODEL3.

* `idealSheaf_le_of_forall_dvr`: **effectivity is detected at the points with a discrete
  valuation ring as local ring.** For an ideal sheaf `J` and an invertible ideal sheaf `K`,
  `J ≤ K` as soon as `J_z ≤ K_z` at every point `z` whose local ring is a DVR (Krull's
  description of a Noetherian normal domain as the intersection of its localizations at height
  one primes, in SGPT.Foundations.Envelope's form `mem_span_singleton_iff_forall_minimalPrimes`).
* `ordPoint`: for such a point `z`, the semi-valuation `ord_z ∈ Y^An` (support the generic point,
  valuation the order of vanishing along the prime divisor `closure {z}`), with centre `z`
  (`isCenter_ordPoint`) and `ord_z(J) = ordIdeal J_z` (`idealVal_ordPoint`), where `ordIdeal` is
  the order of an ideal of the DVR `𝒪_{Y,z}`;
* `idealSheaf_le_of_forall_idealVal`: hence `J ≤ K` as soon as `ord_z(K) ≤ ord_z(J)` for all
  such `z`;
* `colon_isInvertible`, `eq_mul_colon`: for invertible `J ≤ K` the colon `(J : K)` is invertible
  and `J = K (J : K)` (the effective divisor `div J - div K`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open SGPT.NAPotential.Berkovich
open SGPT.NAPotential.Berkovich.BerkovichPoint (specializationMap)
open scoped ENNReal

/-! ### The order of an ideal of a discrete valuation ring -/

section dvr

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The order `ord(I) = min_{a ∈ I} ord(a) ∈ [0, ∞]` of an ideal of a discrete valuation ring. -/
def ordIdeal (I : Ideal R) : ℝ≥0∞ :=
  ⨅ a ∈ I, ((IsDiscreteValuationRing.addVal R a : ℕ∞) : ℝ≥0∞)

/-- The order of an ideal is the order of a generator. -/
theorem ordIdeal_eq (I : Ideal R) :
    ordIdeal I = ((IsDiscreteValuationRing.addVal R (Submodule.IsPrincipal.generator I) : ℕ∞) :
      ℝ≥0∞) := by
  apply le_antisymm
  · exact iInf₂_le _ (Submodule.IsPrincipal.generator_mem I)
  · refine le_iInf₂ fun a ha => ?_
    have hdvd : Submodule.IsPrincipal.generator I ∣ a :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp ha |>.elim fun c hc =>
        ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
    exact ENat.toENNReal_le.mpr ((IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hdvd)

/-- **Ideals of a discrete valuation ring are ordered by their orders**:
`I ≤ I' ↔ ord(I') ≤ ord(I)`. -/
theorem le_iff_ordIdeal_le (I I' : Ideal R) : I ≤ I' ↔ ordIdeal I' ≤ ordIdeal I := by
  constructor
  · intro h
    exact le_iInf₂ fun a ha => iInf₂_le a (h ha)
  · intro h
    rw [ordIdeal_eq, ordIdeal_eq, ENat.toENNReal_le, IsDiscreteValuationRing.addVal_le_iff_dvd] at h
    rw [← Ideal.span_singleton_generator I, ← Ideal.span_singleton_generator I',
      Ideal.span_singleton_le_span_singleton]
    exact h

/-- The order of a proper ideal is positive. -/
theorem ordIdeal_pos {I : Ideal R} (hI : I ≠ ⊤) : 0 < ordIdeal I := by
  rw [ordIdeal_eq, pos_iff_ne_zero, Ne, ENat.toENNReal_eq_zero,
    IsDiscreteValuationRing.addVal_eq_zero_iff]
  intro hu
  apply hI
  rw [← Ideal.span_singleton_generator I]
  exact Ideal.span_singleton_eq_top.mpr hu

/-- The order of a nonzero ideal is finite. -/
theorem ordIdeal_ne_top {I : Ideal R} (hI : I ≠ ⊥) : ordIdeal I ≠ ⊤ := by
  rw [ordIdeal_eq, Ne, ENat.toENNReal_eq_top, IsDiscreteValuationRing.addVal_eq_top_iff]
  intro h0
  apply hI
  rw [← Ideal.span_singleton_generator I, h0, Ideal.span_singleton_eq_bot]

/-- The order of the unit ideal is `0`. -/
theorem ordIdeal_top : ordIdeal (⊤ : Ideal R) = 0 :=
  le_antisymm ((iInf₂_le 1 Submodule.mem_top).trans (by
    rw [IsDiscreteValuationRing.addVal_one]; simp)) zero_le

end dvr

/-! ### Normal schemes: effectivity at the points of codimension one -/

section normal

universe u

variable {Y : Scheme.{u}} [IsIntegral Y]

omit [IsIntegral Y] in
theorem fromSpec_mem_of_affine (U : Y.affineOpens) (P : PrimeSpectrum Γ(Y, U)) :
    U.2.fromSpec P ∈ (U : Y.Opens) := by
  have : U.2.fromSpec P ∈ Set.range U.2.fromSpec := Set.mem_range_self _
  rwa [U.2.range_fromSpec] at this

/-- **Sections of a normal integral scheme over affine opens are integrally closed** (the local
rings are their localizations at the primes). -/
theorem isIntegrallyClosed_of_affineOpen (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.affineOpens) [Nonempty U] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  have hx := fromSpec_mem_of_affine U ⟨P, hP.isPrime⟩
  let _ := Y.presheaf.algebra_section_stalk ⟨U.2.fromSpec ⟨P, hP.isPrime⟩, hx⟩
  have : IsLocalization P.primeCompl (Y.presheaf.stalk (U.2.fromSpec ⟨P, hP.isPrime⟩)) :=
    U.2.isLocalization_stalk' ⟨P, hP.isPrime⟩ hx
  exact (hN _).of_equiv (IsLocalization.algEquiv P.primeCompl
    (Y.presheaf.stalk (U.2.fromSpec ⟨P, hP.isPrime⟩)) (Localization.AtPrime P)).toRingEquiv

/-- The pointwise form of `idealSheaf_le_of_forall_dvr`. -/
theorem stalkIdeal_le_of_forall_dvr [IsLocallyNoetherian Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {J K : Y.IdealSheafData} (hK : K.IsInvertible)
    (h : ∀ z : Y, IsDiscreteValuationRing (Y.presheaf.stalk z) →
      J.stalkIdeal z ≤ K.stalkIdeal z) (x : Y) :
    J.stalkIdeal x ≤ K.stalkIdeal x := by
  obtain ⟨W, hxW, g, hg, hKW⟩ := hK x
  have : Nonempty (W : Y.Opens) := ⟨⟨x, hxW⟩⟩
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian W
  have : IsIntegrallyClosed Γ(Y, W) := isIntegrallyClosed_of_affineOpen hN W
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  suffices hJW : J.ideal W ≤ K.ideal W by
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ J W hxW,
      Scheme.IdealSheafData.stalkIdeal_eq_map_germ K W hxW]
    exact Ideal.map_mono hJW
  intro a ha
  rw [hKW, SGPT.Foundations.Envelope.mem_span_singleton_iff_forall_minimalPrimes hg0]
  intro P hP
  have : P.IsPrime := hP.1.1
  have hz := fromSpec_mem_of_affine W ⟨P, this⟩
  set z := W.2.fromSpec ⟨P, this⟩ with hzdef
  let _ := Y.presheaf.algebra_section_stalk ⟨z, hz⟩
  have hloc : IsLocalization P.primeCompl (Y.presheaf.stalk z) :=
    W.2.isLocalization_stalk' ⟨P, this⟩ hz
  have hdvr : IsDiscreteValuationRing (Y.presheaf.stalk z) := by
    have := SGPT.Foundations.Envelope.isDiscreteValuationRing_localization_of_mem_minimalPrimes hg0 hP
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (Y.presheaf.stalk z))
  have hle := h z hdvr
  have hgerm : ∀ b : Γ(Y, W),
      (Y.presheaf.germ W z hz).hom b = algebraMap Γ(Y, W) (Y.presheaf.stalk z) b :=
    fun b => rfl
  have haz : algebraMap Γ(Y, W) (Y.presheaf.stalk z) a ∈ K.stalkIdeal z := by
    apply hle
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ J W hz]
    exact Ideal.mem_map_of_mem _ ha
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ K W hz, hKW, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at haz
  obtain ⟨c, hc⟩ := haz
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl c
  simp only at hrs
  have heq : algebraMap Γ(Y, W) (Y.presheaf.stalk z) (s * a) =
      algebraMap Γ(Y, W) (Y.presheaf.stalk z) (r * g) := by
    rw [map_mul, map_mul, ← hrs, ← hc, ← hgerm g]
    ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Y.presheaf.stalk z)).mp heq
  refine ⟨(t : Γ(Y, W)) * s, fun hts => ?_, ?_⟩
  · rcases this.mem_or_mem hts with h1 | h1
    · exact t.2 h1
    · exact s.2 h1
  · rw [Ideal.mem_span_singleton']
    exact ⟨t * r, by rw [mul_assoc, ← ht]; ring⟩

/-- **Effectivity is detected in codimension one** ([BJ22, §2.2]; Krull). On an integral locally
Noetherian scheme with integrally closed local rings, an ideal sheaf `J` is contained in an
invertible ideal sheaf `K` as soon as `J_z ≤ K_z` at every point `z` whose local ring is a
discrete valuation ring. -/
theorem idealSheaf_le_of_forall_dvr [IsLocallyNoetherian Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {J K : Y.IdealSheafData} (hK : K.IsInvertible)
    (h : ∀ z : Y, IsDiscreteValuationRing (Y.presheaf.stalk z) →
      J.stalkIdeal z ≤ K.stalkIdeal z) : J ≤ K :=
  Scheme.IdealSheafData.le_of_forall_stalkIdeal_le_of_isMaximal fun _ _ _ =>
    stalkIdeal_le_of_forall_dvr hN hK h _

end normal

/-! ### The colon of invertible ideal sheaves -/

section colon

universe u

variable {Y : Scheme.{u}} [IsIntegral Y]

omit [IsIntegral Y] in
/-- Two ideal sheaves with the same stalks are equal. -/
theorem idealSheaf_eq_of_stalkIdeal_eq {I J : Y.IdealSheafData}
    (h : ∀ x : Y, I.stalkIdeal x = J.stalkIdeal x) : I = J :=
  le_antisymm (Scheme.IdealSheafData.le_of_forall_stalkIdeal_le_of_isMaximal fun _ _ _ =>
      (h _).le)
    (Scheme.IdealSheafData.le_of_forall_stalkIdeal_le_of_isMaximal fun _ _ _ => (h _).ge)

/-- For invertible `J ≤ K`, the stalk of the colon `(J : K)` is principal, generated by the
nonzero element `a / h` (`J_x = (a)`, `K_x = (h)`). -/
theorem exists_stalkIdeal_colon_eq {J K : Y.IdealSheafData} (hJ : J.IsInvertible)
    (hK : K.IsInvertible) (hJK : J ≤ K) (x : Y) :
    ∃ c ∈ nonZeroDivisors (Y.presheaf.stalk x), (J.colon K).stalkIdeal x = Ideal.span {c} ∧
      K.stalkIdeal x * Ideal.span {c} = J.stalkIdeal x := by
  obtain ⟨a, ha, hJx⟩ := hJ.exists_mem_nonZeroDivisors_stalkIdeal_eq_span x
  obtain ⟨g, hg, hKx⟩ := hK.exists_mem_nonZeroDivisors_stalkIdeal_eq_span x
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hax : a ∈ K.stalkIdeal x := by
    apply Scheme.IdealSheafData.stalkIdeal_mono hJK
    rw [hJx]
    exact Ideal.mem_span_singleton_self a
  rw [hKx, Ideal.mem_span_singleton'] at hax
  obtain ⟨c, hc⟩ := hax
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hc
    exact ha0 hc.symm
  refine ⟨c, mem_nonZeroDivisors_of_ne_zero hc0, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.stalkIdeal_colon_of_isInvertible J hK x, hJx, hKx]
    ext y
    rw [Submodule.mem_colon, Ideal.mem_span_singleton']
    constructor
    · intro hy
      have h1 := hy g (Ideal.mem_span_singleton_self g)
      rw [Ideal.mem_span_singleton'] at h1
      obtain ⟨d, hd⟩ := h1
      refine ⟨d, ?_⟩
      rw [← hc, smul_eq_mul] at hd
      have h2 : (d * c - y) * g = 0 := by rw [sub_mul, mul_assoc, hd]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hg0)
    · rintro ⟨d, rfl⟩ p hp
      rw [SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
      rw [Ideal.mem_span_singleton']
      obtain ⟨e, rfl⟩ := hp
      exact ⟨d * e, by rw [smul_eq_mul, ← hc]; ring⟩
  · rw [hKx, hJx, Ideal.span_singleton_mul_span_singleton, ← hc, mul_comm]

/-- **The colon of invertible ideal sheaves `J ≤ K` is invertible.** -/
theorem colon_isInvertible [IsLocallyNoetherian Y] {J K : Y.IdealSheafData} (hJ : J.IsInvertible) (hK : K.IsInvertible)
    (hJK : J ≤ K) : (J.colon K).IsInvertible :=
  Scheme.IdealSheafData.isInvertible_of_forall_stalkIdeal_eq_span _ fun x => by
    obtain ⟨c, hc, h1, -⟩ := exists_stalkIdeal_colon_eq hJ hK hJK x
    exact ⟨c, hc, h1⟩

/-- **`J = K · (J : K)`** for invertible `J ≤ K`. -/
theorem eq_mul_colon {J K : Y.IdealSheafData} (hJ : J.IsInvertible) (hK : K.IsInvertible)
    (hJK : J ≤ K) : J = K * J.colon K :=
  idealSheaf_eq_of_stalkIdeal_eq fun x => by
    obtain ⟨c, -, h1, h2⟩ := exists_stalkIdeal_colon_eq hJ hK hJK x
    rw [Scheme.IdealSheafData.stalkIdeal_mul, h1, h2]

/-- The zero locus of the colon `(J : K)` lies in that of `J`. -/
theorem support_colon_subset {J K : Y.IdealSheafData} (hJ : J.IsInvertible)
    (hK : K.IsInvertible) (hJK : J ≤ K) :
    ((J.colon K).support : Set Y) ⊆ J.support := by
  intro x hx
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal] at hx ⊢
  rw [eq_mul_colon hJ hK hJK, Scheme.IdealSheafData.stalkIdeal_mul]
  exact Ideal.mul_le_right.trans hx

end colon

/-! ### The semi-valuation of a point of codimension one -/

section ordPoint

variable {Y : Scheme.{0}} [IsIntegral Y] (fY : Y ⟶ Spec (.of ℂ))

theorem genericPoint_specializes' (z : Y) : genericPoint Y ⤳ z :=
  (genericPoint_spec Y).specializes trivial

/-- The residue map of the generic point is an isomorphism `ℂ(Y) ≅ κ(ξ)`. -/
def genericResidueEquiv : Y.functionField ≃+* Y.residueField (genericPoint Y) :=
  RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩

theorem genericResidueEquiv_apply (a : Y.functionField) :
    genericResidueEquiv a = (Y.residue (genericPoint Y)).hom a := rfl

/-- `ℕ∞ → (-∞, ∞]`. -/
def natTop (n : ℕ∞) : WithTop ℝ := WithTop.map (fun k : ℕ => (k : ℝ)) n

@[simp] theorem natTop_top : natTop ⊤ = ⊤ := rfl

@[simp] theorem natTop_coe (k : ℕ) : natTop (k : ℕ∞) = ((k : ℝ) : WithTop ℝ) := rfl

theorem natTop_add (a b : ℕ∞) : natTop (a + b) = natTop a + natTop b := by
  cases a with
  | top => simp
  | coe a =>
    cases b with
    | top => simp
    | coe b =>
      rw [← ENat.natCast_add, natTop_coe, natTop_coe, natTop_coe, Nat.cast_add, WithTop.coe_add]

theorem natTop_mono : Monotone natTop := by
  intro a b hab
  cases b with
  | top => exact le_top
  | coe b =>
    cases a with
    | top => exact absurd hab (WithTop.not_top_le_coe b)
    | coe a =>
      rw [natTop_coe, natTop_coe, WithTop.coe_le_coe]
      exact_mod_cast hab

@[simp] theorem natTop_zero : natTop 0 = 0 := by
  change natTop ((0 : ℕ) : ℕ∞) = 0
  rw [natTop_coe, Nat.cast_zero, WithTop.coe_zero]

theorem natTop_nonneg (a : ℕ∞) : 0 ≤ natTop a := by
  have := natTop_mono (zero_le : (0 : ℕ∞) ≤ a)
  rwa [natTop_zero] at this

theorem toENNReal_natTop (a : ℕ∞) : toENNReal (natTop a) = (a : ℝ≥0∞) := by
  cases a with
  | top => simp
  | coe a => rw [natTop_coe, toENNReal_coe, ENNReal.ofReal_natCast]; rfl

variable (z : Y)

/-- The `ℂ`-structure of `𝒪_{Y,z}`. -/
def stalkComplexHom : CommRingCat.of ℂ ⟶ Y.presheaf.stalk z :=
  Spec.preimage (Y.fromSpecStalk z ≫ fY)

/-- The `ℂ`-structure of `κ(ξ)` factors through the specialization map `𝒪_{Y,z} → κ(ξ)`. -/
theorem residueComplexHom_eq :
    residueComplexHom fY (genericPoint Y) =
      stalkComplexHom fY z ≫ specializationMap (genericPoint_specializes' z) := by
  apply Spec.map_injective
  rw [spec_map_residueComplexHom, Spec.map_comp, stalkComplexHom, Spec.map_preimage,
    Scheme.fromSpecResidueField, specializationMap, Spec.map_comp]
  simp only [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]

theorem specializationMap_eq (a : Y.presheaf.stalk z) :
    (specializationMap (genericPoint_specializes' z)).hom a =
      genericResidueEquiv (algebraMap (Y.presheaf.stalk z) Y.functionField a) := rfl

variable [IsDiscreteValuationRing (Y.presheaf.stalk z)]

/-- The order of vanishing `ord_z` on the local ring `𝒪_{Y,z}` (a DVR), with values in
`(-∞, ∞]`. -/
def dvrAddVal : AddValuation (Y.presheaf.stalk z) (WithTop ℝ) :=
  AddValuation.of (fun a => natTop (IsDiscreteValuationRing.addVal _ a))
    (by simp)
    (by simp)
    (fun a b => by
      rw [← natTop_mono.map_min]
      exact natTop_mono (IsDiscreteValuationRing.addVal_add))
    (fun a b => by rw [IsDiscreteValuationRing.addVal_mul, natTop_add])

theorem dvrAddVal_apply (a : Y.presheaf.stalk z) :
    dvrAddVal z a = natTop (IsDiscreteValuationRing.addVal _ a) := rfl

theorem nonZeroDivisors_le_dvr_primeCompl :
    nonZeroDivisors (Y.presheaf.stalk z) ≤
      (AddValuation.toValuation (dvrAddVal z)).supp.primeCompl := by
  intro a ha hsupp
  have h : a ∈ AddValuation.supp (dvrAddVal z) := hsupp
  rw [AddValuation.mem_supp_iff, dvrAddVal_apply] at h
  have h' : IsDiscreteValuationRing.addVal _ a = ⊤ := by
    cases hv : IsDiscreteValuationRing.addVal (Y.presheaf.stalk z) a with
    | top => rfl
    | coe k => rw [hv, natTop_coe] at h; exact absurd h WithTop.coe_ne_top
  exact nonZeroDivisors.ne_zero ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h')

/-- `ord_z` on the function field `ℂ(Y) = Frac 𝒪_{Y,z}`. -/
def dvrFracAddVal : AddValuation Y.functionField (WithTop ℝ) :=
  AddValuation.ofValuation ((AddValuation.toValuation (dvrAddVal z)).extendToLocalization
    (nonZeroDivisors_le_dvr_primeCompl z) Y.functionField)

theorem dvrFracAddVal_algebraMap (a : Y.presheaf.stalk z) :
    dvrFracAddVal z (algebraMap (Y.presheaf.stalk z) Y.functionField a) = dvrAddVal z a := by
  rw [dvrFracAddVal, AddValuation.ofValuation_apply,
    Valuation.extendToLocalization_apply_map_apply, AddValuation.toValuation_apply]
  rfl

/-- **The divisorial semi-valuation `ord_z ∈ Y^An`** of a point `z` whose local ring is a discrete
valuation ring: support the generic point of `Y`, valuation the order of vanishing along the
prime divisor `closure {z}`. -/
def ordPoint : BerkovichPoint fY where
  support := genericPoint Y
  val :=
    letI := residueComplexAlgebra fY (genericPoint Y)
    SourceRealValuation.ofAddValuation
      ((dvrFracAddVal z).comap (genericResidueEquiv (Y := Y)).symm.toRingHom)
      (fun _ => AddValuation.top_iff _)
      (fun c hc => by
        change dvrFracAddVal z (genericResidueEquiv.symm
          ((residueComplexHom fY (genericPoint Y)).hom c)) = 0
        rw [residueComplexHom_eq fY z, CommRingCat.hom_comp, RingHom.comp_apply, specializationMap_eq,
          RingEquiv.symm_apply_apply, dvrFracAddVal_algebraMap, dvrAddVal_apply]
        have hu : IsUnit ((stalkComplexHom fY z).hom c) := (IsUnit.mk0 c hc).map _
        rw [(IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu, natTop_zero])

@[simp] theorem ordPoint_support : (ordPoint fY z).support = genericPoint Y := rfl

/-- The values of `ord_z` on the local ring at `z`. -/
theorem ordPoint_valAt_specializationMap (h : (ordPoint fY z).support ⤳ z)
    (a : Y.presheaf.stalk z) :
    (ordPoint fY z).valAt ((specializationMap h).hom a) =
      natTop (IsDiscreteValuationRing.addVal _ a) := by
  change dvrFracAddVal z (genericResidueEquiv.symm
    (genericResidueEquiv (algebraMap (Y.presheaf.stalk z) Y.functionField a))) = _
  rw [RingEquiv.symm_apply_apply, dvrFracAddVal_algebraMap, dvrAddVal_apply]

/-- **`z` is the centre of `ord_z`.** -/
theorem isCenter_ordPoint : (ordPoint fY z).IsCenter z := by
  refine ⟨genericPoint_specializes' z, fun a => ?_, fun a ha => ?_⟩
  · rw [ordPoint_valAt_specializationMap]
    exact natTop_nonneg _
  · rw [ordPoint_valAt_specializationMap]
    have hne : IsDiscreteValuationRing.addVal (Y.presheaf.stalk z) a ≠ 0 := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
      exact mem_nonunits_iff.mp ((mem_maximalIdeal a).mp ha)
    have h1 : ((1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal (Y.presheaf.stalk z) a :=
      Order.one_le_iff_ne_zero.mpr hne
    have h2 := natTop_mono h1
    rw [natTop_coe] at h2
    refine lt_of_lt_of_le ?_ h2
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe]
    norm_num

variable [IsProper fY]

theorem ordPoint_center : (ordPoint fY z).center = z :=
  ((ordPoint fY z).isCenter_iff_eq_center z).mp (isCenter_ordPoint fY z) |>.symm

/-- **`ord_z(J) = ord(J_z)`**: the value of an ideal sheaf at `ord_z` is the order of its stalk
at `z`. -/
theorem idealVal_ordPoint (J : Y.IdealSheafData) :
    (ordPoint fY z).idealVal J = ordIdeal (J.stalkIdeal z) := by
  rw [idealVal_eq_of_isCenter (ordPoint fY z) (isCenter_ordPoint fY z) J, ordIdeal]
  refine iInf_congr fun a => iInf_congr fun _ => ?_
  rw [ordPoint_valAt_specializationMap, toENNReal_natTop]

/-- **Comparison of stalks at a divisorial point**: `J_z ≤ K_z ↔ ord_z(K) ≤ ord_z(J)`. -/
theorem stalkIdeal_le_iff_idealVal_le (J K : Y.IdealSheafData) :
    J.stalkIdeal z ≤ K.stalkIdeal z ↔
      (ordPoint fY z).idealVal K ≤ (ordPoint fY z).idealVal J := by
  rw [idealVal_ordPoint, idealVal_ordPoint]
  exact le_iff_ordIdeal_le _ _

/-- At a point of the zero locus the value is positive. -/
theorem idealVal_ordPoint_pos {J : Y.IdealSheafData} (hz : z ∈ J.support) :
    0 < (ordPoint fY z).idealVal J := by
  rw [idealVal_ordPoint]
  apply ordIdeal_pos
  intro htop
  have := (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal J z).mp hz
  rw [htop] at this
  exact (maximalIdeal.isMaximal (Y.presheaf.stalk z)).ne_top (top_le_iff.mp this)

/-- Off the zero locus the value is `0`. -/
theorem idealVal_ordPoint_eq_zero {J : Y.IdealSheafData} (hz : z ∉ J.support) :
    (ordPoint fY z).idealVal J = 0 := by
  rw [idealVal_ordPoint]
  have : J.stalkIdeal z = ⊤ := by
    by_contra hne
    apply hz
    rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal J z]
    exact le_maximalIdeal hne
  rw [this, ordIdeal_top]

/-- Invertible ideal sheaves have finite values. -/
theorem idealVal_ordPoint_ne_top {J : Y.IdealSheafData} (hJ : J.IsInvertible) :
    (ordPoint fY z).idealVal J ≠ ⊤ := by
  rw [idealVal_ordPoint]
  apply ordIdeal_ne_top
  obtain ⟨g, hg, hJz⟩ := hJ.exists_mem_nonZeroDivisors_stalkIdeal_eq_span z
  rw [hJz, Ne, Ideal.span_singleton_eq_bot]
  exact nonZeroDivisors.ne_zero hg

end ordPoint

section ordPointNormal

variable {Y : Scheme.{0}} [IsIntegral Y] (fY : Y ⟶ Spec (.of ℂ)) [IsProper fY]
  [IsLocallyNoetherian Y]

/-- **Effectivity from the divisorial values** ([BJ22, §2.2]): on a normal integral locally
Noetherian scheme proper over `ℂ`, `J ≤ K` (with `K` invertible) as soon as
`ord_z(K) ≤ ord_z(J)` at every point `z` with a discrete valuation ring as local ring. -/
theorem idealSheaf_le_of_forall_idealVal
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {J K : Y.IdealSheafData} (hK : K.IsInvertible)
    (h : ∀ (z : Y) (_ : IsDiscreteValuationRing (Y.presheaf.stalk z)),
      (ordPoint fY z).idealVal K ≤ (ordPoint fY z).idealVal J) : J ≤ K :=
  idealSheaf_le_of_forall_dvr hN hK fun z hz =>
    (stalkIdeal_le_iff_idealVal_le fY z J K).mpr (h z hz)

end ordPointNormal

end SGPT.NAPotential.BJ
