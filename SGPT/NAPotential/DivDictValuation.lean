import SGPT.NAPotential.BerkovichDivisorial
import SGPT.NAPotential.BerkovichIdealValue
import SGPT.NAPotential.GAGAMult2Faithful

/-! # Values of semi-valuations on ideal sheaves: sections, centres and scaling

Source: `chapter_NApotential.tex`, equation `eq:va` and the paragraph on divisorial valuations
(Section *Valuations* of the recap of Boucksom–Jonsson's theory).  Blueprint
`claude-div-dict:sections`, `claude-div-dict:scaling`.

For a semi-valuation `v ∈ X^An` on a scheme `X` proper over `ℂ` and an ideal sheaf `𝔞`, the
value `v(𝔞) = min {v(g) : g ∈ 𝔞_{c(v)}}` (`BerkovichPoint.idealVal`) is computed here

* from the values of the sections of `𝔞` over one affine open neighbourhood `U` of the centre:
  `v(𝔞) = inf {v(r) : r ∈ 𝔞(U)}` (`BerkovichPoint.idealVal_eq_iInf_sectionVal`);
* at any point `c` known to be a centre of `v` (`BerkovichPoint.idealVal_eq_of_isCenter`).

For a prime divisor `D` over `X` (`PrimeDivisorOver`) the divisorial valuations `t ord_D`, `t > 0`,
all have the same centre (`PrimeDivisorOver.center_ordVal`) and

`(t ord_D)(𝔞) = t · ord_D(𝔞)`   (`PrimeDivisorOver.idealVal_ordVal`),

where `ord_D(𝔞) := (1 · ord_D)(𝔞)` (`PrimeDivisorOver.ordIdeal`).  This is the homogeneity of
divisorial valuations used in the book's proof of `lma:anaorder` (`eq:legendre_NA`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open scoped ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}

/-! ### Scaling of `[0, ∞]`-valued values -/

/-- Multiplication of a value `a ∈ (-∞, ∞]` by a real number `t` (`t · ∞ = ∞`). -/
def scaleVal (t : ℝ) : WithTop ℝ → WithTop ℝ
  | ⊤ => ⊤
  | (r : ℝ) => ((t * r : ℝ) : WithTop ℝ)

@[simp] theorem scaleVal_top (t : ℝ) : scaleVal t ⊤ = ⊤ := rfl

@[simp] theorem scaleVal_coe (t r : ℝ) : scaleVal t (r : WithTop ℝ) = ((t * r : ℝ) : WithTop ℝ) :=
  rfl

theorem scaleVal_nonneg_iff {t : ℝ} (ht : 0 < t) (a : WithTop ℝ) : 0 ≤ scaleVal t a ↔ 0 ≤ a := by
  cases a with
  | top => simp
  | coe r =>
    rw [scaleVal_coe]
    constructor
    · intro h
      have h' : (0 : ℝ) ≤ t * r := by exact_mod_cast h
      exact_mod_cast (mul_nonneg_iff_of_pos_left ht).mp h'
    · intro h
      have h' : (0 : ℝ) ≤ r := by exact_mod_cast h
      exact_mod_cast mul_nonneg ht.le h'

theorem scaleVal_pos_iff {t : ℝ} (ht : 0 < t) (a : WithTop ℝ) : 0 < scaleVal t a ↔ 0 < a := by
  cases a with
  | top => simp
  | coe r =>
    rw [scaleVal_coe]
    constructor
    · intro h
      have h' : (0 : ℝ) < t * r := by exact_mod_cast h
      exact_mod_cast (mul_pos_iff_of_pos_left ht).mp h'
    · intro h
      have h' : (0 : ℝ) < r := by exact_mod_cast h
      exact_mod_cast mul_pos ht h'

theorem toENNReal_scaleVal {t : ℝ} (ht : 0 < t) (a : WithTop ℝ) :
    toENNReal (scaleVal t a) = ENNReal.ofReal t * toENNReal a := by
  cases a with
  | top =>
    rw [scaleVal_top, toENNReal_top, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.mpr ht).ne'
  | coe r => rw [scaleVal_coe, toENNReal_coe, toENNReal_coe, ENNReal.ofReal_mul ht.le]

namespace BerkovichPoint

/-! ### Values at a centre -/

/-- The value at a germ of a section: `v(s_c) = v(s)` for a section `s` over an open set `U`
containing the point `c` of the support of `v`. -/
theorem valAt_specializationMap_germ (v : BerkovichPoint f) {c : X} (h : v.support ⤳ c)
    (U : X.Opens) (hc : c ∈ U) (s : Γ(X, U)) :
    v.valAt ((specializationMap h).hom ((X.presheaf.germ U c hc).hom s)) =
      v.sectionVal U (h.mem_open U.isOpen hc) s := by
  unfold sectionVal specializationMap
  have e : (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U c hc).hom s) =
      (X.presheaf.germ U v.support (h.mem_open U.isOpen hc)).hom s :=
    congrArg (fun φ => φ.hom s) (X.presheaf.germ_stalkSpecializes hc h)
  change v.valAt ((X.residue v.support).hom ((X.presheaf.stalkSpecializes h).hom
    ((X.presheaf.germ U c hc).hom s))) = _
  rw [e]
  rfl

variable [IsProper f]

/-- `v(𝔞)` computed at any point `c` known to be a centre of `v`. -/
theorem idealVal_eq_of_isCenter (v : BerkovichPoint f) (𝔞 : X.IdealSheafData) {c : X}
    (hc : v.IsCenter c) :
    v.idealVal 𝔞 = ⨅ g ∈ stalkIdeal 𝔞 c, toENNReal (v.valAt ((specializationMap hc.choose).hom g)) := by
  have hcc := (v.isCenter_iff_eq_center c).mp hc
  subst hcc
  rfl

/-- The value of a germ of a section at the centre. -/
theorem centerVal_germ (v : BerkovichPoint f) (U : X.Opens) (hc : v.center ∈ U) (s : Γ(X, U)) :
    v.centerVal ((X.presheaf.germ U v.center hc).hom s) =
      v.sectionVal U (v.support_specializes_center.mem_open U.isOpen hc) s :=
  v.valAt_specializationMap_germ v.support_specializes_center U hc s

/-- Source `eq:va` on an affine chart: for an affine open neighbourhood `U` of the centre,
`v(𝔞) = inf {v(r) : r ∈ 𝔞(U)}`. -/
theorem idealVal_eq_iInf_sectionVal (v : BerkovichPoint f) (𝔞 : X.IdealSheafData)
    (U : X.affineOpens) (hc : v.center ∈ (U : X.Opens)) :
    v.idealVal 𝔞 = ⨅ r ∈ 𝔞.ideal U, toENNReal (v.sectionVal U
      (v.support_specializes_center.mem_open (U : X.Opens).isOpen hc) r) := by
  have hspan : Ideal.span ((X.presheaf.germ U v.center hc).hom '' (𝔞.ideal U : Set Γ(X, U))) =
      stalkIdeal 𝔞 v.center := by
    rw [stalkIdeal_eq_map 𝔞 U hc]
    rfl
  rw [v.idealVal_eq_iInf_of_span 𝔞 hspan, iInf_image]
  refine iInf_congr fun r => iInf_congr fun _ => ?_
  unfold centerValENN
  rw [v.centerVal_germ U hc r]

end BerkovichPoint

/-! ### Divisorial valuations: scaling -/

namespace PrimeDivisorOver

variable (D : PrimeDivisorOver X)

/-- `(t ord_D)(g) = t · (ord_D)(g)` for every rational function `g`. -/
theorem ordVal_valAt_eq_scaleVal (t : ℝ) (ht : 0 < t)
    (g : X.residueField (D.π (genericPoint D.Y))) :
    (D.ordVal f t ht).valAt g = scaleVal t ((D.ordVal f 1 one_pos).valAt g) := by
  by_cases hg : g = 0
  · subst hg
    rw [BerkovichPoint.valAt_zero]
    have h1 : (D.ordVal f 1 one_pos).valAt (0 : X.residueField (D.π (genericPoint D.Y))) = ⊤ :=
      BerkovichPoint.valAt_zero _
    rw [h1, scaleVal_top]
  · rw [D.ordVal_valAt t ht hg, D.ordVal_valAt 1 one_pos hg, scaleVal_coe, one_mul]

/-- The divisorial valuations `t ord_D`, `t > 0`, have the same centres. -/
theorem isCenter_ordVal_iff (t : ℝ) (ht : 0 < t) (c : X) :
    (D.ordVal f t ht).IsCenter c ↔ (D.ordVal f 1 one_pos).IsCenter c := by
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, fun g => ?_, fun g hg => ?_⟩
    · have := h1 g
      rw [D.ordVal_valAt_eq_scaleVal t ht] at this
      exact (scaleVal_nonneg_iff ht _).mp this
    · have := h2 g hg
      rw [D.ordVal_valAt_eq_scaleVal t ht] at this
      exact (scaleVal_pos_iff ht _).mp this
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, fun g => ?_, fun g hg => ?_⟩
    · rw [D.ordVal_valAt_eq_scaleVal t ht]
      exact (scaleVal_nonneg_iff ht _).mpr (h1 g)
    · rw [D.ordVal_valAt_eq_scaleVal t ht]
      exact (scaleVal_pos_iff ht _).mpr (h2 g hg)

variable [IsProper f]

/-- The centre of `t ord_D` does not depend on `t > 0`. -/
theorem center_ordVal (t : ℝ) (ht : 0 < t) :
    (D.ordVal f t ht).center = (D.ordVal f 1 one_pos).center :=
  ((D.ordVal f 1 one_pos).isCenter_iff_eq_center _).mp
    ((D.isCenter_ordVal_iff t ht _).mp (D.ordVal f t ht).isCenter_center)

variable (f) in
/-- `ord_D(𝔞) ∈ [0, ∞]`: the value of the divisorial valuation `ord_D` on an ideal sheaf `𝔞` of
`X` (`eq:va` for `v = ord_D`). -/
def ordIdeal (𝔞 : X.IdealSheafData) : ℝ≥0∞ :=
  (D.ordVal f 1 one_pos).idealVal 𝔞

/-- Homogeneity of divisorial valuations on ideal sheaves: `(t ord_D)(𝔞) = t · ord_D(𝔞)`. -/
theorem idealVal_ordVal (t : ℝ) (ht : 0 < t) (𝔞 : X.IdealSheafData) :
    (D.ordVal f t ht).idealVal 𝔞 = ENNReal.ofReal t * D.ordIdeal f 𝔞 := by
  have hc1 : (D.ordVal f 1 one_pos).IsCenter (D.ordVal f 1 one_pos).center :=
    (D.ordVal f 1 one_pos).isCenter_center
  have hct : (D.ordVal f t ht).IsCenter (D.ordVal f 1 one_pos).center :=
    (D.isCenter_ordVal_iff t ht _).mpr hc1
  rw [ordIdeal, (D.ordVal f t ht).idealVal_eq_of_isCenter 𝔞 hct,
    (D.ordVal f 1 one_pos).idealVal_eq_of_isCenter 𝔞 hc1]
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  simp_rw [ENNReal.mul_iInf_of_ne ht0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun g => iInf_congr fun _ => ?_
  rw [← toENNReal_scaleVal ht]
  exact congrArg toENNReal (D.ordVal_valAt_eq_scaleVal t ht _)

end PrimeDivisorOver

end SGPT.NAPotential.Berkovich

end
