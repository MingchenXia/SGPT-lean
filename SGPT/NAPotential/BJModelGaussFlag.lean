import SGPT.NAPotential.BJModelFlagIdeal
import SGPT.NAPotential.BJModelGauss

/-!
# The function of a flag ideal is minus the Gauss extension of its value

Source: `chapter_NApotential.tex`, equations `eq:va` and `eq:Gext`; Boucksom–Jonsson ([BJ22],
`references/bj22-trivval`), §2.1: for a flag ideal `𝔞 = ∑_λ 𝔞_λ t^{-λ}` and `v ∈ X^An`,
`σ(v)(𝔞) = min_λ (v(𝔞_λ) - λ)`, so that `φ_𝔞(v) = -σ(v)(𝔞)` ([BJ22, `equ:gaussflag`]). Lane
BJ-MODEL, step R4 of `claude-bj-energy:plan`; blueprint `claude-bj-model.tex`.

## Formal setting

For `v ∈ X^An` with support `y` and centre `c = c(v)` the Gauss extension `σ(v)` is the valuation
`gaussExtension v` of `κ(y)(t)`, given on `κ(y)[t]` by `eq:Gext`; elements of `𝒪_{X,c}[t]` are
evaluated through the specialization map `𝒪_{X,c} → κ(y)`. Let `b` bound the weights of `𝔞`
(`𝔞_λ = 0` for `λ > b`). Then `t^b 𝔞` is an ideal of `𝒪_{X × 𝔸¹}`, and its module of sections over
`Spec 𝒪_{X,c} × 𝔸¹` is

`flagStalk 𝔞 c b = {∑_k g_k t^k ∈ 𝒪_{X,c}[t] : g_k ∈ (𝔞_{b-k})_c for all k}`.

(The centre of `σ(v)` on `X × 𝔸¹` is the generic point of `c × {0}`; localizing further does not
change the infimum below, as `σ(v) = 0` on the units of that local ring.)

## Main result

* `isGLB_gaussVal_flagStalk`: `inf {σ(v)(g) : g ∈ t^b 𝔞} = b - φ_𝔞(v)`, i.e.
  `σ(v)(𝔞) = -φ_𝔞(v)` ([BJ22, `equ:gaussflag`]).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJModel

open AlgebraicGeometry CategoryTheory Polynomial
open scoped ENNReal
open SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f]

/-- The Gauss extension `σ(v)` of a semi-valuation `v ∈ X^An` (`eq:Gext`), as a valuation of
`κ(y)(t)`, `y` the support of `v`. -/
def berkovichGaussExtension (v : BerkovichPoint f) :
    letI := residueComplexAlgebra f v.support
    SourceRealValuation (FractionRing (X.residueField v.support)[X]) :=
  letI := residueComplexAlgebra f v.support
  gaussExtension v.val

/-- The value `σ(v)(g)` of a polynomial `g ∈ 𝒪_{X,c(v)}[t]`, through the specialization map
`𝒪_{X,c(v)} → κ(y)`: `σ(v)(∑ g_k t^k) = min_k (v(g_k) + k)` (`eq:Gext`). -/
def gaussStalkVal (v : BerkovichPoint f) (g : (X.presheaf.stalk v.center)[X]) :
    WithTop ℝ :=
  @gaussVal _ _ (residueComplexAlgebra f v.support) v.val
    (g.map (BerkovichPoint.specializationMap v.support_specializes_center).hom)

/-- `σ(v)` on `𝒪_{X,c(v)}[t]` is the Gauss extension `berkovichGaussExtension v` of `eq:Gext`
applied to the image in `κ(y)[t] ⊆ κ(y)(t)`. -/
theorem gaussStalkVal_eq (v : BerkovichPoint f) (g : (X.presheaf.stalk v.center)[X]) :
    letI := residueComplexAlgebra f v.support
    gaussStalkVal v g = berkovichGaussExtension v
      (algebraMap _ (FractionRing (X.residueField v.support)[X])
        (g.map (BerkovichPoint.specializationMap v.support_specializes_center).hom)) := by
  let := residueComplexAlgebra f v.support
  exact (gaussExtension_algebraMap v.val _).symm

/-- The module of sections of `t^b 𝔞` over `Spec 𝒪_{X,c} × 𝔸¹`: the polynomials
`∑_k g_k t^k` with `g_k ∈ (𝔞_{b-k})_c`. -/
def FlagIdeal.flagStalk (𝔞 : FlagIdeal X) (c : X) (b : ℤ) : Set ((X.presheaf.stalk c)[X]) :=
  {g | ∀ k : ℕ, g.coeff k ∈ stalkIdeal (𝔞.ideal (b - k)) c}

section

variable (v : BerkovichPoint f)

theorem gaussStalkVal_le_iff (g : (X.presheaf.stalk v.center)[X]) (r : WithTop ℝ) :
    r ≤ gaussStalkVal v g ↔ ∀ k : ℕ, r ≤ v.centerVal (g.coeff k) + ((k : ℝ) : WithTop ℝ) := by
  unfold gaussStalkVal
  rw [@le_gaussVal_iff _ _ (residueComplexAlgebra f v.support)]
  simp only [coeff_map]
  rfl

theorem gaussStalkVal_C_mul_X_pow (g : X.presheaf.stalk v.center) (k : ℕ) :
    gaussStalkVal v (C g * Polynomial.X ^ k) = v.centerVal g + ((k : ℝ) : WithTop ℝ) := by
  let := residueComplexAlgebra f v.support
  unfold gaussStalkVal
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, gaussVal_mul,
    gaussVal_C]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, gaussVal_mul, ih, gaussVal_X]
    push_cast
    rfl

/-- `ofReal a ≤ toENNReal x` iff `a ≤ x` in `(-∞, ∞]`, for `x ≥ 0`. -/
theorem ofReal_le_toENNReal_iff {x : WithTop ℝ} (hx : 0 ≤ x) (a : ℝ) :
    ENNReal.ofReal a ≤ toENNReal x ↔ ((a : ℝ) : WithTop ℝ) ≤ x := by
  cases x with
  | top => simp
  | coe r =>
    have hr : 0 ≤ r := by exact_mod_cast hx
    rw [toENNReal_coe, ENNReal.ofReal_le_ofReal_iff hr, WithTop.coe_le_coe]

/-- **`σ(v)(𝔞) = -φ_𝔞(v)`** ([BJ22, `equ:gaussflag`] from `eq:Gext`): if `𝔞_λ = 0` for `λ > b`,
the infimum of `σ(v)` over the sections of `t^b 𝔞` over `Spec 𝒪_{X,c(v)} × 𝔸¹` is
`b - φ_𝔞(v)`. -/
theorem isGLB_gaussVal_flagStalk (𝔞 : FlagIdeal X) {b : ℤ} (hb : ∀ l, b < l → 𝔞.ideal l = ⊥) :
    IsGLB (gaussStalkVal v '' 𝔞.flagStalk v.center b)
      ((((b : ℝ) - 𝔞.phi v : ℝ) : WithTop ℝ)) := by
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    rw [gaussStalkVal_le_iff]
    intro k
    have h1 := 𝔞.ofReal_sub_phi_le v (b - k)
    have h2 := (h1.trans (v.idealVal_le _ (hg k)))
    unfold BerkovichPoint.centerValENN at h2
    rw [ofReal_le_toENNReal_iff (v.centerVal_nonneg _)] at h2
    calc ((((b : ℝ) - 𝔞.phi v : ℝ)) : WithTop ℝ)
        = ((((b - k : ℤ) : ℝ) - 𝔞.phi v : ℝ) : WithTop ℝ) + ((k : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]
          congr 1
          push_cast
          ring
      _ ≤ v.centerVal (g.coeff k) + ((k : ℝ) : WithTop ℝ) := add_le_add_left h2 _
  · intro B hB
    by_contra hlt
    rw [not_le] at hlt
    -- a real number strictly between `b - φ_𝔞(v)` and `B`
    obtain ⟨r, hr1, hr2⟩ : ∃ r : ℝ, (b : ℝ) - 𝔞.phi v < r ∧ ((r : ℝ) : WithTop ℝ) < B := by
      induction B with
      | top => exact ⟨(b : ℝ) - 𝔞.phi v + 1, by linarith, WithTop.coe_lt_top _⟩
      | coe B =>
        have hB' : (b : ℝ) - 𝔞.phi v < B := by exact_mod_cast hlt
        exact ⟨((b : ℝ) - 𝔞.phi v + B) / 2, by linarith, by
          rw [WithTop.coe_lt_coe]; linarith⟩
    obtain ⟨l, hl⟩ := (𝔞.lt_phi_iff v (b - r)).mp (by linarith)
    have hlb : l ≤ b := by
      by_contra h
      rw [hb l (not_le.mp h), idealVal_bot] at hl
      exact not_top_lt hl
    obtain ⟨g, hgmem, hglt⟩ : ∃ g ∈ stalkIdeal (𝔞.ideal l) v.center,
        v.centerValENN g < ENNReal.ofReal (l - (b - r)) := by
      have := hl
      unfold BerkovichPoint.idealVal at this
      simp only [iInf_lt_iff] at this
      obtain ⟨g, hg, h⟩ := this
      exact ⟨g, hg, h⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = b - l := ⟨(b - l).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hmem : C g * Polynomial.X ^ k ∈ 𝔞.flagStalk v.center b := by
      intro j
      rw [coeff_C_mul_X_pow]
      split_ifs with hj
      · subst hj
        rw [hk, sub_sub_cancel]
        exact hgmem
      · exact Submodule.zero_mem _
    have hval := hB ⟨_, hmem, rfl⟩
    rw [gaussStalkVal_C_mul_X_pow] at hval
    -- `v(g) < l - b + r`
    have hg' : v.centerVal g < (((l : ℝ) - (b - r) : ℝ) : WithTop ℝ) := by
      unfold BerkovichPoint.centerValENN at hglt
      rw [← not_le] at hglt ⊢
      exact fun h => hglt ((ofReal_le_toENNReal_iff (v.centerVal_nonneg g) _).mpr h)
    have hsum : v.centerVal g + ((k : ℝ) : WithTop ℝ) < ((r : ℝ) : WithTop ℝ) := by
      have hk' : (k : ℝ) = (b : ℝ) - l := by exact_mod_cast hk
      calc v.centerVal g + ((k : ℝ) : WithTop ℝ)
          < (((l : ℝ) - (b - r) : ℝ) : WithTop ℝ) + ((k : ℝ) : WithTop ℝ) :=
            WithTop.add_lt_add_right WithTop.coe_ne_top hg'
        _ = ((r : ℝ) : WithTop ℝ) := by
            rw [← WithTop.coe_add, hk']
            congr 1
            ring
    exact absurd (hval.trans_lt hsum) (not_lt.mpr hr2.le)

end

end SGPT.NAPotential.BJModel
