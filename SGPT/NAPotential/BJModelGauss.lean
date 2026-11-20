import SGPT.NAPotential.BerkovichSpace
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Gauss extension of a valuation

Source: `chapter_NApotential.tex`, equation `eq:Gext` (Section *Valuations* of the recap of
Boucksom–Jonsson's theory): *given any valuation `v` on `X`, the Gauss extension of `v` is a
valuation `σ(v)` on `X × 𝔸¹`,*

`σ(v)(∑_i f_i t^i) := min_i (v(f_i) + i)`,

*where `t` is the standard coordinate on `𝔸¹ = Spec ℂ[t]`.* Also Boucksom–Jonsson ([BJ22],
`references/bj22-trivval`), §1.3 (`sec:Gauss`). Lane BJ-MODEL, step R4 of `claude-bj-energy:plan`
(PL functions via the Gauss extension); blueprint `claude-bj-model.tex`.

## Formal setting

A valuation of `X` is a `SourceRealValuation` of a field `K ⊇ ℂ` (for `K = ℂ(X)`, or the
residue field `κ(y)` of the support of a semi-valuation). The function field of `X × 𝔸¹` is
`K(t) = FractionRing K[t]`. The formula `eq:Gext` defines `σ(v)` on `K[t]` (`gaussVal`); that it
is a valuation is the content of Gauss's lemma, which we obtain from Mathlib's multiplicativity of
the Gauss norm `‖∑ f_i t^i‖ = max_i |f_i| c^i` for the nonarchimedean absolute value
`|f| = e^{-v(f)}` and `c = e^{-1}` (`Polynomial.gaussNorm_mul`). It extends uniquely to `K(t)`.

## Main definitions

* `gaussVal v f = min_i (v(f_i) + i)` for `f ∈ K[t]` (literally `eq:Gext`).
* `gaussExtension v : SourceRealValuation (FractionRing K[t])`: the Gauss extension `σ(v)`.

## Main results

* `gaussVal_mul`, `min_le_gaussVal_add`, `gaussVal_eq_top_iff`: `σ(v)` is a valuation of `K[t]`.
* `gaussExtension_algebraMap`: `σ(v)` is given by `eq:Gext` on polynomials;
  `gaussExtension_unique`: it is the only valuation of `K(t)` with these values.
* `gaussExtension_C`, `gaussExtension_X`: `σ(v)` extends `v`, and `σ(v)(t) = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJModel

open Polynomial

/-! ### `e^{-x}` on `(-∞, ∞]`

We use `SGPT.NAPotential.Berkovich.BerkovichPoint.expNeg` (`expNeg ⊤ = 0`,
`expNeg r = e^{-r}`). -/

open SGPT.NAPotential.Berkovich.BerkovichPoint

theorem expNeg_eq_zero_iff {a : WithTop ℝ} : expNeg a = 0 ↔ a = ⊤ := by
  cases a with
  | top => simp
  | coe r => simp [expNeg_coe, (Real.exp_pos _).ne']

theorem expNeg_add (a b : WithTop ℝ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a with
  | top => simp
  | coe r =>
    cases b with
    | top => simp
    | coe s =>
      rw [← WithTop.coe_add, expNeg_coe, expNeg_coe, expNeg_coe, ← Real.exp_add]
      congr 1
      ring

theorem expNeg_le_expNeg_iff {a b : WithTop ℝ} : expNeg a ≤ expNeg b ↔ b ≤ a := by
  cases a with
  | top => exact iff_of_true (expNeg_nonneg b) le_top
  | coe r =>
    cases b with
    | top =>
      refine iff_of_false ?_ ?_
      · rw [expNeg_coe, expNeg_top, not_le]
        exact Real.exp_pos _
      · exact fun h => WithTop.coe_ne_top (top_le_iff.mp h)
    | coe s =>
      rw [expNeg_coe, expNeg_coe, Real.exp_le_exp, neg_le_neg_iff, WithTop.coe_le_coe]

theorem expNeg_injective : Function.Injective expNeg := fun _ _ h =>
  le_antisymm (expNeg_le_expNeg_iff.mp h.ge) (expNeg_le_expNeg_iff.mp h.le)

theorem expNeg_min (a b : WithTop ℝ) : expNeg (min a b) = max (expNeg a) (expNeg b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (expNeg_le_expNeg_iff.mpr h)]
  · rw [min_eq_right h, max_eq_right (expNeg_le_expNeg_iff.mpr h)]

/-! ### The absolute value `e^{-v}` -/

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- The nonarchimedean absolute value `|f| = e^{-v(f)}` of a valuation `v`. -/
def absValue (v : SourceRealValuation K) : AbsoluteValue K ℝ where
  toFun x := expNeg (v x)
  map_mul' x y := by
    change expNeg (v.toFun (x * y)) = expNeg (v.toFun x) * expNeg (v.toFun y)
    rw [v.map_mul', expNeg_add]
  nonneg' x := expNeg_nonneg _
  eq_zero' x := by
    change expNeg (v.toFun x) = 0 ↔ x = 0
    rw [expNeg_eq_zero_iff, v.eq_top_iff']
  add_le' x y := by
    change expNeg (v.toFun (x + y)) ≤ expNeg (v.toFun x) + expNeg (v.toFun y)
    calc expNeg (v.toFun (x + y)) ≤ max (expNeg (v.toFun x)) (expNeg (v.toFun y)) := by
          rw [← expNeg_min]
          exact expNeg_le_expNeg_iff.mpr (v.min_le_map_add' x y)
      _ ≤ expNeg (v.toFun x) + expNeg (v.toFun y) :=
          max_le_add_of_nonneg (expNeg_nonneg _) (expNeg_nonneg _)

@[simp] theorem absValue_apply (v : SourceRealValuation K) (x : K) :
    absValue v x = expNeg (v x) := rfl

theorem isNonarchimedean_absValue (v : SourceRealValuation K) :
    IsNonarchimedean (absValue v) := fun x y => by
  rw [absValue_apply, absValue_apply, absValue_apply, ← expNeg_min]
  exact expNeg_le_expNeg_iff.mpr (v.min_le_map_add' x y)

/-! ### The Gauss extension on polynomials (`eq:Gext`) -/

/-- **The Gauss extension on polynomials** (`eq:Gext`):
`σ(v)(∑_i f_i t^i) = min_i (v(f_i) + i)`, the minimum over the coefficients (it is `∞` for the zero
polynomial). -/
def gaussVal (v : SourceRealValuation K) (f : K[X]) : WithTop ℝ :=
  f.support.inf fun i => v (f.coeff i) + ((i : ℝ) : WithTop ℝ)

variable (v : SourceRealValuation K)

/-- `σ(v)(f) ≤ v(f_i) + i` for every `i` (the minimum may be taken over all `i`). -/
theorem gaussVal_le (f : K[X]) (i : ℕ) :
    gaussVal v f ≤ v (f.coeff i) + ((i : ℝ) : WithTop ℝ) := by
  by_cases hi : i ∈ f.support
  · exact Finset.inf_le (f := fun i => v (f.coeff i) + ((i : ℝ) : WithTop ℝ)) hi
  · rw [notMem_support_iff.mp hi, v.map_zero, WithTop.top_add]
    exact le_top

theorem le_gaussVal_iff (f : K[X]) (r : WithTop ℝ) :
    r ≤ gaussVal v f ↔ ∀ i : ℕ, r ≤ v (f.coeff i) + ((i : ℝ) : WithTop ℝ) :=
  ⟨fun h i => h.trans (gaussVal_le v f i), fun h => Finset.le_inf fun i _ => h i⟩

/-- The minimum in `eq:Gext` is attained. -/
theorem exists_gaussVal_eq {f : K[X]} (hf : f ≠ 0) :
    ∃ i, gaussVal v f = v (f.coeff i) + ((i : ℝ) : WithTop ℝ) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf f.support (nonempty_support_iff.mpr hf)
    (fun i => v (f.coeff i) + ((i : ℝ) : WithTop ℝ))
  exact ⟨i, hi⟩

@[simp] theorem gaussVal_zero : gaussVal v 0 = ⊤ := by
  simp [gaussVal]

/-- `σ(v)(c) = v(c)` for constants `c ∈ K`. -/
@[simp] theorem gaussVal_C (a : K) : gaussVal v (C a) = v a := by
  apply le_antisymm
  · simpa using gaussVal_le v (C a) 0
  · rw [le_gaussVal_iff]
    intro i
    rw [coeff_C]
    split_ifs with hi
    · subst hi
      simp
    · rw [v.map_zero, WithTop.top_add]
      exact le_top

@[simp] theorem gaussVal_one : gaussVal v 1 = 0 := by
  rw [← C_1, gaussVal_C, SourceRealValuation.map_one]

/-- `σ(v)(t) = 1`. -/
@[simp] theorem gaussVal_X : gaussVal v X = 1 := by
  apply le_antisymm
  · have h := gaussVal_le v X 1
    rwa [coeff_X_one, SourceRealValuation.map_one, zero_add, Nat.cast_one, WithTop.coe_one] at h
  · rw [le_gaussVal_iff]
    intro i
    rw [coeff_X]
    split_ifs with hi
    · subst hi
      rw [SourceRealValuation.map_one, zero_add, Nat.cast_one, WithTop.coe_one]
    · rw [v.map_zero, WithTop.top_add]
      exact le_top

theorem gaussVal_eq_top_iff (f : K[X]) : gaussVal v f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    ext i
    have hi := gaussVal_le v f i
    rw [h, top_le_iff, WithTop.add_eq_top] at hi
    rcases hi with hi | hi
    · rw [coeff_zero]
      exact (v.eq_top_iff' _).mp hi
    · exact absurd hi WithTop.coe_ne_top
  · rintro rfl
    exact gaussVal_zero v

/-- The Gauss norm `max_i e^{-v(f_i)} e^{-i}` is `e^{-σ(v)(f)}`. -/
theorem gaussNorm_absValue (f : K[X]) :
    f.gaussNorm (absValue v) (Real.exp (-1)) = expNeg (gaussVal v f) := by
  by_cases hf : f = 0
  · subst hf
    simp
  have hs : f.support.Nonempty := nonempty_support_iff.mpr hf
  have hterm : ∀ i : ℕ, absValue v (f.coeff i) * Real.exp (-1) ^ i =
      expNeg (v (f.coeff i) + ((i : ℝ) : WithTop ℝ)) := by
    intro i
    rw [absValue_apply, expNeg_add, expNeg_coe, ← Real.exp_nat_mul,
      show (i : ℝ) * -1 = -(i : ℝ) by ring]
  rw [gaussNorm, dif_pos hs]
  apply le_antisymm
  · refine Finset.sup'_le hs _ fun i hi => ?_
    rw [hterm]
    exact expNeg_le_expNeg_iff.mpr
      (Finset.inf_le (f := fun i => v (f.coeff i) + ((i : ℝ) : WithTop ℝ)) hi)
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf f.support hs
      (fun i => v (f.coeff i) + ((i : ℝ) : WithTop ℝ))
    rw [gaussVal, heq, ← hterm]
    exact Finset.le_sup' (fun i => absValue v (f.coeff i) * Real.exp (-1) ^ i) hi

/-- **Gauss's lemma**: `σ(v)(f g) = σ(v)(f) + σ(v)(g)`. -/
theorem gaussVal_mul (f g : K[X]) : gaussVal v (f * g) = gaussVal v f + gaussVal v g := by
  apply expNeg_injective
  rw [expNeg_add, ← gaussNorm_absValue, ← gaussNorm_absValue, ← gaussNorm_absValue]
  exact gaussNorm_mul (isNonarchimedean_absValue v) (Real.exp_pos _) f g

/-- The ultrametric inequality for `σ(v)`. -/
theorem min_le_gaussVal_add (f g : K[X]) :
    min (gaussVal v f) (gaussVal v g) ≤ gaussVal v (f + g) := by
  rw [le_gaussVal_iff]
  intro i
  rw [coeff_add]
  calc min (gaussVal v f) (gaussVal v g)
      ≤ min (v (f.coeff i) + ((i : ℝ) : WithTop ℝ)) (v (g.coeff i) + ((i : ℝ) : WithTop ℝ)) :=
        min_le_min (gaussVal_le v f i) (gaussVal_le v g i)
    _ = min (v (f.coeff i)) (v (g.coeff i)) + ((i : ℝ) : WithTop ℝ) := min_add_add_right _ _ _
    _ ≤ v (f.coeff i + g.coeff i) + ((i : ℝ) : WithTop ℝ) :=
        add_le_add_left (v.min_le_map_add' _ _) _

/-- `σ(v)` as an additive valuation of `K[t]`. -/
def gaussAddVal : AddValuation K[X] (WithTop ℝ) :=
  AddValuation.of (gaussVal v) (gaussVal_zero v) (gaussVal_one v) (min_le_gaussVal_add v)
    (gaussVal_mul v)

@[simp] theorem gaussAddVal_apply (f : K[X]) : gaussAddVal v f = gaussVal v f := rfl

theorem nonZeroDivisors_le_primeCompl :
    nonZeroDivisors K[X] ≤ (AddValuation.toValuation (gaussAddVal v)).supp.primeCompl := by
  intro f hf hsupp
  have h : f ∈ AddValuation.supp (gaussAddVal v) := hsupp
  rw [AddValuation.mem_supp_iff, gaussAddVal_apply, gaussVal_eq_top_iff] at h
  exact nonZeroDivisors.ne_zero hf h

/-! ### The Gauss extension on the function field of `X × 𝔸¹` -/

/-- `σ(v)` as an additive valuation of `K(t) = FractionRing K[t]`: the extension of `gaussAddVal`
to the fraction field. -/
def gaussExtAddVal : AddValuation (FractionRing K[X]) (WithTop ℝ) :=
  AddValuation.ofValuation ((AddValuation.toValuation (gaussAddVal v)).extendToLocalization
    (nonZeroDivisors_le_primeCompl v) (FractionRing K[X]))

theorem gaussExtAddVal_algebraMap (f : K[X]) :
    gaussExtAddVal v (algebraMap K[X] (FractionRing K[X]) f) = gaussVal v f := by
  rw [gaussExtAddVal, AddValuation.ofValuation_apply, Valuation.extendToLocalization_apply_map_apply,
    AddValuation.toValuation_apply]
  rfl

/-- **The Gauss extension** `σ(v)` of a valuation `v` of `K ⊇ ℂ` (`eq:Gext`): a valuation of the
function field `K(t)` of `X × 𝔸¹` in the sense of `def:NApotential:L878`, given on polynomials by
`σ(v)(∑ f_i t^i) = min_i (v(f_i) + i)` (`gaussExtension_algebraMap`). -/
def gaussExtension : SourceRealValuation (FractionRing K[X]) :=
  SourceRealValuation.ofAddValuation (gaussExtAddVal v) (fun _ => AddValuation.top_iff _)
    (fun c hc => by
      rw [IsScalarTower.algebraMap_apply ℂ K[X] (FractionRing K[X]), gaussExtAddVal_algebraMap,
        Polynomial.algebraMap_apply, gaussVal_C]
      exact v.map_complex' c hc)

/-- **`eq:Gext`**: `σ(v)(∑_i f_i t^i) = min_i (v(f_i) + i)`. -/
theorem gaussExtension_algebraMap (f : K[X]) :
    gaussExtension v (algebraMap K[X] (FractionRing K[X]) f) =
      f.support.inf fun i => v (f.coeff i) + ((i : ℝ) : WithTop ℝ) :=
  gaussExtAddVal_algebraMap v f

/-- `σ(v)` extends `v`: `σ(v)(c) = v(c)` for `c ∈ K`. -/
theorem gaussExtension_C (a : K) :
    gaussExtension v (algebraMap K[X] (FractionRing K[X]) (C a)) = v a := by
  rw [gaussExtension_algebraMap, ← gaussVal, gaussVal_C]

/-- `σ(v)(t) = 1`. -/
theorem gaussExtension_X : gaussExtension v (algebraMap K[X] (FractionRing K[X]) X) = 1 := by
  rw [gaussExtension_algebraMap, ← gaussVal, gaussVal_X]

/-- **Uniqueness** ([BJ22, §1.3]): `σ(v)` is the unique valuation of `K(t)` given by `eq:Gext` on
`K[t]`. -/
theorem gaussExtension_unique (w : SourceRealValuation (FractionRing K[X]))
    (hw : ∀ f : K[X], w (algebraMap K[X] (FractionRing K[X]) f) = gaussVal v f) :
    w = gaussExtension v := by
  ext x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors K[X]) x
  have hs : ((s : K[X]) : K[X]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hmk : IsLocalization.mk' (FractionRing K[X]) a s *
      algebraMap K[X] (FractionRing K[X]) (s : K[X]) = algebraMap K[X] (FractionRing K[X]) a :=
    IsLocalization.mk'_spec _ a s
  have h1 := congrArg w.toFun hmk
  have h2 := congrArg (gaussExtension v).toFun hmk
  rw [w.map_mul'] at h1
  rw [(gaussExtension v).map_mul'] at h2
  have hfin : gaussVal v (s : K[X]) ≠ ⊤ := by
    rw [Ne, gaussVal_eq_top_iff]
    exact hs
  have hw' : ∀ f : K[X], w.toFun (algebraMap K[X] (FractionRing K[X]) f) = gaussVal v f := hw
  have hσ : ∀ f : K[X], (gaussExtension v).toFun (algebraMap K[X] (FractionRing K[X]) f) =
      gaussVal v f := gaussExtension_algebraMap v
  rw [hw', hw'] at h1
  rw [hσ, hσ] at h2
  exact WithTop.add_right_cancel hfin (h1.trans h2.symm)

end SGPT.NAPotential.BJModel
