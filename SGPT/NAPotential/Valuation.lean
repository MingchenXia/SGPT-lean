import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Real-valued valuations of a function field

Source `def:NApotential:L878` of `chapter_NApotential.tex`: a (real-valued) valuation of
`ℂ(X)` is a map `v : ℂ(X) → (-∞, ∞]` with
1. `v f = ∞ ↔ f = 0`;
2. `v (f g) = v f + v g`;
3. `v (f + g) ≥ min (v f) (v g)`;
4. `v c = 0` for `c ∈ ℂ^×`.

The definition only uses the field `ℂ(X)` with its `ℂ`-algebra structure, so it is stated
for an arbitrary field `K` with a `ℂ`-algebra structure (to be specialised to `K = ℂ(X)`).
The value set `(-∞, ∞]` is `WithTop ℝ`.  We show that these are exactly Mathlib's additive
valuations `AddValuation K (WithTop ℝ)` which are trivial on `ℂ^×` and have trivial support.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential

/-- Source `def:NApotential:L878`: a real-valued valuation of the field `K ⊇ ℂ`. -/
structure SourceRealValuation (K : Type*) [Field K] [Algebra ℂ K] where
  /-- The valuation map `v : K → (-∞, ∞]`. -/
  toFun : K → WithTop ℝ
  /-- Condition 1: `v f = ∞` if and only if `f = 0`. -/
  eq_top_iff' : ∀ f : K, toFun f = ⊤ ↔ f = 0
  /-- Condition 2: `v (f g) = v f + v g`. -/
  map_mul' : ∀ f g : K, toFun (f * g) = toFun f + toFun g
  /-- Condition 3: `v (f + g) ≥ min (v f) (v g)`. -/
  min_le_map_add' : ∀ f g : K, min (toFun f) (toFun g) ≤ toFun (f + g)
  /-- Condition 4: `v c = 0` for every `c ∈ ℂ^×`. -/
  map_complex' : ∀ c : ℂ, c ≠ 0 → toFun (algebraMap ℂ K c) = 0

variable {K : Type*} [Field K] [Algebra ℂ K]

namespace SourceRealValuation

instance : CoeFun (SourceRealValuation K) (fun _ => K → WithTop ℝ) := ⟨SourceRealValuation.toFun⟩

@[ext] theorem ext {v w : SourceRealValuation K} (h : ∀ f, v f = w f) : v = w := by
  cases v
  cases w
  congr
  funext f
  exact h f

theorem map_zero (v : SourceRealValuation K) : v 0 = ⊤ := (v.eq_top_iff' 0).mpr rfl

theorem map_one (v : SourceRealValuation K) : v 1 = 0 := by
  have h := v.map_complex' 1 one_ne_zero
  rwa [_root_.map_one] at h

/-- A source valuation is a Mathlib additive valuation with values in `WithTop ℝ`. -/
def toAddValuation (v : SourceRealValuation K) : AddValuation K (WithTop ℝ) :=
  AddValuation.of v.toFun v.map_zero v.map_one v.min_le_map_add' v.map_mul'

@[simp] theorem toAddValuation_apply (v : SourceRealValuation K) (f : K) :
    v.toAddValuation f = v f := rfl

/-- The additive valuation attached to a source valuation is trivial on `ℂ^×` and vanishes to
order `∞` only at `0`. -/
theorem toAddValuation_spec (v : SourceRealValuation K) :
    (∀ f : K, v.toAddValuation f = ⊤ ↔ f = 0) ∧
      ∀ c : ℂ, c ≠ 0 → v.toAddValuation (algebraMap ℂ K c) = 0 :=
  ⟨v.eq_top_iff', v.map_complex'⟩

/-- Conversely every such additive valuation is a source valuation. -/
def ofAddValuation (w : AddValuation K (WithTop ℝ)) (htop : ∀ f : K, w f = ⊤ ↔ f = 0)
    (hconst : ∀ c : ℂ, c ≠ 0 → w (algebraMap ℂ K c) = 0) : SourceRealValuation K where
  toFun := w
  eq_top_iff' := htop
  map_mul' := w.map_mul
  min_le_map_add' := w.map_add
  map_complex' := hconst

/-- Source valuations of `K` are exactly the additive valuations `K → WithTop ℝ` with trivial
support that are trivial on `ℂ^×`. -/
def equivAddValuation :
    SourceRealValuation K ≃
      {w : AddValuation K (WithTop ℝ) // (∀ f : K, w f = ⊤ ↔ f = 0) ∧
        ∀ c : ℂ, c ≠ 0 → w (algebraMap ℂ K c) = 0} where
  toFun v := ⟨v.toAddValuation, v.toAddValuation_spec⟩
  invFun w := ofAddValuation w.val w.property.1 w.property.2
  left_inv v := by
    ext f
    rfl
  right_inv w := by
    apply Subtype.ext
    ext f
    rfl

/-- The trivial valuation `v_triv` (`v_triv(f) = 0` for `f ≠ 0`) is a source valuation. -/
def trivial [DecidableEq K] : SourceRealValuation K where
  toFun f := if f = 0 then ⊤ else 0
  eq_top_iff' f := by
    by_cases hf : f = 0 <;> simp [hf]
  map_mul' f g := by
    by_cases hf : f = 0 <;> by_cases hg : g = 0 <;> simp [hf, hg]
  min_le_map_add' f g := by
    by_cases hf : f = 0 <;> by_cases hg : g = 0 <;> by_cases hfg : f + g = 0 <;>
      simp [hf, hg, hfg]
  map_complex' c hc := by
    simp [hc]

end SourceRealValuation

/-- The set `X^val` of valuations on `X`, for `K = ℂ(X)`. -/
abbrev SourceValuationSpace (K : Type*) [Field K] [Algebra ℂ K] := SourceRealValuation K

end SGPT.NAPotential

end
