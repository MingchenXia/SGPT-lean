import SGPT.NAPotential.TowerAlgOrder
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# The divisorial valuation of `ℂ(X)` defined by an analytic prime divisor


Let `p` be an analytic presentation of a prime divisor over `X(ℂ)` (a modification
`π : Y → X(ℂ)` and a smooth connected hypersurface `D ⊆ Y`), `y₀ ∈ D` with a flattening `Φ₀`,
and `P₀ ∈ X` the scheme point of `π(y₀)`.  The analytic order along `D`
(`SGPT.NAPotential.TowerAlg.stalkOrd`) is a discrete valuation of the local ring `𝒪_{X,P₀}`;
since `X` is integral, `ℂ(X)` is the fraction field of `𝒪_{X,P₀}` and the valuation extends.

* `stalkValuation`, `functionFieldValuation`, `residueValuation`: the valuation `ord_D` with values
  in `ℤᵐ⁰`, on `𝒪_{X,P₀}`, on `ℂ(X)`, and on `κ(η) = ℂ(X)` (`η` the generic point).
* `anDivVal p Φ₀ t ht ∈ X^An` (`t > 0`): the semi-valuation `t · ord_D` of `ℂ(X)`
  (`def:NApotential:L878`; trivial on `ℂ^×` because `ℂ^×` is divisible).  No algebraic model of
  `D` is used: this is the *analytic* divisorial valuation.
* `toENNReal_valAt_anDivVal`: its value on the image of `g ∈ 𝒪_{X,P₀}` is `t · ord_D(g)`.
* `center_anDivVal_specializes`: its centre is a generization of `P₀` (it is `≥ 0` on
  `𝒪_{X,P₀}`; valuative criterion of separatedness).
* `idealVal_anDivVal`: for an affine open `U₀ ∋ P₀` and an ideal sheaf `𝔞`,
  `(t ord_D)(𝔞) = inf_{r ∈ 𝔞(U₀)} t · ord_D(r)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.TowerAlg

open Set Filter
open scoped Topology ENNReal WithZero
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.CompactPrimeOver SGPT.NAPotential.Berkovich
open DemaillyApproximantDivisorialLelong

/-! ### `ℕ ∪ {∞}`-valued orders as `ℤᵐ⁰`-valued valuations -/

/-- `n ↦ exp (-n)`, `∞ ↦ 0`. -/
def ordToZ (a : ℕ∞) : ℤᵐ⁰ := if a = ⊤ then 0 else WithZero.exp (-(a.toNat : ℤ))

theorem ordToZ_eq_zero_iff (a : ℕ∞) : ordToZ a = 0 ↔ a = ⊤ := by
  unfold ordToZ
  split_ifs with h
  · simp [h]
  · simp [h]

theorem ordToZ_coe (n : ℕ) : ordToZ (n : ℕ∞) = WithZero.exp (-(n : ℤ)) := by
  simp [ordToZ]

@[simp] theorem ordToZ_top : ordToZ ⊤ = 0 := by simp [ordToZ]

@[simp] theorem ordToZ_zero : ordToZ 0 = 1 := by
  rw [← Nat.cast_zero, ordToZ_coe]
  simp

theorem ordToZ_add (a b : ℕ∞) : ordToZ (a + b) = ordToZ a * ordToZ b := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe b =>
      rw [← Nat.cast_add, ordToZ_coe, ordToZ_coe, ordToZ_coe, ← WithZero.exp_add]
      congr 1
      push_cast
      ring

theorem ordToZ_antitone : Antitone ordToZ := by
  intro a b hab
  induction b using ENat.recTopCoe with
  | top => simp
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => simp at hab
    | coe a =>
      rw [ordToZ_coe, ordToZ_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast hab

/-! ### Real valuations from `ℤᵐ⁰`-valued valuations -/

section IntValuation

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- A `ℤᵐ⁰`-valued valuation of a field containing `ℂ` is trivial on `ℂ^×` (`ℂ^×` is divisible). -/
theorem valuation_algebraMap_eq_one (v : Valuation K ℤᵐ⁰) {c : ℂ} (hc : c ≠ 0) :
    v (algebraMap ℂ K c) = 1 := by
  have hne : ∀ d : ℂ, d ≠ 0 → v (algebraMap ℂ K d) ≠ 0 := fun d hd =>
    (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ (algebraMap ℂ K).injective).mpr hd)
  have hdvd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ WithZero.log (v (algebraMap ℂ K c)) := by
    intro k hk
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hk
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hc (by rw [← hd, zero_pow hk.ne'])
    rw [← hd, map_pow, map_pow, WithZero.log_pow]
    exact ⟨WithZero.log (v (algebraMap ℂ K d)), by simp⟩
  set a := WithZero.log (v (algebraMap ℂ K c))
  have ha : a = 0 := by
    by_contra hk
    have h1 := hdvd (a.natAbs + 1) (Nat.succ_pos _)
    have h2 := Int.natAbs_dvd_natAbs.mpr h1
    rw [Int.natAbs_natCast] at h2
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hk) h2
    omega
  rw [← WithZero.exp_log (hne c hc)]
  change WithZero.exp a = 1
  rw [ha, WithZero.exp_zero]

open Classical in
/-- The real valuation `g ↦ -t log v(g)` (`t > 0`) of a `ℤᵐ⁰`-valued valuation `v`. -/
def ofIntValuation (v : Valuation K ℤᵐ⁰) (t : ℝ) (ht : 0 < t) : SourceRealValuation K where
  toFun g := if g = 0 then ⊤ else ((t * (-WithZero.log (v g) : ℤ) : ℝ) : WithTop ℝ)
  eq_top_iff' g := by
    by_cases hg : g = 0
    · simp [hg]
    · rw [if_neg hg]
      exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h hg⟩
  map_mul' g h := by
    by_cases hg : g = 0
    · simp [hg]
    by_cases hh : h = 0
    · simp [hh]
    have hg' : v g ≠ 0 := (Valuation.ne_zero_iff v).mpr hg
    have hh' : v h ≠ 0 := (Valuation.ne_zero_iff v).mpr hh
    rw [if_neg (mul_ne_zero hg hh), if_neg hg, if_neg hh, ← WithTop.coe_add, map_mul,
      WithZero.log_mul hg' hh']
    congr 1
    push_cast
    ring
  min_le_map_add' g h := by
    by_cases hgh : g + h = 0
    · simp [hgh]
    by_cases hg : g = 0
    · simp [hg]
    by_cases hh : h = 0
    · simp [hh]
    have hg' : v g ≠ 0 := (Valuation.ne_zero_iff v).mpr hg
    have hh' : v h ≠ 0 := (Valuation.ne_zero_iff v).mpr hh
    have hgh' : v (g + h) ≠ 0 := (Valuation.ne_zero_iff v).mpr hgh
    rw [if_neg hgh, if_neg hg, if_neg hh, ← WithTop.coe_min, WithTop.coe_le_coe]
    have hle : WithZero.log (v (g + h)) ≤ max (WithZero.log (v g)) (WithZero.log (v h)) := by
      rcases le_total (v g) (v h) with h1 | h1
      · rw [max_eq_right ((WithZero.log_le_log hg' hh').mpr h1),
          WithZero.log_le_log hgh' hh']
        exact (v.map_add g h).trans (max_eq_right h1).le
      · rw [max_eq_left ((WithZero.log_le_log hh' hg').mpr h1),
          WithZero.log_le_log hgh' hg']
        exact (v.map_add g h).trans (max_eq_left h1).le
    have hle' : min (-WithZero.log (v g)) (-WithZero.log (v h)) ≤ -WithZero.log (v (g + h)) := by
      rw [min_neg_neg]
      exact neg_le_neg hle
    have hleR : min ((-WithZero.log (v g) : ℤ) : ℝ) ((-WithZero.log (v h) : ℤ) : ℝ) ≤
        ((-WithZero.log (v (g + h)) : ℤ) : ℝ) := by
      rw [← Int.cast_min]
      exact_mod_cast hle'
    rw [← mul_min_of_nonneg _ _ ht.le]
    exact mul_le_mul_of_nonneg_left hleR ht.le
  map_complex' c hc := by
    have h0 : algebraMap ℂ K c ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ K).injective).mpr hc
    rw [if_neg h0, valuation_algebraMap_eq_one v hc]
    simp

theorem ofIntValuation_apply_of_ne_zero (v : Valuation K ℤᵐ⁰) (t : ℝ) (ht : 0 < t) {g : K}
    (hg : g ≠ 0) :
    ofIntValuation v t ht g = ((t * (-WithZero.log (v g) : ℤ) : ℝ) : WithTop ℝ) := by
  classical
  change (if g = 0 then ⊤ else _) = _
  convert if_neg hg

theorem ofIntValuation_apply_zero (v : Valuation K ℤᵐ⁰) (t : ℝ) (ht : 0 < t) :
    ofIntValuation v t ht 0 = ⊤ := SourceRealValuation.map_zero _

end IntValuation

/-! ### The analytic divisorial valuation -/

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance towerAlgValPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance towerAlgValPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance towerAlgValPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X] (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
  {y₀ : p.model} (Φ₀ : DivisorFlattening (m := m) p.divisor y₀)

/-- `ord_D` on `𝒪_{X,P₀}` as a `ℤᵐ⁰`-valued valuation. -/
def stalkValuation : Valuation (X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) ℤᵐ⁰ where
  toFun g := ordToZ (stalkOrd p Φ₀ g)
  map_zero' := by rw [stalkOrd_zero, ordToZ_top]
  map_one' := by rw [stalkOrd_one, ordToZ_zero]
  map_mul' g h := by rw [stalkOrd_mul, ordToZ_add]
  map_add_le_max' g h := by
    calc ordToZ (stalkOrd p Φ₀ (g + h)) ≤ ordToZ (min (stalkOrd p Φ₀ g) (stalkOrd p Φ₀ h)) :=
          ordToZ_antitone (min_le_stalkOrd_add p Φ₀ g h)
      _ = max (ordToZ (stalkOrd p Φ₀ g)) (ordToZ (stalkOrd p Φ₀ h)) :=
          ordToZ_antitone.map_min

omit [IsIntegral X] in
theorem stalkValuation_apply (g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) :
    stalkValuation p Φ₀ g = ordToZ (stalkOrd p Φ₀ g) := rfl

theorem le_primeCompl_supp_stalkValuation :
    nonZeroDivisors (X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) ≤
      (stalkValuation p Φ₀).supp.primeCompl := by
  intro s hs hsupp
  rw [SetLike.mem_coe, Valuation.mem_supp_iff, stalkValuation_apply, ordToZ_eq_zero_iff] at hsupp
  exact stalkOrd_ne_top p Φ₀ (nonZeroDivisors.ne_zero hs) hsupp

/-- `ord_D` on the function field `ℂ(X)`, the fraction field of `𝒪_{X,P₀}`. -/
def functionFieldValuation : Valuation X.functionField ℤᵐ⁰ :=
  (stalkValuation p Φ₀).extendToLocalization (le_primeCompl_supp_stalkValuation p Φ₀)
    X.functionField

/-- The identification `ℂ(X) ≅ κ(η)` (`η` the generic point). -/
def functionFieldResidueEquiv : X.functionField ≃+* X.residueField (genericPoint X) :=
  RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩

/-- `ord_D` on the residue field `κ(η) = ℂ(X)` of the generic point. -/
def residueValuation : Valuation (X.residueField (genericPoint X)) ℤᵐ⁰ :=
  (functionFieldValuation p Φ₀).comap (functionFieldResidueEquiv (X := X)).symm.toRingHom

/-- The generic point of `X` specializes to `P₀`. -/
theorem genericPoint_specializes (x : X) : genericPoint X ⤳ x :=
  (genericPoint_spec X).specializes trivial

/-- The value of `ord_D` on the image in `κ(η)` of a germ at `P₀`. -/
theorem residueValuation_specializationMap
    (g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) :
    residueValuation p Φ₀ ((BerkovichPoint.specializationMap
      (genericPoint_specializes (schemeComplexPointImage f (p.projection y₀)))).hom g) =
      ordToZ (stalkOrd p Φ₀ g) := by
  unfold residueValuation
  rw [Valuation.comap_apply]
  have h1 : (functionFieldResidueEquiv (X := X)).symm.toRingHom
      ((BerkovichPoint.specializationMap
        (genericPoint_specializes (schemeComplexPointImage f (p.projection y₀)))).hom g) =
      algebraMap (X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) X.functionField g := by
    change (functionFieldResidueEquiv (X := X)).symm
      ((functionFieldResidueEquiv (X := X)) ((X.presheaf.stalkSpecializes _).hom g)) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  rw [h1]
  unfold functionFieldValuation
  rw [Valuation.extendToLocalization_apply_map_apply]
  rfl

/-- **The analytic divisorial valuation `t · ord_D ∈ X^An`** (`t > 0`): the valuation of
`ℂ(X) = κ(η)` given by `t` times the order of vanishing along `D` of pull-backs to `Y`. -/
def anDivVal (t : ℝ) (ht : 0 < t) : BerkovichPoint f where
  support := genericPoint X
  val := @ofIntValuation _ _ (residueComplexAlgebra f (genericPoint X))
    (residueValuation p Φ₀) t ht

theorem anDivVal_support (t : ℝ) (ht : 0 < t) :
    (anDivVal p Φ₀ t ht).support = genericPoint X := rfl

/-- **Values of `t · ord_D` on germs at `P₀`**: `t · ord_D(g)`. -/
theorem toENNReal_valAt_anDivVal (t : ℝ) (ht : 0 < t)
    (g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) :
    toENNReal ((anDivVal p Φ₀ t ht).valAt ((BerkovichPoint.specializationMap
      (genericPoint_specializes (schemeComplexPointImage f (p.projection y₀)))).hom g)) =
      ENNReal.ofReal t * (stalkOrd p Φ₀ g : ℝ≥0∞) := by
  set x := (BerkovichPoint.specializationMap
    (genericPoint_specializes (schemeComplexPointImage f (p.projection y₀)))).hom g with hx
  have hv := residueValuation_specializationMap p Φ₀ g
  rw [← hx] at hv
  change toENNReal (@ofIntValuation _ _ (residueComplexAlgebra f (genericPoint X))
    (residueValuation p Φ₀) t ht x) = _
  induction h : stalkOrd p Φ₀ g using ENat.recTopCoe with
  | top =>
    rw [h, ordToZ_top] at hv
    have hx0 : x = 0 := (Valuation.zero_iff _).mp hv
    rw [hx0, @ofIntValuation_apply_zero _ _ (residueComplexAlgebra f (genericPoint X))]
    simp [toENNReal, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ht).ne']
  | coe n =>
    rw [h, ordToZ_coe] at hv
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    rw [@ofIntValuation_apply_of_ne_zero _ _ (residueComplexAlgebra f (genericPoint X)) _ t ht x hx0,
      hv, WithZero.log_exp, neg_neg]
    simp only [toENNReal, Int.cast_natCast]
    rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_natCast]
    rfl

theorem valAt_anDivVal_nonneg (t : ℝ) (ht : 0 < t)
    (g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) :
    0 ≤ (anDivVal p Φ₀ t ht).valAt ((BerkovichPoint.specializationMap
      (genericPoint_specializes (schemeComplexPointImage f (p.projection y₀)))).hom g) := by
  set x := (BerkovichPoint.specializationMap
    (genericPoint_specializes (schemeComplexPointImage f (p.projection y₀)))).hom g with hx
  change 0 ≤ @ofIntValuation _ _ (residueComplexAlgebra f (genericPoint X))
    (residueValuation p Φ₀) t ht x
  by_cases hx0 : x = 0
  · rw [hx0, @ofIntValuation_apply_zero _ _ (residueComplexAlgebra f (genericPoint X))]
    exact le_top
  · rw [@ofIntValuation_apply_of_ne_zero _ _ (residueComplexAlgebra f (genericPoint X)) _ t ht x hx0]
    have hv := residueValuation_specializationMap p Φ₀ g
    rw [← hx] at hv
    induction h : stalkOrd p Φ₀ g using ENat.recTopCoe with
    | top =>
      rw [h, ordToZ_top] at hv
      exact absurd ((Valuation.zero_iff _).mp hv) hx0
    | coe n =>
      rw [h, ordToZ_coe] at hv
      rw [hv, WithZero.log_exp, neg_neg]
      exact_mod_cast mul_nonneg ht.le (Nat.cast_nonneg n)

end SGPT.NAPotential.TowerAlg

end
