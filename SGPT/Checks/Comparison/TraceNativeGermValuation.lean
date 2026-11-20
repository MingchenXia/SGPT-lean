import SGPT.Checks.Comparison.TraceGFSectionPullback
import SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-! Actual same native prime germ valuation. Blueprint: `trace-native-image-valuation.tex`.
The small original order-to-Z and divisible-complex constants proofs are a narrow
source port of `SGPT.NAPotential.TowerAlgValuation` (no geometric definitions imported).
The NEW actual native germ/fraction valuation below consumes genuine factoriality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology ENNReal WithZero

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


section Native
variable {m : ℕ} {Z : Type} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel (m+1)) Z]
  {E : Set Z} {z : Z} (Φ : DivisorFlattening (m := m) E z)

/-- The ACTUAL original prime-equation order on the SAME holomorphic germ ring. -/
def germValuation : Valuation (HolGerm (ComplexModel (m+1))) ℤᵐ⁰ where
  toFun g := ordToZ (normalOrder Φ g)
  map_zero' := by rw [normalOrder_zero, ordToZ_top]
  map_one' := by rw [normalOrder_unit Φ isUnit_one, ordToZ_zero]
  map_mul' g h := by rw [normalOrder_mul, ordToZ_add]
  map_add_le_max' g h := by
    calc ordToZ (normalOrder Φ (g+h)) ≤ ordToZ (min (normalOrder Φ g) (normalOrder Φ h)) :=
          ordToZ_antitone min_le_emultiplicity_add
      _ = max (ordToZ (normalOrder Φ g)) (ordToZ (normalOrder Φ h)) := ordToZ_antitone.map_min

/-- Actual factoriality, not a nonvanishing certificate, makes localization legitimate. -/
theorem le_primeCompl_supp_germValuation :
    nonZeroDivisors (HolGerm (ComplexModel (m+1))) ≤ (germValuation Φ).supp.primeCompl := by
  intro g hg hzero
  rw [SetLike.mem_coe, Valuation.mem_supp_iff] at hzero
  have htop : normalOrder Φ g = ⊤ := (ordToZ_eq_zero_iff _).mp hzero
  exact normalOrder_ne_top Φ (nonZeroDivisors.ne_zero hg) htop

/-- The SAME actual discrete normal order on the actual analytic fraction field. -/
def fractionValuation : Valuation (FractionRing (HolGerm (ComplexModel (m+1)))) ℤᵐ⁰ :=
  (germValuation Φ).extendToLocalization (le_primeCompl_supp_germValuation Φ) _

theorem fractionValuation_algebraMap (g : HolGerm (ComplexModel (m+1))) :
    fractionValuation Φ (algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1)))) g) =
      ordToZ (normalOrder Φ g) := by
  rw [fractionValuation, Valuation.extendToLocalization_apply_map_apply]
  rfl

variable [Algebra ℂ (FractionRing (HolGerm (ComplexModel (m+1))))]

/-- The actual normal valuation, with original positive real scaling and
trivial complex constants, on the SAME native analytic fraction field. -/
def fractionRealValuation (t : ℝ) (ht : 0 < t) :
    SourceRealValuation (FractionRing (HolGerm (ComplexModel (m+1)))) :=
  ofIntValuation (fractionValuation Φ) t ht

/-- Literal original scaled-normal-order readback, including the zero germ. -/
theorem fractionRealValuation_algebraMap (t : ℝ) (ht : 0 < t)
    (g : HolGerm (ComplexModel (m+1))) :
    toENNReal (fractionRealValuation Φ t ht
      (algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1)))) g)) =
      ENNReal.ofReal t * (normalOrder Φ g : ℝ≥0∞) := by
  let x := algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1)))) g
  have hv := fractionValuation_algebraMap Φ g
  change fractionValuation Φ x = ordToZ (normalOrder Φ g) at hv
  change toENNReal (ofIntValuation (fractionValuation Φ) t ht x) = _
  induction h : normalOrder Φ g using ENat.recTopCoe with
  | top =>
    rw [h, ordToZ_top] at hv
    have hx0 : x = 0 := (Valuation.zero_iff _).mp hv
    rw [hx0, ofIntValuation_apply_zero]
    simp [toENNReal, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ht).ne']
  | coe r =>
    rw [h, ordToZ_coe] at hv
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    rw [ofIntValuation_apply_of_ne_zero (fractionValuation Φ) t ht hx0,
      hv, WithZero.log_exp, neg_neg]
    simp only [toENNReal, Int.cast_natCast]
    rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_natCast]
    rfl

/-- The actual scaled valuation is nonnegative on the entire genuine
holomorphic germ ring, so its original valuation ring contains that ring. -/
theorem fractionRealValuation_algebraMap_nonneg (t : ℝ) (ht : 0 < t)
    (g : HolGerm (ComplexModel (m+1))) :
    0 ≤ fractionRealValuation Φ t ht
      (algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1)))) g) := by
  let x := algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1)))) g
  change 0 ≤ ofIntValuation (fractionValuation Φ) t ht x
  by_cases hx0 : x = 0
  · rw [hx0, ofIntValuation_apply_zero]
    exact le_top
  · rw [ofIntValuation_apply_of_ne_zero (fractionValuation Φ) t ht hx0]
    have hv := fractionValuation_algebraMap Φ g
    change fractionValuation Φ x = ordToZ (normalOrder Φ g) at hv
    induction h : normalOrder Φ g using ENat.recTopCoe with
    | top =>
      rw [h, ordToZ_top] at hv
      exact absurd ((Valuation.zero_iff _).mp hv) hx0
    | coe r =>
      rw [h, ordToZ_coe] at hv
      rw [hv, WithZero.log_exp, neg_neg]
      exact_mod_cast mul_nonneg ht.le (Nat.cast_nonneg r)

end Native
end SGPT.NAPotential.TraceComparison.NativeImage
