import SGPT.Bergman.SiuNSFinitePotential
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import Mathlib.Topology.Instances.Rat

/-! Rational perturbation of actual smooth closed forms on the original
compact manifold, with a quantitative native positivity proof. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped BigOperators

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- A single actual form is absolutely bounded on every complex line by
the given Kähler form, uniformly over the original compact manifold. -/
theorem exists_abs_line_domination (ω θ : ClosedRealOneOneForm n X)
    (hω : ω.val.IsKahler) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      ∀ v : ComplexModel n,
        |θ.val.coeff c z ![v, Complex.I • v]| ≤ C * ω.val.coeff c z ![v, Complex.I • v] := by
  obtain ⟨A, hA, hdomA⟩ := KahlerDomination.exists_isSemipositive_add_smul θ.val ω.val hω.1
  obtain ⟨B, hB, hdomB⟩ := KahlerDomination.exists_isSemipositive_add_smul (-θ).val ω.val hω.1
  refine ⟨A + B, by positivity, fun c z hz v => ?_⟩
  have h1 := hdomA c z hz v
  have h2 := hdomB c z hz v
  have h0 := KahlerDomination.lineValue_nonneg_of_isHermitian hω.1 c hz v
  simp only [ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.neg_apply] at h2
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Arbitrary finite real coefficients can be approximated by rationals
while preserving actual strict positivity, with no rational-class premise. -/
theorem exists_rational_positive_perturbation {N : ℕ}
    (ω : ClosedRealOneOneForm n X) (hω : ω.val.IsKahler)
    (θ : Fin N → ClosedRealOneOneForm n X) (a : Fin N → ℝ) :
    ∃ r : Fin N → ℚ, (ω + ∑ i, ((r i : ℝ) - a i) • θ i).val.IsKahler := by
  classical
  choose C hC hbound using fun i => exists_abs_line_domination ω (θ i) hω
  let S : ℝ := ∑ i, C i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (hC i).le
  let ε : ℝ := 1 / (2 * (S + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε * S < 1 := by
    dsimp [ε]
    rw [one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  have hex : ∀ i : Fin N, ∃ r : ℚ, |(r : ℝ) - a i| < ε := by
    intro i
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show a i - ε < a i + ε by linarith)
    exact ⟨r, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose r hr using hex
  let η := ω + ∑ i, ((r i : ℝ) - a i) • θ i
  refine ⟨r, ⟨fun c z hz => ⟨η.property.2 c z hz, fun v hv => ?_⟩, η.property.1⟩⟩
  have hpos := (hω.1 c z hz).2 v hv
  let w := ω.val.coeff c z ![v, Complex.I • v]
  have hw : 0 < w := hpos
  have hterm : ∀ i : Fin N,
      |((r i : ℝ) - a i) * (θ i).val.coeff c z ![v, Complex.I • v]| ≤ ε * C i * w := by
    intro i
    rw [abs_mul]
    calc
      _ ≤ ε * (C i * w) := mul_le_mul (hr i).le (hbound i c z hz v)
        (abs_nonneg _) (le_of_lt hε)
      _ = _ := by ring
  have hsum : |∑ i, ((r i : ℝ) - a i) * (θ i).val.coeff c z ![v, Complex.I • v]| ≤ ε * S * w := by
    calc
      _ ≤ ∑ i, |((r i : ℝ) - a i) * (θ i).val.coeff c z ![v, Complex.I • v]| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ε * C i * w := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp only [S, Finset.sum_mul, Finset.mul_sum]
  have hlow := neg_le_of_abs_le hsum
  have hcoef : η.val.coeff c z ![v, Complex.I • v] =
      w + ∑ i, ((r i : ℝ) - a i) * (θ i).val.coeff c z ![v, Complex.I • v] := by
    simp only [η, ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
    congr 1
    have hsumcoeff : (∑ i, ((r i : ℝ) - a i) • θ i).val.coeff c z =
        ∑ i, (((r i : ℝ) - a i) • θ i).val.coeff c z := by
      apply map_sum (show ClosedRealOneOneForm n X →ₗ[ℝ]
        ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) from
        { toFun := fun t => t.val.coeff c z
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
    rw [hsumcoeff]
    simp only [ContinuousAlternatingMap.sum_apply, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change 0 < η.val.coeff c z ![v, Complex.I • v]
  rw [hcoef]
  nlinarith [mul_lt_mul_of_pos_right hsmall hw]

omit [CompactSpace X] [IsComplexManifold n X] [ChartedSpace (ComplexModel n) X]
  [TopologicalSpace X] in
/-- A positive common denominator is manufactured from the actual rational
coefficients, retaining arbitrary signed integral exponents. -/
theorem exists_positive_common_denominator {N : ℕ} (r : Fin N → ℚ) :
    ∃ q : ℕ, 0 < q ∧ ∃ b : Fin N → ℤ, ∀ i, (b i : ℝ) = (q : ℝ) * (r i : ℝ) := by
  classical
  let q : ℕ := ∏ i, (r i).den
  have hq : 0 < q := Finset.prod_pos fun i _ => (r i).den_pos
  let b : Fin N → ℤ := fun i => (r i).num * (∏ j ∈ Finset.univ.erase i, (r j).den : ℕ)
  refine ⟨q, hq, b, fun i => ?_⟩
  have hprod : (r i).den * (∏ j ∈ Finset.univ.erase i, (r j).den) = q :=
    Finset.mul_prod_erase Finset.univ (fun j => (r j).den) (Finset.mem_univ i)
  have hrat : (b i : ℚ) = (q : ℚ) * r i := by
    dsimp only [b]
    rw [← hprod, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    have heq := Rat.num_div_den (r i)
    have hd : ((r i).den : ℚ) ≠ 0 := by exact_mod_cast (r i).den_ne_zero
    field_simp at heq ⊢
    nlinarith [heq]
  exact_mod_cast hrat

end SGPT.BDivisor.NSKodaira
