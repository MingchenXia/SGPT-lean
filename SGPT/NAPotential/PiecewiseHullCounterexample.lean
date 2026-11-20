import SGPT.NAPotential.BerkovichPiecewiseLinear
import SGPT.Convex.Epigraph
import SGPT.Toric.ProjectiveLineNativeManifold
import Mathlib.Data.Fin.VecNotation
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-! # Counterexample to the printed terminal branch in `rmk:pwlinhull`

The data include the original
`PiecewiseLinearData` on a genuine connected compact Kähler manifold: the
background is its Kähler form and the two potentials are the constants 0
and -1, at parameters 0 and -1. The printed inductive expression is 0
on `[-1,0]` but -1 on `(-∞,-1)`. It therefore is not concave and cannot be
the actual upper concave envelope of the existing source curve.

This is a counterexample to the displayed statement, not a formalization of
an amended formula. Source erratum E16 is maintained separately.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.Berkovich.PiecewiseHullCounterexample

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem native_atlas_roundtrip (α : ClosedRealOneOneForm n M) :
    atlasClosedFormToNative (nativeClosedFormToAtlas α) = α := by
  rcases α with ⟨a, ha⟩
  cases a
  rfl

/-- The genuine two-node source data on the actual Kähler background. -/
def data (omega : KahlerBackground n M) :
    PiecewiseLinearData (nativeClosedFormToAtlas omega.form) where
  N := 1
  A := ![(fun _ => (0 : EReal)), (fun _ => (-1 : EReal))]
  τ := ![(0 : ℝ), -1]
  strictAnti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  isThetaPSH := by
    have hform := native_atlas_roundtrip omega.form
    intro i
    fin_cases i
    · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [hform]
      exact PluripolarCapacityDichotomy.isThetaPshPotential_zero omega
    · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [hform]
      have h := (PluripolarCapacityDichotomy.isThetaPshPotential_zero omega).add_const (-1)
      simpa using h

/-- The same two genuine source nodes for the literal zero background used
in the paper counterexample recorded as E16. -/
def zeroData : PiecewiseLinearData (nativeClosedFormToAtlas (0 : ClosedRealOneOneForm n M)) where
  N := 1
  A := ![(fun _ => (0 : EReal)), (fun _ => (-1 : EReal))]
  τ := ![(0 : ℝ), -1]
  strictAnti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  isThetaPSH := by
    have hform := native_atlas_roundtrip (0 : ClosedRealOneOneForm n M)
    have hz : IsThetaPshPotential (0 : ClosedRealOneOneForm n M).val (fun _ => 0) :=
      (LocalPotentials.isThetaPshPotential_zero_iff 0).mpr (by intro e z hz v; exact le_rfl)
    intro i
    fin_cases i
    · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [hform]
      exact hz
    · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [hform]
      have h := hz.add_const (-1)
      simpa using h

/-- The literal output of the book's four displayed branches for the
two-node data. The middle formula is the book's maximum of its displayed
affine interpolation and the already fixed top value. At zero it has the
same value as the separately stated top endpoint. -/
def printedCandidate (s : ℝ) : EReal :=
  if 0 < s then ⊥
  else if s < -1 then (-1 : EReal)
  else ((max ((-s) * (-1) + (s + 1) * 0) 0 : ℝ) : EReal)

/-- The middle maximum simplifies to zero on its actual interval. -/
theorem printedCandidate_shape (s : ℝ) :
    printedCandidate s = if 0 < s then ⊥ else if s < -1 then (-1 : EReal) else 0 := by
  by_cases h0 : 0 < s
  · simp [printedCandidate, h0]
  by_cases h1 : s < -1
  · simp [printedCandidate, h0, h1]
  have hs : s ≤ 0 := not_lt.mp h0
  simp [printedCandidate, h0, h1, max_eq_right hs]

/-- The printed counterexample is upper semicontinuous; its failure is
specifically concavity. -/
theorem printedCandidate_upperSemicontinuous : UpperSemicontinuous printedCandidate := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro y
  by_cases hb : y = ⊥
  · subst y
    simp
  have hbot : ¬ y ≤ (⊥ : EReal) := fun h => hb (le_bot_iff.mp h)
  by_cases hneg : y ≤ (-1 : EReal)
  · have hzero : y ≤ (0 : EReal) := hneg.trans (by norm_num)
    have hset : printedCandidate ⁻¹' Ici y = Iic 0 := by
      ext s
      simp only [mem_preimage, mem_Ici, mem_Iic, printedCandidate_shape]
      by_cases h0 : 0 < s
      · simp [h0, hbot, not_le.mpr h0]
      · have hs0 : s ≤ 0 := not_lt.mp h0
        by_cases h1 : s < -1 <;> simp [h0, h1, hneg, hzero, hs0]
    rw [hset]
    exact isClosed_Iic
  · by_cases hzero : y ≤ (0 : EReal)
    · have hset : printedCandidate ⁻¹' Ici y = Icc (-1) 0 := by
        ext s
        simp only [mem_preimage, mem_Ici, mem_Icc, printedCandidate_shape]
        by_cases h0 : 0 < s
        · simp [h0, hbot, not_le.mpr h0]
        · have hs0 : s ≤ 0 := not_lt.mp h0
          by_cases h1 : s < -1
          · simp [h0, h1, hneg, not_le.mpr h1]
          · have hs1 : -1 ≤ s := not_lt.mp h1
            simp [h0, h1, hzero, hs0, hs1]
      rw [hset]
      exact isClosed_Icc
    · have hset : printedCandidate ⁻¹' Ici y = ∅ := by
        ext s
        simp only [mem_preimage, mem_Ici, mem_empty_iff_false, printedCandidate_shape]
        split_ifs <;> simp [hbot, hneg, hzero]
      rw [hset]
      exact isClosed_empty

/-- The source's terminal branch is indeed the last actual input potential. -/
theorem printed_tail (omega : KahlerBackground n M) {s : ℝ} (hs : s < -1) (x : M) :
    printedCandidate s = (data omega).A (Fin.last 1) x := by
  change printedCandidate s = (-1 : EReal)
  simp [printedCandidate_shape, hs, show ¬ 0 < s by linarith]

/-- The source's initial endpoint is indeed the first actual input potential. -/
theorem printed_top (omega : KahlerBackground n M) (x : M) :
    printedCandidate 0 = (data omega).A 0 x := by
  change printedCandidate 0 = (0 : EReal)
  norm_num [printedCandidate_shape]

/-- On the book's single interpolation interval, this is exactly its
displayed affine/max expression using the same actual two potentials. -/
theorem printed_middle (omega : KahlerBackground n M) {s : ℝ}
    (hs : -1 ≤ s) (ht : s < 0) (x : M) :
    printedCandidate s = max
      ((((-s : ℝ) : EReal) * (data omega).A (Fin.last 1) x) +
        (((s + 1 : ℝ) : EReal) * (data omega).A 0 x))
      ((data omega).A 0 x) := by
  change printedCandidate s = max ((((-s : ℝ) : EReal) * (-1 : EReal)) +
    (((s + 1 : ℝ) : EReal) * 0)) 0
  have hmul : (((-s : ℝ) : EReal) * (-1 : EReal)) = (s : EReal) := by
    calc
      (((-s : ℝ) : EReal) * (-1 : EReal)) = (((-s) * (-1) : ℝ) : EReal) := by
        simp only [EReal.coe_mul, EReal.coe_neg, EReal.coe_one]
      _ = (s : EReal) := by
        congr 1
        ring
  have hs0 : (s : EReal) ≤ 0 := by simpa only [EReal.coe_zero] using EReal.coe_le_coe ht.le
  rw [printedCandidate_shape, if_neg (not_lt.mpr ht.le), if_neg (not_lt.mpr hs),
    hmul, mul_zero, add_zero, max_eq_right hs0]

/-- The same displayed branches use exactly the nodes of the zero-background
source data, with the same cutoff values. -/
theorem printed_middle_zero {s : ℝ} (hs : -1 ≤ s) (ht : s < 0) (x : M) :
    printedCandidate s = max
      ((((-s : ℝ) : EReal) * (zeroData (n := n) (M := M)).A (Fin.last 1) x) +
        (((s + 1 : ℝ) : EReal) * (zeroData (n := n) (M := M)).A 0 x))
      ((zeroData (n := n) (M := M)).A 0 x) := by
  change printedCandidate s = max ((((-s : ℝ) : EReal) * (-1 : EReal)) +
    (((s + 1 : ℝ) : EReal) * 0)) 0
  have hmul : (((-s : ℝ) : EReal) * (-1 : EReal)) = (s : EReal) := by
    calc
      (((-s : ℝ) : EReal) * (-1 : EReal)) = (((-s) * (-1) : ℝ) : EReal) := by
        simp only [EReal.coe_mul, EReal.coe_neg, EReal.coe_one]
      _ = (s : EReal) := by
        congr 1
        ring
  have hs0 : (s : EReal) ≤ 0 := by simpa only [EReal.coe_zero] using EReal.coe_le_coe ht.le
  rw [printedCandidate_shape, if_neg (not_lt.mpr ht.le), if_neg (not_lt.mpr hs),
    hmul, mul_zero, add_zero, max_eq_right hs0]

theorem printed_tail_zero {s : ℝ} (hs : s < -1) (x : M) :
    printedCandidate s = (zeroData (n := n) (M := M)).A (Fin.last 1) x := by
  change printedCandidate s = (-1 : EReal)
  simp [printedCandidate_shape, hs, show ¬ 0 < s by linarith]

theorem printed_top_zero (x : M) :
    printedCandidate 0 = (zeroData (n := n) (M := M)).A 0 x := by
  change printedCandidate 0 = (0 : EReal)
  norm_num [printedCandidate_shape]

theorem printed_above {s : ℝ} (hs : 0 < s) : printedCandidate s = ⊥ := by
  simp [printedCandidate, hs]

/-- The literal printed expression is not concave: the negative trace fails
the project's original epigraph-convexity condition. -/
theorem printed_not_concave : ¬ SGPT.Convex.IsConvex (fun s => -printedCandidate s) := by
  intro h
  have hx : -printedCandidate (-3) < ((3 / 2 : ℝ) : EReal) := by
    have heq : printedCandidate (-3) = (-1 : EReal) := by norm_num [printedCandidate_shape]
    rw [heq]
    have hlt : (((1 : ℝ) : EReal) < ((3 / 2 : ℝ) : EReal)) :=
      EReal.coe_lt_coe (by norm_num)
    simpa using hlt
  have hy : -printedCandidate (-1) < ((1 / 4 : ℝ) : EReal) := by
    have heq : printedCandidate (-1) = (0 : EReal) := by norm_num [printedCandidate_shape]
    rw [heq, neg_zero]
    have hlt : (((0 : ℝ) : EReal) < ((1 / 4 : ℝ) : EReal)) :=
      EReal.coe_lt_coe (by norm_num)
    rw [EReal.coe_zero] at hlt
    exact hlt
  have hm := (SGPT.Convex.isConvex_iff_strict_combo.mp h)
    (-3) (-1) (3 / 2) (1 / 4) (1 / 2) (1 / 2)
    hx hy (by norm_num) (by norm_num) (by norm_num)
  have hm' : -printedCandidate (-2) < ((7 / 8 : ℝ) : EReal) := by
    convert hm using 1 <;> norm_num [smul_eq_mul]
  have heq : printedCandidate (-2) = (-1 : EReal) := by norm_num [printedCandidate_shape]
  rw [heq] at hm'
  have hreal : (1 : ℝ) < 7 / 8 := EReal.coe_lt_coe_iff.mp (by simpa using hm')
  norm_num at hreal

/-- The actual upper-concave envelope of the project's genuine piecewise
linear source curve, formed through the existing convex-envelope API. -/
def actualUpperConcaveEnvelope (omega : KahlerBackground n M) (s : ℝ) (x : M) : EReal :=
  -SGPT.Convex.lowerConvexEnvelope (fun t => -((data omega).curve t x)) s

/-- The printed expression cannot be the actual upper-concave envelope of
the genuine source curve, at any point of the original manifold. -/
theorem printed_ne_actualUpperConcaveEnvelope (omega : KahlerBackground n M) (x : M) :
    printedCandidate ≠ fun s => actualUpperConcaveEnvelope omega s x := by
  intro heq
  apply printed_not_concave
  have h := SGPT.Convex.isConvex_lowerConvexEnvelope (fun t => -((data omega).curve t x))
  simpa only [heq, actualUpperConcaveEnvelope, neg_neg] using h

/-- The counterexample exists on the actual projective line with its native
Fubini--Study Kähler background, in the book's projective setting. -/
theorem projectiveLine_counterexample :
    printedCandidate ≠ fun s => actualUpperConcaveEnvelope SGPT.Toric.projectiveNativeFSBackground s
      (Classical.choice (inferInstance : Nonempty (Projectivization ℂ (Fin 2 → ℂ)))) :=
  printed_ne_actualUpperConcaveEnvelope SGPT.Toric.projectiveNativeFSBackground _

/-- The exact E16 background, zero on the original projective line. -/
def actualZeroUpperConcaveEnvelope (s : ℝ) (x : M) : EReal :=
  -SGPT.Convex.lowerConvexEnvelope (fun t => -((zeroData (n := n) (M := M)).curve t x)) s

theorem printed_ne_actualZeroUpperConcaveEnvelope (x : M) :
    printedCandidate ≠ fun s => actualZeroUpperConcaveEnvelope (n := n) s x := by
  intro heq
  apply printed_not_concave
  have h := SGPT.Convex.isConvex_lowerConvexEnvelope
    (fun t => -((zeroData (n := n) (M := M)).curve t x))
  simpa only [heq, actualZeroUpperConcaveEnvelope, neg_neg] using h

theorem projectiveLine_zero_counterexample :
    printedCandidate ≠ fun s => actualZeroUpperConcaveEnvelope (n := 1) s
      (Classical.choice (inferInstance : Nonempty (Projectivization ℂ (Fin 2 → ℂ)))) :=
  printed_ne_actualZeroUpperConcaveEnvelope (n := 1) _

end SGPT.NAPotential.Berkovich.PiecewiseHullCounterexample
