import SGPT.PSH.HermitianComparisonMetricBound
import SGPT.PSH.HermitianComparisonCompactPartition

/-!
# The actual compact partition supplies uniform trace dominators

Compact coercivity is applied on each inner domain closure, where the
outer background and correction remain smooth. One finite geometry
constant dominates every correction trace and coordinate trace, before
any Hermitian potential is supplied.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonTorsionGeometry

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents
open Hermitian HermitianGlobalProducts HermitianComparisonGlobalOneFactor
  HermitianComparisonMetricBound
open scoped Topology ContDiff Distributions

variable {n : ℕ}

theorem semipositive_domination_enlarge {a b : RealForm n 2} {c C : ℝ}
    (ha : IsSemipositiveOneOne a) (hcb : IsSemipositiveOneOne (c • a - b))
    (hcC : c ≤ C) : IsSemipositiveOneOne (C • a - b) := by
  have hp := (ha.smul (sub_nonneg.mpr hcC)).add hcb
  have he : (C - c) • a + (c • a - b) = C • a - b := by module
  rwa [he] at hp

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

private theorem exists_patch_trace_dominators (C : CompactPartition omega)
    (i : Fin C.outer.count) : ∃ G F : NNReal,
    (∀ z ∈ C.domain i, IsSemipositiveOneOne ((G : ℝ) •
      omega.form.coeff (C.patch i).geometry.chart z - -(C.patch i).residual z)) ∧
    (∀ z ∈ C.domain i, IsSemipositiveOneOne ((F : ℝ) •
      omega.form.coeff (C.patch i).geometry.chart z - kahlerForm (m + 1))) := by
  let P := C.outer.patch i
  let K := closure (C.domain i : Set (ComplexModel (m + 1)))
  have hK : IsCompact K := (C.relativelyCompact i).1
  have hKP : K ⊆ P.geometry.domain := (C.relativelyCompact i).2
  have hKT : K ⊆ P.geometry.chart.val.target := hKP.trans P.geometry.domain_le_target
  have ha : ContinuousOn (omega.form.coeff P.geometry.chart) K :=
    (omega.form.smooth P.geometry.chart).continuousOn.mono hKT
  have ha11 : ∀ z ∈ K, IsOneOne (omega.form.coeff P.geometry.chart z) :=
    fun z hz => omega.isTypeOneOne P.geometry.chart z (hKT hz)
  have hpos : ∀ z ∈ K, IsStrictlyPositive (omega.form.coeff P.geometry.chart z) :=
    fun z hz => (omega.isHermitian P.geometry.chart z (hKT hz)).2
  have hg : ContinuousOn (fun z => -P.residual z) K :=
    P.residual_smooth.neg.continuousOn.mono hKP
  have hg11 : ∀ z ∈ K, IsOneOne (-P.residual z) := by
    intro z hz v w
    change -(P.residual z ![Complex.I • v, Complex.I • w]) = -(P.residual z ![v, w])
    rw [P.residual_isOneOne z (hKP hz) v w]
  obtain ⟨G, hG⟩ := exists_compact_semipositive_domination
    (omega.form.coeff P.geometry.chart) (fun z => -P.residual z) hK ha hg ha11 hg11 hpos
  obtain ⟨F, hF⟩ := exists_compact_semipositive_domination
    (omega.form.coeff P.geometry.chart) (fun _ => kahlerForm (m + 1)) hK ha
    continuousOn_const ha11 (fun _ _ => isSemipositiveOneOne_kahlerForm.1) hpos
  exact ⟨G, F, (fun z hz => hG z (subset_closure hz)), (fun z hz => hF z (subset_closure hz))⟩

/-- The same geometry number dominates every fixed form on every actual
inner chart. Its construction uses no potential or measure inputs. -/
theorem exists_uniform_trace_dominator (C : CompactPartition omega) :
    ∃ A : NNReal, 1 ≤ A ∧ ∀ i z, z ∈ C.domain i →
      IsSemipositiveOneOne ((A : ℝ) • omega.form.coeff (C.patch i).geometry.chart z -
        -(C.patch i).residual z) ∧
      IsSemipositiveOneOne ((A : ℝ) • omega.form.coeff (C.patch i).geometry.chart z -
        kahlerForm (m + 1)) := by
  classical
  choose G F hG hF using exists_patch_trace_dominators C
  let A : NNReal := 1 + ∑ i, (G i + F i)
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  have hGi (i : Fin C.outer.count) : G i ≤ A := by
    calc
      G i ≤ G i + F i := le_add_of_nonneg_right (by positivity)
      _ ≤ ∑ j, (G j + F j) := Finset.single_le_sum (fun j _ => (show (0 : NNReal) ≤ G j + F j by positivity)) (Finset.mem_univ i)
      _ ≤ A := le_add_of_nonneg_left zero_le_one
  have hFi (i : Fin C.outer.count) : F i ≤ A := by
    calc
      F i ≤ G i + F i := le_add_of_nonneg_left (by positivity)
      _ ≤ ∑ j, (G j + F j) := Finset.single_le_sum (fun j _ => (show (0 : NNReal) ≤ G j + F j by positivity)) (Finset.mem_univ i)
      _ ≤ A := le_add_of_nonneg_left zero_le_one
  refine ⟨A, hA, ?_⟩
  intro i z hz
  have hzT := (C.patch i).geometry.domain_le_target hz
  have hp : IsSemipositiveOneOne (omega.form.coeff (C.patch i).geometry.chart z) :=
    ⟨omega.isTypeOneOne _ _ hzT, omega.isSemipositive _ _ hzT⟩
  exact ⟨semipositive_domination_enlarge hp (hG i z hz) (by exact_mod_cast hGi i),
    semipositive_domination_enlarge hp (hF i z hz) (by exact_mod_cast hFi i)⟩

end SGPT.PSH.HermitianComparisonTorsionGeometry
