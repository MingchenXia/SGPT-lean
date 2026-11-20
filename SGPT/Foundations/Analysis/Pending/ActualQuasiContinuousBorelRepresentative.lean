import SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # Bounded Borel representatives of actual capacity-quasicontinuous weights

An independent representative step for Lu's weighted convergence argument.
The original quasicontinuous weight need not be Borel measurable.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousBorelRepresentative

open FirstPass FirstPass.PositiveClasses ThetaCapacity
  CapacityWeightedConvergence PluripolarCapacityZero

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- A bounded quasicontinuous weight has a bounded Borel and quasicontinuous
representative outside a measurable set of actual outer capacity zero. -/
theorem exists_borel_representative (omega : KahlerBackground n M)
    {f : M → ℝ} {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B)
    (hf : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) f) :
    ∃ g : M → ℝ, Measurable g ∧ (∀ x, |g x| ≤ B) ∧
      QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) g ∧
      ∃ E : Set M, MeasurableSet E ∧ OuterCapacityZero omega E ∧ EqOn f g Eᶜ := by
  classical
  have := DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold n M
  let r : ℝ≥0∞ := 2⁻¹
  have hr : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  choose G hG hGcap hfG using fun j : ℕ => hf (r ^ j) (ENNReal.pow_pos hr j)
  choose v hvB hfv using fun j => exists_continuous_eqOn_compl hB hfB (hG j) (hfG j)
  let T (N : ℕ) : Set M := ⋃ j : ℕ, G (j + N)
  have hTo : ∀ N, IsOpen (T N) := fun N => isOpen_iUnion fun j => hG (j + N)
  have hTcap : ∀ N, thetaCapacity omega.form (fun _ => 0) (T N) ≤ r ^ N * 2 := by
    intro N
    calc
      thetaCapacity omega.form (fun _ => 0) (T N)
          ≤ ∑' j : ℕ, thetaCapacity omega.form (fun _ => 0) (G (j + N)) :=
        thetaCapacity_iUnion_le _ _ _
      _ ≤ ∑' j : ℕ, r ^ (j + N) := ENNReal.tsum_le_tsum fun j => (hGcap (j + N)).le
      _ = r ^ N * 2 := by
        simp only [Nat.add_comm _ N, pow_add, ENNReal.tsum_mul_left, r,
          ENNReal.tsum_geometric_two]
  have hsmall : ∀ eta : ℝ≥0∞, 0 < eta → ∃ N, thetaCapacity omega.form (fun _ => 0) (T N) < eta := by
    intro eta heta
    have ht : Tendsto (fun N : ℕ => r ^ N * 2) atTop (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
        (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
    obtain ⟨N, hN⟩ := (ht.eventually_lt_const heta).exists
    exact ⟨N, (hTcap N).trans_lt hN⟩
  let g (x : M) : ℝ := limsup (fun j => v j x) atTop
  have hg : Measurable g := Measurable.limsup fun j => (v j).continuous.measurable
  have hgB : ∀ x, |g x| ≤ B := by
    intro x
    have hu : atTop.IsBoundedUnder (· ≤ ·) (fun j : ℕ => v j x) :=
      isBoundedUnder_of ⟨B, fun j => (abs_le.mp (hvB j x)).2⟩
    have hl : atTop.IsCoboundedUnder (· ≤ ·) (fun j : ℕ => v j x) :=
      isCoboundedUnder_le_of_le atTop fun j => (abs_le.mp (hvB j x)).1
    refine abs_le.mpr ⟨le_limsup_of_le hu ?_, limsup_le_of_le hl
      (Eventually.of_forall fun j => (abs_le.mp (hvB j x)).2)⟩
    intro b hb
    obtain ⟨j, hj⟩ := hb.exists
    exact (abs_le.mp (hvB j x)).1.trans hj
  have heq : ∀ N, EqOn g f (T N)ᶜ := by
    intro N x hx
    have hevent : ∀ᶠ j : ℕ in atTop, v j x = f x := by
      filter_upwards [eventually_ge_atTop N] with j hj
      have hxG : x ∉ G j := by
        intro hxj
        apply hx
        exact mem_iUnion.mpr ⟨j - N, by simpa only [Nat.sub_add_cancel hj] using hxj⟩
      exact (hfv j hxG).symm
    have ht : Tendsto (fun j => v j x) atTop (𝓝 (f x)) :=
      tendsto_const_nhds.congr' (hevent.mono fun _ hj => hj.symm)
    exact ht.limsup_eq
  have hgQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) g := by
    intro eta heta
    obtain ⟨N, hN⟩ := hsmall eta heta
    refine ⟨T N, hTo N, hN, (hfG N).congr_mono (heq N) ?_⟩
    intro x hx hxG
    exact hx (mem_iUnion.mpr ⟨0, by simpa using hxG⟩)
  let E : Set M := ⋂ N : ℕ, T N
  have hEm : MeasurableSet E := MeasurableSet.iInter fun N => (hTo N).measurableSet
  have hEcap : OuterCapacityZero omega E := by
    intro eta heta
    obtain ⟨N, hN⟩ := hsmall eta heta
    exact ⟨T N, hTo N, iInter_subset T N, hN⟩
  refine ⟨g, hg, hgB, hgQC, E, hEm, hEcap, ?_⟩
  intro x hx
  have hxN : ∃ N, x ∉ T N := by
    by_contra h
    apply hx
    exact mem_iInter.mpr fun N => by by_contra hxN; exact h ⟨N, hxN⟩
  obtain ⟨N, hxN⟩ := hxN
  exact (heq N hxN).symm

end
end SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousBorelRepresentative
