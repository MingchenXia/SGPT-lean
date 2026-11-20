import SGPT.PSH.IntrinsicRationalAnalytic
import SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSingleGenerator

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers
open scoped BigOperators

universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem chartHolomorphicOn_tensorPowerFamily {N : ℕ} {f : Fin N → X → ℂ}
    {U : Set X} (hf : ∀ j, A.ChartHolomorphicOn (f j) U) (r : ℕ) :
    ∀ s, A.ChartHolomorphicOn (tensorPowerFamily f r s) U := by
  intro s i y hy
  change DifferentiableWithinAt ℂ
    (fun z => ∏ a : Fin r,
      f ((Fintype.equivFin (Fin r → Fin N)).symm s a) ((A.chart i).symm z))
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) y
  exact (HasFDerivWithinAt.finsetProd fun a _ =>
    (hf ((Fintype.equivFin (Fin r → Fin N)).symm s a) i y hy).hasFDerivWithinAt).differentiableWithinAt

theorem exists_uniform_rational_analytic_coefficient [CompactSpace X] {u : X → EReal}
    (hu : A.HasRationalAnalyticType u) :
    ∃ (c : ℚ) (m : ℕ) (N : Fin m → ℕ) (f : ∀ i, Fin (N i) → X → ℂ)
      (b : Fin m → X → ℝ) (C : Fin m → ℝ) (U : Fin m → Set X),
      0 < c ∧ (∀ y, ∃ i, y ∈ U i) ∧
      ∀ i, 0 ≤ C i ∧ IsOpen (U i) ∧ IsConnected (U i) ∧
        (∀ j, A.ChartHolomorphicOn (f i j) (U i)) ∧
        (∀ y ∈ U i, |b i y| ≤ C i) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog (f i) y + (b i y : EReal)) (U i) := by
  classical
  choose c N f b C U hc hC hU hconn hx hf hb heq using hu
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro y _
    exact mem_iUnion.mpr ⟨y, hx y⟩)
  let e := (Fintype.equivFin s).symm
  let a : Fin (Fintype.card s) → ℚ := fun i => c (e i)
  obtain ⟨q, p, hq, hp⟩ :=
    SGPT.Foundations.Analysis.Pending.MeteredDivisorSingleGenerator.exists_commonDenominator
      a (fun i => (hc (e i)).le)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hpR (i : Fin (Fintype.card s)) :
      (1 / (q : ℝ)) * (p i : ℝ) = (c (e i) : ℝ) := by
    rw [hp i]
    ring
  refine ⟨1 / (q : ℚ), Fintype.card s,
    fun i => Fintype.card (Fin (p i) → Fin (N (e i))),
    fun i => tensorPowerFamily (f (e i)) (p i),
    fun i => b (e i), fun i => C (e i), fun i => U (e i),
    div_pos zero_lt_one hqQ, ?_, ?_⟩
  · intro y
    obtain ⟨x, hy⟩ := mem_iUnion.mp (hs (mem_univ y))
    obtain ⟨hxS, hy⟩ := mem_iUnion.mp hy
    let i := Fintype.equivFin s ⟨x, hxS⟩
    refine ⟨i, ?_⟩
    simpa only [i, e, Equiv.symm_apply_apply] using hy
  · intro i
    refine ⟨hC (e i), hU (e i), hconn (e i),
      chartHolomorphicOn_tensorPowerFamily (hf (e i)) (p i), hb (e i), ?_⟩
    intro y hy
    rw [heq (e i) hy]
    dsimp only
    rw [generatorLog_tensorPowerFamily]
    congr 1
    rw [← mul_assoc, ← EReal.coe_mul]
    congr 1
    push_cast
    simpa only [EReal.coe_mul, EReal.coe_natCast] using
      congrArg (fun t : ℝ => (t : EReal)) (hpR i).symm

end SGPT.PSH.VariableComplexAtlas
