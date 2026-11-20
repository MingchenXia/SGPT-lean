import SGPT.BDivisor.DFAlgNeronSeveri
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual finite Cartier data and an actual global smooth potential from
membership in the original real Néron--Severi subspace. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped BigOperators

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original span membership supplies finitely many actual divisor
metrics and a genuine globally chart-smooth potential. -/
theorem exists_finite_divisor_potential (ω : ClosedRealOneOneForm n X)
    (hω : RealBottChern.ofRepresentative ω ∈ DFAlg.neronSeveri n X) :
    ∃ (N : ℕ) (D : Fin N → EffectiveDivisor n X)
      (E : Fin N → MeteredEffectiveQDivisor n X) (a : Fin N → ℝ),
      (∀ i, DivisorMetric.IsDivisorMetric (D i) (E i)) ∧
      ∃ f : X → ℝ, ChartSmooth (n := n) f ∧
        ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
          ω.val.coeff c z = (∑ i, a i • (E i).curvature).val.coeff c z +
            smoothDDC (fun w => f (c.val.symm w)) z := by
  classical
  obtain ⟨a, t, ht, _, heq⟩ :=
    (Submodule.mem_span_iff_exists_finset_subset).mp hω
  have hdata : ∀ i : t, ∃ (D : EffectiveDivisor n X)
      (E : MeteredEffectiveQDivisor n X),
      DivisorMetric.IsDivisorMetric D E ∧
        i.val = RealBottChern.ofRepresentative E.curvature := fun i => ht i.property
  choose D E hDE hclass using hdata
  let e := Fintype.equivFin t
  let D' : Fin (Fintype.card t) → EffectiveDivisor n X := fun j => D (e.symm j)
  let E' : Fin (Fintype.card t) → MeteredEffectiveQDivisor n X := fun j => E (e.symm j)
  let a' : Fin (Fintype.card t) → ℝ := fun j => a (e.symm j).val
  have hsum : RealBottChern.ofRepresentative (∑ j, a' j • (E' j).curvature) =
      RealBottChern.ofRepresentative ω := by
    change RealBottChern.ofRepresentativeLinearMap (∑ j, a' j • (E' j).curvature) = _
    rw [map_sum]
    simp only [map_smul]
    change (∑ j, a' j • RealBottChern.ofRepresentative (E' j).curvature) = _
    change (∑ j, a (e.symm j).val • RealBottChern.ofRepresentative (E (e.symm j)).curvature) = _
    simp only [← hclass]
    calc
      _ = ∑ i : t, a i.val • i.val := e.symm.sum_comp (fun i : t => a i.val • i.val)
      _ = _ := (Finset.sum_coe_sort t (fun x => a x • x)).trans heq
  obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hsum
  exact ⟨Fintype.card t, D', E', a', fun j => hDE (e.symm j), f, hf, hfeq⟩

end SGPT.BDivisor.NSKodaira
