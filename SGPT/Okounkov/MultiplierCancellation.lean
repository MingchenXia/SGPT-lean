import SGPT.Okounkov.FlagLelong
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open GlobalMultilinearExpansion SourceTraceRepresentativeDefinition

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Thin two-term specialization of the existing genuine positive finite-sum
producer. Nondegeneracy is produced there, including original pole values. -/
theorem isThetaPshPotential_add_from_positive_sum
    {θ σ : ClosedRealOneOneForm n X} {u v : X → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n X := fun b => if b then θ else σ
  let f : Bool → X → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := MixedSummandCapacityDomination.isThetaPshPotential_sumPot
    (T := Finset.univ) (w := fun _ : Bool => (1 : ℝ))
    Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h

/-- The actual all-prime criterion cancels a common genuine theta-PSH
summand. Its generic reader is genuinely finite on each original upstairs
prime, so no subtraction of infinite readers is used. -/
theorem iOrder_of_iOrder_add_common_potential
    {θ σ γ : ClosedRealOneOneForm n X} {u v w : X → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hw : IsThetaPshPotential γ.val w)
    (hI : IOrderOnManifold (n := n) (fun x => u x + w x) (fun x => v x + w x)) :
    IOrderOnManifold (n := n) u v := by
  have huw := isThetaPshPotential_add_from_positive_sum hu hw
  have hvw := isThetaPshPotential_add_from_positive_sum hv hw
  have hprimes := (SourceGenericPrimeIdealOrder.iOrder_iff_all_source_prime_orders
    huw.quasiPshPotential.1 hvw.quasiPshPotential).mp hI
  apply (SourceGenericPrimeIdealOrder.iOrder_iff_all_source_prime_orders
    hu.quasiPshPotential.1 hv.quasiPshPotential).mpr
  intro Y _ _ _ π hπ Z hclosed hconn hhyper
  obtain ⟨k, hkn, hreg⟩ := hhyper
  have hZ : IsClosedConnectedSubmanifold n Z k := ⟨hclosed, hconn, hreg⟩
  have hpu := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ θ hu
  have hpv := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ σ hv
  have hpw := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ γ hw
  have hsum : sourceGenericLelongNumber (n := n) (Subtype.val : Z → Y)
      (fun y => v (π y) + w (π y)) ≤
      sourceGenericLelongNumber (n := n) (Subtype.val : Z → Y)
        (fun y => u (π y) + w (π y)) := by
    rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf,
      SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf]
    exact hprimes Y π hπ Z hclosed hconn ⟨k, hkn, hreg⟩
  rw [sourceGeneric_subtype_add_eq hZ hpv.quasiPshPotential hpw.quasiPshPotential,
    sourceGeneric_subtype_add_eq hZ hpu.quasiPshPotential hpw.quasiPshPotential] at hsum
  have hcancel := (ENNReal.add_le_add_iff_right
    (sourceGeneric_subtype_ne_top hZ hpw.quasiPshPotential)).mp hsum
  rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf,
    SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf] at hcancel
  exact hcancel

/-- Both actual ideal orders give original multiplier equivalence after
cancelling a genuine common potential, without any finite-value premise. -/
theorem iEquivalent_of_iEquivalent_add_common_potential
    {θ σ γ : ClosedRealOneOneForm n X} {u v w : X → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hw : IsThetaPshPotential γ.val w)
    (hI : IEquivalentOnManifold (n := n) (fun x => u x + w x) (fun x => v x + w x)) :
    IEquivalentOnManifold (n := n) u v :=
  ⟨iOrder_of_iOrder_add_common_potential hu hv hw hI.1,
    iOrder_of_iOrder_add_common_potential hv hu hw hI.2⟩

end SGPT.Okounkov
