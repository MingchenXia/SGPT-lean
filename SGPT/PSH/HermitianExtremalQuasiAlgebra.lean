import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord
import SGPT.Foundations.Analysis.Pending.PshConvexCone

/-!
# Finite nonnegative algebra of genuine local quasi-PSH potentials

The local PSH-plus-smooth decompositions add and scale. Chartwise almost
everywhere finiteness produces common finite points, so addition does not
collapse a genuine potential on any open set. No closed background occurs.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalQuasiAlgebra

open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]

/-- Actual local PSH-plus-smooth decompositions add as functions. -/
theorem quasiPlurisubharmonicAt_add {u v : E → EReal} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) (hv : QuasiPlurisubharmonicAt v x) :
    QuasiPlurisubharmonicAt (fun y => u y + v y) x := by
  obtain ⟨p, g, hp, hg, heq⟩ := hu
  obtain ⟨q, h, hq, hh, hveq⟩ := hv
  refine ⟨fun y => p y + q y, fun y => g y + h y, hp.add hq, ?_, ?_⟩
  · filter_upwards [hg, hh] with y hgy hhy
    exact hgy.add hhy
  · filter_upwards [heq, hveq] with y hy hvy
    rw [hy, hvy, EReal.coe_add]
    ac_rfl

/-- Nonnegative real scaling preserves actual local quasi-PSH germs,
including the zero scaling and every negative pole. -/
theorem quasiPlurisubharmonicAt_nonneg_mul {u : E → EReal} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) {a : ℝ} (ha : 0 ≤ a) :
    QuasiPlurisubharmonicAt (fun y => (a : EReal) * u y) x := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using (plurisubharmonicAt_const (0 : EReal) EReal.zero_ne_top x).quasiPlurisubharmonicAt
  obtain ⟨p, g, hp, hg, heq⟩ := hu
  refine ⟨fun y => (a : EReal) * p y, fun y => a * g y, hp.const_mul ha, ?_, ?_⟩
  · filter_upwards [hg] with y hy
    exact hy.const_smul a
  · filter_upwards [heq] with y hy
    rw [hy, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ha.le)
      (EReal.coe_ne_top a), ← EReal.coe_mul]

end Local

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Common finite points are manufactured from the two actual chartwise
almost-everywhere finite loci; no nondegeneracy of the sum is supplied. -/
theorem isGlobalQuasiPshPotential_add {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    IsGlobalQuasiPshPotential (n := n) (fun x => u x + v x) := by
  refine ⟨fun e z hz => quasiPlurisubharmonicAt_add (hu.1 e z hz) (hv.1 e z hz), ?_⟩
  intro x O hO hxO
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  let G := e.val.target ∩ e.val.symm ⁻¹' O
  have hG : IsOpen G := e.val.isOpen_inter_preimage_symm hO
  have hxG : e.val x ∈ G := by
    refine ⟨e.val.map_source hx, ?_⟩
    simpa only [mem_preimage, e.val.left_inv hx] using hxO
  have hae := ae_restrict_of_ae_restrict_of_subset
    (show G ⊆ e.val.target from inter_subset_left)
    ((hu.ae_finite_chart e).and (hv.ae_finite_chart e))
  obtain ⟨z, hz, huz, hvz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hG.measure_pos volume ⟨_, hxG⟩).ne' hae
  exact ⟨e.val.symm z, hz.2, EReal.add_ne_bot_iff.mpr ⟨huz.2, hvz.2⟩⟩

/-- A nonnegative real scaling is a genuine quasi-PSH potential, with its
local finite witnesses preserved (and the zero function treated separately). -/
theorem isGlobalQuasiPshPotential_nonneg_mul {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) {a : ℝ} (ha : 0 ≤ a) :
    IsGlobalQuasiPshPotential (n := n) (fun x => (a : EReal) * u x) := by
  by_cases ha0 : a = 0
  · simpa only [ha0, EReal.coe_zero, zero_mul] using
      (isGlobalQuasiPshPotential_const (n := n) (M := M) 0)
  refine ⟨fun e z hz => quasiPlurisubharmonicAt_nonneg_mul (hu.1 e z hz) ha, ?_⟩
  intro x O hO hx
  obtain ⟨y, hy, hfin⟩ := hu.2 x O hO hx
  refine ⟨y, hy, ?_⟩
  exact (EReal.mul_ne_bot _ _).mpr
    ⟨Or.inl (EReal.coe_ne_bot a), Or.inr hfin,
      Or.inl (EReal.coe_ne_top a), Or.inl (EReal.coe_nonneg.mpr ha)⟩

/-- Finite nonnegative combinations are genuine potentials, including an
empty family and vanishing coefficients. -/
theorem isGlobalQuasiPshPotential_finset_nonnegSum {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 ≤ a j) (u : ι → M → EReal)
    (hu : ∀ j ∈ s, IsGlobalQuasiPshPotential (n := n) (u j)) :
    IsGlobalQuasiPshPotential (n := n)
      (fun x => ∑ j ∈ s, (a j : EReal) * u j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isGlobalQuasiPshPotential_const (n := n) (M := M) 0)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact isGlobalQuasiPshPotential_add
      (isGlobalQuasiPshPotential_nonneg_mul (hu j (Finset.mem_insert_self j s))
        (ha j (Finset.mem_insert_self j s)))
      (ih (fun k hk => ha k (Finset.mem_insert_of_mem hk))
        (fun k hk => hu k (Finset.mem_insert_of_mem hk)))

end SGPT.PSH.HermitianExtremalQuasiAlgebra
