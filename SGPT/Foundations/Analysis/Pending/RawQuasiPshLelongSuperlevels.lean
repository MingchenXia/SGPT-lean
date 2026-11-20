import SGPT.Foundations.Analysis.Pending.RawPshLelongAnalyticGerm
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # Raw manifold Siu superlevels and entire irreducible generic minima

Actual finite common-domain equations are transported through the preferred
chart. Genuine analytic propagation and Baire then give the whole/open-piece
reader and its attained minimum, including infinite raw readers.
-/

open Set Filter
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshLelongSuperlevels

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

private theorem translated_reader_at {n : ℕ} (u : ComplexModel n → EReal)
    (p x : ComplexModel n) :
    lelongNumber (n := n) (fun z => u (z + p)) x = lelongNumber (n := n) u (x + p) := by
  let Φ : LocalHolomorphicEquivAt (n := n) (x + p) := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := fun z => z - p
    invFun := fun z => z + p
    toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun z _ => sub_add_cancel z p
    right_inv := fun z _ => add_sub_cancel_right z p }
  simpa only [Φ, add_sub_cancel_right] using
    (LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ (mem_univ (x + p))
      (u := u))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every real raw quasi-PSH Lelong superlevel is an actual complex analytic
subset, with no analytic type, nondegeneracy, mass or finite reader premise. -/
theorem isComplexAnalyticSubset_superlevel {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (q : ℝ) :
    IsComplexAnalyticSubset (n := n)
      {x : M | ENNReal.ofReal q ≤ lelongNumber (n := n) u x} := by
  classical
  intro x
  let e := complexChartAt (n := n) x
  let p := e.val x
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hp : p ∈ e.val.target := e.val.map_source hxsrc
  have hraw : QuasiPlurisubharmonicAt (chartFunction u e) p := hu e p hp
  have hqt : QuasiPlurisubharmonicAt (fun z : ComplexModel n => chartFunction u e (z + p)) 0 :=
    HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic isOpen_univ
      ((contDiff_id.add contDiff_const).contDiffOn :
        ContDiffOn ℂ ∞ (fun z : ComplexModel n => z + p) univ) (mem_univ 0)
      (by simpa only [id_eq, zero_add] using hraw)
  obtain ⟨N, g, hg, hzero⟩ :=
    RawPshLelongAnalyticGerm.isAnalyticGerm_superlevel_of_quasiPlurisubharmonicAt hqt q
  have htend : Tendsto (fun z : ComplexModel n => z + p) (𝓝 0) (𝓝 p) := by
    simpa only [zero_add] using
      (show ContinuousAt (fun z : ComplexModel n => z + p) 0 from
        continuousAt_id.add continuousAt_const).tendsto
  have htarget : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z + p ∈ e.val.target :=
    htend.eventually (e.val.open_target.mem_nhds hp)
  obtain ⟨W, hprops, hW, h0⟩ :=
    eventually_nhds_iff.mp (((eventually_all.mpr hg).and hzero).and htarget)
  refine ⟨{
    generatorCount := N
    generator := fun i w => g i (w - p)
    coordinateNeighborhood := (fun w => w - p) ⁻¹' W
    isOpen_coordinateNeighborhood := hW.preimage (continuous_id.sub continuous_const)
    center_mem_coordinateNeighborhood := by simpa only [p, e, mem_preimage, sub_self] using h0
    coordinateNeighborhood_subset_target := ?_
    generator_holomorphic := ?_
    zeroLocus := ?_ }⟩
  · intro w hw
    simpa only [sub_add_cancel] using (hprops (w - p) hw).2
  · intro i w hw
    exact (((hprops (w - p) hw).1.1 i).comp w
      (differentiableAt_id.sub_const p)).differentiableWithinAt
  · intro y hysrc hy
    change (ENNReal.ofReal q ≤ lelongNumber (n := n) u y) ↔ ∀ i, g i (e.val y - p) = 0
    rw [← LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hysrc]
    have hread := translated_reader_at (chartFunction u e) p (e.val y - p)
    simp only [sub_add_cancel] at hread
    rw [← hread]
    exact (hprops (e.val y - p) hy).1.2

/-- Actual analytic superlevels propagate a local lower bound to the entire
irreducible variety, giving literal equality of the two raw infimum readers. -/
theorem iInf_eq_open_piece {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (V : ClosedIrreducibleAnalyticSubvariety n M) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    (⨅ x ∈ V.carrier, lelongNumber (n := n) u x) =
      ⨅ x ∈ V.carrier ∩ U, lelongNumber (n := n) u x := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    exact iInf₂_le_of_le x hx.1 le_rfl
  · refine le_iInf₂ fun x hx => ?_
    apply ENNReal.le_of_forall_nnreal_lt
    intro a ha
    have hA := isComplexAnalyticSubset_superlevel hu (a : ℝ)
    have hsub : V.carrier ∩ U ⊆
        {y : M | ENNReal.ofReal (a : ℝ) ≤ lelongNumber (n := n) u y} := by
      intro y hy
      simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal] using
        (ha.le.trans (iInf₂_le_of_le y hy le_rfl))
    have hwhole := StrictTransformLocus.subset_of_inter_isOpen_subset V hA hU hVU hsub
    simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal] using hwhole hx

/-- The entire raw generic reader is genuinely attained in every nonempty
ambient open piece, with no finite value or generic point certificate. -/
theorem exists_minimum_on_open_piece {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (V : ClosedIrreducibleAnalyticSubvariety n M) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    ∃ x ∈ V.carrier ∩ U, lelongNumber (n := n) u x =
      ⨅ y ∈ V.carrier, lelongNumber (n := n) u y := by
  let L : ℝ≥0∞ := ⨅ y ∈ V.carrier, lelongNumber (n := n) u y
  by_cases hLtop : L = ⊤
  · obtain ⟨x, hx⟩ := hVU
    refine ⟨x, hx, ?_⟩
    have hlow : L ≤ lelongNumber (n := n) u x := iInf₂_le_of_le x hx.1 le_rfl
    rw [hLtop] at hlow
    exact (top_le_iff.mp hlow).trans hLtop.symm
  · by_contra hnot
    let q : ℕ → ℝ := fun j => L.toReal + 1 / ((j : ℝ) + 1)
    let A : ℕ → Set M := fun j => {x | ENNReal.ofReal (q j) ≤ lelongNumber (n := n) u x}
    have hA : ∀ j, IsComplexAnalyticSubset (n := n) (A j) :=
      fun j => isComplexAnalyticSubset_superlevel hu (q j)
    have hr : Tendsto q atTop (𝓝 L.toReal) := by
      simpa only [q, add_zero] using
        (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hlim : Tendsto (fun j => ENNReal.ofReal (q j)) atTop (𝓝 L) := by
      have ht := (ENNReal.continuous_ofReal.tendsto L.toReal).comp hr
      rwa [ENNReal.ofReal_toReal hLtop] at ht
    have hcover : V.carrier ∩ U ⊆ ⋃ j, A j := by
      intro x hx
      have hneq : lelongNumber (n := n) u x ≠ L := fun h => hnot ⟨x, hx, h⟩
      have hstrict : L < lelongNumber (n := n) u x :=
        lt_of_le_of_ne (iInf₂_le_of_le x hx.1 le_rfl) hneq.symm
      have hevent : ∀ᶠ j in atTop, ENNReal.ofReal (q j) < lelongNumber (n := n) u x :=
        (tendsto_order.mp hlim).2 _ hstrict
      obtain ⟨j, hj⟩ := hevent.exists
      exact mem_iUnion.mpr ⟨j, hj.le⟩
    obtain ⟨j, hj⟩ :=
      StrictTransformLocus.exists_subset_of_inter_isOpen_subset_iUnion V hA hU hVU hcover
    have hqL : ENNReal.ofReal (q j) ≤ L := le_iInf₂ fun x hx => hj hx
    have hLq : L < ENNReal.ofReal (q j) := by
      rw [← ENNReal.ofReal_toReal hLtop]
      apply ENNReal.ofReal_lt_ofReal_iff'.mpr
      constructor
      · dsimp only [q]
        linarith [show 0 < 1 / ((j : ℝ) + 1) by positivity]
      · dsimp only [q]
        positivity
    exact (not_lt_of_ge hqL) hLq

end

end SGPT.Foundations.Analysis.Pending.RawQuasiPshLelongSuperlevels
