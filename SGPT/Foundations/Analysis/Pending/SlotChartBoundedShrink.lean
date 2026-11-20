import SGPT.Foundations.Analysis.Pending.ThetaCapacityChart

set_option autoImplicit false

/-!
# Shrinking a slot chart inside a prescribed neighbourhood

The local step of Xia's Theorem 2.4.4
(`Pending.RooftopLocalConcentration.diagonalPotentialMeasure_inter_lt_add_eq_zero`)
consumes a slot chart `diagSlotChart theta e D hD rho hrho` together with

* a uniform bound `|rho| <= L` on the coordinate domain `D`;
* two-sided bounds for all the data **on the whole slot-chart source**;
* an open `O` with `closure O` inside that source.

Xia produces these by working on `G' <<- G <<- X \ nK({theta})`
(`xia-sgpt:page-0081`), where Lemma 2.4.1 bounds the data.  This module is the
geometric half of that sentence and nothing else: given any open `Omega`
containing `x`, it produces a slot chart whose **source** already lies inside
`Omega`, a bound for its local potential, and a coordinate ball around `x`
whose closure lies inside that source.

Both nestings come from one radius.  The coordinate domain is the ball of
radius `r/4` around `e x` and `O` is the ball of radius `r/8`; the closure of
`O` is trapped because `e.symm '' closedBall (r/8)` is a compact — hence
closed, `M` being Hausdorff — superset of `O` contained in the source.  The
bound on `rho` is the continuity of a smooth local potential on the compact
`closedBall (r/4)`.

Boundedness of the *data* is not part of this statement: once the source sits
inside `Omega`, `IsBoundedPotentialOn.mono` transports any bound available on
`Omega`, which is how the consumers use it.
-/

open Set Metric TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The chart preimage of a coordinate ball inside the chart target, read as
the symmetric image.  Both descriptions are used below: the first is an open
set by construction, the second makes its closure computable. -/
theorem symm_image_eq_source_inter_preimage (e : ComplexChart n M)
    {S : Set (ComplexModel n)} (hS : S ⊆ e.val.target) :
    e.val.symm '' S = e.val.source ∩ e.val ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e.val.map_target (hS hz), ?_⟩
    show e.val (e.val.symm z) ∈ S
    rwa [e.val.right_inv (hS hz)]
  · rintro ⟨hys, hyS⟩
    exact ⟨e.val y, hyS, e.val.left_inv hys⟩

/-- **A slot chart shrunk inside a prescribed neighbourhood, with a relatively
compact coordinate ball around the given point.**  This is the geometric input
of Xia's Theorem 2.4.4 on `xia-sgpt:page-0081`. -/
theorem exists_diagSlotChart_source_subset_closure_subset
    (theta : ClosedRealOneOneForm n M) {Omega : Set M} (hOmega : IsOpen Omega)
    {x : M} (hx : x ∈ Omega) :
    ∃ (e : ComplexChart n M) (D : Opens (ComplexModel n))
      (hD : (D : Set (ComplexModel n)) ⊆ e.val.target) (rho : ComplexModel n → ℝ)
      (hrho : IsSmoothLocalPotential theta.val e D rho) (L : ℝ) (O : Set M),
      (∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L) ∧
        ((diagSlotChart theta e D hD rho hrho).source : Set M) ⊆ Omega ∧
        IsOpen O ∧ x ∈ O ∧
        closure O ⊆ ((diagSlotChart theta e D hD rho hrho).source : Set M) := by
  classical
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel n := e.val x with hz₀
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hxs
  obtain ⟨W, rho, hz₀W, hrhoW⟩ :=
    SGPT.Foundations.Analysis.Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials
      theta e z₀ hz₀t
  -- the coordinate points whose chart preimage lies in `Omega`
  set T : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' Omega with hT
  have hTopen : IsOpen T :=
    e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hOmega
  have hz₀T : z₀ ∈ T := by
    refine ⟨hz₀t, ?_⟩
    show e.val.symm (e.val x) ∈ Omega
    rwa [e.val.left_inv hxs]
  obtain ⟨r, hr, hrWT⟩ :=
    Metric.isOpen_iff.mp (hrhoW.1.inter hTopen) z₀ ⟨hz₀W, hz₀T⟩
  -- the two nested radii
  have hq4 : closedBall z₀ (r / 4) ⊆ ball z₀ r := by
    refine closedBall_subset_ball ?_; linarith
  have hb4 : ball z₀ (r / 4) ⊆ closedBall z₀ (r / 4) := ball_subset_closedBall
  have hq8 : closedBall z₀ (r / 8) ⊆ ball z₀ (r / 4) := by
    refine closedBall_subset_ball ?_; linarith
  have hb8 : ball z₀ (r / 8) ⊆ closedBall z₀ (r / 8) := ball_subset_closedBall
  have h4W : ball z₀ (r / 4) ⊆ W := fun z hz => (hrWT (hq4 (hb4 hz))).1
  have h4T : ball z₀ (r / 4) ⊆ T := fun z hz => (hrWT (hq4 (hb4 hz))).2
  set D : Opens (ComplexModel n) := ⟨ball z₀ (r / 4), isOpen_ball⟩ with hDdef
  have hD : (D : Set (ComplexModel n)) ⊆ e.val.target := fun z hz => (h4T hz).1
  have hrho : IsSmoothLocalPotential theta.val e D rho :=
    hrhoW.mono isOpen_ball h4W
  -- the bound on the local potential, by continuity on a compact closed ball
  obtain ⟨L, hL⟩ :=
    (isCompact_closedBall z₀ (r / 4)).exists_bound_of_continuousOn
      (hrhoW.2.2.1.continuousOn.mono ((hq4.trans hrWT).trans inter_subset_left))
  refine ⟨e, D, hD, rho, hrho, L, e.val.source ∩ e.val ⁻¹' ball z₀ (r / 8),
    fun z hz => hL z (hb4 hz), ?_, ?_, ?_, ?_⟩
  · -- the source lies inside `Omega`
    rintro y ⟨hys, hyD⟩
    have hyT : e.val y ∈ T := h4T hyD
    have hmem : e.val.symm (e.val y) ∈ Omega := hyT.2
    rwa [e.val.left_inv hys] at hmem
  · exact e.val.isOpen_inter_preimage isOpen_ball
  · exact ⟨hxs, mem_ball_self (by positivity)⟩
  · -- the closure of the small ball stays inside the source
    have hOeq : e.val.source ∩ e.val ⁻¹' ball z₀ (r / 8) =
        e.val.symm '' ball z₀ (r / 8) :=
      (symm_image_eq_source_inter_preimage e
        (fun z hz => hD (hq8 (hb8 hz)))).symm
    have hKcompact : IsCompact (e.val.symm '' closedBall z₀ (r / 8)) :=
      (isCompact_closedBall z₀ (r / 8)).image_of_continuousOn
        (e.val.continuousOn_symm.mono (fun z hz => hD (hq8 hz)))
    have hKsub : e.val.symm '' closedBall z₀ (r / 8) ⊆
        ((diagSlotChart theta e D hD rho hrho).source : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      have hzt : z ∈ e.val.target := hD (hq8 hz)
      refine ⟨e.val.map_target hzt, ?_⟩
      show e.val (e.val.symm z) ∈ (D : Set (ComplexModel n))
      rw [e.val.right_inv hzt]
      exact hq8 hz
    refine subset_trans ?_ hKsub
    rw [hOeq]
    exact closure_minimal (Set.image_mono hb8) hKcompact.isClosed

end

end SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink
