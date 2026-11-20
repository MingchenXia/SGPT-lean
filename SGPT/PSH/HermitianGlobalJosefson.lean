import SGPT.PSH.HermitianExistence
import SGPT.PSH.HermitianExtremalLocalPoleCover
import SGPT.PSH.HermitianAtlasComponents
import SGPT.PSH.HermitianJosefsonMassZero
import SGPT.PSH.HermitianBoundedMassPositive

/-!
# Global Josefson in the genuine local quasi-PSH class

Source: FPT, Theorem 14.8.7, and blueprint node
`hermitian-josefson:global-poles`. The connected positive-dimensional
proof uses the actual Hermitian background, genuine radial compact
sublevels, canonical zero-mass outer extremal and positive bounded mass.
The finite original pole cover and genuine pole-series closure then give
one nonpositive potential. Actual open-component gluing handles arbitrary
native dimensions and reads the result back to the original variable atlas.

Both canonical mass producers are instantiated directly; no mass-positivity
or continuity certificate is introduced in the final theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalJosefson

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open Hermitian HermitianExtremal HermitianGlobalProducts
open scoped Topology

/-- A genuine pluripolar witness in the zero-dimensional model is finite
at its unique point. Consequently every locally pluripolar set is empty. -/
theorem manifoldLocallyPluripolar_eq_empty_dim_zero
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel 0) N]
    [IsComplexManifold 0 N] {S : Set N}
    (hS : ManifoldLocallyPluripolar (n := 0) S) : S = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  let e : ComplexChart 0 N := complexChartAt y
  have hys : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hys
  obtain ⟨V, u, _, hzV, _, _, ⟨a, _, hua⟩, hpole⟩ := hS e (e.val y) hz
  have ha : a = e.val y := by
    ext i
    exact i.elim0
  apply hua
  rw [ha]
  apply hpole _ hzV
  exact ⟨hz, by simpa only [mem_preimage, e.val.left_inv hys] using hy⟩

/-- The actual zero-dimensional case, including disconnected or empty
manifolds, uses the genuine zero quasi-PSH potential. -/
theorem exists_nonpositive_quasiPsh_pole_dim_zero
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel 0) N]
    [IsComplexManifold 0 N] (S : Set N)
    (hS : ManifoldLocallyPluripolar (n := 0) S) :
    ∃ q : N → EReal, IsGlobalQuasiPshPotential (n := 0) q ∧
      (∀ x, q x ≤ 0) ∧ ∀ x ∈ S, q x = ⊥ := by
  have hEmpty := manifoldLocallyPluripolar_eq_empty_dim_zero hS
  refine ⟨fun _ => 0, isGlobalQuasiPshPotential_const 0, fun _ => le_rfl, fun x hx => ?_⟩
  exact False.elim (by rw [hEmpty] at hx; exact hx)

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The actual radial outer extremal of a buffered local witness has zero
canonical mass if its genuine local pole set has no global Hermitian pole.
All neighborhoods and geometric buffers are manufactured from the local
witness; no capacity, support or mass-continuity statement is assumed. -/
theorem localPoleBall_zero_mass_outer_of_no_global_pole
    (omega : Background (m + 1) M) {S : Set M}
    (B : LocalPoleBall (m := m) S) (hpole : B.poleSet.Nonempty)
    (hnot : ¬ ∃ q : M → EReal, IsHermitianPSH omega q ∧
      ∀ x ∈ B.poleSet, q x = ⊥) :
    ∃ (C : ℝ)
      (hO : IsHermitianPSH omega
        (chartRadialOuter omega B.e B.center B.radius (32 * B.radius) B.potential))
      (hbO : ∀ x,
        0 ≤ chartRadialOuter omega B.e B.center B.radius (32 * B.radius) B.potential x ∧
        chartRadialOuter omega B.e B.center B.radius (32 * B.radius) B.potential x ≤
          (C : EReal)),
      globalMixedMeasure omega
        (fun _ => chartRadialOuter omega B.e B.center B.radius (32 * B.radius) B.potential)
        (fun _ => hO) (fun _ => ⟨0, C, hbO⟩) univ = 0 := by
  let Ω : Opens (ComplexModel (m + 1)) :=
    ⟨ball B.center (24 * B.radius), isOpen_ball⟩
  have hcompact : IsCompact (closure (Ω : Set (ComplexModel (m + 1)))) :=
    (isCompact_closedBall B.center (24 * B.radius)).of_isClosed_subset
      isClosed_closure closure_ball_subset_closedBall
  have htarget : closure (Ω : Set (ComplexModel (m + 1))) ⊆ B.e.val.target :=
    closure_ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith [B.radius_pos])).trans B.target_buffer)
  have hΩ : closedBall B.center (5 * (4 * B.radius)) ⊆ Ω :=
    closedBall_subset_ball (by linarith [B.radius_pos])
  obtain ⟨x, hx⟩ := hpole
  exact chartRadial_outer_globalMass_eq_zero omega B.e Ω hcompact htarget B.center
    (R := 4 * B.radius) (by positivity [B.radius_pos])
    (by linarith [B.radius_pos]) (by linarith [B.radius_pos]) hΩ
    B.plurisubharmonic B.nontrivial B.nonpositive ⟨B.e.val x, hx.1.2, hx.2⟩ hnot

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual global witnesses for the finitely selected coordinate pole
sets combine by the proved genuine quasi-PSH pole series. -/
theorem exists_nonpositive_hermitian_pole_of_finite_localPoleBall_poles
    (omega : Background (m + 1) M) (S : Set M)
    (B : M → LocalPoleBall (m := m) S) (t : Finset M)
    (hcover : ∀ x : M, ∃ i ∈ t, x ∈ (B i).domain)
    (u : t → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hpole : ∀ (i : t) x, x ∈ (B i.val).poleSet → u i x = ⊥) :
    ∃ q : M → EReal, IsHermitianPSH omega q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ S, q x = ⊥ := by
  classical
  obtain ⟨q, hq, hq0, hqPole⟩ := exists_pole_iUnion_countable_of_quasiPsh_poles
    omega (fun i : t => (B i.val).poleSet)
      (fun i => ⟨u i, (hu i).quasiPshPotential, fun x hx => hpole i x hx⟩)
  refine ⟨q, hq, hq0, fun x hxS => ?_⟩
  obtain ⟨i, hit, hxi⟩ := hcover x
  exact hqPole x (mem_iUnion.mpr ⟨⟨i, hit⟩, (B i).subset_poleSet ⟨hxS, hxi⟩⟩)

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine buffered local PSH pole set has an actual global Hermitian
pole. In the nonempty case the manufactured bounded zero-mass extremal
contradicts the proved positive canonical mass of every bounded potential. -/
theorem exists_hermitian_pole_localPoleBall
    (omega : Background (m + 1) M) {S : Set M} (B : LocalPoleBall (m := m) S) :
    ∃ q : M → EReal, IsHermitianPSH omega q ∧ ∀ x ∈ B.poleSet, q x = ⊥ := by
  classical
  borelize M
  by_cases hpole : B.poleSet.Nonempty
  · by_contra hnot
    obtain ⟨C, hO, hbO, hzero⟩ :=
      localPoleBall_zero_mass_outer_of_no_global_pole omega B hpole hnot
    have hpos := globalMixedMeasure_diagonal_mass_pos omega hO ⟨0, C, hbO⟩
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  · refine ⟨fun _ => 0, isHermitianPSH_zero omega, fun x hx => ?_⟩
    exact False.elim (hpole ⟨x, hx⟩)

omit [MeasurableSpace M] [BorelSpace M] in
/-- Global Josefson on a connected compact positive-dimensional native
complex manifold, retaining an arbitrary actual Hermitian background.
The finite original coordinate witnesses and their global poles are
manufactured internally from the original local pluripolarity predicate. -/
theorem exists_connected_nonpositive_hermitian_pole
    (omega : Background (m + 1) M) (S : Set M)
    (hS : ManifoldLocallyPluripolar (n := m + 1) S) :
    ∃ q : M → EReal, IsHermitianPSH omega q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ S, q x = ⊥ := by
  classical
  obtain ⟨B, t, hcover⟩ := exists_finite_localPoleBall_cover S hS
  have hw (i : t) : ∃ q : M → EReal, IsHermitianPSH omega q ∧
      ∀ x ∈ (B i.val).poleSet, q x = ⊥ :=
    exists_hermitian_pole_localPoleBall omega (B i.val)
  choose u hu hpole using hw
  exact exists_nonpositive_hermitian_pole_of_finite_localPoleBall_poles
    omega S B t hcover u hu hpole

/-- The connected native theorem in every dimension. The auxiliary
Hermitian metric is produced from compactness, and dimension zero uses
the proved empty-set case. -/
theorem exists_connected_nonpositive_quasiPsh_pole
    {n : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel n) N]
    [IsComplexManifold n N] [CompactSpace N] [ConnectedSpace N]
    (S : Set N) (hS : ManifoldLocallyPluripolar (n := n) S) :
    ∃ q : N → EReal, IsGlobalQuasiPshPotential (n := n) q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ S, q x = ⊥ := by
  cases n with
  | zero => exact exists_nonpositive_quasiPsh_pole_dim_zero S hS
  | succ k =>
    obtain ⟨omega⟩ := exists_background (n := k + 1) (M := N)
    obtain ⟨q, hq, hq0, hqPole⟩ := exists_connected_nonpositive_hermitian_pole omega S hS
    exact ⟨q, hq.quasiPshPotential, hq0, hqPole⟩

/-- Native Global Josefson on an arbitrary compact complex manifold,
including empty and disconnected manifolds and dimension zero. Genuine
open-component potentials retain their local nondegeneracy when glued. -/
theorem exists_nonpositive_quasiPsh_pole
    {n : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel n) N]
    [IsComplexManifold n N] [CompactSpace N]
    (S : Set N) (hS : ManifoldLocallyPluripolar (n := n) S) :
    ∃ q : N → EReal, IsGlobalQuasiPshPotential (n := n) q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ S, q x = ⊥ := by
  let : LocallyConnectedSpace N := OpensRestrictionMeasure.locallyConnectedSpace n N
  apply HermitianComponents.glue_component_quasiPsh_poles S
  intro c
  exact exists_connected_nonpositive_quasiPsh_pole _
    (OpensRestrictionMeasure.manifoldLocallyPluripolar_preimage_val hS)

end SGPT.PSH.HermitianGlobalJosefson

namespace SGPT.PSH.VariableComplexAtlas

open Set

variable {X : Type*} [TopologicalSpace X]

/-- The actual original-atlas component is compact when the original
space is compact, regardless of dimensions on the other components. -/
theorem compactSpace_componentOpen [CompactSpace X] (A : VariableComplexAtlas X) (a : X) :
    CompactSpace (A.componentOpen a) :=
  isCompact_iff_compactSpace.mp
    (show IsClosed (A.componentOpen a : Set X) from isClosed_connectedComponent).isCompact

/-- Connectedness uses the actual original component topology. -/
theorem connectedSpace_componentOpen (A : VariableComplexAtlas X) (a : X) :
    ConnectedSpace (A.componentOpen a) :=
  Subtype.connectedSpace (show IsConnected (A.componentOpen a : Set X) from
    isConnected_connectedComponent)

/-- FPT Global Josefson in the ORIGINAL independently dimensional atlas:
every locally pluripolar subset of a compact complex manifold is contained
in the poles of one nonpositive genuine local quasi-PSH function. The
predicate retains local nondegeneracy, and the auxiliary metric and every
native component structure are produced internally. -/
theorem source_exists_nonpositive_global_pluripolar_pole_compact_localQPSH
    [T2Space X] [CompactSpace X] (A : VariableComplexAtlas X) (S : Set X)
    (hS : A.LocallyPluripolar S) :
    ∃ q : X → EReal, A.IsLocalQPSH q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ S, q x = ⊥ := by
  apply A.glue_native_component_localQPSH_poles S
  intro c
  let a : X := HermitianComponents.representative c
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  let := A.compactSpace_componentOpen a
  let := A.connectedSpace_componentOpen a
  exact HermitianGlobalJosefson.exists_connected_nonpositive_quasiPsh_pole
    (Subtype.val ⁻¹' S) (hS.nativeComponent a)

end SGPT.PSH.VariableComplexAtlas
