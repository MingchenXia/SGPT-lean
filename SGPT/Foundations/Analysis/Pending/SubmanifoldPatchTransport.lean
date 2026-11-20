import SGPT.Foundations.Analysis.Pending.DominationBigRestriction
import SGPT.Foundations.Analysis.Pending.RegularPatchPushforward
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Regular patches of `V ⊆ X` read as regular patches of the complex manifold `↥V`

Route F, `F-b` step P1 (plan §8 of `scratch/tn23-envelopes-qea-plan-0117.md`; blueprint
`pc:f-restricted-volume-le`).  The restricted absolutely continuous mass `acTopMass` of an
admissible presentation along `V` is computed in the flattening patches of `V` inside the charts of
`X` (`NumericalRestrictedVolume.RegularPatch`).  The submanifold `↥V` is a complex manifold in its own
right (`SubmanifoldChartedSpace`), and on a complex manifold the restricted mass of the WHOLE space
is bounded by the non-pluripolar mass (`FullSpaceAmbientComparison`).  This module is the bridge
between the two descriptions, at the level of one patch:

* `patchFlatData P` — a regular patch `P` of `V` is a flattening datum of `↥V`; its chart is the
  inverse of `P`'s parametrization (`patchFlatData_ofCoord`);
* `transitionEquiv` — the transition from the preferred chart of `↥V` at a point to that chart, a
  local biholomorphism of `ℂ^{dim V}` (holomorphic transitions of `↥V`);
* `targetPatch P hv₀` — for a parameter `v₀` of `P`, a regular patch of the whole of `↥V`
  (`DominationBigRestriction.univSubvariety`) centred at `P(v₀)` with
  `targetPatch(w) = P(w + v₀)` (`val_targetPatch_toManifold`), defined on a neighbourhood of `0`
  (`exists_ball_targetPatch`).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.SubmanifoldPatchTransport

noncomputable section

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularLocusDense
  SubmanifoldChartedSpace RegularPatchPullback

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {V : ClosedIrreducibleAnalyticSubvariety n X}

/-- **A regular patch of `V` is a flattening datum of `↥V`.** -/
def patchFlatData (P : RegularPatch V) : FlatData n V.dim X V.carrier where
  amb := complexChartAt (n := n) P.center
  flat := P.flattening.toOpenPartialHomeomorph
  differentiableOn_flat := P.flattening.toFun_holomorphic
  differentiableOn_flat_symm := P.flattening.invFun_holomorphic
  flat_source_subset := P.source_subset
  mem_iff := fun _ hy hyΦ => P.flattens hy hyΦ
  base := P.center
  base_mem := P.center_mem

theorem patchFlatData_ofCoord (P : RegularPatch V) (w : ComplexModel V.dim) :
    (patchFlatData P).ofCoord w = P.toManifold w := rfl

theorem patchFlatData_coordTarget (P : RegularPatch V) :
    (patchFlatData P).coordTarget = P.parameterDomain := rfl

theorem mem_patchFlatData_ambSource (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) : P.toManifold w ∈ (patchFlatData P).ambSource :=
  (patchFlatData P).ofCoord_mem_ambSource hw

theorem patchFlatData_toCoord (hk : V.dim ≤ n) (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) :
    (patchFlatData P).toCoord ⟨P.toManifold w, RegularPatchNeighborhood.RegularPatch.toManifold_mem_carrier P hw⟩ = w :=
  (patchFlatData P).toCoord_ofCoord hk hw _

section Transition

variable (hk : V.dim ≤ n) (hW : ∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim)

/-- The flattening datum of the preferred chart of `↥V` at `c`. -/
def chartData (c : V.carrier) : FlatData n V.dim X V.carrier :=
  FlatData.ofRegularAtDim (hW c.1 c.2)

/-- The transition from the preferred chart of `↥V` at `c` to the chart of the patch `P`. -/
def transition (P : RegularPatch V) (c : V.carrier) :
    OpenPartialHomeomorph (ComplexModel V.dim) (ComplexModel V.dim) :=
  ((chartData hW c).chart hk).symm.trans ((patchFlatData P).chart hk)

theorem transition_source (P : RegularPatch V) (c : V.carrier) :
    (transition hk hW P c).source = FlatData.transSource (chartData hW c) (patchFlatData P) := by
  rw [← FlatData.chart_target_inter_preimage]
  rfl

theorem transition_target (P : RegularPatch V) (c : V.carrier) :
    (transition hk hW P c).target = FlatData.transSource (patchFlatData P) (chartData hW c) := by
  rw [← FlatData.chart_target_inter_preimage]
  rfl

theorem transition_apply (P : RegularPatch V) (c : V.carrier) (ζ : ComplexModel V.dim) :
    transition hk hW P c ζ = (patchFlatData P).toCoord ((chartData hW c).invPoint ζ) := rfl

theorem transition_symm_apply (P : RegularPatch V) (c : V.carrier) (w : ComplexModel V.dim) :
    (transition hk hW P c).symm w = (chartData hW c).toCoord ((patchFlatData P).invPoint w) := rfl

theorem differentiableOn_transition (P : RegularPatch V) (c : V.carrier) :
    DifferentiableOn ℂ (transition hk hW P c) (transition hk hW P c).source := by
  rw [transition_source]
  refine (FlatData.differentiableOn_transMap _ _).congr fun ζ hζ => ?_
  exact FlatData.toCoord_invPoint_eqOn _ _ hζ

theorem differentiableOn_transition_symm (P : RegularPatch V) (c : V.carrier) :
    DifferentiableOn ℂ (transition hk hW P c).symm (transition hk hW P c).target := by
  rw [transition_target]
  refine (FlatData.differentiableOn_transMap _ _).congr fun ζ hζ => ?_
  exact FlatData.toCoord_invPoint_eqOn _ _ hζ

theorem chart_mem_transition_source (P : RegularPatch V) (c : V.carrier)
    (hc : c.1 ∈ (patchFlatData P).ambSource) :
    (chartData hW c).chart hk c ∈ (transition hk hW P c).source := by
  have hcs : c ∈ ((chartData hW c).chart hk).source :=
    FlatData.mem_ambSource_ofRegularAtDim (hW c.1 c.2)
  refine ⟨((chartData hW c).chart hk).map_source hcs, ?_⟩
  change ((chartData hW c).chart hk).symm ((chartData hW c).chart hk c) ∈
    ((patchFlatData P).chart hk).source
  rw [((chartData hW c).chart hk).left_inv hcs]
  exact hc

/-- The transition, as a local holomorphic equivalence centred at the chart point of `c`. -/
def transitionEquiv (P : RegularPatch V) (c : V.carrier)
    (hc : c.1 ∈ (patchFlatData P).ambSource) :
    LocalHolomorphicEquivAt (n := V.dim) ((chartData hW c).chart hk c) where
  source := (transition hk hW P c).source
  target := (transition hk hW P c).target
  isOpen_source := (transition hk hW P c).open_source
  isOpen_target := (transition hk hW P c).open_target
  center_mem_source := chart_mem_transition_source hk hW P c hc
  toFun := transition hk hW P c
  invFun := (transition hk hW P c).symm
  toFun_holomorphic := differentiableOn_transition hk hW P c
  invFun_holomorphic := differentiableOn_transition_symm hk hW P c
  mapsTo_toFun := fun _ hz => (transition hk hW P c).map_source hz
  mapsTo_invFun := fun _ hw => (transition hk hW P c).map_target hw
  left_inv := fun _ hz => (transition hk hW P c).left_inv hz
  right_inv := fun _ hw => (transition hk hW P c).right_inv hw

end Transition

/-! ### The target patch -/

section TargetPatch

variable (hk : V.dim ≤ n) (hW : ∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim)

/-- The point `P(v₀)` of `↥V`. -/
def patchPoint (P : RegularPatch V) {v₀ : ComplexModel V.dim} (hv₀ : v₀ ∈ P.parameterDomain) :
    V.carrier :=
  ⟨P.toManifold v₀, RegularPatchNeighborhood.RegularPatch.toManifold_mem_carrier P hv₀⟩

theorem transition_patchPoint (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) :
    transition hk hW P (patchPoint P hv₀)
      ((chartData hW (patchPoint P hv₀)).chart hk (patchPoint P hv₀)) = v₀ := by
  have hcs : patchPoint P hv₀ ∈ ((chartData hW (patchPoint P hv₀)).chart hk).source :=
    FlatData.mem_ambSource_ofRegularAtDim (hW _ (patchPoint P hv₀).2)
  change ((patchFlatData P).chart hk)
    (((chartData hW (patchPoint P hv₀)).chart hk).symm
      (((chartData hW (patchPoint P hv₀)).chart hk) (patchPoint P hv₀))) = v₀
  rw [((chartData hW (patchPoint P hv₀)).chart hk).left_inv hcs]
  exact patchFlatData_toCoord hk P hv₀

variable [ConnectedSpace V.carrier] [Nonempty V.carrier]

/-- **The target patch.**  For a parameter `v₀` of a regular patch `P` of `V`, the regular patch of
the whole complex manifold `↥V` centred at `P(v₀)`, whose flattening is the transition from the
preferred chart of `↥V` at `P(v₀)` to the chart of `P`, shifted by `v₀`. -/
def targetPatch (P : RegularPatch V) {v₀ : ComplexModel V.dim} (hv₀ : v₀ ∈ P.parameterDomain) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    RegularPatch (DominationBigRestriction.univSubvariety (k := V.dim) (Z := V.carrier)) :=
  letI := chartedSpace hk hW
  haveI := isComplexManifold_chartedSpace hk hW
  { center := patchPoint P hv₀
    center_mem := mem_univ _
    flattening := subConst (transitionEquiv hk hW P (patchPoint P hv₀)
      (mem_patchFlatData_ambSource P hv₀)) v₀
    source_subset := fun _ hz => hz.1
    center_to_zero := by
      change transition hk hW P (patchPoint P hv₀)
        ((chartData hW (patchPoint P hv₀)).chart hk (patchPoint P hv₀)) - v₀ = 0
      rw [transition_patchPoint hk hW P hv₀, sub_self]
    flattens := fun _ _ => by
      refine iff_of_true (mem_univ _) ?_
      intro i hi
      exact absurd i.2 (not_lt.mpr hi) }

theorem targetPatch_center (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (targetPatch hk hW P hv₀).center = patchPoint P hv₀ := rfl

theorem targetPatch_coordinateParametrization (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) (w : ComplexModel V.dim) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (targetPatch hk hW P hv₀).coordinateParametrization w =
      (transition hk hW P (patchPoint P hv₀)).symm (w + v₀) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  change (transition hk hW P (patchPoint P hv₀)).symm (planeInclusion V.dim V.dim w + v₀) = _
  rw [FullSpaceRegularPatch.planeInclusion_self]

theorem mem_targetPatch_parameterDomain_iff (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) (w : ComplexModel V.dim) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    w ∈ (targetPatch hk hW P hv₀).parameterDomain ↔
      w + v₀ ∈ (transition hk hW P (patchPoint P hv₀)).target := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  change planeInclusion V.dim V.dim w + v₀ ∈ (transition hk hW P (patchPoint P hv₀)).target ↔ _
  rw [FullSpaceRegularPatch.planeInclusion_self]

/-- `w + v₀` lies in the target of the transition as soon as it is a parameter of `P` whose point
lies in the preferred chart of `↥V` at `P(v₀)`. -/
theorem mem_transition_target (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) {v : ComplexModel V.dim} (hv : v ∈ P.parameterDomain)
    (hvG : P.toManifold v ∈ (chartData hW (patchPoint P hv₀)).ambSource) :
    v ∈ (transition hk hW P (patchPoint P hv₀)).target := by
  rw [transition_target]
  refine ⟨hv, ?_⟩
  rw [mem_preimage, patchFlatData_ofCoord]
  exact hvG

/-- **The target patch parametrizes `V` as `P` does, shifted by `v₀`.** -/
theorem val_targetPatch_toManifold (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) {w : ComplexModel V.dim}
    (hw : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      w ∈ (targetPatch hk hW P hv₀).parameterDomain) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ((targetPatch hk hW P hv₀).toManifold w : X) = P.toManifold (w + v₀) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  set G := chartData hW (patchPoint P hv₀)
  set F := patchFlatData P
  have hτ : w + v₀ ∈ (transition hk hW P (patchPoint P hv₀)).target :=
    (mem_targetPatch_parameterDomain_iff hk hW P hv₀ w).mp hw
  have hτ' := hτ
  rw [transition_target] at hτ'
  -- `F.invPoint (w + v₀)` lies in the source of `G`'s chart
  have hFsrc : F.invPoint (w + v₀) ∈ (G.chart hk).source := by
    change (F.invPoint (w + v₀) : X) ∈ G.ambSource
    rw [F.invPoint_val hτ'.1]
    exact hτ'.2
  have h1 : (targetPatch hk hW P hv₀).toManifold w =
      (G.chart hk).symm ((transition hk hW P (patchPoint P hv₀)).symm (w + v₀)) := by
    rw [← targetPatch_coordinateParametrization hk hW P hv₀ w]
    rfl
  rw [h1]
  change (((G.chart hk).symm ((G.chart hk) (F.invPoint (w + v₀))) : V.carrier) : X) = _
  rw [(G.chart hk).left_inv hFsrc, F.invPoint_val hτ'.1, patchFlatData_ofCoord]

/-- **The target patch is defined on a ball around `0`**: for `v` near `v₀`, `v - v₀` is a parameter
of the target patch and `v` one of `P`. -/
theorem exists_ball_targetPatch (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∃ r : ℝ, 0 < r ∧ ∀ v ∈ Metric.ball v₀ r,
      v ∈ P.parameterDomain ∧ v - v₀ ∈ (targetPatch hk hW P hv₀).parameterDomain := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  set T := (transition hk hW P (patchPoint P hv₀)).target
  have hT : IsOpen T := (transition hk hW P (patchPoint P hv₀)).open_target
  have hv₀T : v₀ ∈ T :=
    mem_transition_target hk hW P hv₀ hv₀
      (FlatData.mem_ambSource_ofRegularAtDim (hW _ (patchPoint P hv₀).2))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hT v₀ hv₀T
  refine ⟨r, hr, fun v hv => ?_⟩
  have hvT : v ∈ T := hball hv
  refine ⟨?_, ?_⟩
  · have hvT' := hvT
    change v ∈ (transition hk hW P (patchPoint P hv₀)).target at hvT'
    rw [transition_target] at hvT'
    exact hvT'.1
  · rw [mem_targetPatch_parameterDomain_iff, sub_add_cancel]
    exact hvT

end TargetPatch

end

end SGPT.Foundations.Analysis.Pending.SubmanifoldPatchTransport
