import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole
import SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor
import SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.FlattenedGlobalGenericLelongComparison
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.HironakaActualPointBlowupCoordinates
import SGPT.Foundations.Analysis.Pending.HironakaLocalPrincipalization
import SGPT.Foundations.Analysis.Pending.LelongNumberComparison
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
import SGPT.Foundations.Analysis.Pending.ProperFiberFiniteNeighborhoodCover
import SGPT.Foundations.Analysis.Pending.RawQuasiPshDivisorialSliceBound
import Mathlib.Data.ENNReal.Inv

/-! Actual point-blowup fibre geometry and the literal native reader.
All local logarithmic constants and the global target neighborhood are
produced from actual analytic charts and proper geometry. Dimension one
uses the point-ideal divisor carrier; dimension zero point-blowup data
are excluded by the original nowhere-dense-centre predicate.
The interpretation of the source's implicit admissible-prime domain is
recorded separately; this file alone makes no source-coverage claim.
-/

set_option autoImplicit false
noncomputable section
universe u

open Set Filter Metric
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.PointBlowupLelong

open FirstPass FirstPass.NonKahlerLocus FirstPass.BlowupSequences
open HironakaActualPointBlowupCoordinates HironakaActualAnalyticBlowupTaylor
open BlowupFlatCoordinates DemaillyApproximantDivisorialLelong

/-- An actual complex linear coordinate permutation, preserving the two
analytic inverse identities. Copied from the existing adapted-coordinate
producer; no formal power-series coordinate surrogate is introduced. -/
private def permuteCoordinates {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (σ : Fin n ≃ Fin n) :
    LocalHolomorphicEquivAt (n := n) p := by
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ
  exact
    { source := Φ.source
      target := L.symm ⁻¹' Φ.target
      isOpen_source := Φ.isOpen_source
      isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
      center_mem_source := Φ.center_mem_source
      toFun := fun z => L (Φ.toFun z)
      invFun := fun z => Φ.invFun (L.symm z)
      toFun_holomorphic := L.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn.comp
        Φ.toFun_holomorphic (fun _ _ => mem_univ _)
      invFun_holomorphic := Φ.invFun_holomorphic.comp
        L.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn
        (fun _ hz => hz)
      mapsTo_toFun := fun z hz => by
        change L.symm (L (Φ.toFun z)) ∈ Φ.target
        rw [L.symm_apply_apply]
        exact Φ.mapsTo_toFun hz
      mapsTo_invFun := fun z hz => Φ.mapsTo_invFun hz
      left_inv := fun z hz => by
        rw [L.symm_apply_apply]
        exact Φ.left_inv z hz
      right_inv := fun z hz => by
        rw [Φ.right_inv _ hz]
        exact L.apply_symm_apply z }

private theorem permuteCoordinates_apply {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (σ : Fin n ≃ Fin n)
    (z : ComplexModel n) (i : Fin n) :
    (permuteCoordinates Φ σ).toFun z (σ i) = Φ.toFun z i := by
  simp [permuteCoordinates, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The whole actual point fibre has a genuine hypersurface flattening whose
normal coordinate is literally one coordinate of the centered original base
map. This includes dimension one, without identifying the fibre with the
differential exceptional locus. -/
theorem exists_point_fibre_flattening
    {m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong (m + 1) ({x} : Set X) π)
    {y : Y} (hy : π y = x) :
    ∃ (A : LocalHolomorphicEquivAt (n := m + 1) (chartAt (ComplexModel (m + 1)) x x))
      (Φ : DivisorFlattening (m := m) (π ⁻¹' ({x} : Set X)) y) (j : Fin (m + 1)),
      A.source ⊆ (chartAt (ComplexModel (m + 1)) x).target ∧
      A.toFun (chartAt (ComplexModel (m + 1)) x x) = 0 ∧
      ∀ z : Y, z ∈ (chartAt (ComplexModel (m + 1)) y).source →
        chartAt (ComplexModel (m + 1)) y z ∈ Φ.Φ.source →
        π z ∈ flatDomain A ∧
        Φ.coord z (Fin.last m) = A.toFun (chartAt (ComplexModel (m + 1)) x (π z)) j := by
  subst x
  have hreg : RegularAtDim (n := m + 1) ({π y} : Set X) (π y) 0 :=
    (DominationLogResolution.isClosedConnectedSubmanifold_singleton (π y)).2.2
      (π y) (mem_singleton (π y))
  obtain ⟨A, j, b, B, hAs, hA0, hBs, hB0, _hbj, hmap⟩ :=
    exists_actual_point_blowup_coordinates hπ y hreg
  let P := permuteCoordinates B (Equiv.swap j (Fin.last m))
  have hlast (w : ComplexModel (m + 1)) : P.toFun w (Fin.last m) = B.toFun w j := by
    simpa only [Equiv.swap_apply_left] using
      permuteCoordinates_apply B (Equiv.swap j (Fin.last m)) w j
  have hP0 : P.toFun (chartAt (ComplexModel (m + 1)) y y) = 0 := by
    simp only [P, permuteCoordinates, hB0, map_zero]
  have hpiv (z : Y) (hz : z ∈ (chartAt (ComplexModel (m + 1)) y).source)
      (hzB : chartAt (ComplexModel (m + 1)) y z ∈ B.source) :
      A.toFun (chartAt (ComplexModel (m + 1)) (π y) (π z)) j =
        B.toFun (chartAt (ComplexModel (m + 1)) y z) j := by
    have h := congrArg (fun w : ComplexModel (m + 1) => w j) (hmap z hz hzB).2
    simpa only [actualAnalyticBlowupMap_apply, actualAnalyticBlowupCoordinate,
      mem_univ, if_true] using h
  let Φ : DivisorFlattening (m := m) (π ⁻¹' ({π y} : Set X)) y :=
    { Φ := P
      source_subset := hBs
      map_center := hP0
      mem_iff := by
        intro z hz hzP
        have hzB : chartAt (ComplexModel (m + 1)) y z ∈ B.source := hzP
        have hgeom := hmap z hz hzB
        change π z ∈ ({π y} : Set X) ↔
          P.toFun (chartAt (ComplexModel (m + 1)) y z) (Fin.last m) = 0
        rw [mem_singleton_iff, hlast]
        constructor
        · intro hzy
          rw [← hpiv z hz hzB, hzy, hA0]
          rfl
        · intro hzero
          have hmzero : actualAnalyticBlowupMap univ j b
              (B.toFun (chartAt (ComplexModel (m + 1)) y z)) = 0 := by
            ext i
            by_cases hij : i = j
            · subst i
              simpa only [actualAnalyticBlowupMap_apply, actualAnalyticBlowupCoordinate,
                mem_univ, if_true, PiLp.zero_apply] using hzero
            · simp only [actualAnalyticBlowupMap_apply, actualAnalyticBlowupCoordinate,
                mem_univ, if_true, if_neg hij, hzero, zero_mul, PiLp.zero_apply]
          have hAzero := hgeom.2.trans hmzero
          have hcoord : chartAt (ComplexModel (m + 1)) (π y) (π z) =
              chartAt (ComplexModel (m + 1)) (π y) (π y) := by
            calc
              _ = A.invFun (A.toFun _) := (A.left_inv _ hgeom.1.2).symm
              _ = A.invFun (A.toFun (chartAt (ComplexModel (m + 1)) (π y) (π y))) := by
                rw [hAzero, hA0]
              _ = _ := A.left_inv _ A.center_mem_source
          exact (chartAt (ComplexModel (m + 1)) (π y)).injOn
            hgeom.1.1 (mem_chart_source _ _) hcoord }
  refine ⟨A, Φ, j, hAs, hA0, ?_⟩
  intro z hz hzΦ
  have hzB : chartAt (ComplexModel (m + 1)) y z ∈ B.source := hzΦ
  refine ⟨(hmap z hz hzB).1, ?_⟩
  change P.toFun _ (Fin.last m) = _
  rw [hlast]
  exact (hpiv z hz hzB).symm

/-- Actual point-blowup coordinates and the genuine three-circle slice
producer give a local bound in the FIXED downstairs preferred chart. All
neighborhoods and constants are constructed from the raw QPSH germ. -/
theorem exists_local_log_bound_of_pointBlowup
    {m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong (m + 1) ({x} : Set X) π)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) < ⨅ z ∈ π ⁻¹' ({x} : Set X),
      lelongNumber (n := m + 1) (fun t => u (π t)) z)
    {y : Y} (hy : π y = x) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∃ C : ℝ, ∀ z ∈ U,
      π z ∈ (chartAt (ComplexModel (m + 1)) x).source ∧
      (π z ≠ x → u (π z) ≤
        (((γ : ℝ) * Real.log ‖chartAt (ComplexModel (m + 1)) x (π z) -
          chartAt (ComplexModel (m + 1)) x x‖ + C : ℝ) : EReal)) := by
  obtain ⟨A, Φ, j, _hAs, hA0, hgeom⟩ := exists_point_fibre_flattening hπ hy
  have huπ := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.contMDiff hu
  let w : ComplexModel (m + 1) → EReal := fun z => u (π (Φ.point z))
  have hw : QuasiPlurisubharmonicAt w 0 := by
    have hchart := huπ (complexChartAt (n := m + 1) y) (Φ.Φ.invFun 0)
      (Φ.invFun_mem_target Φ.zero_mem_target)
    exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
      Φ.Φ.isOpen_target Φ.contDiffOn_invFun Φ.zero_mem_target hchart
  obtain ⟨R, hR, hwhole⟩ := FlattenedGlobalGenericLelongComparison.exists_radius_generic_le_local
    Φ (fun t => u (π t))
  obtain ⟨r, hr, _hrR, B, hB⟩ := RawQuasiPshDivisorialSliceBound.exists_slice_bound
    hw hR (hγ.trans_le (hwhole R hR le_rfl))
  have hAdiff := A.toFun_holomorphic.differentiableAt
    (A.isOpen_source.mem_nhds A.center_mem_source)
  obtain ⟨K, hK, hLip⟩ := hAdiff.hasFDerivAt.isBigO_sub.exists_pos
  have hbaseT : Tendsto (fun z => chartAt (ComplexModel (m + 1)) x (π z)) (𝓝 y)
      (𝓝 (chartAt (ComplexModel (m + 1)) x x)) := by
    have hπT : Tendsto π (𝓝 y) (𝓝 x) := by
      simpa only [hy] using hπ.contMDiff.continuous.tendsto y
    exact ((chartAt (ComplexModel (m + 1)) x).continuousAt
      (mem_chart_source _ _)).tendsto.comp hπT
  have hcoordT : Tendsto Φ.coord (𝓝 y) (𝓝 (0 : ComplexModel (m + 1))) := by
    simpa only [Φ.coord_x] using Φ.mdifferentiableAt_coord.continuousAt.tendsto
  have hnear : ∀ᶠ z in 𝓝 y,
      π z ∈ (chartAt (ComplexModel (m + 1)) x).source ∧
      (π z ≠ x → u (π z) ≤
        (((γ : ℝ) * Real.log ‖chartAt (ComplexModel (m + 1)) x (π z) -
          chartAt (ComplexModel (m + 1)) x x‖ + (B + (γ : ℝ) * Real.log K) : ℝ) : EReal)) := by
    have hsrc : ∀ᶠ z in 𝓝 y,
        z ∈ (chartAt (ComplexModel (m + 1)) y).source ∧
          chartAt (ComplexModel (m + 1)) y z ∈ Φ.Φ.source := by
      exact (show ∀ᶠ z in 𝓝 y, z ∈ (complexChartAt (n := m + 1) y).val.source from
        (complexChartAt (n := m + 1) y).val.open_source.mem_nhds
          (mem_complexChartAt_source y)).and
        (((complexChartAt (n := m + 1) y).val.continuousAt (mem_complexChartAt_source y)).eventually
          (Φ.Φ.isOpen_source.mem_nhds Φ.chart_mem_source))
    filter_upwards [hsrc, hcoordT.eventually (ball_mem_nhds 0 hr),
      hbaseT.eventually hLip.bound, Φ.eventually_point_coord] with z hz hzr hzLip hzInv
    have hgz := hgeom z hz.1 hz.2
    refine ⟨hgz.1.1, ?_⟩
    intro hzx
    have hnormal : Φ.coord z (Fin.last m) ≠ 0 := by
      intro hzero
      have hfibre := (Φ.mem_iff z hz.1 hz.2).mpr hzero
      exact hzx (mem_singleton_iff.mp hfibre)
    have hnorm : ‖Φ.coord z (Fin.last m)‖ ≤
        K * ‖chartAt (ComplexModel (m + 1)) x (π z) - chartAt (ComplexModel (m + 1)) x x‖ := by
      calc
        _ = ‖A.toFun (chartAt (ComplexModel (m + 1)) x (π z)) j‖ := congrArg norm hgz.2
        _ ≤ ‖A.toFun (chartAt (ComplexModel (m + 1)) x (π z))‖ := PiLp.norm_apply_le _ _
        _ ≤ _ := by simpa only [hA0, sub_zero] using hzLip
    have hbasepos : 0 < ‖chartAt (ComplexModel (m + 1)) x (π z) -
        chartAt (ComplexModel (m + 1)) x x‖ := by
      apply norm_pos_iff.mpr
      intro heq
      exact hzx ((chartAt (ComplexModel (m + 1)) x).injOn hgz.1.1
        (mem_chart_source _ _) (sub_eq_zero.mp heq))
    have hlog : Real.log ‖Φ.coord z (Fin.last m)‖ ≤
        Real.log K + Real.log ‖chartAt (ComplexModel (m + 1)) x (π z) -
          chartAt (ComplexModel (m + 1)) x x‖ := by
      rw [← Real.log_mul hK.ne' hbasepos.ne']
      exact Real.log_le_log (norm_pos_iff.mpr hnormal) hnorm
    have hbound := hB (Φ.coord z) hzr hnormal
    change u (π (Φ.point (Φ.coord z))) ≤ _ at hbound
    rw [hzInv] at hbound
    apply hbound.trans (EReal.coe_le_coe_iff.mpr ?_)
    calc
      _ ≤ (γ : ℝ) * (Real.log K + Real.log ‖chartAt (ComplexModel (m + 1)) x (π z) -
          chartAt (ComplexModel (m + 1)) x x‖) + B := by
        exact add_le_add (mul_le_mul_of_nonneg_left hlog γ.coe_nonneg) le_rfl
      _ = _ := by ring
  obtain ⟨U, hUbound, hU, hyU⟩ := eventually_nhds_iff.mp hnear
  exact ⟨U, hU, hyU, B + (γ : ℝ) * Real.log K, hUbound⟩

/-- Proper closedness and the actual compact fibre make the produced local
constants uniform in one genuine downstairs neighborhood. -/
theorem exists_whole_fibre_log_bound_of_pointBlowup
    {m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong (m + 1) ({x} : Set X) π)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) < ⨅ z ∈ π ⁻¹' ({x} : Set X),
      lelongNumber (n := m + 1) (fun t => u (π t)) z) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ C : ℝ, ∀ z ∈ W,
      z ∈ (chartAt (ComplexModel (m + 1)) x).source ∧
      (z ≠ x → u z ≤
        (((γ : ℝ) * Real.log ‖chartAt (ComplexModel (m + 1)) x z -
          chartAt (ComplexModel (m + 1)) x x‖ + C : ℝ) : EReal)) := by
  classical
  have hlocal (y : π ⁻¹' ({x} : Set X)) : ∃ U : Set Y, IsOpen U ∧ (y : Y) ∈ U ∧
      ∃ C : ℝ, ∀ z ∈ U,
        π z ∈ (chartAt (ComplexModel (m + 1)) x).source ∧
        (π z ≠ x → u (π z) ≤
          (((γ : ℝ) * Real.log ‖chartAt (ComplexModel (m + 1)) x (π z) -
            chartAt (ComplexModel (m + 1)) x x‖ + C : ℝ) : EReal)) :=
    exists_local_log_bound_of_pointBlowup hπ hu hγ (mem_singleton_iff.mp y.property)
  choose U hU hyU C hbound using hlocal
  obtain ⟨t, W, hW, hxW, _hpre, hcover⟩ :=
    ProperFiberFiniteNeighborhoodCover.exists_finite_fiber_cover_target_neighborhood
      (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ)
      (HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ) x U
      (fun y => ⟨hU y, hyU y⟩)
  refine ⟨W, hW, hxW, ∑ y ∈ t, |C y|, ?_⟩
  intro z hz
  obtain ⟨y, hyt, w, hwU, hwz⟩ := mem_iUnion₂.mp (hcover hz)
  have hb := hbound y w hwU
  rw [hwz] at hb
  refine ⟨hb.1, fun hne => (hb.2 hne).trans (EReal.coe_le_coe_iff.mpr ?_)⟩
  have hC : C y ≤ ∑ q ∈ t, |C q| :=
    (le_abs_self (C y)).trans (Finset.single_le_sum (fun q _ => abs_nonneg (C q)) hyt)
  exact add_le_add le_rfl hC

/-- In dimension zero every singleton is open, so the ORIGINAL blowup
predicate's nowhere-dense-centre requirement forbids point-blowup data. -/
theorem dimension_pos_of_pointBlowup
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong n ({x} : Set X) π) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  let e := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hsrc : e.val.source = ({x} : Set X) := by
    ext z
    constructor
    · intro hz
      exact mem_singleton_iff.mpr (e.val.injOn hz hx (Subsingleton.elim _ _))
    · intro hz
      simpa only [mem_singleton_iff.mp hz] using hx
  have hopen : IsOpen ({x} : Set X) := hsrc ▸ e.val.open_source
  have hxint : x ∈ interior ({x} : Set X) := by rw [hopen.interior_eq]; exact mem_singleton x
  rw [hπ.2.1] at hxint
  exact hxint

/-- The actual native point reader equals the whole actual point-fibre
infimum. Genuine theta-PSH supplies the pullback pole implication; all
positive-dimensional local geometry and every bound are produced internally. -/
theorem lelongNumber_eq_iInf_pointBlowup
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong n ({x} : Set X) π)
    {θ : SmoothRealForm n X 2} {u : X → EReal} (hu : ThetaPlurisubharmonic θ u) :
    lelongNumber (n := n) u x =
      ⨅ z ∈ π ⁻¹' ({x} : Set X), lelongNumber (n := n) (fun t => u (π t)) z := by
  have hn := dimension_pos_of_pointBlowup hπ
  cases n with
  | zero => omega
  | succ m =>
      apply le_antisymm
      · refine le_iInf fun z => le_iInf fun hz => ?_
        have hzx : π z = x := mem_singleton_iff.mp hz
        have hpull := LelongNumberComparison.lelongNumber_le_comp
          ((hπ.contMDiff z).mdifferentiableAt (by simp))
          (fun hpos => eq_bot_of_lelongNumber_pos (Nat.succ_pos m) hu hpos)
        simpa only [hzx] using hpull
      · apply ENNReal.le_of_forall_nnreal_lt
        intro γ hγ
        obtain ⟨W, hW, hxW, C, hbound⟩ :=
          exists_whole_fibre_log_bound_of_pointBlowup hπ hu.quasiPlurisubharmonic hγ
        unfold lelongNumber
        refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] x,
          u z ≤ (((γ : ℝ) * Real.log
            ‖(complexChartAt (n := m + 1) x).val z -
              (complexChartAt (n := m + 1) x).val x‖ + C : ℝ) : EReal)) =>
          (γ : ℝ≥0∞)) γ ⟨C, ?_⟩ le_rfl
        rw [eventually_nhdsWithin_iff]
        filter_upwards [hW.mem_nhds hxW] with z hz hne
        have hzx : z ≠ x := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
        exact (hbound z hz).2 hzx

/-- The actual exceptional point-ideal carrier is a closed connected smooth
hypersurface, including the fibre-point divisor in dimension one. -/
theorem point_exceptional_carrier_is_prime
    {m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong (m + 1) ({x} : Set X) π) :
    IsClosedConnectedSubmanifold (m + 1)
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).support m := by
  rw [BlowupExceptionalDivisor.support_exceptionalDivisor]
  have hmod := PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hπ
  refine ⟨isClosed_singleton.preimage hπ.contMDiff.continuous,
    (AnalyticModificationConnectedFibres.isConnected_fibre hmod x).1, ?_⟩
  intro y hy
  obtain ⟨_A, Φ, _j, _hAs, _hA0, _hgeom⟩ :=
    exists_point_fibre_flattening hπ (mem_singleton_iff.mp hy)
  refine ⟨by omega, hy, Φ.Φ, Φ.source_subset, Φ.map_center, ?_⟩
  intro z hz hzΦ
  rw [Φ.mem_iff z hz hzΦ]
  constructor
  · intro hzero i hi
    have hilast : i = Fin.last m :=
      Fin.ext (le_antisymm (Nat.lt_succ_iff.mp i.2) hi)
    simpa only [hilast] using hzero
  · intro hplane
    exact hplane (Fin.last m) le_rfl

end SGPT.Foundations.Analysis.Pending.PointBlowupLelong
