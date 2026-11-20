import SGPT.Okounkov.FlagLelong
import SGPT.Okounkov.LocalThetaReader
import SGPT.Okounkov.CoordinateResidual

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Metric
open scoped Topology Manifold ContDiff ENNReal NNReal
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition

/-- The actual codimension-one flattened plane is the original last-coordinate
hyperplane, with no replacement divisor membership predicate. -/
theorem mem_codimension_one_plane_iff {m : ℕ} (z : ComplexModel (m + 1)) :
    z ∈ complexCoordinatePlane (m + 1) m ↔ z (Fin.last m) = 0 := by
  constructor
  · intro hz
    exact hz (Fin.last m) (by simp)
  · intro hz i hi
    have heq : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa only [heq] using hz

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The already-proved local residual in an actual GIVEN original flattening.
This exposes the same chosen coordinates needed by the actual divisor metric;
all residual data and original-reader zero are genuinely produced. -/
theorem exists_smooth_divisor_local_residual_of_flattening
    {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) (p : M) (_hp : p ∈ W)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) p).val p))
    (hΦe : Φ.source ⊆ (complexChartAt (n := m + 1) p).val.target)
    (hΦ0 : Φ.toFun ((complexChartAt (n := m + 1) p).val p) = 0)
    (hflat : ∀ {y : M}, y ∈ (complexChartAt (n := m + 1) p).val.source →
      (complexChartAt (n := m + 1) p).val y ∈ Φ.source →
      (y ∈ W ↔ Φ.toFun ((complexChartAt (n := m + 1) p).val y) ∈
        complexCoordinatePlane (m + 1) m)) :
    ∃ c : ℝ≥0,
      (c : ℝ≥0∞) = sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u ∧
      ∃ (ρ : ComplexModel (m + 1) → ℝ) (r C : ℝ)
        (q : ComplexModel (m + 1) → EReal),
        0 < r ∧ ball 0 r ⊆ Φ.target ∧
        (∀ z ∈ ball 0 r, ContDiffAt ℝ ∞ ρ (Φ.invFun z)) ∧
        (∀ z ∈ ball 0 r, (complexChartAt (n := m + 1) p).val.symm (Φ.invFun z) ∈ W ↔
          z (Fin.last m) = 0) ∧
        PlurisubharmonicOn q (ball 0 r) ∧ (∀ z ∈ ball 0 r, q z ≤ (C : EReal)) ∧
        (∀ z ∈ ball 0 r,
          chartFunction u (complexChartAt (n := m + 1) p) (Φ.invFun z) +
            (ρ (Φ.invFun z) : EReal) =
            ((c : ℝ) : EReal) * logNormSq (z (Fin.last m)) + q z) ∧
        (squaredLogLelongNumber (n := m + 1) u p =
          sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u →
            lelongNumber (n := m + 1) q 0 = 0) := by
  let e := complexChartAt (n := m + 1) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  let c : ℝ≥0 :=
    (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  have hc : (c : ℝ≥0∞) =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u :=
    ENNReal.coe_toNNReal (sourceGeneric_subtype_ne_top hW hu.quasiPshPotential)
  obtain ⟨D, ρ, hD, hpD, hDT, hρD, hvD, hνD⟩ :=
    exists_flattened_theta_psh_reader hu e p hpe Φ
  let v : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction u e (Φ.invFun z) + (ρ (Φ.invFun z) : EReal)
  have h0D : (0 : ComplexModel (m + 1)) ∈ D := hΦ0 ▸ hpD
  have hWiff (z : ComplexModel (m + 1)) (hz : z ∈ D) :
      e.val.symm (Φ.invFun z) ∈ W ↔ z (Fin.last m) = 0 := by
    have hzT : z ∈ Φ.target := hDT hz
    have hiS : Φ.invFun z ∈ Φ.source := Φ.mapsTo_invFun hzT
    have hiT : Φ.invFun z ∈ e.val.target := hΦe hiS
    have hxS : e.val.symm (Φ.invFun z) ∈ e.val.source := e.val.map_target hiT
    have hi : e.val (e.val.symm (Φ.invFun z)) ∈ Φ.source := by
      rwa [e.val.right_inv hiT]
    have he := hflat hxS hi
    rwa [e.val.right_inv hiT, Φ.right_inv z hzT, mem_codimension_one_plane_iff] at he
  have hthreshold (z : ComplexModel (m + 1)) (hz : z ∈ D)
      (hz0 : z (Fin.last m) = 0) :
      2 * (c : ℝ≥0∞) ≤ lelongNumber (n := m + 1) v z := by
    have hxW : e.val.symm (Φ.invFun z) ∈ W := (hWiff z hz).mpr hz0
    rw [hνD z hz, lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m), hc]
    gcongr
    exact iInf_le _ (⟨e.val.symm (Φ.invFun z), hxW⟩ : W)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds h0D)
  let R : ℝ := ε / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have h2R : 2 * R < ε := by dsimp [R]; linarith
  have hclosed : closedBall (0 : ComplexModel (m + 1)) (2 * R) ⊆ D :=
    (closedBall_subset_ball h2R).trans hball
  have hRD : ball (0 : ComplexModel (m + 1)) R ⊆ D :=
    ((ball_subset_ball (by linarith : R ≤ 2 * R)).trans ball_subset_closedBall).trans hclosed
  obtain ⟨K, _hK, hbound⟩ :=
    hvD.exists_nonnegative_compact_upper_bound (isCompact_closedBall 0 (2 * R)) hclosed
  obtain ⟨r, hr, hrR, C, q, hq, hqb, heq⟩ :=
    exists_coordinate_divisorial_residual hvD hR hclosed hbound (Fin.last m) c
      (fun z hz hz0 => hthreshold z (hRD hz) hz0)
  have hrD : ball (0 : ComplexModel (m + 1)) r ⊆ D :=
    (ball_subset_ball hrR).trans hRD
  refine ⟨c, hc, ρ, r, C, q, hr,
    hrD.trans hDT, (fun z hz => hρD z (hrD hz)),
    (fun z hz => hWiff z (hrD hz)), hq, hqb, heq, ?_⟩
  intro hmin
  have hν0 : lelongNumber (n := m + 1) v 0 = 2 * (c : ℝ≥0∞) := by
    have hi0 : Φ.invFun (0 : ComplexModel (m + 1)) = e.val p := by
      rw [← hΦ0, Φ.left_inv _ Φ.center_mem_source]
    calc
      _ = lelongNumber (n := m + 1) u (e.val.symm (Φ.invFun 0)) := hνD 0 h0D
      _ = lelongNumber (n := m + 1) u p := by rw [hi0, e.val.left_inv hpe]
      _ = 2 * squaredLogLelongNumber (n := m + 1) u p :=
        lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m) u p
      _ = _ := by rw [hmin, ← hc]
  let B : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
  let xB : B := ⟨0, mem_ball_self hr⟩
  exact lelongNumber_coordinate_residual_eq_zero
    (Ω := B) (u := v) (q := q) hq (Fin.last m) c (fun z hz => heq z hz) xB
    rfl hν0

/-- Original smooth-divisor geometry and original theta-PSH membership produce
every actual local residual, its genuine radius and bound, its all-point
identity, and actual point zero whenever the source coefficient is attained.
None of these objects or properties is supplied as a certificate. -/
theorem exists_smooth_divisor_local_residual
    {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) (p : M) (hp : p ∈ W) :
    let e := complexChartAt (n := m + 1) p
    ∃ c : ℝ≥0,
      (c : ℝ≥0∞) = sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u ∧
      ∃ (Φ : LocalHolomorphicEquivAt (n := m + 1) (e.val p)),
        Φ.source ⊆ e.val.target ∧ Φ.toFun (e.val p) = 0 ∧
        ∃ (ρ : ComplexModel (m + 1) → ℝ) (r C : ℝ)
          (q : ComplexModel (m + 1) → EReal),
          0 < r ∧ ball 0 r ⊆ Φ.target ∧
          (∀ z ∈ ball 0 r, ContDiffAt ℝ ∞ ρ (Φ.invFun z)) ∧
          (∀ z ∈ ball 0 r, e.val.symm (Φ.invFun z) ∈ W ↔ z (Fin.last m) = 0) ∧
          PlurisubharmonicOn q (ball 0 r) ∧ (∀ z ∈ ball 0 r, q z ≤ (C : EReal)) ∧
          (∀ z ∈ ball 0 r,
            chartFunction u e (Φ.invFun z) + (ρ (Φ.invFun z) : EReal) =
              ((c : ℝ) : EReal) * logNormSq (z (Fin.last m)) + q z) ∧
          (squaredLogLelongNumber (n := m + 1) u p =
            sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u →
              lelongNumber (n := m + 1) q 0 = 0) := by
  let e := complexChartAt (n := m + 1) p
  obtain ⟨_hle, _hp, Φ, hΦe, hΦ0, hflat⟩ := hW.2.2 p hp
  obtain ⟨c, hc, ρ, r, C, q, hdata⟩ :=
    exists_smooth_divisor_local_residual_of_flattening hu hW p hp Φ hΦe hΦ0 hflat
  exact ⟨c, hc, Φ, hΦe, hΦ0, ρ, r, C, q, hdata⟩

end SGPT.Okounkov
