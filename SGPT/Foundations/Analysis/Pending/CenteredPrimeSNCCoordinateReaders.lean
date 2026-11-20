import SGPT.Foundations.Analysis.Pending.PointCenteredHolomorphicPrimeReaders
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance

set_option autoImplicit false

/-! # Whole centered prime readers in the same actual coordinate neighborhood

One genuine coordinate radius precedes every finite holomorphic family and
raw comparison weight. Analytic whole-piece equality and raw one-way infimum
comparison are kept distinct. Reference: Xia generic analytic readers;
supplementary coordinate adaptation of the proved centered-prime theorem.
-/

open Set Filter Metric
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.CenteredPrimeSNCCoordinateReaders

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus

noncomputable section


private theorem lelongNumber_comp_adapted_point_eq {m : ℕ} {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {y : Y}
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target)
    (v : Y → EReal) {z : ComplexModel (m + 1)} (hz : z ∈ Φ.target) :
    lelongNumber (n := m + 1)
      (fun w => v ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w))) z =
      lelongNumber (n := m + 1) v
        ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z)) := by
  let e := complexChartAt (n := m + 1) y
  have ht : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hz)
  have hcov := LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq
    Φ (Φ.mapsTo_invFun hz) (u := chartFunction v e)
  rw [Φ.right_inv z hz] at hcov
  have hchart := LelongChartReaderInvariance.lelongNumber_chartFunction_eq e
    (e.val.map_target ht) (u := v)
  rw [e.val.right_inv ht] at hchart
  exact hcov.trans hchart

/-- The actual geometry supplies one radius before all original finite
families and raw weights; only the analytic family gets whole-piece equality. -/
theorem exists_radius_whole_prime_coordinate_readers {n m : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel n) ∞ π)
    (x : X) (V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y)
    (hcenter : ∀ z ∈ V.carrier, π z = x) (y : Y) (hyV : y ∈ V.carrier)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := m + 1) y).val y) = 0)
    (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y,
      z ∈ V.carrier ↔ (Φ.toFun ((complexChartAt (n := m + 1) y).val z)) j = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      (∀ (s : ℕ) (G : Fin s → X → ℂ), (∀ i, HolomorphicAt n (G i) x) →
        ∀ c : ℝ, 0 < c →
          (⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
            (fun w => (c : EReal) * generatorLog G (π w)) z) =
            ⨅ z ∈ ball (0 : ComplexModel (m + 1)) r ∩ {z | z j = 0},
              lelongNumber (n := m + 1)
                (fun w => (c : EReal) * generatorLog G (π
                  ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w)))) z) ∧
      (∀ v : Y → EReal,
        (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) v z) ≤
          ⨅ z ∈ ball (0 : ComplexModel (m + 1)) r ∩ {z | z j = 0},
            lelongNumber (n := m + 1)
              (fun w => v ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w))) z) := by
  classical
  obtain ⟨O, hOsub, hO, hyO⟩ := _root_.mem_nhds_iff.mp hflat
  let e := complexChartAt (n := m + 1) y
  let T : ComplexModel (m + 1) → Y := fun z => e.val.symm (Φ.invFun z)
  have h0t : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val y := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hT0 : T 0 = y := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_complexChartAt_source y)]
  have hTc : ContinuousAt T 0 :=
    (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
      ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt)
  have ht : Tendsto T (𝓝 0) (𝓝 y) := by simpa only [hT0] using hTc.tendsto
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ Φ.target ∧ T z ∈ O :=
    (show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ Φ.target from
      Φ.isOpen_target.mem_nhds h0t).and (ht.eventually (hO.mem_nhds hyO))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  let A : Set (ComplexModel (m + 1)) := Φ.source ∩ Φ.toFun ⁻¹' ball 0 r
  have hA : IsOpen A :=
    Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_source isOpen_ball
  let W : Set Y := (e.val.source ∩ e.val ⁻¹' A) ∩ O
  have hW : IsOpen W := (e.val.continuousOn.isOpen_inter_preimage e.val.open_source hA).inter hO
  have hyball : Φ.toFun (e.val y) ∈ ball (0 : ComplexModel (m + 1)) r := by
    rw [h0]
    exact mem_ball_self hr
  have hyA : e.val y ∈ A := ⟨Φ.center_mem_source, hyball⟩
  have hyW : y ∈ W := ⟨⟨mem_complexChartAt_source y, hyA⟩, hyO⟩
  have hparameter (v : Y → EReal) :
      (⨅ z ∈ V.carrier ∩ W, lelongNumber (n := m + 1) v z) =
        ⨅ z ∈ ball (0 : ComplexModel (m + 1)) r ∩ {z | z j = 0},
          lelongNumber (n := m + 1) (fun w => v (T w)) z := by
    apply le_antisymm
    · refine le_iInf fun z => le_iInf fun hz => ?_
      obtain ⟨hzΦ, hzO⟩ := hball (ball_subset_ball hrR hz.1)
      have hzT : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hzΦ)
      have hzsource : T z ∈ e.val.source := e.val.map_target hzT
      have hchart : e.val (T z) = Φ.invFun z := e.val.right_inv hzT
      have hΦsource : e.val (T z) ∈ Φ.source := by
        rw [hchart]
        exact Φ.mapsTo_invFun hzΦ
      have hcoords : Φ.toFun (e.val (T z)) = z := by rw [hchart, Φ.right_inv z hzΦ]
      have hzV : T z ∈ V.carrier := (hOsub hzO).mpr (by rw [hcoords]; exact hz.2)
      have hzcoordsball : Φ.toFun (e.val (T z)) ∈ ball 0 r := by
        rw [hcoords]
        exact hz.1
      have hzA : e.val (T z) ∈ A := ⟨hΦsource, hzcoordsball⟩
      have hzW : T z ∈ W := ⟨⟨hzsource, hzA⟩, hzO⟩
      exact (iInf₂_le (f := fun w (_ : w ∈ V.carrier ∩ W) =>
        lelongNumber (n := m + 1) v w) (T z) ⟨hzV, hzW⟩).trans_eq
          (lelongNumber_comp_adapted_point_eq Φ hsrc v hzΦ).symm
    · refine le_iInf fun w => le_iInf fun hw => ?_
      let z : ComplexModel (m + 1) := Φ.toFun (e.val w)
      have hzball : z ∈ ball (0 : ComplexModel (m + 1)) r := hw.2.1.2.2
      have hzj : z j = 0 := (hOsub hw.2.2).mp hw.1
      have hzΦ : z ∈ Φ.target := Φ.mapsTo_toFun hw.2.1.2.1
      have hTz : T z = w := by
        dsimp only [T, z]
        rw [Φ.left_inv _ hw.2.1.2.1, e.val.left_inv hw.2.1.1]
      have hreader := lelongNumber_comp_adapted_point_eq Φ hsrc v hzΦ
      change lelongNumber (n := m + 1) (fun z => v (T z)) z =
        lelongNumber (n := m + 1) v (T z) at hreader
      rw [hTz] at hreader
      exact (iInf₂_le (f := fun z (_ : z ∈ ball (0 : ComplexModel (m + 1)) r ∩
        {z | z j = 0}) => lelongNumber (n := m + 1) (fun w => v (T w)) z)
          z ⟨hzball, hzj⟩).trans_eq hreader
  refine ⟨?_, ?_⟩
  · intro s G hG c hc
    exact (PointCenteredHolomorphicPrimeReaders.iInf_generatorLog_comp_eq_open_piece
      hπ x G hG V hcenter hc hW ⟨y, hyV, hyW⟩).trans
        (hparameter (fun z => (c : EReal) * generatorLog G (π z)))
  · intro v
    calc
      _ ≤ ⨅ z ∈ V.carrier ∩ W, lelongNumber (n := m + 1) v z :=
        le_iInf fun z => le_iInf fun hz => iInf₂_le z hz.1
      _ = _ := hparameter v

end
end SGPT.Foundations.Analysis.Pending.CenteredPrimeSNCCoordinateReaders
