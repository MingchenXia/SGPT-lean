import SGPT.Foundations.Analysis.Pending.XiaoYauTestVolume
import SGPT.Foundations.Analysis.Pending.XiaoGlobalTestDensity

set_option autoImplicit false

/-!
# The actual Yau test-form producer together with Xiao's integral estimate

The original mixed mass survives the smooth correction by the existing slot
class-invariance theorem. The Yau solution and the compact-manifold estimate
are combined here, with the smooth correction retained inside the test integral.
No Gauduchon cancellation or Lamari criterion is assumed.
-/

open MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.XiaoYauTestEstimate

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms IntegrationCurrent TopDegreeDensity MixedMassClassInvariance
  ManifoldTubePositivity

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The genuine total mixed measure identifies slot integrals in either background. -/
theorem slotIntegral_eq_of_background (w w' : KahlerBackground (m + 1) X)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X)
    (hθ : ∀ i, (θ i).val.IsSemipositive) :
    NefMixedMass.slotIntegral w θ = NefMixedMass.slotIntegral w' θ := by
  have hpsh : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0) :=
    fun i => (LocalPotentials.thetaPlurisubharmonic_zero_iff (θ i)).mpr (hθ i)
  exact (globalMixedMeasure_real_univ_eq_integral w θ hpsh).symm.trans
    (globalMixedMeasure_real_univ_eq_integral w' θ hpsh)

/-- Correcting every repeated slot by the actual `ddᶜu` preserves the one-slot mixed mass. -/
theorem slotIntegral_cons_add_ddc_const (w : KahlerBackground (m + 1) X)
    (A B : ClosedRealOneOneForm (m + 1) X) (u : X → ℝ) (hu : ChartSmooth (n := m + 1) u) :
    NefMixedMass.slotIntegral w (Fin.cons B (fun _ : Fin m => A + ddcClosedForm u hu)) =
      NefMixedMass.slotIntegral w (Fin.cons B (fun _ : Fin m => A)) := by
  let pots : Fin (m + 1) → X → ℝ := Fin.cons (fun _ => 0) (fun _ => u)
  have hpots : ∀ i, ChartSmooth (n := m + 1) (pots i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact fun _ => contDiffOn_const
    · exact hu
  have hclass := NefMixedMass.slotIntegral_add_ddc w (Fin.cons B (fun _ : Fin m => A))
    pots hpots
  have hfamily : (fun i => (Fin.cons B (fun _ : Fin m => A) :
      Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) i + ddcClosedForm (pots i) (hpots i)) =
      Fin.cons B (fun _ : Fin m => A + ddcClosedForm u hu) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i
    · simp only [pots, Fin.cons_zero, NefCoreKahlerCurrent.ddcClosedForm_zero, add_zero]
    · simp only [pots, Fin.cons_succ]
  rw [hfamily] at hclass
  exact hclass

/-- The produced Yau form satisfies Xiao's estimate with the original actual mixed mass. -/
theorem exists_kahler_correction_and_test_estimate [ConnectedSpace X]
    (A B : KahlerBackground (m + 1) X) (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m)
    (hv : ∀ x, 0 < topRatio A.form.val (wedgeTwo G B.form.val) x)
    (hnorm : ∫ x, topRatio A.form.val (wedgeTwo G B.form.val) x ∂(kahlerVolume A) = 1)
    (hM : 0 < NefMixedMass.slotIntegral A (Fin.cons B.form (fun _ : Fin m => A.form))) :
    ∃ (u : X → ℝ) (hu : ChartSmooth (n := m + 1) u),
      (A.form + ddcClosedForm u hu).val.IsKahler ∧
      (∀ e z, z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
          (kahlerVolume A).real Set.univ *
            topDensity (coordinateWedge (G.coeff e z) (B.form.val.coeff e z))) ∧
      (kahlerVolume A).real Set.univ /
          (4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
            (Fin.cons B.form (fun _ : Fin m => A.form))) ≤
        ∫ x, topRatio A.form.val (wedgeTwo G (A.form + ddcClosedForm u hu).val) x
          ∂(kahlerVolume A) := by
  obtain ⟨u, hu, hK, hMA⟩ := XiaoYauTestVolume.exists_kahler_mongeAmpere_eq_topForm
    A (wedgeTwo G B.form.val) hv hnorm
  have hc := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos A
  have hmass := slotIntegral_cons_add_ddc_const A A.form B.form u hu
  have hM' : 0 < NefMixedMass.slotIntegral A
      (Fin.cons B.form (fun _ : Fin m => A.form + ddcClosedForm u hu)) := by
    rw [hmass]
    exact hM
  have hMA' : ∀ e z, z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
        (kahlerVolume A).real Set.univ *
          topDensity (coordinateWedge (G.coeff e z) (B.form.val.coeff e z)) := by
    intro e z hz
    simpa only [wedgeTwo_coeff] using hMA e z hz
  have hest := XiaoGlobalTestDensity.integral_testWedge_ge A
    (A.form + ddcClosedForm u hu) B.form hK B.isKahler G hG hv hnorm hc hM' hMA'
  rw [hmass] at hest
  exact ⟨u, hu, hK, hMA', hest⟩

end SGPT.Foundations.Analysis.Pending.XiaoYauTestEstimate
