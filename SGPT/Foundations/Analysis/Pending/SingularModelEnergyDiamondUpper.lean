import SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondPaths
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyEndpointBounds

set_option autoImplicit false

/-!
# Actual upper diamond-path estimate for singular same-type potentials

Xia SGPT PDF0137, Corollary 3.1.7. The actual finite energy endpoint
comparison and actual plurifine max locality estimate the upper path's
energy increment by the canonical positive gap on the affine path.
The final diamond proof uses telescoping partitions instead of derivative
formulas; no path differentiability or target diamond premise is assumed.
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondUpper

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeEnergyIntegrability
  SingularModelEnergyDiamondPaths SingularModelEnergyCocycle
  SingularModelEnergyEndpointBounds GlobalNonPluripolar ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The canonical positive gap integrated against the actual affine-path
measure whenever the path's genuine PSH contract is produced. -/
def gap (θ : ClosedRealOneOneForm n M) (u v : M → EReal) (t : ℝ) : ℝ :=
  ∫ x, max (canonicalERealDiffToReal (v x) (u x)) 0
    ∂RelativeEnergyDiamond.measureOf θ (path u v t)

/-- The actual upper path energy increment dominates the actual canonical
gap integral on the affine path, with the common poles retained. -/
theorem sub_mul_gap_le_energyOf_upperPath (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : RelativeEInfinity θ φ u)
    (hv : RelativeEInfinity θ φ v) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (t - s) * gap θ u v t ≤
      RelativeEnergyDiamond.energyOf θ φ hφ (upperPath u v t) -
        RelativeEnergyDiamond.energyOf θ φ hφ (upperPath u v s) := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.trans ht1⟩
  have hAt := relativeEInfinity_upperPath hu hv htI
  have hAs := relativeEInfinity_upperPath hu hv hsI
  have hf := relativeEInfinity_path hu hv htI
  rw [RelativeEnergyDiamond.energyOf_eq hAt.1, RelativeEnergyDiamond.energyOf_eq hAs.1]
  refine le_trans ?_ (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ
    hAt.1 hAs.1 hAt.2 hAs.2).1
  let h := fun x => max (canonicalERealDiffToReal (v x) (u x)) 0
  have hpt : ∀ x, canonicalERealDiffToReal (upperPath u v t x) (upperPath u v s x) =
      (t - s) * h x := canonicalDiff_upperPath hu hv hsI htI
  simp_rw [hpt]
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sub_nonneg.mpr hst)
  let S := {x | u x < v x}
  have hzero : ∀ x, x ∉ S → h x = 0 := by
    intro x hx
    change ¬ u x < v x at hx
    have hpole := sameSingularityTypeOn_eq_bot_iff (hv.2.trans hu.2.symm) (mem_univ x)
    have hd : canonicalERealDiffToReal (v x) (u x) ≤ 0 := by
      by_cases hvb : v x = ⊥
      · have hub : u x = ⊥ := hpole.mp hvb
        simp [hvb, hub]
      · rw [canonicalDiff_eq_sub_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x)
          (hu.1.1.quasiPlurisubharmonic.ne_top x) hpole]
        exact sub_nonpos.mpr (EReal.toReal_le_toReal (not_lt.mp hx) hvb
          (hu.1.1.quasiPlurisubharmonic.ne_top x))
    exact max_eq_right hd
  have hmax : ∀ _i : Fin n, ThetaPlurisubharmonic θ.val
      (fun x => max (path u v t x) (u x)) := fun _ =>
    (IsThetaPshPotential.max hf.1 hu.1).1
  have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq (θ := fun _ => θ)
    (u := fun _ => path u v t) (w := fun _ => u) (fun _ => hf.1.1) (fun _ => hu.1.1) hmax
  have hST : S ⊆ {x | ∀ _i : Fin n, u x < path u v t x} := by
    intro x hx _
    change u x < v x at hx
    have hvb : v x ≠ ⊥ := ne_bot_of_gt hx
    have hub : u x ≠ ⊥ := fun hb =>
      hvb ((sameSingularityTypeOn_eq_bot_iff (hu.2.trans hv.2.symm) (mem_univ x)).mp hb)
    have hux : (u x).toReal < (v x).toReal := by
      rwa [← EReal.coe_toReal (hu.1.1.quasiPlurisubharmonic.ne_top x) hub,
        ← EReal.coe_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x) hvb,
        EReal.coe_lt_coe_iff] at hx
    simp only [path, convexComb]
    rw [← EReal.coe_toReal (hu.1.1.quasiPlurisubharmonic.ne_top x) hub,
      ← EReal.coe_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x) hvb,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    nlinarith
  have hA : globalMixedMeasure (fun _ : Fin n => θ) (fun _ => upperPath u v t)
      (fun _ => hAt.1.1) =
      globalMixedMeasure (fun _ : Fin n => θ) (fun _ x => max (path u v t x) (u x)) hmax :=
    GlobalDiagonalScaling.globalMixedMeasure_congr rfl
      (by funext _ x; exact max_comm _ _) _ _
  have hres : (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => upperPath u v t)
      (fun _ => hAt.1.1)).restrict S =
      (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => path u v t)
        (fun _ => hf.1.1)).restrict S := by
    rw [← Measure.restrict_restrict_of_subset hST, hA, hloc,
      Measure.restrict_restrict_of_subset hST]
  rw [gap, RelativeEnergyDiamond.measureOf_eq hf.1.1,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← hres,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondUpper
