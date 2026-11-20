import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncation

set_option autoImplicit false

/-!
# Actual endpoint bounds below singular references

Xia SGPT PDF0121--0122, the energy bounds used in Proposition 3.1.17.
Actual canonical finite-type energy terms are integrable and nonpositive
below the reference. Dropping all but the last actual diagonal term gives
the quantitative bound for singular max-truncation gaps.
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyEndpointBounds

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeEnergyIntegrability
  SingularModelEnergyCocycle SingularModelEnergyLayout BoundedMongeAmpereEnergy
  GlobalNonPluripolar DiagonalMass

noncomputable section

/-- Canonical ordered same-type differences are nonpositive, including their common poles. -/
theorem canonicalDiff_nonpos_of_le_of_sameType {X : Type*} {u v : X → EReal}
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤)
    (htype : SameSingularityTypeOn u v univ) (hule : u ≤ v) (x : X) :
    canonicalERealDiffToReal (u x) (v x) ≤ 0 := by
  by_cases hux : u x = ⊥
  · have hvx : v x = ⊥ := (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mp hux
    simp [hux, hvx]
  · rw [canonicalDiff_eq_sub_toReal (hu x) (hv x)
      (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))]
    exact sub_nonpos.mpr (EReal.toReal_le_toReal (hule x) hux (hv x))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual diagonal canonical endpoint integral bounds singular finite-type energy below. -/
theorem integral_le_energy (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ w : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hw : IsThetaPshPotential θ.val w) (hwφ : SameSingularityTypeOn w φ univ) :
    (∫ x, canonicalERealDiffToReal (w x) (φ x) ∂diagonalPotentialMeasure θ w hw) ≤
      relativeEnergyOfMinimalType θ φ w hφ hw := by
  have h := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hw hφ
    hwφ (SameSingularityTypeOn.refl φ univ)).1
  rwa [relativeEnergyOfMinimalType_self, sub_zero] at h

/-- Dropping genuinely integrable nonpositive mixed terms bounds the actual energy sum
by its last diagonal integral, even when the reference is singular. -/
theorem energy_mul_le_integral (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ w : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hw : IsThetaPshPotential θ.val w)
    (htype : SameSingularityTypeOn w φ univ) (hwφ : w ≤ φ) :
    ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ φ w hφ hw ≤
      ∫ x, canonicalERealDiffToReal (w x) (φ x) ∂diagonalPotentialMeasure θ w hw := by
  rw [relativeEnergyOfMinimalType_mul_canonical θ hφ hw, Finset.sum_range_succ]
  have hnp : ∀ j ∈ Finset.range n,
      (∫ x, canonicalERealDiffToReal (w x) (φ x)
        ∂layMeasure θ n j w φ (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1)) ≤ 0 := by
    intro j _
    have hint := integrable_canonicalDiff_globalMixedMeasure omega hw.1 hφ.1 htype
      (lay_psh (k := n) (j := j) hw.1 hφ.1 (fun _ => hφ.1))
    have hz : Integrable (fun _x : M => (0 : ℝ))
        (layMeasure θ n j w φ (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1)) :=
      integrable_zero M ℝ _
    have hle := integral_mono_ae hint hz
      (Eventually.of_forall fun x => canonicalDiff_nonpos_of_le_of_sameType
        hw.1.quasiPlurisubharmonic.ne_top hφ.1.quasiPlurisubharmonic.ne_top htype hwφ x)
    change (∫ x, canonicalERealDiffToReal (w x) (φ x)
      ∂layMeasure θ n j w φ (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1)) ≤
        ∫ _x : M, (0 : ℝ) ∂layMeasure θ n j w φ (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1) at hle
    rwa [integral_zero] at hle
  have hlast : layMeasure θ n n w φ (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1) =
      diagonalPotentialMeasure θ w hw :=
    GlobalDiagonalScaling.globalMixedMeasure_congr rfl
      (by funext i; simp [lay, i.isLt]) _ _
  rw [hlast]
  linarith [Finset.sum_nonpos hnp]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyEndpointBounds
