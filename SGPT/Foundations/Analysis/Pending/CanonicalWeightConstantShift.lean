import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim
import SGPT.Foundations.Analysis.Pending.NonPluripolarMixedCutoffs

set_option autoImplicit false

/-!
# Actual canonical weighted mixed integrals under finite constant shifts

The normalization input in Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2.
Canonical differences have a finite-shift correction off their common poles;
genuine pole nullity makes this an actual integral identity. Produced same-type
mixed mass equality cancels the correction in measure differences.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.CanonicalWeightConstantShift

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open RelativeEnergyIntegrability GlobalMeasureInvariance GlobalDiagonalScaling
open NonPluripolarMixedCutoffs

noncomputable section

private theorem canonicalDiff_sub_consts_of_finite {a b : EReal}
    (hat : a ≠ ⊤) (hbt : b ≠ ⊤) (hab : a ≠ ⊥) (hbb : b ≠ ⊥) (c d : ℝ) :
    canonicalERealDiffToReal (a - (c : EReal)) (b - (d : EReal)) =
      canonicalERealDiffToReal a b + d - c := by
  rw [← EReal.coe_toReal hat hab, ← EReal.coe_toReal hbt hbb]
  simp only [← EReal.coe_sub, canonicalERealDiffToReal_coe_coe]
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The canonical constant-shift formula is an actual almost-everywhere
identity, with the genuine common pole set proved null for the actual measure. -/
theorem canonicalDiff_sub_consts_ae_globalMixedMeasure
    {alpha beta : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) (c d : ℝ) :
    (fun x => canonicalERealDiffToReal (u x - (c : EReal)) (v x - (d : EReal)))
      =ᵐ[globalMixedMeasure eta s hs]
    (fun x => canonicalERealDiffToReal (u x) (v x) + (d - c)) := by
  have hnull := globalMixedMeasure_pole_null_of_nondegenerate hs hu
  have hae : ∀ᵐ x ∂globalMixedMeasure eta s hs, u x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not] using hnull
  filter_upwards [hae] with x hux
  have hvx : v x ≠ ⊥ := fun h => hux ((sameSingularityTypeOn_eq_bot_iff htype
    (mem_univ x)).mpr h)
  have h := canonicalDiff_sub_consts_of_finite (hu.1.quasiPlurisubharmonic.ne_top x)
    (hv.1.quasiPlurisubharmonic.ne_top x) hux hvx c d
  convert h using 1; ring

/-- The actual signed-weight integral changes by the finite constant times
the actual total mass, including singular weights and arbitrary mixed slots. -/
theorem integral_canonicalDiff_sub_consts_globalMixedMeasure
    (omega : KahlerBackground n M) {alpha beta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : IsThetaPshPotential alpha u)
    (hv : IsThetaPshPotential beta v) (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) (c d : ℝ) :
    (∫ x, canonicalERealDiffToReal (u x - (c : EReal)) (v x - (d : EReal))
      ∂globalMixedMeasure eta s hs) =
    (∫ x, canonicalERealDiffToReal (u x) (v x) ∂globalMixedMeasure eta s hs) +
      (d - c) * (globalMixedMeasure eta s hs).real univ := by
  have : IsFiniteMeasure (globalMixedMeasure eta s hs) := globalMixedMeasure_isFiniteMeasure omega hs
  rw [integral_congr_ae (canonicalDiff_sub_consts_ae_globalMixedMeasure hu hv htype hs c d)]
  rw [integral_add (integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype hs)
    (integrable_const (d - c)), integral_const, smul_eq_mul]
  ring

/-- Produced same-type total mixed mass equality cancels the actual signed
weight's constant correction in a difference of two actual mixed integrals. -/
theorem integral_sub_canonicalDiff_sub_consts_of_sameTypeTuples
    (omega : KahlerBackground n M) {alpha beta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : IsThetaPshPotential alpha u)
    (hv : IsThetaPshPotential beta v) (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s t : Fin n → M → EReal}
    (hs : ∀ i, IsThetaPshPotential (eta i).val (s i))
    (ht : ∀ i, IsThetaPshPotential (eta i).val (t i))
    (hst : ∀ i, SameSingularityTypeOn (s i) (t i) univ) (c d : ℝ) :
    (∫ x, canonicalERealDiffToReal (u x - (c : EReal)) (v x - (d : EReal))
      ∂globalMixedMeasure eta s (fun i => (hs i).1)) -
    (∫ x, canonicalERealDiffToReal (u x - (c : EReal)) (v x - (d : EReal))
      ∂globalMixedMeasure eta t (fun i => (ht i).1)) =
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure eta s (fun i => (hs i).1)) -
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure eta t (fun i => (ht i).1)) := by
  rw [integral_canonicalDiff_sub_consts_globalMixedMeasure omega hu hv htype
    (fun i => (hs i).1) c d,
    integral_canonicalDiff_sub_consts_globalMixedMeasure omega hu hv htype
      (fun i => (ht i).1) c d]
  have hmass : (globalMixedMeasure eta s (fun i => (hs i).1)).real univ =
      (globalMixedMeasure eta t (fun i => (ht i).1)).real univ :=
    congrArg ENNReal.toReal
      (FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega hs ht hst)
  rw [hmass]
  ring

/-- Independent finite translations of the two binary potentials and the
distinguished potential leave the actual binary mixed measure unchanged. -/
theorem binaryMixedMeasure_sub_consts
    (theta : ClosedRealOneOneForm n M) {a b r : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hr : ThetaPlurisubharmonic theta.val r) (sigma : Fin n → Bool) (i0 : Fin n)
    (c d e : ℝ) :
    binaryMixedMeasure theta (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const ha c)
      (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hb d)
      (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hr e) sigma i0 =
    binaryMixedMeasure theta ha hb hr sigma i0 := by
  let cs : Fin n → ℝ := fun i => if i = i0 then e else if sigma i then c else d
  have heq : Function.update
      (binaryPotentialTuple sigma (fun x => a x - (c : EReal)) (fun x => b x - (d : EReal)))
      i0 (fun x => r x - (e : EReal)) =
      fun i x => Function.update (binaryPotentialTuple sigma a b) i0 r i x - (cs i : EReal) := by
    funext i x
    by_cases hi : i = i0
    · subst hi
      simp [cs]
    · simp only [Function.update_of_ne hi, binaryPotentialTuple, cs, if_neg hi]
      split <;> rfl
  exact (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple heq _ _).trans
    (globalMixedMeasure_sub_const (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hr sigma i0) cs)

end

end SGPT.Foundations.Analysis.Pending.CanonicalWeightConstantShift
