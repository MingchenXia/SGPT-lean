import SGPT.Okounkov.SourceTestCurveAllDimensions
import SGPT.NAPotential.DHIntrinsicFlag
import SGPT.NAPotential.DHIntrinsic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Genuine zero-dimensional source flag Duistermaat--Heckman measure

Source: revised SGPT 69360cfd, def:DHm and thm:DHindep.
The literal flag measure uses the actual all-dimension source body family,
its original concave transform, actual Euclidean Lebesgue measure and the
original factorial. The zero branch computes that genuine pushforward.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential.DHSource

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n F.carrier)}

/-- Literal original def:DHm, retaining the actual source family and its
actual original concave-transform Lebesgue pushforward, in every dimension. -/
def naDuistermaatHeckman
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) : Measure ℝ :=
  (n.factorial : ENNReal) •
    (SourceTestCurveAllDimensions.okounkovTestCurve F hbig Γ.val).duistermaatHeckman

/-- Actual source flag measure finiteness is produced in every dimension. -/
instance naDuistermaatHeckman_finite
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) : IsFiniteMeasure (naDuistermaatHeckman F hbig Γ) where
  measure_univ_lt_top := by
    rw [naDuistermaatHeckman, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (measure_lt_top _ _)

/-- Exact original source slice I-volume on the original integration
interval; the auxiliary zero branch is only outside that interval. -/
def naSliceVolume (Γ : SourcePositiveIModelTestCurve θ) (τ : ℝ) : ℝ :=
  if hτ : τ < Γ.val.max then
    (iVolume (atlasClosedFormToNative θ)
      (LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative θ))
      (Γ.val.potential ⟨τ, hτ⟩) (Γ.val.native_thetaPSH ⟨τ, hτ⟩)).toReal
  else 0

namespace Zero

/-- Every actual zero-dimensional nonempty body has its actual whole carrier. -/
theorem carrier_eq_univ (Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))) :
    (Δ : Set (EuclideanSpace ℝ (Fin 0))) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨y, hy⟩ := Δ.nonempty
  simpa only [Subsingleton.elim x y] using hy

/-- The source uses canonical Euclidean zero-dimensional Lebesgue measure,
whose literal restriction to the actual source body is the unit Dirac. -/
theorem restrictedVolume_eq_dirac (Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))) :
    volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin 0))) = Measure.dirac 0 := by
  rw [carrier_eq_univ, Measure.restrict_univ]
  exact volume_euclideanSpace_eq_dirac (Fin 0)

/-- Actual original zero-dimensional body volume, before any real projection. -/
theorem volume_eq_one (Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))) :
    volume (Δ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  rw [carrier_eq_univ, volume_euclideanSpace_eq_dirac,
    Measure.dirac_apply_of_mem (mem_univ (0 : EuclideanSpace ℝ (Fin 0)))]

/-- The original supremum defining the genuine concave transform is the
original real cutoff, because every actual sub-cutoff body contains the point. -/
theorem transform_eq_max {Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))}
    (K : TestCurve Δ) (x : Δ) : K.transform x = (K.max : EReal) := by
  apply (K.transform_eq_max_iff x).mpr
  rw [K.mem_endpoint]
  intro τ
  change (x : EuclideanSpace ℝ (Fin 0)) ∈ (K.body τ : Set (EuclideanSpace ℝ (Fin 0)))
  rw [carrier_eq_univ]
  exact mem_univ _

/-- Exact actual finite real representative of the original transform. -/
theorem realLegendre_eq_max {Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))}
    (K : TestCurve Δ) (x : EuclideanSpace ℝ (Fin 0)) : K.realLegendre x = K.max := by
  have hx : x ∈ Δ := by
    change x ∈ (Δ : Set (EuclideanSpace ℝ (Fin 0)))
    rw [carrier_eq_univ]
    exact mem_univ _
  rw [TestCurve.realLegendre, TestFunction.valueAt, dif_pos hx]
  change (K.transform ⟨x, hx⟩).toReal = K.max
  rw [transform_eq_max, EReal.toReal_coe]

/-- Computation of the actual original flag/transform/body pushforward.
It is not inferred from an intrinsic measure or a measure equality input. -/
theorem duistermaatHeckman_eq_dirac {Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))}
    (K : TestCurve Δ) : K.duistermaatHeckman = Measure.dirac K.max := by
  rw [TestCurve.duistermaatHeckman, restrictedVolume_eq_dirac,
    Measure.map_dirac' K.measurable_realLegendre, realLegendre_eq_max]

variable (F : OriginalFlagGeometry.{u} 0) [MeasurableSpace F.carrier]
  [BorelSpace F.carrier] {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 F.carrier)}

/-- The actual source flag DH measure is Dirac at the unchanged original cutoff. -/
theorem naDuistermaatHeckman_eq_dirac
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman F hbig Γ = Measure.dirac Γ.val.max := by
  rw [naDuistermaatHeckman, Nat.factorial_zero, Nat.cast_one, one_smul,
    duistermaatHeckman_eq_dirac, SourceTestCurveAllDimensions.okounkovTestCurve_max]

/-- The exact original NA volume is the actual original limit mass, hence one. -/
theorem sourceNAVolume_eq_one (Γ : SourcePositiveIModelTestCurve θ) :
    sourceNAVolume (sourcePositiveTestCurveToNA Γ) = 1 := by
  rw [sourceNAVolume_positiveTestCurve F.omega Γ,
    SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero]

/-- The original slice I-volume, on every original parameter, is one. -/
theorem naSliceVolume_eq_one (Γ : SourcePositiveIModelTestCurve θ) {τ : ℝ}
    (hτ : τ < Γ.val.max) : naSliceVolume F Γ τ = 1 := by
  rw [naSliceVolume, dif_pos hτ,
    ← sourceIVolume_eq_native θ (Γ.val.potential ⟨τ, hτ⟩) (Γ.val.thetaPSH ⟨τ, hτ⟩)
      (LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative θ)),
    SGPT.Hodge.BDivChain.sourceIVolume_eq_one_of_dim_zero, ENNReal.toReal_one]

/-- The already constructed intrinsic measure of the same original curve
has the same computed Dirac value, by actual slice-mass tails. -/
theorem naIntrinsicDuistermaatHeckman_eq_dirac (ω : KahlerBackground 0 F.carrier)
    (Γ : SourcePositiveIModelTestCurve θ) :
    DH.naIntrinsicDuistermaatHeckman ω Γ = Measure.dirac Γ.val.max := by
  apply DH.measure_eq_of_Ici_of_Ioi_eq_zero _ _ Γ.val.max
  · exact DH.naIntrinsicDuistermaatHeckman_Ioi_max ω Γ
  · simp
  · intro t ht
    rw [DH.naIntrinsicDuistermaatHeckman_Ici ω Γ ⟨t, ht⟩,
      SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero,
      Measure.dirac_apply_of_mem (show Γ.val.max ∈ Ici t from ht.le)]

/-- Output comparison, after the actual flag pushforward has been computed. -/
theorem naDuistermaatHeckman_eq_intrinsic (ω : KahlerBackground 0 F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman F hbig Γ = DH.naIntrinsicDuistermaatHeckman ω Γ := by
  rw [naDuistermaatHeckman_eq_dirac, naIntrinsicDuistermaatHeckman_eq_dirac]

/-- Literal source total mass in the actual zero-dimensional flag branch. -/
theorem naDuistermaatHeckman_univ
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman F hbig Γ univ = sourceNAVolume (sourcePositiveTestCurveToNA Γ) := by
  rw [naDuistermaatHeckman_eq_dirac, sourceNAVolume_eq_one F Γ,
    Measure.dirac_apply_of_mem (mem_univ Γ.val.max)]

/-- Every positive integer source moment for the actual zero-dimensional
flag measure, retaining the original extended integral and weighted interval. -/
theorem naDuistermaatHeckman_moment
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) (p : ℕ) (hp : 0 < p) :
    SGPT.Convex.extendedSignedIntegral (naDuistermaatHeckman F hbig Γ)
        (fun t : ℝ => (t : EReal) ^ p) =
      ((Γ.val.max ^ p * (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal : ℝ) : EReal) +
        (p : EReal) * SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio Γ.val.max))
          (fun t : ℝ => ((t ^ (p - 1) * (naSliceVolume F Γ t -
            (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal) : ℝ) : EReal)) := by
  have hmoment :=
    (SourceTestCurveAllDimensions.okounkovTestCurve F hbig Γ.val).polynomial_moment_eq p hp
  have hleft : SGPT.Convex.extendedSignedIntegral (naDuistermaatHeckman F hbig Γ)
      (fun t : ℝ => (t : EReal) ^ p) = ((Γ.val.max ^ p : ℝ) : EReal) := by
    simpa [naDuistermaatHeckman, SGPT.AlmostSemigroup.BrunnMinkowski.volume_zero_dimensional,
      SGPT.Convex.extendedSignedIntegral] using hmoment
  have hzero : SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio Γ.val.max))
      (fun t : ℝ => ((t ^ (p - 1) * (naSliceVolume F Γ t - 1) : ℝ) : EReal)) = 0 := by
    calc
      _ = SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio Γ.val.max)) (fun _ => 0) := by
        apply DH.extendedSignedIntegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
        rw [naSliceVolume_eq_one F Γ ht, sub_self, mul_zero, EReal.coe_zero]
      _ = 0 := by simp [SGPT.Convex.extendedSignedIntegral]
  rw [hleft, sourceNAVolume_eq_one F Γ, ENNReal.toReal_one, mul_one, hzero, mul_zero, add_zero]

end Zero
end SGPT.NAPotential.DHSource
