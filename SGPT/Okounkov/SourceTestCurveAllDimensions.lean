import SGPT.Okounkov.ZeroSourceTestCurve
import SGPT.Okounkov.ValuativeTestCurveEnergyComparison

/-!
# Revised source Okounkov test curves in every dimension

Source: revised SGPT 69360cfd, `thm:Okountescurvex`, in all natural dimensions.

This dimension-dispatch API uses the genuine zero-dimensional
source construction and the existing positive-dimensional source construction.
It retains the original curve, cutoff, slice potentials and original limit.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov.SourceTestCurveAllDimensions

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-- The original general body, with its literal source construction in
each dimension. The zero branch retains the source intersections. -/
def generalBody {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (θ : ClosedRealOneOneForm n F.carrier) (u : ThetaPshL1 θ.val) : Set (Fin n → ℝ) := by
  cases n with
  | zero => exact ZeroSource.generalBody F θ u.val u.property
  | succ m => exact PartialBody.generalPartialBody F θ u.val

/-- The convex body with the exact original source general-body carrier. -/
def partialConvexBody {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (θ : ClosedRealOneOneForm n F.carrier) (u : ThetaPshL1 θ.val) :
    ConvexBody (EuclideanSpace ℝ (Fin n)) := by
  cases n with
  | zero => exact ZeroSource.partialConvexBody F θ u.val u.property
  | succ m => exact PartialBody.partialConvexBody F θ u

/-- Exact source carrier readback in every dimension, including zero. -/
theorem coe_partialConvexBody {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (θ : ClosedRealOneOneForm n F.carrier) (u : ThetaPshL1 θ.val) :
    (partialConvexBody F θ u : Set (EuclideanSpace ℝ (Fin n))) =
      TranscendentalMain.euclideanImage (generalBody F θ u) := by
  cases n <;> rfl

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n) [MeasurableSpace F.carrier]
  [BorelSpace F.carrier] {θ : AtlasClosedRealOneOneForm (ofFixedModel n F.carrier)}

/-- The actual original source limit in the actual native potential space. -/
def nativeLimit (Γ : SourceTestCurve θ) : ThetaPshL1 (atlasClosedFormToNative θ).val :=
  ⟨sourceTestCurveLimit Γ.toSourceTestCurvePredata,
    (isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.limit_thetaPSH⟩

/-- The actual original slice in the actual native potential space. -/
def nativeSlice (Γ : SourceTestCurve θ) (τ : Iio Γ.max) :
    ThetaPshL1 (atlasClosedFormToNative θ).val :=
  ⟨Γ.potential τ, Γ.native_thetaPSH τ⟩

/-- The original limit body has the genuine positive Euclidean volume
required by the standing source definition of an Okounkov test curve. -/
theorem volume_limitBody_pos (Γ : SourceTestCurve θ) :
    0 < volume (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit F Γ) :
      Set (EuclideanSpace ℝ (Fin n))) := by
  cases n with
  | zero =>
      apply pos_iff_ne_zero.mpr
      intro hzero
      have hreal := SGPT.AlmostSemigroup.BrunnMinkowski.volume_zero_dimensional
        (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit F Γ))
      rw [measureReal_def, hzero, ENNReal.toReal_zero] at hreal
      exact zero_ne_one hreal
  | succ m =>
      change 0 < volume (TranscendentalMain.euclideanImage
        (PartialBody.generalPartialBody F (atlasClosedFormToNative θ)
          (sourceTestCurveLimit Γ.toSourceTestCurvePredata)))
      rw [PartialBody.volume_euclideanImage]
      exact PartialBody.volume_generalPartialBody_pos
        (nativeLimit F Γ).property Γ.positiveLimitMass

/-- Source `thm:Okountescurvex`, actual family construction in all dimensions. -/
def okounkovTestCurve
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) :
    TestCurve (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit F Γ)) := by
  cases n with
  | zero => exact ZeroSource.okounkovTestCurve F Γ
  | succ m => exact Valuative.okounkovTestCurve (F := F) hbig Γ

/-- Exact original cutoff, with no reparametrization. -/
@[simp] theorem okounkovTestCurve_max
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) : (okounkovTestCurve F hbig Γ).max = Γ.max := by
  cases n <;> rfl

/-- Every family member is the original general partial body of the same
actual source slice at the exact original parameter. -/
theorem coe_okounkovTestCurve_body
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) (τ : Iio Γ.max) :
    ((okounkovTestCurve F hbig Γ).body
        ⟨τ.val, by simpa only [okounkovTestCurve_max] using τ.property⟩ :
        Set (EuclideanSpace ℝ (Fin n))) =
      TranscendentalMain.euclideanImage
        (generalBody F (atlasClosedFormToNative θ) (nativeSlice F Γ τ)) := by
  cases n <;> rfl

/-- Source `thm:Okountescurvex`, boundedness clause in all dimensions. -/
theorem okounkovTestCurve_isBounded
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) :
    (okounkovTestCurve F hbig Γ).IsBounded := by
  cases n with
  | zero => exact ZeroSource.okounkovTestCurve_isBounded F Γ
  | succ m => exact Valuative.okounkovTestCurve_isBounded hbig hΓ

/-- Revised source energy comparison in all dimensions. Only the actual
original base is assumed I-model; there is no slice I-model premise. -/
theorem sourceTestCurveEnergy_le_okounkovTestCurve_energy
    (ω : KahlerBackground n F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ) :
    sourceTestCurveEnergy ω hφ Γ hΓ ≤ (okounkovTestCurve F hbig Γ).energy := by
  cases n with
  | zero => exact (ZeroSource.okounkovTestCurve_energy_eq F ω hφ Γ hΓ).symm.le
  | succ m => exact Valuative.sourceTestCurveEnergy_le_okounkovTestCurve_energy ω hbig hΓ hφI

/-- Revised source finite-energy transfer in all dimensions, using only
the I-model base and the original finite-energy membership. -/
theorem okounkovTestCurve_hasFiniteEnergy_of_base_iModel
    (ω : KahlerBackground n F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ)
    (hE : Γ ∈ SourceFiniteEnergyTestCurves ω θ φ hφ) :
    (okounkovTestCurve F hbig Γ).HasFiniteEnergy := by
  obtain ⟨hΓ, hfinite⟩ := hE
  exact hfinite.trans_le
    (sourceTestCurveEnergy_le_okounkovTestCurve_energy F ω hbig hΓ hφI)

/-- Revised source equality clause in all dimensions, with the original
source slice I-model hypotheses retained. -/
theorem okounkovTestCurve_energy_eq_of_iModel
    (ω : KahlerBackground n F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceIModelTestCurves θ φ hφ)
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ) :
    (okounkovTestCurve F hbig Γ).energy = sourceTestCurveEnergy ω hφ Γ hΓ.1 := by
  cases n with
  | zero => exact ZeroSource.okounkovTestCurve_energy_eq F ω hφ Γ hΓ.1
  | succ m => exact Valuative.okounkovTestCurve_energy_eq_of_iModel ω hbig hΓ hφI

end SGPT.Okounkov.SourceTestCurveAllDimensions
