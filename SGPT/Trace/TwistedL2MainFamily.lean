import SGPT.Trace.TwistedL2MainPiece
import SGPT.Trace.TwistedL2MainRiesz

/-!
# Finite families of actual local test pieces

The free vector space on local test pieces makes finite sums in unrelated charts
and frames honest complex-linear test objects. Each generator uses an actual
smooth positive chart density and an actual compactly supported test field.
The adjoint image lives in the genuine weighted `H₁` realization. The conjugate
of the data pairing is linear, as required by the Riesz step. The quantitative
functional bound and the weak-to-holomorphic assembly remain separate work.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set MeasureTheory Bundle
open scoped ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- A genuine local test piece, including its actual chart-density witness. -/
structure LocalTestPiece where
  chart : ComplexChart n X
  frame : AtlasFrame T.L
  density : ComplexModel n → ℝ
  field : ComplexModel n → ComplexModel n
  density_spec : IsChartDensity T.μ chart density
  field_spec : IsLocalTestField T.L T.U chart frame field

/-- The genuine local adjoint test as an `L²(μ|U)` element, in the unit frame. -/
def LocalTestPiece.adjoint (p : T.LocalTestPiece) : Lp ℂ 2 (T.μ.restrict T.U) :=
  T.tstarL2 p.density_spec p.field_spec

/-- The actual local `∂̄G` pairing, conjugate-linear in the test field. -/
def LocalTestPiece.pairing (p : T.LocalTestPiece) : ℂ :=
  T.localDataPairing p.chart p.frame p.density p.field

/-- Scaling an actual local field preserves its support and smoothness. -/
def LocalTestPiece.scale (p : T.LocalTestPiece) (κ : ℂ) : T.LocalTestPiece where
  chart := p.chart
  frame := p.frame
  density := p.density
  field := κ • p.field
  density_spec := p.density_spec
  field_spec := T.isLocalTestField_smul p.field_spec κ

/-- The data pairing is conjugate-linear under this actual scaling. -/
theorem LocalTestPiece.pairing_scale (p : T.LocalTestPiece) (κ : ℂ) :
    (LocalTestPiece.scale T p κ).pairing = conj κ * p.pairing := by
  exact T.localDataPairing_smul p.chart p.frame p.density p.field κ

omit [BorelSpace X] in
/-- The unit-frame coordinate is complex-linear in the actual section. -/
theorem H1coord_smul (s : (x : X) → T.L.Fiber x) (κ : ℂ) (x : X) :
    T.H1coord (fun y => κ • s y) x = κ * T.H1coord s x := by
  simp only [H1coord, inner_smul_right]
  ring

/-- The Hilbert-space adjoint image is complex-linear under the same
actual scaling of the local field. -/
theorem LocalTestPiece.adjoint_scale (p : T.LocalTestPiece) (κ : ℂ) :
    (LocalTestPiece.scale T p κ).adjoint = κ • p.adjoint := by
  apply Lp.ext
  filter_upwards [
    (T.memLp_H1coord_localTStar p.density_spec (LocalTestPiece.scale T p κ).field_spec).coeFn_toLp,
    (T.memLp_H1coord_localTStar p.density_spec p.field_spec).coeFn_toLp,
    Lp.coeFn_smul κ p.adjoint] with x hleft hright hsmul
  change ((T.memLp_H1coord_localTStar p.density_spec (LocalTestPiece.scale T p κ).field_spec).toLp
      (T.H1coord (T.localTStar p.chart p.frame p.density (κ • p.field)))) x =
      (κ • p.adjoint : Lp ℂ 2 (T.μ.restrict T.U)) x
  dsimp [LocalTestPiece.scale] at hleft
  change (p.adjoint : Lp ℂ 2 (T.μ.restrict T.U)) x = _ at hright
  rw [hleft, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, hright]
  have hs : T.localTStar p.chart p.frame p.density (κ • p.field) =
      (fun y => κ • T.localTStar p.chart p.frame p.density p.field y) := by
    funext y
    exact T.localTStar_smul p.field_spec.1 κ y
  rw [hs]
  exact T.H1coord_smul _ κ x

/-- The free complex vector space on the actual local pieces. -/
abbrev TestFamilies := T.LocalTestPiece →₀ ℂ

/-- The genuine adjoint image of any finite formal combination of pieces. -/
def familyAdjoint : T.TestFamilies →ₗ[ℂ] Lp ℂ 2 (T.μ.restrict T.U) :=
  Finsupp.linearCombination ℂ (fun p : T.LocalTestPiece => p.adjoint)

/-- Conjugating the actual data pairing makes it a complex-linear map. -/
def familyData : T.TestFamilies →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun p : T.LocalTestPiece => conj p.pairing)

open Classical in
@[simp] theorem familyAdjoint_single (p : T.LocalTestPiece) :
    T.familyAdjoint (Finsupp.single p 1) = p.adjoint := by
  classical
  simp [familyAdjoint]

omit [BorelSpace X] in
open Classical in
@[simp] theorem familyData_single (p : T.LocalTestPiece) :
    T.familyData (Finsupp.single p 1) = conj p.pairing := by
  classical
  simp [familyData]

end TwistedDatum
end SGPT.Trace.TwistedL2
