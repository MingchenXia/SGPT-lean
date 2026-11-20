import SGPT.Projective.NativeCITower
import SGPT.Foundations.Analysis.Pending.FormPullbackCompMixed

/-! The actual terminal compact native curve and original inclusion of the
whole regular CI tower. No component, period or intersection certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BlowupTowers

/-- Ordinary native compact curve geometry over the original manifold.
The source is the existing CMfd object with actual topology and native
charts; the inclusion is an actual ordinary ContMDiffMap. -/
structure NativeCompactCurveOver (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] where
  source : CMfd.{0} 1
  [compact : CompactSpace source]
  background : KahlerBackground 1 source
  inclusion : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) source X ∞

attribute [instance] NativeCompactCurveOver.compact

namespace WholeNativeCITower

/-- The SAME terminal whole subtype, with its actual induced compact
complex curve structure, actual restricted background and actual composed
holomorphic inclusion into the original manifold. -/
def terminal (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P)
    (κ : KahlerBackground (k + 1) X) : NativeCompactCurveOver (k + 1) X := by
  cases k with
  | zero =>
      exact {
        source := CMfd.of X
        compact := inferInstance
        background := κ
        inclusion := ⟨id, contMDiff_id⟩ }
  | succ k =>
      let D := T.1
      let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
      let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
      let C := terminal k D.carrier T.2 (D.restrictKahler κ)
      exact {
        source := C.source
        compact := C.compact
        background := C.background
        inclusion := ⟨D.inclusion ∘ C.inclusion,
          D.inclusion.contMDiff.comp C.inclusion.contMDiff⟩ }
termination_by k

/-- Every component of the actual terminal curve embeds into the same
original manifold through literal subtype inclusions. -/
theorem terminal_injective (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P)
    (κ : KahlerBackground (k + 1) X) : Function.Injective (terminal k X T κ).inclusion := by
  cases k with
  | zero =>
      rw [terminal]
      exact Function.injective_id
  | succ k =>
      rw [terminal]
      let D := T.1
      let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
      let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
      exact Subtype.val_injective.comp
        (terminal_injective k D.carrier T.2 (D.restrictKahler κ))
termination_by k

/-- Compactness and the actual holomorphic inclusion give a genuine native
closed embedding of the entire terminal curve, without connectedness. -/
theorem terminal_isClosedEmbedding (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P)
    (κ : KahlerBackground (k + 1) X) : Topology.IsClosedEmbedding (terminal k X T κ).inclusion :=
  (terminal k X T κ).inclusion.contMDiff.continuous.isClosedEmbedding (terminal_injective k X T κ)

/-- The actual terminal Kähler form is the original background pulled back
through the SAME composed original inclusion, in every actual chart. -/
theorem terminal_background_geometrically (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P)
    (κ : KahlerBackground (k + 1) X) :
    (terminal k X T κ).background.form.val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (terminal k X T κ).inclusion.contMDiff κ.form).val := by
  cases k with
  | zero =>
      rw [terminal]
      exact (SmoothRealForm.pullback_id_geometricallyEq κ.form.val).symm
  | succ k =>
      rw [terminal]
      let D := T.1
      let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
      let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
      let C := terminal k D.carrier T.2 (D.restrictKahler κ)
      exact (terminal_background_geometrically k D.carrier T.2 (D.restrictKahler κ)).trans
        (FormPullbackCompMixed.pullback_comp_geometricallyEq
          D.inclusion.contMDiff C.inclusion.contMDiff κ.form.val).symm
termination_by k

end WholeNativeCITower

/-- Actual whole complete-intersection curve geometry is produced from the
same original native positive bundles, before ANY test form is introduced.
All stages, powers, physical bundle restrictions and original section data
remain in T; its terminal is an actual compact native CMfd 1 with a genuine
closed holomorphic inclusion and actual original pulled-back Kähler form. -/
theorem exists_wholeNativeCICurve (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    (P : Fin k → NativePositiveLine (k + 1) X) (κ : KahlerBackground (k + 1) X) :
    ∃ T : WholeNativeCITower k X P,
      Topology.IsClosedEmbedding (WholeNativeCITower.terminal k X T κ).inclusion ∧
        ∀ i, 0 < WholeNativeCITower.powers k T i := by
  obtain ⟨T⟩ := exists_wholeNativeCITower k X P
  exact ⟨T, WholeNativeCITower.terminal_isClosedEmbedding k X T κ,
    WholeNativeCITower.powers_pos k T⟩

end SGPT.Projective.NumEq.CompleteIntersections
