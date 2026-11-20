import SGPT.Projective.NativePositiveRestriction
import SGPT.Projective.NativeBertiniWholeMember

/-! Actual whole native regular complete-intersection towers. Every power,
section and full subtype is manufactured before any test form is considered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Output DATA of one actual regular cut: literal original positive power,
original global sections, original map and its actual whole regular member.
It carries no period or complete-intersection degree equality field. -/
structure NativeRegularCut (L : NativePositiveLine n X) where
  power : ℕ
  power_pos : 0 < power
  ambient : ℕ
  sections : Fin (ambient + 1) → HolomorphicSections (n := n)
    (positivePower L.bundle (power - 1)).Fiber
  generated : ∀ x : X, ∃ i, sections i x ≠ 0
  hyperplane : HyperplaneSpace ambient
  holomorphic : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel ambient) ∞
    (sourceNativeFiniteSectionProjectiveMap (positivePower L.bundle (power - 1)) sections generated)
  regular : IsSmoothHypersurfaceMember n
    (sourceNativeFiniteSectionProjectiveMap (positivePower L.bundle (power - 1)) sections generated) hyperplane

/-- The proved original Kodaira/Bertini producers manufacture the whole cut. -/
theorem exists_nativeRegularCut [CompactSpace X] (hn : 0 < n) (L : NativePositiveLine n X) :
    Nonempty (NativeRegularCut L) := by
  obtain ⟨d, hd, N, s, hgen, l, hp, hl, _⟩ := exists_positivePower_regularSection hn
    L.bundle L.smooth L.curvature L.own L.positive
  exact ⟨⟨d, hd, N, s, hgen, l, hp, hl⟩⟩

namespace NativeRegularCut
variable {L : NativePositiveLine n X} (D : NativeRegularCut L)

/-- SAME original finite-family projective map; no replacement embedding. -/
def projectiveMap : X → ComplexProjectiveSpace D.ambient :=
  sourceNativeFiniteSectionProjectiveMap (positivePower L.bundle (D.power - 1)) D.sections D.generated

/-- The entire zero subtype is retained, including ALL its components. -/
def carrier : Set X := member D.projectiveMap D.hyperplane

theorem regularAtDim : ∀ x ∈ D.carrier, RegularAtDim (n := n) D.carrier x (n - 1) :=
  fun _ hx => regularAtDim_member D.projectiveMap D.holomorphic D.regular hx

instance carrierCharts : ChartedSpace (ComplexModel (n - 1)) D.carrier :=
  SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n 1) D.regularAtDim

instance carrierComplex : IsComplexManifold (n - 1) D.carrier :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le n 1) D.regularAtDim

instance carrierCompact [CompactSpace X] : CompactSpace D.carrier :=
  wholeMember_compact D.projectiveMap D.holomorphic D.hyperplane

/-- The actual inclusion of the SAME whole regular member. -/
def inclusion : ContMDiffMap 𝓘(ℂ, ComplexModel (n - 1)) 𝓘(ℂ, ComplexModel n) D.carrier X ∞ :=
  ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val (Nat.sub_le n 1) D.regularAtDim⟩

/-- The actual original section whose entire zero set is the chosen member. -/
def cuttingSection : HolomorphicSections (n := n) (positivePower L.bundle (D.power - 1)).Fiber :=
  linearSection _ D.sections D.hyperplane

/-- The SAME original section remains densely nonzero on disconnected X. -/
theorem section_dense (hn : 0 < n) :
    ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, D.cuttingSection y ≠ 0 :=
  linearSection_dense_nonzero hn _ D.sections D.generated D.hyperplane D.holomorphic D.regular

/-- Restrict the SAME next original native bundle/physical metric to this
exact whole member; actual own curvature and positivity are produced. -/
def restrictPositive (B : NativePositiveLine n X) : NativePositiveLine (n - 1) D.carrier :=
  B.restrict (Nat.sub_le n 1) D.regularAtDim

/-- The original background is restricted through the literal inclusion. -/
def restrictKahler (κ : KahlerBackground n X) : KahlerBackground (n - 1) D.carrier :=
  SubmanifoldKahlerRestriction.kahlerBackground (Nat.sub_le n 1) D.regularAtDim κ

/-- Exact literal pullback of the original own curvature at each stage. -/
theorem restrictPositive_curvature (B : NativePositiveLine n X) :
    (D.restrictPositive B).curvature = ClosedRealOneOneForm.pullback D.inclusion.contMDiff B.curvature := rfl

end NativeRegularCut

/-- An actual recursive whole regular tower. At every step the tail bundles
are the SAME actual native physical pullbacks, not only chosen class representatives. -/
def WholeNativeCITower : (k : ℕ) → (X : Type) → [TopologicalSpace X] →
    [ChartedSpace (ComplexModel (k + 1)) X] → [IsComplexManifold (k + 1) X] →
    (Fin k → NativePositiveLine (k + 1) X) → Type 1
  | 0, _, _, _, _, _ => PUnit
  | k + 1, _, _, _, _, P =>
    Σ D : NativeRegularCut (P 0),
      let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
      let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
      WholeNativeCITower k D.carrier (fun i => D.restrictPositive (P i.succ))

/-- ALL powers/sections/full members are manufactured before any test form.
The zero-cut case is the same original curve. Empty/disconnected members
are retained, and no current or degree identity is a producer premise. -/
theorem exists_wholeNativeCITower (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    (P : Fin k → NativePositiveLine (k + 1) X) : Nonempty (WholeNativeCITower k X P) := by
  cases k with
  | zero => exact ⟨PUnit.unit⟩
  | succ k =>
      obtain ⟨D⟩ := exists_nativeRegularCut (by omega : 0 < k + 1 + 1) (P 0)
      let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
      let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
      obtain ⟨T⟩ := exists_wholeNativeCITower k D.carrier (fun i => D.restrictPositive (P i.succ))
      exact ⟨⟨D, T⟩⟩
termination_by k

namespace WholeNativeCITower

/-- The actual positive powers chosen in the SAME order as the original bundles. -/
def powers : (k : ℕ) → {X : Type} → [TopologicalSpace X] →
    [ChartedSpace (ComplexModel (k + 1)) X] → [IsComplexManifold (k + 1) X] →
    {P : Fin k → NativePositiveLine (k + 1) X} → WholeNativeCITower k X P → Fin k → ℕ
  | 0, _, _, _, _, _, _ => Fin.elim0
  | k + 1, _, _, _, _, _, T => by
      let : ChartedSpace (ComplexModel (k + 1)) T.1.carrier := T.1.carrierCharts
      let : IsComplexManifold (k + 1) T.1.carrier := T.1.carrierComplex
      exact Fin.cons T.1.power (powers k T.2)

theorem powers_pos (k : ℕ) {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P) :
    ∀ i, 0 < powers k T i := by
  cases k with
  | zero => intro i; exact Fin.elim0 i
  | succ k =>
      let : ChartedSpace (ComplexModel (k + 1)) T.1.carrier := T.1.carrierCharts
      let : IsComplexManifold (k + 1) T.1.carrier := T.1.carrierComplex
      intro i
      exact Fin.cases T.1.power_pos (fun j => powers_pos k T.2 j) i
termination_by k

end WholeNativeCITower
end SGPT.Projective.NumEq.CompleteIntersections
