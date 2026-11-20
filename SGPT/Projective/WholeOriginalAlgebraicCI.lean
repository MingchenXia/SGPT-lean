import SGPT.Projective.OriginalAlgebraicRegularCut

/-! Actual WHOLE ORIGINAL algebraic CI choices and terminal scheme,
before ANY test form. Blueprint: whole-original-algebraic-ci.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass

local instance towerPointTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance towerPointCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d
local instance towerPointManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

/-- Actual original schemes, original positive physical restrictions and all original section/ideal readers.
No period or degree equality field. -/
def WholeOriginalCITower : (k : ℕ) → {X : Scheme.{0}} → (f : X ⟶ Spec (.of ℂ)) →
    [SmoothOfRelativeDimension (k + 1) f] → [IsSeparated f] → [QuasiCompact f] →
    (E : ClosedProjectiveEmbedding f) → (Fin k → OriginalPositiveLine f (k + 1) E) → Type 1
  | 0, _, _, _, _, _, _, _ => PUnit
  | k + 1, _, f, _, _, _, E, P =>
    Σ C : OriginalRegularCut f (k + 1) E (P 0),
      WholeOriginalCITower k (C.inclusion ≫ f) C.embedding (fun i => C.restrictLine (P i.succ))

/-- The SAME actual original algebraic geometry is manufactured before any test form. -/
theorem exists_wholeOriginalCITower (k : ℕ) {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (P : Fin k → OriginalPositiveLine f (k + 1) E) :
    Nonempty (WholeOriginalCITower k f E P) := by
  cases k with
  | zero => exact ⟨PUnit.unit⟩
  | succ k =>
      obtain ⟨C⟩ := exists_originalRegularCut f (k + 1) E (P 0)
      obtain ⟨T⟩ := exists_wholeOriginalCITower k (C.inclusion ≫ f) C.embedding
        (fun i => C.restrictLine (P i.succ))
      exact ⟨⟨C, T⟩⟩
termination_by k

/-- Only actual original algebraic curve and original closed immersion data.
No analytic algebraization, period, degree or connected-component certificate. -/
structure OriginalCurveOver {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) where
  source : Scheme.{0}
  structureMap : source ⟶ Spec (.of ℂ)
  inclusion : source ⟶ X
  over_base : inclusion ≫ f = structureMap
  closed : IsClosedImmersion inclusion
  smooth : SmoothOfRelativeDimension 1 structureMap

namespace OriginalCurveOver
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (C : OriginalCurveOver f)

instance inclusion_closedImmersion : IsClosedImmersion C.inclusion := C.closed
instance structure_smooth : SmoothOfRelativeDimension 1 C.structureMap := C.smooth

/-- The actual total original inclusion followed by the actual original embedding. -/
def embedding (E : ClosedProjectiveEmbedding f) : ClosedProjectiveEmbedding C.structureMap where
  ambientDimension := E.ambientDimension
  map := C.inclusion ≫ E.map
  closedImmersion := inferInstance
  over_base := by rw [Category.assoc, E.over_base, C.over_base]

end OriginalCurveOver

namespace WholeOriginalCITower

/-- The actual positive integer powers, in the SAME original bundle order. -/
def powers : (k : ℕ) → {X : Scheme.{0}} → {f : X ⟶ Spec (.of ℂ)} →
    [SmoothOfRelativeDimension (k + 1) f] → [IsSeparated f] → [QuasiCompact f] →
    {E : ClosedProjectiveEmbedding f} → {P : Fin k → OriginalPositiveLine f (k + 1) E} →
    WholeOriginalCITower k f E P → Fin k → ℕ
  | 0, _, _, _, _, _, _, _, _ => Fin.elim0
  | k + 1, _, _, _, _, _, _, _, T => Fin.cons T.1.nativeCut.power (powers k T.2)

theorem powers_pos (k : ℕ) {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    {E : ClosedProjectiveEmbedding f} {P : Fin k → OriginalPositiveLine f (k + 1) E}
    (T : WholeOriginalCITower k f E P) : ∀ i, 0 < powers k T i := by
  cases k with
  | zero => intro i; exact Fin.elim0 i
  | succ k =>
      intro i
      exact Fin.cases T.1.nativeCut.power_pos (fun j => powers_pos k T.2 j) i
termination_by k

/-- The actual ENTIRE original terminal scheme, retaining its genuine original structural map. -/
def terminal (k : ℕ) {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    {E : ClosedProjectiveEmbedding f} {P : Fin k → OriginalPositiveLine f (k + 1) E}
    (T : WholeOriginalCITower k f E P) : OriginalCurveOver f := by
  cases k with
  | zero =>
      exact
        { source := X
          structureMap := f
          inclusion := 𝟙 X
          over_base := Category.id_comp f
          closed := inferInstance
          smooth := inferInstance }
  | succ k =>
      let C := T.1
      let Z := terminal k (C.inclusion ≫ f) T.2
      exact
        { source := Z.source
          structureMap := Z.structureMap
          inclusion := Z.inclusion ≫ C.inclusion
          over_base := by rw [Category.assoc, Z.over_base]
          closed := inferInstance
          smooth := Z.smooth }
termination_by k

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
