import SGPT.PSH.HermitianProductOverlap

/-!
# The genuine global nonclosed Hermitian mixed measure

Every local measure is the positive Riesz trace of the literal background
expansion. Actual holomorphic covariance and correction invariance produce
its overlap equalities internally. The resulting measure has the prescribed
reading on every correction patch, is independent of the finite cover, and
has finite total mass on compact manifolds.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] {omega : Background (m + 1) M}

namespace BackgroundFiniteCover

/-- Ordinary overlap equalities are produced from original class members;
they are never a premise of the global Hermitian measure producer. -/
theorem traceMeasuresAgree (C : BackgroundFiniteCover omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    TraceMeasuresAgree (fun j => (C.patch j).geometry)
      (fun j => (C.patch j).current u) (fun j => (C.patch j).current_isPositive u hu hb) :=
  traceMeasuresAgree_of_coordinate_covariance _ _ _
    (fun i j => (C.patch i).current_trace_overlap (C.patch j) u hu hb)

/-- The disjoint finite gluing of the original local Hermitian products. -/
def measure (C : BackgroundFiniteCover omega) (u : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) : Measure M :=
  glueTraceMeasure (fun j => (C.patch j).geometry) (fun j => (C.patch j).current u)
    (fun j => (C.patch j).current_isPositive u hu hb)

/-- Every genuine correction patch has its original local product reading,
whether or not it was selected in the finite cover. -/
theorem measure_restrict_patch (C : BackgroundFiniteCover omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) :
    (C.measure u hu hb).restrict P.geometry.source =
      P.geometry.pushTraceMeasure (P.current u) (P.current_isPositive u hu hb) := by
  let ν := P.geometry.pushTraceMeasure (P.current u) (P.current_isPositive u hu hb)
  have hcover : (P.geometry.source : Set M) ⊆
      ⋃ j, ((C.patch j).geometry.source : Set M) := by
    intro x _
    obtain ⟨j, hj⟩ := C.covers x
    exact mem_iUnion.mpr ⟨j, hj⟩
  change (FiniteMeasureGluing.glue (fun j => ((C.patch j).geometry.source : Set M))
    (fun j => (C.patch j).geometry.pushTraceMeasure ((C.patch j).current u)
      ((C.patch j).current_isPositive u hu hb))).restrict P.geometry.source = ν
  calc
    _ = ν.restrict P.geometry.source :=
      FiniteMeasureGluing.glue_restrict _ _
        (fun j => (C.patch j).geometry.source.isOpen.measurableSet)
        P.geometry.source.isOpen.measurableSet hcover ν
        (fun j => (C.patch j).geometry.pushMeasure_restrict_inter_eq P.geometry
          ((C.patch j).current_trace_overlap P u hu hb))
    _ = ν := P.geometry.pushMeasure_restrict_source (P.current_isPositive u hu hb).traceMeasure

/-- Actual local trace finiteness and compactness give finite total mass. -/
theorem measure_isFiniteMeasure [CompactSpace M] (C : BackgroundFiniteCover omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsFiniteMeasure (C.measure u hu hb) :=
  glueTraceMeasure_isFiniteMeasure _ _ _ C.covers (C.traceMeasuresAgree u hu hb)

/-- The global measure is independent of the actual finite cover. -/
theorem measure_independent_cover (C D : BackgroundFiniteCover omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    C.measure u hu hb = D.measure u hu hb := by
  apply glueTraceMeasure_unique _ _ _ C.covers (C.traceMeasuresAgree u hu hb)
  intro j
  exact D.measure_restrict_patch u hu hb (C.patch j)

end BackgroundFiniteCover

variable [CompactSpace M]

/-- The global nonclosed Hermitian mixed measure of the original bounded
tuple. Both the finite cover and every overlap equality are internal. -/
def globalMixedMeasure (omega : Background (m + 1) M)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) : Measure M :=
  (Classical.choice (nonempty_backgroundFiniteCover omega)).measure u hu hb

/-- The global product retains the actual current trace on every chart patch. -/
theorem globalMixedMeasure_restrict_patch
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) :
    (globalMixedMeasure omega u hu hb).restrict P.geometry.source =
      P.geometry.pushTraceMeasure (P.current u) (P.current_isPositive u hu hb) :=
  (Classical.choice (nonempty_backgroundFiniteCover omega)).measure_restrict_patch u hu hb P

/-- The actual global Hermitian mixed product is finite on a compact manifold. -/
theorem globalMixedMeasure_isFiniteMeasure
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsFiniteMeasure (globalMixedMeasure omega u hu hb) :=
  (Classical.choice (nonempty_backgroundFiniteCover omega)).measure_isFiniteMeasure u hu hb

/-- Every original finite cover constructs this same global mixed measure. -/
theorem globalMixedMeasure_eq_cover (C : BackgroundFiniteCover omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    globalMixedMeasure omega u hu hb = C.measure u hu hb :=
  BackgroundFiniteCover.measure_independent_cover _ C u hu hb

end SGPT.PSH.HermitianGlobalProducts
