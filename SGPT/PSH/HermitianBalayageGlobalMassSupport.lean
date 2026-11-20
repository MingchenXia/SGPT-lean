import SGPT.PSH.HermitianBalayageMassSupportLocal
import SGPT.PSH.HermitianGlobalMeasure

/-!
# Actual global mass support of the bounded Hermitian extremal

The original local background measures vanish off the prescribed closed
set by the full frozen-ball argument. The genuine global Hermitian measure
has exactly those patch readings, so a manufactured finite chart cover
proves that the same canonical global measure is carried by the set.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremal HermitianGlobalProducts

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual canonical global Hermitian measure of the bounded original
regularized extremal is carried by the original prescribed closed set. -/
theorem global_extremal_measure_compl_eq_zero
    (omega : Background (m + 1) M) (K : Set M) (hK : IsClosed K)
    (hE : IsHermitianPSH omega (regularizedExtremal omega K))
    {S : ℝ} (hES : ∀ x, regularizedExtremal omega K x ≤ (S : EReal)) :
    globalMixedMeasure omega (fun _ => regularizedExtremal omega K) (fun _ => hE)
      (fun _ => ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩) Kᶜ = 0 := by
  classical
  let E := regularizedExtremal omega K
  let hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ E x ∧ E x ≤ (b : EReal) :=
    ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
  let μ := globalMixedMeasure omega (fun _ => E) (fun _ => hE) (fun _ => hb)
  let C := Classical.choice (nonempty_backgroundFiniteCover omega)
  have hzero (i : Fin C.count) : μ (Kᶜ ∩ ((C.patch i).geometry.source : Set M)) = 0 := by
    have h := congrArg (fun ν : Measure M => ν Kᶜ)
      (globalMixedMeasure_restrict_patch (omega := omega) (fun _ => E) (fun _ => hE)
        (fun _ => hb) (C.patch i))
    rw [Measure.restrict_apply hK.measurableSet.compl] at h
    exact h.trans (background_extremal_pushMeasure_compl_eq_zero omega K hK (C.patch i) hE hES)
  have hcover : Kᶜ ⊆ ⋃ i : Fin C.count, Kᶜ ∩ ((C.patch i).geometry.source : Set M) := by
    intro x hx
    obtain ⟨i, hi⟩ := C.covers x
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  exact measure_mono_null hcover (measure_iUnion_null hzero)

variable [ConnectedSpace M]

/-- In the actual bounded branch, both the Hermitian PSH class of the
original regularized extremal and support of its canonical global measure
are produced from the finite bound. No class or support certificate for
the extremal is assumed. -/
theorem exists_bounded_extremal_mass_supported
    (omega : Background (m + 1) M) (K : Set M) (hK : IsClosed K)
    (S : ℝ) (hES : ∀ x, regularizedExtremal omega K x ≤ (S : EReal)) :
    ∃ hE : IsHermitianPSH omega (regularizedExtremal omega K),
      globalMixedMeasure omega (fun _ => regularizedExtremal omega K) (fun _ => hE)
        (fun _ => ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩) Kᶜ = 0 := by
  obtain ⟨_, hE, _, _⟩ := bounded_regularizedExtremal_of_not_pole omega K
    (not_pole_of_bounded_regularizedExtremal omega K S hES)
  exact ⟨hE, global_extremal_measure_compl_eq_zero omega K hK hE hES⟩

end SGPT.PSH.HermitianBalayage
